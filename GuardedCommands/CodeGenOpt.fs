namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018, 07-01-2021
// A part of the program is directly copied from the file 
// File MicroC/Contcomp.fs of the MicroC compiler by Peter Sestoft


open Machine

open GuardedCommands.Frontend.AST

module CodeGenerationOpt =
 
    type Var = 
      | GloVar of int                   (* absolute address in stack           *)
      | LocVar of int                   (* address relative to bottom of frame *)
 
 (* The variable environment keeps track of global and local variables, and 
    keeps track of next available offset for local variables *)
 
    type varEnv = Map<string, Var * Typ> * int
 
 (* The function environment maps function name to label and parameter decs *)
 
    type ParamDecs = (Typ * string) list
    type funEnv = Map<string, label * Typ option * ParamDecs>
 
    //define the expression signal here
 
 
 
 (* Directly copied from Peter Sestoft   START  
    Code-generating functions that perform local optimizations *)
 
    let rec addINCSP m1 C : instr list =
        match C with
        | INCSP m2            :: C1 -> addINCSP (m1+m2) C1
        | RET m2              :: C1 -> RET (m2-m1) :: C1
        | Label lab :: RET m2 :: _  -> RET (m2-m1) :: C
        | _                         -> if m1=0 then C else INCSP m1 :: C
 
    /// Conditional jump to C
    let addLabel C : label * instr list =          (* Conditional jump to C *)
        match C with
        | Label lab :: _ -> (lab, C)
        | GOTO lab :: _  -> (lab, C)
        | _              -> let lab = newLabel() 
                            (lab, Label lab :: C)

    /// Unconditional jump to C 
    let makeJump C : instr * instr list =          (* Unconditional jump to C *)
        match C with
        | RET m              :: _ -> (RET m, C)
        | Label lab :: RET m :: _ -> (RET m, C)
        | Label lab          :: _ -> (GOTO lab, C)
        | GOTO lab           :: _ -> (GOTO lab, C)
        | _                       -> let lab = newLabel() 
                                     (GOTO lab, Label lab :: C)
    ///  Create function call
    let makeCall m lab C : instr list =
        match C with
        | RET n            :: C1 -> TCALL(m, n, lab) :: C1
        | Label _ :: RET n :: _  -> TCALL(m, n, lab) :: C
        | _                      -> CALL(m, lab) :: C
 
    let rec deadcode C =
        match C with
        | []              -> []
        | Label lab :: _  -> C
        | _         :: C1 -> deadcode C1
 
    let addNOT C =
        match C with
        | NOT        :: C1 -> C1
        | IFZERO lab :: C1 -> IFNZRO lab :: C1 
        | IFNZRO lab :: C1 -> IFZERO lab :: C1 
        | _                -> NOT :: C
 
    let addJump jump C =                    (* jump is GOTO or RET *)
        let C1 = deadcode C
        match (jump, C1) with
        | (GOTO lab1, Label lab2 :: _) -> if lab1=lab2 then C1 
                                          else GOTO lab1 :: C1
        | _                            -> jump :: C1
     
    let addGOTO lab C = addJump (GOTO lab) C
 
    let rec addCST i C =
        match (i, C) with
        | (0, ADD        :: C1) -> C1
        | (0, SUB        :: C1) -> C1
        | (0, NOT        :: C1) -> addCST 1 C1
        | (_, NOT        :: C1) -> addCST 0 C1
        | (1, MUL        :: C1) -> C1
        | (1, DIV        :: C1) -> C1
        | (0, EQ         :: C1) -> addNOT C1
        | (_, INCSP m    :: C1) -> if m < 0 then addINCSP (m+1) C1
                                   else CSTI i :: C
        | (0, IFZERO lab :: C1) -> addGOTO lab C1
        | (_, IFZERO lab :: C1) -> C1
        | (0, IFNZRO lab :: C1) -> C1
        | (_, IFNZRO lab :: C1) -> addGOTO lab C1
        | _                     -> CSTI i :: C
             
 (* ------------------------------------------------------------------- *)
 
 (* End code directly copied from Peter Sestoft *)

    let addADD C =
        ADD :: C // TODO

    let rec function_call vEnv fEnv function_name es k =
        
        match Map.tryFind function_name fEnv with
        | None -> failwith "Function call to nonexistant function" 
        
        | Some(lab, topt, (parameters: (Typ * string) list)) ->
            // Fix stack pointer after returning from procedure
            let k = match topt with
                              | None -> INCSP -1 :: k //TODO: optimized incsp
                              | Some _ -> k
            // Perform call
            let k = makeCall parameters.Length lab k // TODO: not parameters.Length, but their size on the stack
            
            // Add expression list
            List.fold (fun s exp -> CE exp vEnv fEnv s) k es

 /// CE e vEnv fEnv k gives the code for an expression e on the basis of a variable and a function environment and continuation k
    and CE e vEnv fEnv k = 
        match e with
        | N n          -> addCST n k
        | B b          -> addCST (if b then 1 else 0) k
        | Access acc  -> CA acc vEnv fEnv (LDI :: k) 
        // negative 
        | Apply("-",[e]) -> CE e vEnv fEnv (addCST 0 (SWAP:: SUB :: k))
        //add "!"
        | Apply("!", [e]) -> CE e vEnv fEnv (addNOT (k))
        | Apply("&&",[b1;b2]) -> 
                 match k with
                 //  "if(b1&&b2)"
                 | IFZERO lab :: _ -> CE b1 vEnv fEnv (IFZERO lab :: CE b2 vEnv fEnv k)
                 //   "while(b1&&b2)
                 | IFNZRO labthen :: k1 -> 
                         let (labelse, k2) = addLabel k1
                         CE b1 vEnv fEnv
                              (IFZERO labelse :: CE b2 vEnv fEnv (IFNZRO labthen :: k2))
                 // x = b1&&b2
                 | _ ->  let (jumpend,  k1) = makeJump k
                         let (labfalse, k2) = addLabel (addCST 0 k1)
                         CE b1 vEnv fEnv (IFZERO labfalse :: CE b2 vEnv fEnv (addJump jumpend k2))
        
        | Apply("||",[b1;b2]) ->
            match k with 
             //  "if(b1b2)"
            | IFNZRO lab :: _ -> CE b1 vEnv fEnv (IFNZRO lab :: CE b2 vEnv fEnv k)
            | IFZERO labthen :: k1 -> 
                    let (labelse, k2) = addLabel k1
                    CE b1 vEnv fEnv
                         (IFNZRO labelse :: CE b2 vEnv fEnv (IFZERO labthen :: k2))
            | _ ->  let (jumpend,  k1) = makeJump k
                    let (labfalse, k2) = addLabel (addCST 1 k1)
                    CE b1 vEnv fEnv (IFNZRO labfalse :: CE b2 vEnv fEnv (addJump jumpend k2))
        
        //add operation case 
        | Apply(o,[e1;e2])  when List.exists (fun x -> o=x) ["+";"*";"/";"<";">";"<=";">=";"<>";"="]
                           -> let ins = match o with
                                        | "+"  -> ADD::k
                                        | "*"  -> MUL::k
                                        | "/" -> DIV::k
                                        | "-" -> SUB::k
 
                                        | "<" -> LT::k
                                        | ">" -> SWAP:: LT::k
                                        | ">=" -> LT::(addNOT(k))
                                        | "<=" -> SWAP::LT::(addNOT(k))
 
                                        | "<>" -> EQ::(addNOT(k))
                                        | "="  -> EQ::k
                                        | _    -> failwith "CE: this operation case is not possible"
                              CE e1 vEnv fEnv (CE e2 vEnv fEnv ins) 
        | Apply(f, es) ->   function_call vEnv fEnv f es k
        
        | Addr(acc) -> CA acc vEnv fEnv k
        //| _                -> failwith "CE: not supported yet"
        
    and CEs es vEnv fEnv k = 
       match es with 
       | []     -> k
       | e::es' -> CE e vEnv fEnv (CEs es' vEnv fEnv k) 
 
 /// CA acc vEnv fEnv k gives the code for an access acc on the basis of a variable and a function environment and continuation k
    and CA acc vEnv fEnv k = 
       match acc with 
       | AVar x         -> match Map.find x (fst vEnv) with
                           | (GloVar addr,_) -> addCST addr k
                           | (LocVar addr,_) -> GETBP :: addADD k |> addCST addr
       | AIndex(acc, e) -> addADD k |> CA acc vEnv fEnv |> CE e vEnv fEnv
       | ADeref e       -> CE e vEnv fEnv k
 
    
 (* Bind declared variable in env and generate code to allocate it: *)  
    let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv)  =
     let (env, fdepth) = vEnv 
     match typ with
     | ATyp (ATyp _, _) -> failwith "allocate: array of arrays not permitted"
     | ATyp (t, Some i) ->
         let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+i)
         let code = [INCSP i]
         (newEnv, code)
     | _ -> 
       let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
       let code = [INCSP 1]
       (newEnv, code)
 
 /// CS s vEnv fEnv k gives the code for a statement s on the basis of a variable and a function environment and continuation k                            
    let rec CS stm vEnv fEnv k = 
        match stm with
        | PrintLn e        -> CE e vEnv fEnv (PRINTI:: INCSP -1 :: k) 
 
        | Ass(acc,e)       -> CA acc vEnv fEnv (CE e vEnv fEnv (STI:: addINCSP -1 k))
 
        | Block([],stms)   -> CSs stms vEnv fEnv k
 
        | Block(decs, stms) ->
             k // TODO
        
        | Alt(gc) -> 
            let (outer_label, k) = addLabel k
            let k = STOP :: k
            CGC gc vEnv fEnv k outer_label

        | Do(gc) ->
            let outer_label = newLabel()
            CGC gc vEnv fEnv k outer_label

        | Call(f, es) ->
            function_call vEnv fEnv f es k

        | Return optexp ->
            
            let stack_frame_size = snd vEnv

        // add here
        //| Block(declarations, stms) ->
        //      let (vEnv, dec_instructions, dealloc_instructions) =
        //          List.fold (fun (env,instrs, dealloc_instrs) t ->
        //              let (env, instrs2) = modify_local_environment env t
        //              let dealloc_instrs2 = [INCSP -1]
        //              (env, instrs @ instrs2, dealloc_instrs @ dealloc_instrs2)
        //          ) (vEnv, [], []) declarations
              
        //      dec_instructions @ CSs vEnv fEnv stms @ dealloc_instructions
 
        //  | Alt(gc) -> 
        //      let outer_label = newLabel()
        //      CGC vEnv fEnv gc outer_label @ [STOP; Label outer_label] //No matches in an alternate GC = abort
 
        //  | Do(gc) ->
        //      let outer_label = newLabel()
        //      [Label outer_label] @ CGC vEnv fEnv gc outer_label //Every match in a do GC means jumping to the start
 
        //  | Return(optexp) ->
        //      let (first_instructions, last_instructions) = 
        //          match optexp with
        //          | None -> ([CSTI 0], [INCSP -1]) 
        //          | Some(exp) -> (CE vEnv fEnv exp, [])
        //      let stack_frame_size = snd vEnv 
 
        //      first_instructions @ [RET (stack_frame_size)] @ last_instructions
 
        //  | Call(f, expressions) ->
        //      function_call vEnv fEnv f expressions
 
        | _                -> failwith "CS: this statement is not supported yet"
    
    and CGCsingle vEnv fEnv outer_label k (exp, stms)=
        // First, make a label for the next GC branch
        let (nextLabel, k) = addLabel k
        // Then, if we don't hit the next state, we jump back to the outer label
        let k = addJump (GOTO outer_label) k
        // We deal with the statements
        let k = CSs stms vEnv fEnv k
        // If the expression is false, we go to the next branch
        let k = IFZERO nextLabel :: k
        // We deal with the expression
        CE exp vEnv fEnv k

        // Just read this all bottom up

    and CGC (GC(ls)) vEnv fEnv k outer_label =
        List.fold (CGCsingle vEnv fEnv outer_label) k (List.rev ls) // We gotta do it in reverse

    and CSs stms vEnv fEnv k = 
         match stms with
         | []   -> k
         | stm::stms' -> CS stm vEnv fEnv (CSs stms' vEnv fEnv k) 
 
 (* ------------------------------------------------------------------- *)
 
 (* Build environments for global variables and functions *)
 
    let makeGlobalEnvs decs = 
        let rec addv decs vEnv fEnv = 
            match decs with 
            | []         -> (vEnv, fEnv, [])
            | dec::decr  -> 
              match dec with
              | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                     let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                     (vEnv2, fEnv2, code1 @ code2)
              | FunDec (tyOpt, f, xs, body) -> failwith "makeGlobalEnvs: function/procedure declarations not supported yet"
        addv decs (Map.empty, 0) Map.empty
 
 (* CP compiles a program *)
 
    let CP (P(decs,stms)) = 
        let _ = resetLabels ()
        let ((gvM,_) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
        initCode @ CSs stms gvEnv fEnv [STOP]     
 
 
 
 