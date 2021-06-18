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
 
    let type_size t =
        match t with
        | ATyp (_, Some i) -> i+1
        | ATyp _ -> failwith "Cannot find the size of an unsized array"
        | _ -> 1
 
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
    let allocate_environment (kind: int -> Var) (vEnv : varEnv) (typ,x) =
        let (env, fdepth) = vEnv 
        match typ with
        | ATyp (ATyp _, _) -> failwith "allocate: array of arrays not permitted"
        | ATyp (_, None) -> failwith "Allocation of unsized array is only permitted in function declaration!"
        | ATyp (t, Some i) ->
            (Map.add x (kind fdepth, typ) env, fdepth+i+1)
        | _ -> 
            let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
            newEnv

    /// Must happen after creating the environment for the declarations.
    ///
    /// Declarations must be passed in reverse to this function
    let allocate_instructions (kind : int -> Var) (vEnv : varEnv) k (typ,x)  =
        let (env, _) = vEnv
        match typ with
        | ATyp (ATyp _, _) -> failwith "allocate: array of arrays not permitted"
        | ATyp (_, None) -> failwith "Allocation of unsized array is only permitted in function declaration!"
        | ATyp (t, Some i) ->
            let (var, _) = Map.find x env
            let k = addINCSP i k
            match var with
            | LocVar offset -> GETBP :: addCST (offset+1) ( ADD :: k)
            | GloVar offset -> addCST (offset+1) k
        | _ -> 
            addINCSP 1 k

    let deallocate_instructions k (typ,_) =
        addINCSP -(type_size typ) k

    /// Separates variable declarations and function declarations
    let separate_decs decs =
        List.fold (fun (vds, fds) -> function
        | VarDec (typ, name) -> ((typ, name)::vds, fds)
        | FunDec (tyOpt, f, xs, body) -> (vds, (tyOpt,f,xs,body)::fds)) ([],[]) decs

    let rec function_call vEnv fEnv function_name es k =
        
        match Map.tryFind function_name fEnv with
        | None -> failwith ("Function call to nonexistant function " + function_name)
        
        | Some(lab, topt, (parameters: (Typ * string) list)) ->
            // Fix stack pointer after returning from procedure
            let k = match topt with
                              | None -> addINCSP -1 k
                              | Some _ -> k
            // Perform call
            let k = makeCall parameters.Length lab k // TODO: not parameters.Length, but their size on the stack. Actually, I think anything passed to a function are 1 long words
            
            // Add expression list
            List.fold (fun s exp -> CE exp vEnv fEnv s) k (List.rev es)

 /// CE e vEnv fEnv k gives the code for an expression e on the basis of a variable and a function environment and continuation k
    and CE e vEnv fEnv k = 
        match e with
        | N n          -> addCST n k
        | B b          -> addCST (if b then 1 else 0) k
        | Access acc  -> CA acc vEnv fEnv (LDI :: k) 
        | Apply("-",[e]) -> CE e vEnv fEnv (addCST 0 (SWAP:: SUB :: k))
        | Apply("++", [e]) -> CE e vEnv fEnv (addCST 1 (ADD :: k))
        | Apply("--", [e]) -> CE e vEnv fEnv (addCST 1 (SUB :: k))
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
        | Apply(o,[e1;e2])  when List.exists (fun x -> o=x) ["+";"*";"/";"<";">";"<=";">=";"<>";"=";"-"]
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
                            | (LocVar addr,_) -> GETBP :: ( addCST addr (ADD :: k))
        | AIndex(acc, e) -> 
            // We end up with adding the address of the 0th element to the index
            let k = ADD :: k

            // Before that, we need the index
            let k = CE e vEnv fEnv k



            // And we also need to deref the pointer to the 0th element
            let k = LDI::k
            // And, to start with, we need that pointer
            CA acc vEnv fEnv k
            //First, we need to deref the pointer to the 0th elem
//            let k = LDI :: k
//            let k = CA acc vEnv fEnv k
            
       
//            ADD :: k |> CA acc vEnv fEnv |> CE e vEnv fEnv
        | ADeref e       -> CE e vEnv fEnv k
 
    

    


 /// CS s vEnv fEnv k gives the code for a statement s on the basis of a variable and a function environment and continuation k                            
    let rec CS stm vEnv fEnv k = 
        match stm with
        | PrintLn e        -> CE e vEnv fEnv (PRINTI:: addINCSP -1 k) 
 
        | Ass(acc,e)       -> CA acc vEnv fEnv (CE e vEnv fEnv (STI:: addINCSP -1 k))
        
        | Mass(accs, es) -> 
            List.fold (fun s (acc, e) -> CS (Ass(acc,e)) vEnv fEnv k ) k (List.zip accs es)

        | Block([],stms)   -> CSs stms vEnv fEnv k
 
        | Block(decs, stms) ->

            let (var_decs, fun_decs) = separate_decs decs

            let block_fold fn = List.fold (fun s dec ->
                    match dec with
                    | VarDec (typ,name) -> fn typ name s
                    | FunDec _ -> failwith "Local function definitions are a big nono"
                )

            // Start with deallocate instructions
//            let k1 = block_fold (fun typ name s -> addINCSP -(type_size typ) s) [] decs
//            let k2 = List.fold deallocate_instructions [] var_decs
//            printfn "k1: %A, k2: %A" k1 k2
            let k = List.fold deallocate_instructions k var_decs
            // Then generate local variable environment
            let vEnv = List.fold (allocate_environment LocVar) vEnv var_decs

                    

            (*let vEnv1 = 
                block_fold (fun typ name (env, offset) -> 
                    (Map.add name (LocVar offset, typ) env, offset+ (type_size typ))
                ) vEnv decs
            let vEnv2 = List.fold (allocate_environment LocVar) vEnv var_decs
            printfn "k1: %A, k2: %A" vEnv1 vEnv2*)
            
//             let (vEnv, alloc_instrs) = List.fold (allocate LocVar)  TODO
            
            // Then we do our statements
            let k = CSs stms vEnv fEnv k

            // Aaaand, we allocate (which actually happens first)
            (*let k1 = List.fold (allocate_instructions LocVar vEnv) [] (var_decs)
            let k2 =
                block_fold (fun typ name (s, offset) ->
                    match typ with
                    | ATyp(_, Some i) ->
                        let s = addINCSP i s
                        // We need the absolute path to our array, so we need to add the base pointer
                        let s = GETBP :: (addCST (offset+1) (ADD :: s))
                
                        (s,offset+i+1)
                    | _ -> (addINCSP 1 s,offset+1)
                ) ([], 0) decs |> fst
            printfn "k1: %A, k2: %A" k1 k2 *)
            List.fold (allocate_instructions LocVar vEnv) k (List.rev var_decs)
            


//            block_fold (fun typ name (s, offset) ->
//                match typ with
//                | ATyp(_, Some i) ->
//                    let s = addINCSP i s
                    // We need the absolute path to our array, so we need to add the base pointer
//                    let s = GETBP :: (addCST (offset+1) (ADD :: s))

//                    (s,offset+i+1)
//                | _ -> (addINCSP 1 s,offset+1)
//            ) (k, 0) decs |> fst

        | Alt(gc) -> 
            let (outer_label, k) = addLabel k
            let k = STOP :: k
            CGC gc vEnv fEnv k outer_label

        | Do(gc) ->
            let outer_label = newLabel()
            Label outer_label :: CGC gc vEnv fEnv k outer_label // Can this be optimized?

        | Call(f, es) ->
            function_call vEnv fEnv f es k

        | Return optexp ->
            let stack_frame_size = snd vEnv
            
            let k = RET stack_frame_size :: k

            match optexp with
                    | None -> addCST 0 k
                    | Some e -> CE e vEnv fEnv k
        | Inc(acc) -> CA acc vEnv fEnv (LDI :: addCST 1 (ADD :: (CA acc vEnv fEnv (addINCSP (-1) (STI :: k)))))
        | Dec(acc) -> CA acc vEnv fEnv (LDI :: addCST 1 (SUB :: (CA acc vEnv fEnv (addINCSP (-1) (STI :: k)))))
 
 
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
 
    let generateParamDecs xs =
        List.map (fun (d:Dec) -> 
            match d with
            | VarDec(typ, name) -> (typ, name)
            | _ -> failwith "Only variables are allowed as function parameters!"
        ) xs
    
    /// Register functions so we can do mutual recursion
    let preDecFuncs decs =
        List.fold (fun s (tyOpt, f, xs, _) ->
                Map.add f (newLabel(), tyOpt, generateParamDecs xs) s
            ) Map.empty decs

    let decFunc vEnv fEnv k (tyOpt, f, xs, body) =
        let (lab, _, parameters) = Map.find f fEnv
        //let parameters = generateParamDecs xs
        let types, offset = vEnv

        let vEnv_inner = 
            List.fold (fun (env, offset) (typ, name) -> 
                (Map.add name (LocVar offset, typ) env,offset+1)
            ) (types, 0) parameters

        let (_, dealloc_size) = vEnv_inner

        let k = match tyOpt with
                    | None -> 
                        match dealloc_size with
                        | 0 -> addCST 0 ( RET 0 :: k)
                        | _ -> RET (dealloc_size-1) :: k
                    | Some _ -> k

        Label lab :: CS body vEnv_inner fEnv k

        

    let makeGlobalEnvs decs =
        // Start out by filtering out variable and function declarations
        let (vardecs, fundecs) = separate_decs decs

        // Generate function and variable environment 
        let fEnv = preDecFuncs fundecs
        let vEnv = List.fold (allocate_environment GloVar ) (Map.empty, 0) vardecs

        // Then generate function and variable instructions
        let var_instructions = List.fold (allocate_instructions GloVar vEnv) [] (List.rev vardecs)
        let fun_instructions = List.fold (decFunc vEnv fEnv) [] fundecs

        (vEnv, fEnv, var_instructions, fun_instructions)

 
 (* CP compiles a program *)
 
    let CP (P(decs,stms)) = 
        let _ = resetLabels ()
        let ((gvM,_) as gvEnv, fEnv, initCode, postCode) = makeGlobalEnvs decs
        initCode @ CSs stms gvEnv fEnv [STOP] @ postCode
 
 
 
 
