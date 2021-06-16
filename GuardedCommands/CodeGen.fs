namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018, 07-07-2021
// This file is obtained by an adaption of the file MicroC/Comp.fs by Peter Sestoft

open Machine

open GuardedCommands.Frontend.AST
module CodeGeneration =
 
 
 (* A global variable has an absolute address, a local one has an offset: *)
    type Var = 
      | GloVar of int                   (* absolute address in stack           *)
      | LocVar of int                   (* address relative to bottom of frame *)
 
 (* The variable environment keeps track of global and local variables, and 
    keeps track of next available offset for local variables *)
 
    type varEnv = Map<string, Var*Typ> * int
 
 (* The function environment maps function name to label and parameter decs *)
 
    type ParamDecs = (Typ * string) list
    type funEnv = Map<string, label * Typ option * ParamDecs>

    let simple_binary_expressions = ["+";"*";"/";"-";
        "<";">";"<=";">=";
        "<>";"="]


    let rec binary_expression_bytecode =
        function
        | "+"  -> [ADD]
        | "*"  -> [MUL]
        | "/" -> [DIV]
        | "-" -> [SUB]

        | "<" -> [LT]
        | ">" -> [SWAP; LT]
        | ">=" -> [LT;NOT]
        | "<=" -> SWAP::(binary_expression_bytecode ">=")

        | "<>" -> [EQ;NOT]
        | "="  -> [EQ]
        | s -> failwith ("Binary expression " + s + " not supported")

    
    (* Bind declared variable in env and generate code to allocate it: *)   
    let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv) in_function_declaration =
        let (env, fdepth) = vEnv 
        match typ with
        | ATyp (ATyp _, _) -> 
            raise (Failure "allocate: array of arrays not permitted")
        | ATyp (t, Some i) ->

            if in_function_declaration then // If we're in a function declaration, we just make space for the pointer
                let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
                let code = [INCSP 1]
                (newEnv, code)
            else // If we're truly declaring a new array, we need the list as well
                let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+i+1)
                // adding the current depth to the base pointer gets the absolute offset of the start of the array
                let code = match kind 1 with
                           | GloVar _ -> [CSTI (fdepth+1); INCSP i]
                           | LocVar _ -> [CSTI (fdepth+1);GETBP;ADD; INCSP i]
                
                (newEnv, code)
        | _ -> 
            let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
            let code = [INCSP 1]
            (newEnv, code)
    
    /// Returns the modified variable environment and the instructions for local declarations of variables
    let modify_local_environment vEnv =
        function
        | VarDec(typ, string) -> allocate LocVar (typ, string) vEnv false
        | FunDec(_) -> failwith "Cannot locally define a function"

    let rec function_call vEnv fEnv function_name es =
        match Map.tryFind function_name fEnv with
        | None -> failwith "Function call to nonexistant function" 
        | Some(lab, topt, (parameters: (Typ * string) list)) ->
            let expr_instr_list =
                List.fold (fun s exp -> s @ CE vEnv fEnv exp) [] es
            let final_instr = match topt with
                              | None -> [INCSP -1]
                              | Some _ -> []
            expr_instr_list @  [CALL (parameters.Length, lab)] @ final_instr

    
    /// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
    ///
    /// CE = Code (generation for an) Expression 
    and CE vEnv fEnv = 
        function
        | N n          -> [CSTI n]
        | B b          -> [CSTI (if b then 1 else 0)]
        | Access acc   -> CA vEnv fEnv acc @ [LDI] 
 
        | Apply("-", [e]) -> CE vEnv fEnv e @  [CSTI 0; SWAP; SUB]
        | Apply("!", [e]) -> CE vEnv fEnv e @  [NOT]
        | Apply("++", [e]) -> CE vEnv fEnv e @  [CSTI 1; ADD]
        | Apply("--", [e]) -> CE vEnv fEnv e @  [CSTI 1; SUB]
 
        | Apply("&&",[b1;b2]) -> let labend   = newLabel()
                                 let labfalse = newLabel()
                                 CE vEnv fEnv b1 @ [IFZERO labfalse] @ CE vEnv fEnv b2
                                 @ [GOTO labend; Label labfalse; CSTI 0; Label labend]
        
        | Apply("||",[b1;b2]) -> let labend   = newLabel()
                                 let labtrue = newLabel()
                                 CE vEnv fEnv b1 @ [IFNZRO labtrue] @ CE vEnv fEnv b2
                                 @ [GOTO labend; Label labtrue; CSTI 1; Label labend]

        | Apply(o,[e1;e2]) when List.exists (fun x -> o=x) simple_binary_expressions
                              -> let ins = binary_expression_bytecode o
                                 CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ ins 
        | Apply("<", [e1;e2]) -> 
                     CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ [LT]
        | Apply(function_name, es) ->
            function_call vEnv fEnv function_name es
        | Addr acc -> CA vEnv fEnv acc
        | _            -> failwith "CE: not supported yet"
        
 /// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
 ///
 /// CA = Code (generation for an) Access
    and CA vEnv fEnv = function | AVar x ->
                                    match Map.find x (fst vEnv) with
                                    | (GloVar addr,_) -> [CSTI addr]
                                    | (LocVar addr,_) -> [GETBP; CSTI (addr); ADD]
                                | AIndex(acc, e) -> (CE vEnv fEnv e) @ (CA vEnv fEnv acc) @ [LDI; ADD]
                                | ADeref(e) -> CE vEnv fEnv e
 
   
 
                       
 /// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment                          
 /// Code (generation for a) Statement
    let rec CS vEnv fEnv = function
        | PrintLn e        -> CE vEnv fEnv e @ [PRINTI; INCSP -1] 
 
        | Ass(acc,e)       -> CA vEnv fEnv acc @ CE vEnv fEnv e @ [STI; INCSP -1]
        
        | Mass(accs, es)   ->
            let listOfAccess = List.zip accs es
            List.collect (fun (a,e) -> CS vEnv fEnv (Ass(a,e))) listOfAccess
 
        | Block([],stms) ->   CSs vEnv fEnv stms
        | Block(declarations, stms) ->
            let (vEnv, dec_instructions, dealloc_instructions) =
                List.fold (fun (env,instrs, dealloc_instrs) t ->
                    let (env, instrs2) = modify_local_environment env t
                    let dealloc_instrs2 = match t with
                                          | VarDec(ATyp(_, Some i), _) -> [INCSP (-i-1)]
                                          | _ -> [INCSP -1] //FunDecs are already handled in the type checker
                    (env, instrs @ instrs2, dealloc_instrs @ dealloc_instrs2)
                ) (vEnv, [], []) declarations
            
            dec_instructions @ CSs vEnv fEnv stms @ dealloc_instructions

        | Alt(gc) -> 
            let outer_label = newLabel()
            CGC vEnv fEnv gc outer_label @ [STOP; Label outer_label] //No matches in an alternate GC = abort

        | Do(gc) ->
            let outer_label = newLabel()
            [Label outer_label] @ CGC vEnv fEnv gc outer_label //Every match in a do GC means jumping to the start

        | Return(optexp) ->
            let (first_instructions, last_instructions) = 
                match optexp with
                | None -> ([CSTI 0], [INCSP -1]) 
                | Some(exp) -> (CE vEnv fEnv exp, [])
            let stack_frame_size = snd vEnv 

            first_instructions @ [RET (stack_frame_size)] @ last_instructions

        | Call(f, expressions) ->
            function_call vEnv fEnv f expressions
 
    and CSs vEnv fEnv stms = List.collect (CS vEnv fEnv) stms 
 
    /// Code generation for a Guarded Command
    and CGC vEnv fEnv (GC(ls)) outer_label =
        let instrs = 
            List.collect (fun (exp, stms) ->
                let lab = newLabel()
                let inner_statements = CSs vEnv fEnv stms
                CE vEnv fEnv exp @ [IFZERO lab] @ inner_statements @ [GOTO outer_label; Label lab]
            ) ls
        instrs
 
 (* ------------------------------------------------------------------- *)
 
 (* Build environments for global variables and functions *)
 
    let generateParamDecs xs =
        List.map (fun (d:Dec) -> 
            match d with
            | VarDec(typ, name) -> (typ, name)
            | _ -> failwith "Only variables are allowed as function parameters!"
        ) xs
       
       
    /// Find all function declarations and put them in a map with labels, so they can be used before being defined.
    /// Allows all functions to be mutually recursive with one another
    let pre_function_handling fEnv decs =
        let function_label s = function
            | VarDec _ -> s
            | FunDec(tyOpt,f,xs,_) -> Map.add f (newLabel(), tyOpt, generateParamDecs xs) s
        List.fold function_label fEnv decs


    let makeGlobalEnvs decs = 
        // addv takes the list of declarations, pops off the top declaration,
        // makes code for that declaration (as well as changes in environment), and
        // then goes on to the next declaration in the list.
        let rec addv decs vEnv fEnv = 
            match decs with 
            | []         -> (vEnv, fEnv, [], [])
            | dec::decr  -> 
              match dec with
              | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv false
                                     let (vEnv2, fEnv2, var_code_2, fun_code_2) = addv decr vEnv1 fEnv
                                     (vEnv2, fEnv2, code1 @var_code_2, fun_code_2)
              | FunDec (tyOpt, f, xs, body) -> 
                  let (lab, _, _) = Map.find f fEnv
                  let parameters = generateParamDecs xs
                  let types, offset = vEnv

                  let (vEnv_inner, _) = 
                      List.fold (fun (variable_environment, instructions) x ->
                          let (v2,i2) = allocate LocVar (x) variable_environment true
                          (v2, instructions@i2)
                      ) ((types,0), []) parameters 

                    
                  let (vEnv2, fEnv2, var_code_2, fun_code_2) = addv decr vEnv fEnv 

                  let (_, dealloc_size) = vEnv_inner

                  let rcode = match tyOpt with
                              | None -> [INCSP -dealloc_size; CSTI 0; RET 0]
                              | Some(_) -> []

                  vEnv2, fEnv2, var_code_2, [Label lab] @ CS vEnv_inner fEnv body @ rcode @ fun_code_2
                  
        let fEnv = pre_function_handling Map.empty decs

        addv decs (Map.empty, 0) fEnv
 

 /// CP prog gives the code for a program prog
    let CP (P(decs,stms)) = 
        let _ = resetLabels ()
        let ((gvM,_) as gvEnv, fEnv, var_code, fun_code) = makeGlobalEnvs decs
        var_code @ CSs gvEnv fEnv stms @ [STOP] @ fun_code
 
 
 
 
