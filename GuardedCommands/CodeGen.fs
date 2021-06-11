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

    let simple_binary_expressions = ["+";"*";"/";
        "<";">";"<=";">=";
        "<>";"="]


    let rec binary_expression_bytecode =
        function
        | "+"  -> [ADD]
        | "*"  -> [MUL]
        | "/" -> [DIV]

        | "<" -> [LT]
        | ">" -> [SWAP; LT]
        | ">=" -> [LT;NOT]
        | "<=" -> SWAP::(binary_expression_bytecode ">=")

        | "<>" -> [EQ;NOT]
        | "="  -> [EQ]
        | s -> failwith ("Binary expression " + s + " not supported")

    
    (* Bind declared variable in env and generate code to allocate it: *)   
    let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv)  =
        let (env, fdepth) = vEnv 
        match typ with
        | ATyp (ATyp _, _) -> 
            raise (Failure "allocate: array of arrays not permitted")
        | ATyp (t, Some i) -> failwith "allocate: array not supported yet"
        | _ -> 
            let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
            let code = [INCSP 1]
            (newEnv, code)

    let rec function_call vEnv fEnv function_name es =
        match Map.tryFind function_name fEnv with
        | None -> failwith "Function call to nonexistant function" 
        | Some(lab, topt, parameters) ->
            let expr_instr_list =
                List.fold (fun s exp -> s @ CE vEnv fEnv exp) [] es

            let (vEnv, instr_list) = 
                List.fold (fun (variable_environment, instructions) x ->
                    let (v2,i2) = allocate LocVar (x) vEnv
                    (v2, instructions@i2)
                ) (vEnv, []) parameters 
            
            expr_instr_list @ [INCSP -parameters.Length] @ instr_list @ [CALL (parameters.Length, lab)] //TODO: Test function calls

    
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
        | _            -> failwith "CE: not supported yet"
        
 /// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
 ///
 /// CA = Code (generation for an) Access
    and CA vEnv fEnv = function | AVar x         -> match Map.find x (fst vEnv) with
                                                    | (GloVar addr,_) -> [CSTI addr]
                                                    | (LocVar addr,_) -> failwith "CA: Local variables not supported yet"
                                | AIndex(acc, e) -> failwith "CA: array indexing not supported yet" 
                                | ADeref e       -> failwith "CA: pointer dereferencing not supported yet"
 
   
 
                       
 /// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment                          
 /// Code (generation for a) Statement
    let rec CS vEnv fEnv = function
        | PrintLn e        -> CE vEnv fEnv e @ [PRINTI; INCSP -1] 
 
        | Ass(acc,e)       -> CA vEnv fEnv acc @ CE vEnv fEnv e @ [STI; INCSP -1]
 
        | Block([],stms) ->   CSs vEnv fEnv stms
 
        | _                -> failwith "CS: this statement is not supported yet"
 
    and CSs vEnv fEnv stms = List.collect (CS vEnv fEnv) stms 
 
 
 
 (* ------------------------------------------------------------------- *)
 
 (* Build environments for global variables and functions *)
 
    let generateParamDecs xs =
        List.map (fun (d:Dec) -> 
            match d with
            | VarDec(typ, name) -> (typ, name)
            | _ -> failwith "Only variables are allowed as declarations!"
        ) xs

    let makeGlobalEnvs decs = 
        // addv takes the list of declarations, pops off the top declaration,
        // makes code for that declaration (as well as changes in environment), and
        // then goes on to the next declaration in the list.
        let rec addv decs vEnv fEnv = 
            match decs with 
            | []         -> (vEnv, fEnv, [])
            | dec::decr  -> 
              match dec with
              | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                     let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                     (vEnv2, fEnv2, code1 @ code2)
              | FunDec (tyOpt, f, xs, body) -> 
                  let lab = newLabel()
                  let fEnv = Map.add f (lab, tyOpt, generateParamDecs xs) fEnv
                  let (vEnv2, fEnv2, code2) = addv decr vEnv fEnv
                  (vEnv2, fEnv2, [Label lab] @ CS vEnv fEnv body @ code2) //TODO: Test function declarations
        addv decs (Map.empty, 0) Map.empty
 
 /// CP prog gives the code for a program prog
    let CP (P(decs,stms)) = 
        let _ = resetLabels ()
        let ((gvM,_) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
        initCode @ CSs gvEnv fEnv stms @ [STOP]     
 
 
 
 