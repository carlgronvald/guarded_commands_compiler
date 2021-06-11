namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016 , 04-01-2018, 07-06 2021

open GuardedCommands.Frontend.AST

module TypeCheck = 
    let bool_logic_operators = ["&&";"=";"<>";"||"]
    let int_logic_operators = ["<";">";"<=";">=";"<>"]
    let arithmetic_operators = ["+";"*";"/"]
    let binary_operators = Seq.ofList (bool_logic_operators @ int_logic_operators @ arithmetic_operators) |> Seq.distinct |> List.ofSeq
    let unary_operators = ["-"]
    let return_prefix = "return "
    let procedure_prefix = "procedure "
    /// If we're inside a function, this is set in the local environment to the return type of the function
    let enter_procedure ltenv = Map.add "in procedure" ITyp ltenv
    let enter_function ltenv typ = Map.add "return type" typ ltenv
    /// If we're inside a procedure, this is set in the local environment to some type (that is not further defined)
    let in_procedure ltenv = Map.containsKey "in procedure" ltenv
    let in_function ltenv = Map.containsKey "return type" ltenv
    let current_function_return_type ltenv = Map.tryFind "return type" ltenv
    let function_parameter_name function_name (type_number:int) = function_name + " type " + (string)type_number
    let function_parameter_type gtenv function_name (type_number:int) =
        Map.tryFind (function_parameter_name function_name type_number) gtenv 
    


    /// tcE gtenv ltenv e gives the type for expression e on the basis of type environments gtenv and ltenv
    /// for global and local variables 
    let rec tcE gtenv ltenv = function                            
            | N _              -> ITyp   
            | B _              -> BTyp   
            | Access acc       -> tcA gtenv ltenv acc     
                   
            | Apply(f,[e]) when List.exists (fun x ->  x=f) unary_operators
                            -> tcMonadic gtenv ltenv f e        

            | Apply(f,[e1;e2]) when List.exists (fun x ->  x=f) binary_operators
                            -> tcDyadic gtenv ltenv f e1 e2   

            | Apply(f, es) -> //Function call
                tcNaryFunction gtenv ltenv f es
            | s                -> failwith (sprintf "tcE: not supported yet %A" s)

    and tcMonadic gtenv ltenv f e = match (f, tcE gtenv ltenv e) with
                                    | ("-", ITyp) -> ITyp
                                    | s           -> failwith (sprintf "illegal/illtyped monadic expression %A" s)
   
    and tcDyadic gtenv ltenv f e1 e2 = match (f, tcE gtenv ltenv e1, tcE gtenv ltenv e2) with
                                        | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) arithmetic_operators -> ITyp
                                        | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) int_logic_operators  -> BTyp
                                        | (o, BTyp, BTyp) when List.exists (fun x ->  x=o) arithmetic_operators -> BTyp 
                                        | _                      -> failwith("illegal/illtyped dyadic expression: " + f)
    
    /// Checks the inputs for a function or procedure
    and tcFPInputs gtenv ltenv f es=
        let types = List.map (tcE gtenv ltenv) es
        
        //Check the i'th type in the function input list
        let check_type i x =
            match function_parameter_type gtenv f i with
            | None -> failwith ("At least " + (string)(i+1) + " parameters were supplied for function or procedure " + f + ", but it only needs " + (string)(i))
            | Some(typ) -> 
                if typ = x then
                    ()
                else failwith ("parameter " + (string)(i+1) + " for function or procedure " + f + " is of wrong type")

        List.mapi check_type types  |> ignore

    and tcNaryFunction gtenv ltenv f es =
        let rtype = match Map.tryFind (return_prefix + f) gtenv with //Find the return type
                    | Some(typ) -> typ
                    | None -> failwith ("Trying to call an undefined function " + f)

        tcFPInputs gtenv ltenv f es

        rtype
 
    and tcNaryProcedure gtenv ltenv f es =
        match Map.tryFind (procedure_prefix + f) gtenv with
            | Some(_) -> ()
            | None -> failwith ("Trying to call an undefined procedure " + f)

        tcFPInputs gtenv ltenv f es

        ()

    /// tcA gtenv ltenv e gives the type for access acc on the basis of type environments gtenv and ltenv
    /// for global and local variables 
    and tcA gtenv ltenv = 
            function 
            | AVar x         -> match Map.tryFind x ltenv with
                                | None   -> match Map.tryFind x gtenv with
                                            | None   -> failwith ("no declaration for : " + x)
                                            | Some t -> t
                                | Some t -> t
            | AIndex(acc, e) ->
                match (tcE gtenv ltenv e) with
                                          | ITyp -> ()
                                          | _ -> failwith ("Illegal variable indexing. Variables can only be indexed with integers.")
                tcA gtenv ltenv acc
            | ADeref e       -> failwith "tcA: pointer dereferencing not supported yet"
                                        //TODO: I don't understand how pointers work in this language

    /// tcS gtenv ltenv s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
    /// for global and local variables 
    and tcS gtenv ltenv = function                           
                            | PrintLn e -> tcE gtenv ltenv e |> ignore
                            | Ass(acc,e) -> if tcA gtenv ltenv acc = tcE gtenv ltenv e 
                                            then ()
                                            else failwith "illtyped assignment"                                

                            | Block([],stms) -> List.iter (tcS gtenv ltenv) stms
                            | Block(decs, stms) ->
                                let (ltenv,_) = tcLDecs gtenv (ltenv, []) decs
                                List.iter (tcS gtenv ltenv) stms

                            | Return(expopt) ->
                                match expopt with // First, check if we're supposed to have a return type
                                | None -> // If not, we are either inside a procedure, which is good, or we're not, which is bad
                                    if not (in_procedure ltenv)
                                    then failwith "Return statement with no type must be inside a procedure"
                                | Some(exp) -> // If we are supposed to have a return type, we actually have three options
                                               // We could 1) be inside a function with the same return type, which is great
                                               // Or 2), be inside a function with a different return type, which is not good
                                               // Or 3), not be inside a function at all! also not good.
                                    match current_function_return_type ltenv with
                                    | Some(typ) ->  if not (tcE gtenv ltenv exp = typ) then failwith "Trying to return wrong type from function."
                                    | None -> failwith "Typed return statement must be inside a function"
                            
                            | Alt(gc) -> tcGC gtenv ltenv gc
                            | Do(gc) -> tcGC gtenv ltenv gc
                            | Call(f, es) -> tcNaryProcedure gtenv ltenv f es
    
    and tcFunDec gtenv topt f decs stm =
        // Start by creating the local environment; and append to the global environment
        // if we have a function (there's an output type), and not a procedure (no output type)
        let (ltenv,gtenv) = 
            match topt with
            | None -> (Map.empty, Map.add (procedure_prefix + f) ITyp gtenv)
            | Some(typ) -> ( enter_function Map.empty typ, Map.add (return_prefix+f) typ gtenv)
        
        // Then type check declarations and the statement
        let (ltenv, types) = tcLDecs gtenv (ltenv, []) decs

        // Add function input types to the global environment so we can type check them later
        let gtenv = 
            List.mapi (fun i x -> ((function_parameter_name f i),x)) types
            |> List.fold (fun s (name,typ) -> Map.add name typ s) gtenv

        // Type check the insides of the function
        tcS gtenv ltenv stm
        gtenv

    /// Handles a single global declaration
    and tcGDec gtenv =  function  
                        | VarDec(t,s)               -> Map.add s t gtenv
                        | FunDec(topt,f, decs, stm) -> tcFunDec gtenv topt f decs stm

    /// Handles a list of global declarations
    and tcGDecs gtenv = function
                        | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
                        | _         -> gtenv

    /// Handles a single local declaration
    and tcLDec gtenv (ltenv, local_types) = function
                             | VarDec(t,s) -> (Map.add s t ltenv, local_types @ [t])
                             | FunDec(topt, f, decs, stm) -> failwith "Local function declarations are not allowed"

    /// Handles a list of local declarations
    /// 
    /// Returns both the resulting local environment and the list of locally declared types in order,
    /// since the types are needed for function definitions
    and tcLDecs gtenv (ltenv, local_types) = function
                              | dec::decs -> tcLDecs gtenv (tcLDec gtenv (ltenv,local_types) dec) decs
                              | _ -> (ltenv, local_types)

    and tcGC gtenv ltenv = function
        | GC(ls) ->
            List.iter (fun (exp, stmts) -> 
                if tcE gtenv ltenv exp <> BTyp then failwith "Guarded Command expression not of boolean type!"
                List.iter (tcS gtenv ltenv) stmts
            ) ls

    /// tcP prog checks the well-typeness of a program prog
    and tcP(P(decs, stms)) = let gtenv = tcGDecs Map.empty decs
                             List.iter (tcS gtenv Map.empty) stms

  
