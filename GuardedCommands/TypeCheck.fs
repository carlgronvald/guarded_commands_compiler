namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016 , 04-01-2018, 07-06 2021

open GuardedCommands.Frontend.AST

module TypeCheck = 
    let distinct list = list |> Set.ofList |> Set.toList

    let bool_logic_operators = ["&&";"=";"<>";"||"]
    let int_logic_operators = ["<";">";"<=";">=";"<>";"="]
    let arithmetic_operators = ["+";"*";"/";"-"] //TODO: BINARY MINUS OPERATORY
    let binary_operators = bool_logic_operators @ int_logic_operators @ arithmetic_operators |> distinct
    let unary_int_operators = ["-"]
    let unary_bool_operators = ["!"]
    let unary_operators = unary_int_operators @ unary_bool_operators |> distinct
    let return_prefix = "return "
    let procedure_prefix = "procedure "

    /// When we enter a function or procedure, we need to know that. This adds it to the local environment
    let enter_procedure ltenv = Map.add "in procedure" ITyp ltenv
    let enter_function ltenv typ = Map.add "return type" typ ltenv
    /// If we're inside a procedure, this is set in the local environment to some type (that is not further defined)
    let in_procedure ltenv = Map.containsKey "in procedure" ltenv
    let in_function ltenv = Map.containsKey "return type" ltenv
    let current_function_return_type ltenv = Map.tryFind "return type" ltenv
    let function_parameter_name function_name (type_number:int) = function_name + " type " + (string)type_number
    let function_parameter_type gtenv function_name (type_number:int) =
        Map.tryFind (function_parameter_name function_name type_number) gtenv 

    /// Check if a function, procedure, or variable is already declared in the given environment
    let check_exists name env =
        if List.exists (fun n ->
            Map.containsKey n env) [name;procedure_prefix+name;return_prefix+name]
        then failwith ("Duplicate declaration of " + name)
    
    // TODO: Is accessing a global variable allowed in a function??
    /// Checks whether all paths through a statement end in a return
    let rec returning_statement = function
        | PrintLn _ -> false
        | Ass _ -> false
        | Return _ -> true
        | Alt(gc) -> returning_gc gc
        | Do(gc) -> returning_gc gc
        | Block(_, stms) -> List.exists returning_statement stms
        | Call _ -> false

    /// Checks whether all paths through a GC end in a return
    and returning_gc (GC(ls)) =
        let gc_path_returns = List.exists (fun stm -> returning_statement stm)
        // Check that all paths return a value by checking that no paths do not return a value
        List.exists (fun (_, stms) -> not (gc_path_returns stms)) ls |> not

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

            // e1 ? e2 : e3 
            | Apply("?", [e1;e2;e3]) -> if tcE gtenv ltenv e1 <> BTyp then failwith ("Illigal type for conditional expression")  else
                                        if tcE gtenv ltenv e2  <> tcE gtenv ltenv e3 then failwith ("The two branches in conditional should be the same type!") else
                                            tcE gtenv ltenv e2

            | Apply(f, es) -> // Function call
                tcNaryFunction gtenv ltenv f es

            | Addr(acc) ->
                tcA gtenv ltenv acc |> PTyp
            



            | s                -> failwith (sprintf "tcE: not supported yet %A" s)

    and tcMonadic gtenv ltenv f e = match (f, tcE gtenv ltenv e) with
                                    | (o, ITyp) when List.exists (fun x -> x=o) unary_int_operators -> ITyp
                                    | (o, BTyp) when List.exists (fun x -> x=o) unary_bool_operators -> BTyp
                                    | s           -> failwith (sprintf "illegal/illtyped monadic expression %A" s)
   
    and tcDyadic gtenv ltenv f e1 e2 = match (f, tcE gtenv ltenv e1, tcE gtenv ltenv e2) with
                                        | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) arithmetic_operators -> ITyp
                                        | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) int_logic_operators  -> BTyp
                                        | (o, BTyp, BTyp) when List.exists (fun x ->  x=o) bool_logic_operators -> BTyp 
                                        | _                     -> failwith(sprintf "Illegal/illtyped dyadic expression %A %s %A" e1 f e2 )
    
    /// Checks the inputs for a function or procedure
    and tcFPInputs gtenv ltenv f es=
        let types = List.map (tcE gtenv ltenv) es
        
        // Check the i'th type in the function input list
        let check_type i x =
            match function_parameter_type gtenv f i with
            | None -> failwith ("At least " + (string)(i+1) + " parameters were supplied for function or procedure " + f + ", but it only needs " + (string)(i))
            | Some(typ) -> 
                match (typ, x) with
                | (ATyp(t1, None), ATyp(t2, _))->
                    if t1 <> t2 then failwith ("Parameter " + (string)(i+1) + " for function or procedure " + f + " is of wrong type")
                | _, _ ->
                    if typ <> x then failwith ("Parameter " + (string)(i+1) + " for function or procedure " + f + " is of wrong type")
                
        
        match function_parameter_type gtenv f types.Length with
        | None -> ()
        | Some(_) -> failwith ("Function " + f + " was not supplied enough parameters! It got " + (string)types.Length + ", but needs more TODO:HOW MANY?")
        List.mapi check_type types |> ignore

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

    /// tcA gtenv ltenv acc gives the type for access acc on the basis of type environments gtenv and ltenv
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
                match tcA gtenv ltenv acc with
                | ATyp(element_type, _) -> element_type
                | _ -> failwith "Trying to index a non-array variable!"
                
            | ADeref e       ->
                match tcE gtenv ltenv e with
                | PTyp(typ) -> typ
                | _ -> failwith "Only pointers can be dereferenced"

    /// tcS gtenv ltenv s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
    /// for global and local variables 
    and tcS gtenv ltenv = function                           
                            | PrintLn e -> tcE gtenv ltenv e |> ignore
                            | Ass(acc,e) -> 
                                let atyp = tcA gtenv ltenv acc
                                let etyp = tcE gtenv ltenv e
                                if atyp = etyp 
                                then ()
                                else failwith (sprintf "illtyped assignment %A = %A, %A=%A" acc e atyp etyp) 
                            | Mass(accs, es)   ->
                                let listOfAccess = List.zip accs es
                                List.iter (fun (a,e) -> tcS gtenv ltenv (Ass(a,e))) listOfAccess                               
                            | Block([],stms) -> List.iter (tcS gtenv ltenv) stms
                            | Block(decs, stms) ->
                                //if List.length decs > 0 then failwith "Inner local declarations are currently disallowed!" 
                                let (ltenv,_) = tcLDecs gtenv false (ltenv, []) decs
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

    /// Handles preparing for function declarations.
    and tcFunDecOuter gtenv topt f decs stm =
        // Append to the global environment
        let gtenv = 
            match topt with
            | None -> Map.add (procedure_prefix + f) ITyp gtenv
            | Some(typ) -> Map.add (return_prefix + f) typ gtenv

        let (_, types) = tcLDecs gtenv true (Map.empty, []) decs //TODO maybe split tcLDecs
        // Add function input types to the global environment so we can type check them later
        let gtenv = 
            List.mapi (fun i x -> ((function_parameter_name f i),x)) types
            |> List.fold (fun s (name,typ) -> Map.add name typ s) gtenv
        gtenv
        
    /// Handle a function declaration; append its parameter and return types to the global environment,
    /// and handle the inner environment as well.
    and tcFunDec gtenv topt f decs stm =
        // Check that if we're dealing with a function, all paths return a value
        match topt with
        | Some(_) when not (returning_statement stm) -> failwith ("Not all paths through function " + f + " have a return value!")
        | _ -> ()
        
        // Create and prepare the local environment for entry
        let ltenv = match topt with
                    | None -> enter_procedure Map.empty
                    | Some(typ) -> enter_function Map.empty typ

        // Then type check declarations
        let (ltenv, _) = tcLDecs gtenv true (ltenv, []) decs

        // Type check the insides of the function
        tcS gtenv ltenv stm
        gtenv

    /// Handles a single global declaration
    and tcGDec gtenv = function
                       | VarDec(t,s) -> 
                           check_exists s gtenv
                           
                           match t with
                           | ATyp(_, None) -> failwith "Arrays cannot be declared without a length"
                           | _ -> ()
                           Map.add s t gtenv
                       | FunDec(topt,f, decs, stm) ->
                           tcFunDec gtenv topt f decs stm

    /// Handles a list of global declarations
    and tcGDecs gtenv = function
                        | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
                        | _         -> gtenv

    /// Handles a single global declaration
    and tcPreDec gtenv = function
                        | VarDec _-> gtenv
                        | FunDec(topt,f, decs, stm) ->
                            check_exists f gtenv
                            tcFunDecOuter gtenv topt f decs stm

    /// Handles a list of global declarations
    and tcPreDecs gtenv = function
                        | dec::decs -> tcPreDecs (tcPreDec gtenv dec) decs
                        | _         -> gtenv

    /// Handles a single local declaration
    and tcLDec gtenv in_function_declaration (ltenv, local_types)  = function
                                            | VarDec(t,s) -> 
                                                check_exists s ltenv
                                                match t with
                                                | ATyp(_, None) when not in_function_declaration -> failwith "Arrays cannot be declared without a length"
                                                | _ -> ()
                                                Map.add s t ltenv, local_types @ [t]
                                            | FunDec(_,_,_,_) -> failwith "Local function declarations are not allowed"

    /// Handles a list of local declarations
    /// 
    /// Returns both the resulting local environment and the list of locally declared types in order,
    /// since the types are needed for function definitions
    and tcLDecs gtenv in_function_declaration (ltenv, local_types) = function
                              | dec::decs -> tcLDecs gtenv in_function_declaration (tcLDec gtenv in_function_declaration (ltenv,local_types)  dec) decs
                              | _ -> (ltenv, local_types)

    and tcGC gtenv ltenv = function
        | GC(ls) ->
            List.iter (fun (exp, stmts) -> 
                if tcE gtenv ltenv exp <> BTyp then failwith "Guarded Command expression not of boolean type!"
                List.iter (tcS gtenv ltenv) stmts
            ) ls

    /// tcP prog checks the well-typeness of a program prog
    and tcP(P(decs, stms)) = 
        let gtenv = tcPreDecs Map.empty decs
        let gtenv = tcGDecs gtenv decs
        List.iter (tcS gtenv Map.empty) stms

  
