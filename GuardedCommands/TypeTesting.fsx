
#r "C:/Users/carl/.nuget/packages/fscheck/2.15.3/lib/netstandard2.0/FsCheck.dll"
#load "AST.fs"
#load "TypeCheck.fs"

open GuardedCommands.Frontend.AST
open GuardedCommands.Frontend.TypeCheck
open FsCheck

let type_checking_tree_1 = 
    P(
        [FunDec(None, "f", [], Do(GC([])))],
        [Call("f", [])]
    )

let type_checking_tree_2 =
    P(
        [
            FunDec(Some ITyp, "g", [], Return (Some (Exp.N 2)));
            FunDec(None, "f", [], 
                PrintLn (Apply("+", [Apply("g",[]); Exp.N 2])))
                ],
        [Call("f", [])]
    )

let type_failing_tree_1 = 
    P(
        [FunDec(Some ITyp, "f", [], Do(GC([])))],
        [Call("f", [])]
    )

let type_failing_tree_2 =
    P(
        [
            FunDec(Some BTyp, "g", [], Return (Some (Exp.N 2)));
            FunDec(None, "f", [], 
                PrintLn (Apply("+", [Apply("g",[]); Exp.N 2])))
                ],
        [Call("f", [])]
    )

let type_failing_tree_3 =
    P(
        [
            FunDec(Some BTyp, "g", [], Return (Some (Exp.B true)));
            FunDec(None, "f", [], 
                PrintLn (Apply("+", [Apply("g",[]); Exp.N 2])))
                ],
        [Call("f", [])]
    )

let type_failing_tree_4 =
    P(
        [
            FunDec(Some ITyp, "g", [VarDec(ITyp, "k")], Return (Some (Exp.N 2)));
            FunDec(None, "f", [], 
                PrintLn (Apply("+", [Apply("g",[]); Exp.N 2])))
                ],
        [Call("f", [])]
    )

let type_checking_tree_3=
    P(
        [
            VarDec(ITyp, "l");
            FunDec(Some ITyp, "g", [VarDec(ITyp, "k")], Return (Some (Exp.N 2)));
            FunDec(None, "f", [VarDec(ITyp, "o")], 
                PrintLn (Apply("+", [Apply("g",[Access(AVar("o"))]); Exp.N 2])))
                ],
        [Call("f", [Access(AVar("l"))])]
    )
    
let type_failing_tree_5 =
    P([FunDec(None, "f", [], Do(GC([])));
        FunDec(Some ITyp, "f", [], Return (Some (Exp.N 2)))],
        [Call("f", [])])


let type_failing_tree_6 =
    P([FunDec(None, "f", [VarDec(ITyp, "k");VarDec(ITyp, "k")], Do(GC([])))],
        [Call("f", [Exp.N 2;Exp.N 2])])

let type_checking_tree_4 =
    P([VarDec(ITyp, "k");VarDec(PTyp(ITyp), "j")],
        [Ass(AVar("j"), Addr(AVar("k")))])

/// Contains all unary and binary operators
let type_checking_tree_5 =
    P([VarDec(ITyp, "k");VarDec(PTyp(ITyp), "j");VarDec(BTyp, "b")],
        [Ass(AVar("j"), Addr(AVar("k")));
        Ass(ADeref(Access(AVar("j"))), Exp.N 2);
        Do(
            GC([
                Apply("=", [Access(ADeref(Access(AVar("j")))); Exp.N 2]),[];
                Apply("<>", [Access(ADeref(Access(AVar("j")))); Exp.N 2]),[];
                Apply("<", [Access(ADeref(Access(AVar("j")))); Exp.N 2]),[];
                Apply(">", [Access(ADeref(Access(AVar("j")))); Exp.N 2]),[];
                Apply("<=", [Access(ADeref(Access(AVar("j")))); Exp.N 2]),[];
                Apply(">=", [Access(ADeref(Access(AVar("j")))); Exp.N 2]),[];
                Apply("<>", [Access(AVar("b")); Exp.B true]),[];
                Apply("=", [Access(AVar("b")); Exp.B true]),[];
                Apply("&&", [Access(AVar("b")); Exp.B true]),[];
                Apply("||", [Access(AVar("b")); Exp.B true]),[];
                Apply("=", [Apply("/", [Exp.N 1; Exp.N 1]); Exp.N 1]),[];
                Apply("=", [Apply("*", [Exp.N 1; Exp.N 1]); Exp.N 1]),[];
                Apply("=", [Apply("+", [Exp.N 1; Exp.N 1]); Exp.N 1]),[];
                Apply("=", [Apply("/", [Apply("-", [Exp.N 1]); Exp.N 1]); Exp.N 1]),[];
                Apply("!", [Exp.B false]), [];
            ])
        )
    ])

let type_checking_tree_6 =
    P(
        [VarDec(ATyp (ITyp, Some 3), "a");VarDec(PTyp(ITyp), "j")],
        [
            //Ass(AVar("j"), Addr(AIndex(AVar("a"), Exp.N 1)));
            Do(
                GC([
                    Apply("=", [Access(AIndex(AVar("a"), Exp.N 1)); Exp.N 1]),[]
                ])
            )
        ])

/// Check that all paths must return a value
let type_failing_tree_7 =
    P(
        [FunDec(Some ITyp, "f", [], PrintLn (Exp.N 2))],
        [PrintLn ( Apply ("f", []) )]
    )

/// Check that when all paths return a value, it type checks
let type_checking_tree_7 =
    P(
        [FunDec(Some ITyp, "f", [], Block([], [PrintLn (Exp.N 2); Return (Some (Exp.N 3))]))],
        [PrintLn ( Apply ("f", []) )]
    )

let test_failing_program program name=
    let mutable failed = true
    try
        tcP program
        failed <- false
    with
        | _ -> ()
    
    if not failed then failwith "Failing program didn't fail to typecheck"
    printfn "Failing program %s failed successfully " name

let test_passing_program program name =
    tcP program
    printfn "Passing program %s passed successfully " name

type BinaryOp = BOP of string
let binaryIntOps = ["="; "<>"; "/"; "*"; "-"; "+"; "<"; ">"; "<="; ">="]
let binaryBoolOps = ["="; "<>"; "&&"; "||"]
let binaryOps = binaryIntOps @ binaryBoolOps |> Set.ofList |> Set.toList

type Generators =
    static member BinaryOp() =
        { new Arbitrary<BinaryOp>() with
            override x.Generator =
                binaryOps
                |> Gen.elements 
                |> Gen.map BOP
        }
Arb.register<Generators>() |> ignore

type Properties =
    //Check that address and deref are inverse
    static member type_check_addr_deref (typ:Typ) =
        let gtenv = Map.add "a" typ Map.empty
        let e1 = Access(ADeref(Addr(AVar("a"))))
        let e2 = Access(AVar("a"))
        tcE gtenv Map.empty e1 = tcE gtenv Map.empty e2

    /// Chck that the inner type of an array is returned when indexing the array
    static member type_check_arr_index (typ:Typ) =
        let gtenv = Map.add "a" typ Map.empty |> Map.add "b" (ATyp (typ,Some 3))
        let e1 = Access(AIndex(AVar "b", Exp.N 1))
        let e2 = Access(AVar("a"))
        tcE gtenv Map.empty e1 = tcE gtenv Map.empty e2
    
    /// Check that local variables are preferred over global variables
    static member type_check_local_global (gtyp:Typ) (ltyp:Typ) =
        let gtenv = Map.add "a" gtyp Map.empty
        let ltenv = Map.add "a" ltyp Map.empty
        let e = Access(AVar("a"))
        tcE gtenv ltenv e = ltyp
    
    /// Check that binary operators work correctly (Types must be correct, and types can't be incorrect)
    static member type_check_binary_operators (typ1:Typ) (typ2:Typ) (BOP(op)) =
        let gtenv = Map.add "a" typ1 Map.empty |> Map.add "b" typ2
        let e = Apply(op, [Access(AVar("a")); Access(AVar("b"))])
        match (typ1, typ2) with
        | (ITyp, ITyp) when List.contains op binaryIntOps->
            tcE gtenv Map.empty e |> ignore
            true
        | (BTyp, BTyp) when List.contains op binaryBoolOps ->
            tcE gtenv Map.empty e |> ignore
            true
        | (_, _) -> 
            try
                tcE gtenv Map.empty e |> ignore
                false
            with
            | _ -> true
   
Check.QuickAll<Properties>()

let test () =
    test_passing_program type_checking_tree_1 "1"
    test_passing_program type_checking_tree_2 "2"
    test_passing_program type_checking_tree_3 "3"
    test_passing_program type_checking_tree_4 "4"
    test_passing_program type_checking_tree_5 "5"
    test_passing_program type_checking_tree_6 "6"
    test_passing_program type_checking_tree_7 "7"
    test_failing_program type_failing_tree_1 "1"
    test_failing_program type_failing_tree_2 "2"
    test_failing_program type_failing_tree_3 "3"
    test_failing_program type_failing_tree_4 "4"
    test_failing_program type_failing_tree_5 "5"
    test_failing_program type_failing_tree_6 "6"
    test_failing_program type_failing_tree_7 "7"


test()
