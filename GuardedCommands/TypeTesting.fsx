#load "AST.fs"
#load "TypeCheck.fs"

open GuardedCommands.Frontend.AST
open GuardedCommands.Frontend.TypeCheck


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
    

let test () =
    test_passing_program type_checking_tree_1 "1"
    test_passing_program type_checking_tree_2 "2"
    test_passing_program type_checking_tree_3 "3"
    test_passing_program type_checking_tree_4 "4"
    test_passing_program type_checking_tree_5 "5"
    test_passing_program type_checking_tree_6 "6"
    test_failing_program type_failing_tree_1 "1"
    test_failing_program type_failing_tree_2 "1"
    test_failing_program type_failing_tree_3 "3"
    test_failing_program type_failing_tree_4 "4"
    test_failing_program type_failing_tree_5 "5"
    test_failing_program type_failing_tree_6 "6"

test()
