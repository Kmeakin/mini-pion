#![feature(iter_intersperse)]
#![allow(clippy::needless_raw_string_hashes)]

use expect_test::*;

const PION: &str = env!("CARGO_BIN_EXE_pion");

fn check(expr: &str, mut expected: Expect) {
    let mut shell = std::process::Command::new("/bin/sh");
    let shell = shell.arg("-c");
    let command = shell.arg(format!(
        "\
{PION} check - <<EOF
{expr}
EOF"
    ));
    let output = command.output().unwrap();

    let output = {
        let mut stdout = output.stdout;
        let mut stderr = output.stderr;
        stdout.append(&mut stderr);
        String::from_utf8(stdout).unwrap()
    };

    let output: String = output
        .lines()
        .map(str::trim_end)
        .intersperse("\n")
        .collect();

    expected.indent(false);
    expected.assert_eq(&output);
}

fn eval(expr: &str, mut expected: Expect) {
    let mut shell = std::process::Command::new("/bin/sh");
    let shell = shell.arg("-c");
    let command = shell.arg(format!(
        "\
{PION} eval - <<EOF
{expr}
EOF"
    ));
    let output = command.output().unwrap();

    let output = {
        let mut stdout = output.stdout;
        let mut stderr = output.stderr;
        stdout.append(&mut stderr);
        String::from_utf8(stdout).unwrap()
    };

    let output: String = output
        .lines()
        .map(str::trim_end)
        .intersperse("\n")
        .collect();

    expected.indent(false);
    expected.assert_eq(&output);
}

#[test]
fn parse_errors() {
    check(
        "fun ",
        expect![[r##"
#error : #error
error: Syntax error: unexpected end of file
  ┌─ <stdin>:1:4
  │
1 │ fun
  │    ^ expected one of "(", "@", "Ident" or "_"
"##]],
    );
}

#[test]
fn consts() {
    check("true", expect!["true : Bool"]);
    check("false", expect!["false : Bool"]);
    check("5", expect!["5 : Int"]);
}

#[test]
fn prims() {
    check("Type", expect!["Type : Type"]);
    check("Int", expect!["Int : Type"]);
    check("Bool", expect!["Bool : Type"]);
    check("add", expect!["add : Int -> Int -> Int"]);
    check("sub", expect!["sub : Int -> Int -> Int"]);
    check("mul", expect!["mul : Int -> Int -> Int"]);
    check("eq", expect!["eq : Int -> Int -> Bool"]);
    check("ne", expect!["ne : Int -> Int -> Bool"]);
    check("lt", expect!["lt : Int -> Int -> Bool"]);
    check("gt", expect!["gt : Int -> Int -> Bool"]);
    check("lte", expect!["lte : Int -> Int -> Bool"]);
    check("gte", expect!["gte : Int -> Int -> Bool"]);
    check(
        "fix",
        expect!["fix : forall (@A : Type) (@B : Type) -> ((A -> B) -> A -> B) -> A -> B"],
    );
}

#[test]
fn arith_prims() {
    eval("add 3 2", expect!["5 : Int"]);
    eval("sub 3 2", expect!["1 : Int"]);
    eval("mul 3 2", expect!["6 : Int"]);
    eval("eq 1 0", expect!["false : Bool"]);
    eval("ne 1 0", expect!["true : Bool"]);
    eval("lt 1 0", expect!["false : Bool"]);
    eval("gt 1 0", expect!["true : Bool"]);
    eval("lte 1 0", expect!["false : Bool"]);
    eval("gte 1 0", expect!["true : Bool"]);
}

#[test]
fn fun_arrow() { check("Int -> Bool", expect!["(Int -> Bool) : Type"]); }

#[test]
fn fun_type() {
    check("forall (x : Int) -> Bool", expect!["(Int -> Bool) : Type"]);
    check(
        "forall (A : Type) -> A -> A",
        expect!["(forall (A : Type) -> A -> A) : Type"],
    );
    check(
        "forall (A : Type) (B: Type) -> A -> B",
        expect!["(forall (A : Type) (B : Type) -> A -> B) : Type"],
    );
    check(
        "forall (A : Type) (_ : A) -> A",
        expect!["(forall (A : Type) -> A -> A) : Type"],
    );
}

#[test]
fn fun_lit() {
    check(
        "fun(x : Int) => x",
        expect!["(fun (x : Int) => x) : Int -> Int"],
    );
    check(
        "fun (x : Int) (y : Bool) => x",
        expect!["(fun (x : Int) (y : Bool) => x) : Int -> Bool -> Int"],
    );
    check(
        "fun x => x",
        expect![[r#"
(fun (x : ?0) => x) : ?0 -> ?0
error: Unsolved metavariable: ?0
  ┌─ <stdin>:1:5
  │
1 │ fun x => x
  │     ^ could not infer type of variable `x`
"#]],
    );
    check(
        "fun x y => x",
        expect![[r#"
(fun (x : ?0) (y : ?1 x) => x) : forall (x : ?0) -> ?1 x -> ?0
error: Unsolved metavariable: ?0
  ┌─ <stdin>:1:5
  │
1 │ fun x y => x
  │     ^ could not infer type of variable `x`

error: Unsolved metavariable: ?1
  ┌─ <stdin>:1:7
  │
1 │ fun x y => x
  │       ^ could not infer type of variable `y`
"#]],
    );
    check(
        "(fun x => x) : Int -> Int",
        expect!["(fun (x : Int) => x) : Int -> Int"],
    );
    check(
        "(fun x y => x) : Int -> Bool -> Int",
        expect!["(fun (x : Int) (y : Bool) => x) : Int -> Bool -> Int"],
    );
}

#[test]
fn fun_app() {
    check("(fun x => x) 1", expect!["((fun (x : Int) => x) 1) : Int"]);
    check(
        "(fun x => x) 1 2 3",
        expect![[r#"
#error : #error
error: Expected function, found `Int`
  ┌─ <stdin>:1:1
  │
1 │ (fun x => x) 1 2 3
  │ ^^^^^^^^^^^^^^
"#]],
    );
}

#[test]
fn r#let() {
    check(
        "let f = fun x => x; f false",
        expect![[r#"
let f : Bool -> Bool = fun (x : Bool) => x;
(f false) : Bool"#]],
    );
    check(
        "let f : Bool -> Bool = fun x => x; f false",
        expect![[r#"
let f : Bool -> Bool = fun (x : Bool) => x;
(f false) : Bool"#]],
    );
}

#[test]
fn holes() {
    check(
        "let x: _ = 5; x",
        expect![[r#"
let x : Int = 5;
x : Int"#]],
    );
}

#[test]
fn implicit_args() {
    check("@Int -> Bool", expect!["(@Int -> Bool) : Type"]);
    check("forall (@x: Int) -> Bool", expect!["(@Int -> Bool) : Type"]);
    check(
        "fun (@x : Int) => x",
        expect!["(fun (@x : Int) => x) : @Int -> Int"],
    );
    check(
        "(fun (@x : Int) => x) @5",
        expect!["((fun (@x : Int) => x) @5) : Int"],
    );
    eval("(fun (@x : Int) => x) @5", expect!["5 : Int"]);
}

#[test]
fn generalize() {
    check(
        "let id: forall (@A: Type) -> A -> A = fun x => x; id",
        expect![[r#"
let id : forall (@A : Type) -> A -> A = fun (@A : Type) (x : A) => x;
id : forall (@A : Type) -> A -> A"#]],
    );
}

#[test]
fn specialize() {
    check(
        "let id: forall (@A: Type) -> A -> A = fun x => x; id 5",
        expect![[r#"
let id : forall (@A : Type) -> A -> A = fun (@A : Type) (x : A) => x;
(id @Int 5) : Int"#]],
    );
}

#[test]
fn plicity_mismatch() {
    check(
        "(fun (x : Int) => x) @5",
        expect![[r#"
#error : #error
error: Applied implicit argument when explicit argument was expected
  ┌─ <stdin>:1:22
  │
1 │ (fun (x : Int) => x) @5
  │ -------------------- ^^ implicit argument
  │ │
  │ function has type Int -> Int
"#]],
    );
}

#[test]
fn if_then_else() {
    check(
        "if true then 1 else 0",
        expect!["(if true then 1 else 0) : Int"],
    );
    eval("if true then 1 else 0", expect!["1 : Int"]);
}

#[test]
fn fixpoint_factorial() {
    let fact = "fix (fun fact n => if eq n 0 then 1 else mul n (fact (sub n 1)))";

    check(
        fact,
        expect![
            "(fix @Int @Int (fun (fact : Int -> Int) (n : Int) => if eq n 0 then 1 else mul n \
             (fact (sub n 1)))) : Int -> Int"
        ],
    );
    eval(
        fact,
        expect![
            "(fix @Int @Int (fun (fact : Int -> Int) (n : Int) => if eq n 0 then 1 else mul n \
             (fact (sub n 1)))) : Int -> Int"
        ],
    );
    eval(&format!("{fact} 5"), expect!["120 : Int"]);
}

#[test]
fn fixpoint_parity() {
    let evenodd = "fix (fun (evenodd : Bool -> Int -> Bool) b n => if b then (if eq n 0 then true \
                   else evenodd false (sub n 1)) else (if eq n 0 then false else evenodd true \
                   (sub n 1)))";

    check(
        evenodd,
        expect![
            "(fix @Bool @(Int -> Bool) (fun (evenodd : Bool -> Int -> Bool) (b : Bool) (n : Int) \
             => if b then if eq n 0 then true else evenodd false (sub n 1) else if eq n 0 then \
             false else evenodd true (sub n 1))) : Bool -> Int -> Bool"
        ],
    );
    eval(
        evenodd,
        expect![
            "(fix @Bool @(Int -> Bool) (fun (evenodd : Bool -> Int -> Bool) (b : Bool) (n : Int) \
             => if b then if eq n 0 then true else evenodd false (sub n 1) else if eq n 0 then \
             false else evenodd true (sub n 1))) : Bool -> Int -> Bool"
        ],
    );
    eval(
        &format!("{evenodd} true"),
        expect![
            "(fun (n : Int) => if eq n 0 then true else fix @Bool @(Int -> Bool) (fun (evenodd : \
             Bool -> Int -> Bool) (b : Bool) (n : Int) => if b then if eq n 0 then true else \
             evenodd false (sub n 1) else if eq n 0 then false else evenodd true (sub n 1)) false \
             (sub n 1)) : Int -> Bool"
        ],
    );
    eval(&format!("{evenodd} true 3"), expect!["false : Bool"]);
}

#[test]
fn dpairs() {
    check(
        "DPair",
        expect!["DPair : forall (A : Type) -> (A -> Type) -> Type"],
    );
    check(
        "MkDPair",
        expect!["MkDPair : forall (@A : Type) (@B : A -> Type) (a : A) -> B a -> DPair A B"],
    );
    check(
        "dhead",
        expect!["dhead : forall (@A : Type) (@B : A -> Type) -> DPair A B -> A"],
    );
    check(
        "dtail",
        expect!["dtail : forall (@A : Type) (@B : A -> Type) (p : DPair A B) -> B (dhead @A @B p)"],
    );
}

#[test]
fn pairs() {
    let pair_type = "fun A B => DPair A (fun _ => B)";
    let mkpair = "fun @A @B a b => MkDPair @A @(fun _ => B) a b";
    let head = "fun @A @B p => dhead @A @(fun _ => B) p";
    let tail = "fun @A @B p => dtail @A @(fun _ => B) p";

    check(
        pair_type,
        expect!["(fun (A : Type) (B : Type) => DPair A (fun (_ : A) => B)) : Type -> Type -> Type"],
    );
    check(
        mkpair,
        expect![
            "(fun (@A : Type) (@B : Type) (a : A) (b : B) => MkDPair @A @(fun (_ : A) => B) a b) \
             : forall (@A : Type) (@B : Type) -> A -> B -> DPair A (fun (_ : A) => B)"
        ],
    );
    check(
        head,
        expect![
            "(fun (@A : Type) (@B : Type) (p : DPair A (fun (_ : A) => B)) => dhead @A @(fun (_ : \
             A) => B) p) : forall (@A : Type) (@B : Type) -> DPair A (fun (_ : A) => B) -> A"
        ],
    );
    check(
        tail,
        expect![
            "(fun (@A : Type) (@B : Type) (p : DPair A (fun (_ : A) => B)) => dtail @A @(fun (_ : \
             A) => B) p) : forall (@A : Type) (@B : Type) -> DPair A (fun (_ : A) => B) -> B"
        ],
    );

    eval(
        &format!("let MKPair = {mkpair}; MKPair 1 false"),
        expect![
            "(MkDPair @Int @(fun (_ : Int) => Bool) 1 false) : DPair Int (fun (_ : Int) => Bool)"
        ],
    );
    eval(
        &format!("let MKPair = {mkpair}; let head = {head}; let p = MKPair 1 false; head p"),
        expect!["1 : Int"],
    );
    eval(
        &format!("let MKPair = {mkpair}; let tail = {tail}; let p = MKPair 1 false; tail p"),
        expect!["false : Bool"],
    );
}

#[test]
fn fixpoint_fix2() {
    check(
        r#"
let Pair = fun A B => DPair A (fun _ => B);
let MkPair = fun @A @B a b => MkDPair @A @(fun _ => B) a b;
let head = fun @A @B p => dhead @A @(fun _ => B) p;
let tail = fun @A @B p => dtail @A @(fun _ => B) p;

let fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) -> ((Pair (A1 -> B1) (A2 -> B2)) -> Pair (A1 -> B1) (A2 -> B2)) -> (Pair (A1 -> B1) (A2 -> B2))
= fun @A1 @B1 @A2 @B2 =>
fix (fun (fix2 : ((Pair (A1 -> B1) (A2 -> B2)) -> Pair (A1 -> B1) (A2 -> B2)) -> (Pair (A1 -> B1) (A2 -> B2))) f => MkPair
   (fun x => head (f (fix2 f)) x)
   (fun x => tail (f (fix2 f)) x)
);
fix2
"#,
        expect![[r#"
let Pair : Type -> Type -> Type = fun (A : Type) (B : Type) => DPair A (fun (_ : A) => B);
let MkPair : forall (@A : Type) (@B : Type) -> A -> B -> DPair A (fun (_ : A) => B) = fun (@A : Type) (@B : Type) (a : A) (b : B) => MkDPair @A @(fun (_ : A) => B) a b;
let head : forall (@A : Type) (@B : Type) -> DPair A (fun (_ : A) => B) -> A = fun (@A : Type) (@B : Type) (p : DPair A (fun (_ : A) => B)) => dhead @A @(fun (_ : A) => B) p;
let tail : forall (@A : Type) (@B : Type) -> DPair A (fun (_ : A) => B) -> B = fun (@A : Type) (@B : Type) (p : DPair A (fun (_ : A) => B)) => dtail @A @(fun (_ : A) => B) p;
let fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) -> (DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2) = fun (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) => fix @(DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)) @(DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)) (fun (fix2 : (DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)) (f : DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)) => MkPair @(A1 -> B1) @(A2 -> B2) (fun (x : A1) => head @(A1 -> B1) @(A2 -> B2) (f (fix2 f)) x) (fun (x : A2) => tail @(A1 -> B1) @(A2 -> B2) (f (fix2 f)) x));
fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) -> (DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)) -> DPair (A1 -> B1) (fun (_ : A1 -> B1) => A2 -> B2)"#]],
    );
}

#[test]
fn fix2_parity() {
    eval(
        r#"
let Pair = fun A B => DPair A (fun _ => B);
let MkPair = fun @A @B a b => MkDPair @A @(fun _ => B) a b;
let head = fun @A @B p => dhead @A @(fun _ => B) p;
let tail = fun @A @B p => dtail @A @(fun _ => B) p;

let fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type)
           -> ((Pair (A1 -> B1) (A2 -> B2)) -> Pair (A1 -> B1) (A2 -> B2))
           -> (Pair (A1 -> B1) (A2 -> B2))
= fun @A1 @B1 @A2 @B2 =>
fix (fun (fix2 : ((Pair (A1 -> B1) (A2 -> B2)) -> Pair (A1 -> B1) (A2 -> B2)) -> (Pair (A1 -> B1) (A2 -> B2))) f => MkPair
   (fun x => head (f (fix2 f)) x)
   (fun x => tail (f (fix2 f)) x)
);

let evenodd : Pair (Int -> Bool) (Int -> Bool)
= fix2 (fun evenodd => MkPair
    (fun n => if eq n 0 then true else tail evenodd (sub n 1))
    (fun n => if eq n 0 then false else head evenodd (sub n 1))
);
let even = head evenodd;
let odd = tail evenodd;
even 2
"#,
        expect!["true : Bool"],
    );
}

#[test]
fn letrec() {
    check(
        "let rec fact : Int -> Int = fun n => if eq n 0 then 1 else mul n (fact (sub n 1)); fact",
        expect![[r#"
let fact : Int -> Int = fix @Int @Int (fun (fact : Int -> Int) (n : Int) => if eq n 0 then 1 else mul n (fact (sub n 1)));
fact : Int -> Int"#]],
    );
    eval(
        "let rec fact : Int -> Int = fun n => if eq n 0 then 1 else mul n (fact (sub n 1)); fact",
        expect![
            r#"(fix @Int @Int (fun (fact : Int -> Int) (n : Int) => if eq n 0 then 1 else mul n (fact (sub n 1)))) : Int -> Int"#
        ],
    );
    eval(
        "let rec fact : Int -> Int = fun n => if eq n 0 then 1 else mul n (fact (sub n 1)); fact 5",
        expect!["120 : Int"],
    );
}

#[test]
fn record_literals() {
    check("{}", expect!["{} : {}"]);
    check(
        "{x=1, y=false}",
        expect!["{x = 1, y = false} : {x : Int, y : Bool}"],
    );
    check("{x=1, y=false}.x", expect!["{x = 1, y = false}.x : Int"]);
    eval("{x=1, y=false}.x", expect!["1 : Int"]);
}

#[test]
fn record_types() {
    check("{} : Type", expect!["{} : Type"]);
    check("{x: Int}", expect!["{x : Int} : Type"]);
    check("{A: Type, a: A}", expect!["{A : Type, a : A} : Type"]);
}

#[test]
fn tuple_literals() {
    check("()", expect!["{} : {}"]);
    check("(1,)", expect!["{_0 = 1} : {_0 : Int}"]);
    check(
        "(1,2,3)",
        expect!["{_0 = 1, _1 = 2, _2 = 3} : {_0 : Int, _1 : Int, _2 : Int}"],
    );
    check("() : Type", expect!["{} : Type"]);
    check("(Bool,) : Type", expect!["{_0 : Bool} : Type"]);
    check("(Bool, Int) : Type", expect!["{_0 : Bool, _1 : Int} : Type"]);
}
