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
  │    ^ expected one of "(", "@", "BinInt", "DecInt", "HexInt", "Ident", "_", "false", "true" or "{"
"##]],
    );
}

#[test]
fn literals() {
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
    check("let _ = 5; 10", expect!["10 : Int"]);
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
        expect![[r#"
match true {
    true => 1,
    false => 0,
} : Int"#]],
    );
    eval("if true then 1 else 0", expect!["1 : Int"]);
}

#[test]
fn record_literals() {
    check("{}", expect!["() : ()"]);
    check(
        "{x=1, y=false}",
        expect!["{x = 1, y = false} : {x : Int, y : Bool}"],
    );
    check("{x=1, y=false}.x", expect!["{x = 1, y = false}.x : Int"]);
    eval("{x=1, y=false}.x", expect!["1 : Int"]);
    check(
        "({A = Int, a = 5} : {A : Type, a : A}).a",
        expect!["{A = Int, a = 5}.a : Int"],
    );
}

#[test]
fn record_types() {
    check("{} : Type", expect!["() : Type"]);
    check("{x: Int}", expect!["{x : Int} : Type"]);
    check("{A: Type, a: A}", expect!["{A : Type, a : A} : Type"]);
}

#[test]
fn tuple_literals() {
    check("()", expect!["() : ()"]);
    check("(1,)", expect!["(1,) : (Int,)"]);
    check("(1,2,3)", expect!["(1, 2, 3) : (Int, Int, Int)"]);
    check("() : Type", expect!["() : Type"]);
    check("(Bool,) : Type", expect!["(Bool,) : Type"]);
    check("(Bool, Int) : Type", expect!["(Bool, Int) : Type"]);
}

#[test]
fn fixpoint_factorial() {
    let fact = "fix (fun fact n => if eq n 0 then 1 else mul n (fact (sub n 1)))";

    check(
        fact,
        expect![[r#"
(fix
    @Int
    @Int
    (fun (fact : Int -> Int) (n : Int) =>
        match (eq n 0) {
            true => 1,
            false => mul n (fact (sub n 1)),
        })) : Int -> Int"#]],
    );
    eval(
        fact,
        expect![[r#"
(fix
    @Int
    @Int
    (fun (fact : Int -> Int) (n : Int) =>
        match (eq n 0) {
            true => 1,
            false => mul n (fact (sub n 1)),
        })) : Int -> Int"#]],
    );
    eval(&format!("{fact} 5"), expect!["120 : Int"]);
}

#[test]
fn fixpoint_fix2() {
    check(
        r#"
let fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) -> ((A1 -> B1, A2 -> B2) -> (A1 -> B1, A2 -> B2)) -> (A1 -> B1, A2 -> B2)
= fun @A1 @B1 @A2 @B2 =>
fix (fun (fix2 : ((A1 -> B1, A2 -> B2) -> (A1 -> B1, A2 -> B2)) -> (A1 -> B1, A2 -> B2)) f => (
   (fun x => (f (fix2 f))._0 x),
   (fun x => (f (fix2 f))._1 x)
));
fix2
"#,
        expect![[r#"
let fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) ->
    ((A1 -> B1, A2 -> B2) -> (A1 -> B1, A2 -> B2)) -> (A1 -> B1, A2 -> B2)
    = fun (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) =>
        fix
            @((A1 -> B1, A2 -> B2) -> (A1 -> B1, A2 -> B2))
            @(A1 -> B1, A2 -> B2)
            (fun (fix2 : ((A1 -> B1, A2 -> B2) -> (A1 -> B1,
            A2 -> B2)) -> (A1 -> B1, A2 -> B2)) (f : (A1 -> B1,
            A2 -> B2) -> (A1 -> B1, A2 -> B2)) =>
                (fun (x : A1) => (f (fix2 f))._0 x,
                fun (x : A2) => (f (fix2 f))._1 x));
fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) ->
    ((A1 -> B1, A2 -> B2) -> (A1 -> B1, A2 -> B2)) -> (A1 -> B1, A2 -> B2)"#]],
    );
}

#[test]
fn fix2_parity() {
    eval(
        r#"
let fix2 : forall (@A1 : Type) (@B1 : Type) (@A2 : Type) (@B2 : Type) -> ((A1 -> B1, A2 -> B2) -> (A1 -> B1, A2 -> B2)) -> (A1 -> B1, A2 -> B2)
= fun @A1 @B1 @A2 @B2 =>
fix (fun (fix2 : ((A1 -> B1, A2 -> B2) -> (A1 -> B1, A2 -> B2)) -> (A1 -> B1, A2 -> B2)) f => (
   (fun x => (f (fix2 f))._0 x),
   (fun x => (f (fix2 f))._1 x)
));

let evenodd : (Int -> Bool, Int -> Bool)
= fix2 (fun evenodd => (
    fun n => if eq n 0 then true else evenodd._1 (sub n 1),
    fun n => if eq n 0 then false else evenodd._0 (sub n 1)
));
let even = evenodd._0;
let odd = evenodd._1;
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
let fact : Int -> Int
    = fix
        @Int
        @Int
        (fun (fact : Int -> Int) (n : Int) =>
            match (eq n 0) {
                true => 1,
                false => mul n (fact (sub n 1)),
            });
fact : Int -> Int"#]],
    );
    eval(
        "let rec fact : Int -> Int = fun n => if eq n 0 then 1 else mul n (fact (sub n 1)); fact",
        expect![[r#"
(fix
    @Int
    @Int
    (fun (fact : Int -> Int) (n : Int) =>
        match (eq n 0) {
            true => 1,
            false => mul n (fact (sub n 1)),
        })) : Int -> Int"#]],
    );
    eval(
        "let rec fact : Int -> Int = fun n => if eq n 0 then 1 else mul n (fact (sub n 1)); fact 5",
        expect!["120 : Int"],
    );
}

#[test]
fn record_pats() {
    check(
        "let p = (1, 2); let (x, y) = p; 5",
        expect![[r#"
let p : (Int, Int) = (1, 2);
let x : Int = p._0;
let y : Int = p._1;
5 : Int"#]],
    );
    check(
        "let (x, y) = (1, 2); (y, x)",
        expect![[r#"
let x : Int = (1, 2)._0;
let y : Int = (1, 2)._1;
(y, x) : (Int, Int)"#]],
    );

    check(
        "fun ((x, y) : (Int, Bool)) => (y, x)",
        expect![[r#"
(fun (_ : (Int, Bool)) =>
    let x : Int = _#0._0;
    let y : Bool = _#1._1;
    (y, x)) : (Int, Bool) -> (Bool, Int)"#]],
    );

    check(
        "forall ((x, y) : (Int, Bool)) -> Int",
        expect![[r#"
(forall (_ : (Int, Bool)) ->
    let x : Int = _#0._0;
    let y : Bool = _#1._1;
    Int) : Type"#]],
    );
}

#[test]
fn lists() {
    check("[1, 2, 3]", expect!["[1, 2, 3] : List Int"]);
    check("[] : List Int", expect!["[] : List Int"]);
    check(
        "[]",
        expect![[r#"
[] : List ?0
error: Unsolved metavariable: ?0
  ┌─ <stdin>:1:1
  │
1 │ []
  │ ^^ could not infer element type of empty list
"#]],
    );

    eval("len [1, 2, 3]", expect!["3 : Int"]);
    eval("push [1, 2, 3] 4", expect!["[1, 2, 3, 4] : List Int"]);
    eval(
        "append [1, 2, 3] [4, 5, 6]",
        expect!["[1, 2, 3, 4, 5, 6] : List Int"],
    );
}

#[test]
fn equality() {
    check("Eq", expect!["Eq : forall (@A : Type) -> A -> A -> Type"]);
    check(
        "refl",
        expect!["refl : forall (@A : Type) (a : A) -> Eq @A a a"],
    );
    check(
        "subst",
        expect![[r#"
subst : forall (@A : Type) (@p : A -> Type) (a : A) (b : A) ->
    Eq @A a b -> p a -> p b"#]],
    );
    check(
        "
let sym: forall (@A: Type) (@a: A) (@b: A) -> Eq a b -> Eq b a
    = fun a_eq_b =>
        let p = fun x => Eq @A x a;
        let p_a  : p a = refl a;
        let goal : p b = subst @A @p a b a_eq_b p_a;
        goal
        ;
sym
    ",
        expect![[r#"
let sym : forall (@A : Type) (@a : A) (@b : A) -> Eq @A a b -> Eq @A b a
    = fun (@A : Type) (@a : A) (@b : A) (a_eq_b : Eq @A a b) =>
        let p : A -> Type = fun (x : A) => Eq @A x a;
        let p_a : Eq @A a a = refl @A a;
        let goal : Eq @A b a = subst @A @p a b a_eq_b p_a;
        goal;
sym : forall (@A : Type) (@a : A) (@b : A) -> Eq @A a b -> Eq @A b a"#]],
    );

    check(
        "
let trans: forall (@A: Type) (@a: A) (@b: A) (@c: A) -> Eq a b -> Eq b c -> Eq a c
    = fun a_eq_b b_eq_c =>
        let p = fun x => Eq @A a x;
        let p_b  : p b = a_eq_b;
        let goal : p c = subst @A @p b c b_eq_c p_b;
        goal
        ;
trans
    ",
        expect![[r#"
let trans : forall (@A : Type) (@a : A) (@b : A) (@c : A) ->
    Eq @A a b -> Eq @A b c -> Eq @A a c
    = fun (@A : Type) (@a : A) (@b : A) (@c : A) (a_eq_b : Eq @A a b)
    (b_eq_c : Eq @A b c) =>
        let p : A -> Type = fun (x : A) => Eq @A a x;
        let p_b : Eq @A a b = a_eq_b;
        let goal : Eq @A a c = subst @A @p b c b_eq_c p_b;
        goal;
trans : forall (@A : Type) (@a : A) (@b : A) (@c : A) ->
    Eq @A a b -> Eq @A b c -> Eq @A a c"#]],
    );

    check(
        "
let cong: forall (@A: Type) (@B: Type) (@a: A) (@b: A) (f: A -> B) -> Eq a b -> Eq (f a) (f b)
    = fun f a_eq_b =>
        let p = fun x => Eq @B (f a) (f x);
        let p_a:  p a = refl (f a);
        let goal: p b = subst @A @p a b a_eq_b p_a;
        goal
        ;
cong
        ",
        expect![[r#"
let cong : forall (@A : Type) (@B : Type) (@a : A) (@b : A) (f : A -> B) ->
    Eq @A a b -> Eq @B (f a) (f b)
    = fun (@A : Type) (@B : Type) (@a : A) (@b : A) (f : A -> B) (a_eq_b : Eq
        @A
        a
        b) =>
        let p : A -> Type = fun (x : A) => Eq @B (f a) (f x);
        let p_a : Eq @B (f a) (f a) = refl @B (f a);
        let goal : Eq @B (f a) (f b) = subst @A @p a b a_eq_b p_a;
        goal;
cong : forall (@A : Type) (@B : Type) (@a : A) (@b : A) (f : A -> B) ->
    Eq @A a b -> Eq @B (f a) (f b)"#]],
    );

    check(
        "
let cong-app: forall (@A: Type) (@B: Type) (a: A) (f: A -> B) (g: A -> B)
    -> Eq f g -> Eq (f a) (g a)
    = fun a f g f_eq_g =>
        let p = fun (x : A -> B) => Eq @B (f a) (x a);
        let p_f : p f = refl _;
        let goal = subst @(A -> B) @p f g f_eq_g p_f;
        goal
        ;
cong-app
        ",
        expect![[r#"
let cong-app : forall (@A : Type) (@B : Type) (a : A) (f : A -> B)
(g : A -> B) -> Eq @(A -> B) f g -> Eq @B (f a) (g a)
    = fun (@A : Type) (@B : Type) (a : A) (f : A -> B) (g : A -> B) (f_eq_g : Eq
        @(A -> B)
        f
        g) =>
        let p : (A -> B) -> Type = fun (x : A -> B) => Eq @B (f a) (x a);
        let p_f : Eq @B (f a) (f a) = refl @B (f a);
        let goal : Eq @B (f a) (g a) = subst @(A -> B) @p f g f_eq_g p_f;
        goal;
cong-app : forall (@A : Type) (@B : Type) (a : A) (f : A -> B) (g : A -> B) ->
    Eq @(A -> B) f g -> Eq @B (f a) (g a)"#]],
    );
}

#[test]
fn dependent_if_then_else() {
    check(
        "
let not = fun b => if b then false else true;

let not-false-is-true : Eq (not false) true = refl _;
let not-true-is-false : Eq (not true) false = refl _;

let not-inverse : forall b -> Eq (not (not b)) b
    = fun b =>
        let p = fun a => Eq (not (not a)) a;
        let p-true = refl _;
        let p-false = refl _;
        bool_rec @p b p-true p-false
        ;
()
",
        expect![[r#"
let not : Bool -> Bool
    = fun (b : Bool) =>
        match b {
            true => false,
            false => true,
        };
let not-false-is-true : Eq @Bool true true = refl @Bool true;
let not-true-is-false : Eq @Bool false false = refl @Bool false;
let not-inverse : forall (b : Bool) ->
    Eq
        @Bool
        match match b {
            true => false,
            false => true,
        } {
            true => false,
            false => true,
        }
        b
    = fun (b : Bool) =>
        let p : Bool -> Type = fun (a : Bool) => Eq @Bool (not (not a)) a;
        let p-true : Eq @Bool true true = refl @Bool true;
        let p-false : Eq @Bool false false = refl @Bool false;
        bool_rec @p b p-true p-false;
() : ()"#]],
    );
}

#[test]
fn r#match() {
    check(
        "
let and1 = fun x y => match (x, y) {
    (true, true) => true,
    _ => false,
};

let and2 = fun x y => match (x, y) {
    (true, true) => true,
    (_, _) => false,
};

let and3 = fun x y => match (x, y) {
    (true, true) => true,
    (false, true) => false,
    (true, false) => false,
    (false, false) => false,
};

let or1 = fun x y => match (x, y) {
    (false, false) => false,
    _ => true,
};

let or2 = fun x y => match (x, y) {
    (false, false) => false,
    (_, _) => true,
};

let or3 = fun x y => match (x, y) {
    (true, true) => true,
    (false, true) => true,
    (true, false) => true,
    (false, false) => false,
};

let or4 = fun x y => match (x, y) {
    (true, _) => true,
    (_, true) => true,
    _ => false,
};
()
",
        expect![[r#"
let and1 : Bool -> Bool -> Bool
    = fun (x : Bool) (y : Bool) =>
        match (x, y)._0 {
            true => match (x, y)._1 {
                true => true,
                false => false,
            },
            false => false,
        };
let and2 : Bool -> Bool -> Bool
    = fun (x : Bool) (y : Bool) =>
        match (x, y)._0 {
            true => match (x, y)._1 {
                true => true,
                false => false,
            },
            false => false,
        };
let and3 : Bool -> Bool -> Bool
    = fun (x : Bool) (y : Bool) =>
        match (x, y)._0 {
            true => match (x, y)._1 {
                true => true,
                false => false,
            },
            false => match (x, y)._1 {
                true => false,
                false => false,
            },
        };
let or1 : Bool -> Bool -> Bool
    = fun (x : Bool) (y : Bool) =>
        match (x, y)._0 {
            true => true,
            false => match (x, y)._1 {
                true => true,
                false => false,
            },
        };
let or2 : Bool -> Bool -> Bool
    = fun (x : Bool) (y : Bool) =>
        match (x, y)._0 {
            true => true,
            false => match (x, y)._1 {
                true => true,
                false => false,
            },
        };
let or3 : Bool -> Bool -> Bool
    = fun (x : Bool) (y : Bool) =>
        match (x, y)._0 {
            true => match (x, y)._1 {
                true => true,
                false => true,
            },
            false => match (x, y)._1 {
                true => true,
                false => false,
            },
        };
let or4 : Bool -> Bool -> Bool
    = fun (x : Bool) (y : Bool) =>
        match (x, y)._0 {
            true => true,
            false => match (x, y)._1 {
                true => true,
                false => false,
            },
        };
() : ()"#]],
    );

    // regression test: dont bind `z` twice (once as the default branch of the
    // match, then again as a `let` in RHS). This required removing the ability of
    // core `match` exprs to bind variables in their default branch.
    check(
        "
let apply = fun (x: Bool) (f: Bool -> Int) => match x {
    true => 1,
    z => f(z),
};
()
    ",
        expect![[r#"
let apply : Bool -> (Bool -> Int) -> Int
    = fun (x : Bool) (f : Bool -> Int) =>
        match x {
            true => 1,
            false => let z : Bool = x;
            f z,
        };
() : ()"#]],
    );

    check(
        "
let fst1 = fun (A: Type) (B: Type) (p: (A, B)) => match p {
    (x, y) => x,
};

let fst2 = fun (A: Type) (B: Type) (p: (A, B)) => match p {
    (x, _) => x,
};

let snd1 = fun (A: Type) (B: Type) (p: (A, B)) => match p {
    (x, y) => y,
};

let snd2 = fun (A: Type) (B: Type) (p: (A, B)) => match p {
    (_, y) => y,
};

let swap = fun (A: Type) (B: Type) (p: (A, B)) => match p {
    (x, y) => (y, x),
};
()
    ",
        expect![[r#"
let fst1 : forall (A : Type) (B : Type) -> (A, B) -> A
    = fun (A : Type) (B : Type) (p : (A, B)) =>
        let x : A = p._0;
        let y : B = p._1;
        x;
let fst2 : forall (A : Type) (B : Type) -> (A, B) -> A
    = fun (A : Type) (B : Type) (p : (A, B)) =>
        let x : A = p._0;
        x;
let snd1 : forall (A : Type) (B : Type) -> (A, B) -> B
    = fun (A : Type) (B : Type) (p : (A, B)) =>
        let x : A = p._0;
        let y : B = p._1;
        y;
let snd2 : forall (A : Type) (B : Type) -> (A, B) -> B
    = fun (A : Type) (B : Type) (p : (A, B)) =>
        let y : B = p._1;
        y;
let swap : forall (A : Type) (B : Type) -> (A, B) -> (B, A)
    = fun (A : Type) (B : Type) (p : (A, B)) =>
        let x : A = p._0;
        let y : B = p._1;
        (y, x);
() : ()"#]],
    );

    check(
        "
let foo = fun (x: Int) (y: Bool) (z: Bool) => match x {
    1 if y => 1,
    2 if z => 2,
    3 if y => 3,
    4 if z => 4,
    5 => 5,
    _ => 6,
};

let bar = fun (x: Bool) (f: Bool -> Bool) (y: Int) => match x {
    true => 0,
    z if f(z) => y,
    _ => 3,
};

let baz = fun (x) (y: Int) (f: Int -> Bool) => match (x, y) {
    (0, a) if f(a) => a,
    (0, b) if f(b) => b,
    (0, c) if f(c) => c,
    (0, d) if f(d) => d,
    (aa, bb) => bb,
};
()

    ",
        expect![[r#"
let foo : Int -> Bool -> Bool -> Int
    = fun (x : Int) (y : Bool) (z : Bool) =>
        match x {
            1 => 1,
            2 => 2,
            3 => 3,
            4 => 4,
            5 => 5,
            _ => 6,
        };
let bar : Bool -> (Bool -> Bool) -> Int -> Int
    = fun (x : Bool) (f : Bool -> Bool) (y : Int) =>
        match x {
            true => 0,
            false => let z : Bool = x;
            y,
        };
let baz : Int -> Int -> (Int -> Bool) -> Int
    = fun (x : Int) (y : Int) (f : Int -> Bool) =>
        match (x, y)._0 {
            0 => let a : Int = (x, y)._1;
            a,
            _ => let aa : Int = (x, y)._0;
            let bb : Int = (x, y)._1;
            bb,
        };
() : ()"#]],
    );
    // FIXME: type annotations required on `y`, otherwise we get an
    // `escaping local variable` error when checking `a`.
    check(
        "
let foo = fun (x) (y: Int) => match (x, y) {
    (0, a) => a,
    (b, 0) => b,
    (1, c) => c,
    (d, 1) => d,
    (xx, yy) => xx,
};
()
    ",
        expect![[r#"
let foo : Int -> Int -> Int
    = fun (x : Int) (y : Int) =>
        match (x, y)._0 {
            0 => let a : Int = (x, y)._1;
            a,
            1 => match (x, y)._1 {
                0 => let b : Int = (x, y)._0;
                b,
                1 => let c : Int = (x, y)._1;
                c,
                _ => let c : Int = (x, y)._1;
                c,
            },
            _ => match (x, y)._1 {
                0 => let b : Int = (x, y)._0;
                b,
                1 => let d : Int = (x, y)._0;
                d,
                _ => let xx : Int = (x, y)._0;
                let yy : Int = (x, y)._1;
                xx,
            },
        };
() : ()"#]],
    );

    check(
        "
let is-zero = fun(x) => match x {
    0 => true,
    _ => false,
};
()
    ",
        expect![[r#"
let is-zero : Int -> Bool
    = fun (x : Int) =>
        match x {
            0 => true,
            _ => false,
        };
() : ()"#]],
    );

    // TODO: record field shorthand
    check(
        "
let fst1 = fun (A: Type) (B: Type) (p: {x: A, y: B}) => match p {
    {x=x, y=y} => x,
};
()
",
        expect![[r#"
let fst1 : forall (A : Type) (B : Type) -> {x : A, y : B} -> A
    = fun (A : Type) (B : Type) (p : {x : A, y : B}) =>
        let x : A = p.x;
        let y : B = p.y;
        x;
() : ()"#]],
    );

    check(
        "
let foo = fun(x: Bool) => match x {
    true => 1,
    false => 2,
    true => 3,
};
()
",
        expect![[r#"
let foo : Bool -> Int
    = fun (x : Bool) =>
        match x {
            true => 1,
            false => 2,
        };
() : ()"#]],
    );
}
