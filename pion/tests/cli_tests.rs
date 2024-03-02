#![feature(iter_intersperse)]

use expect_test::*;

const PION: &str = env!("CARGO_BIN_EXE_pion");

fn check(
    command: &str,
    mut expected_stdout: expect_test::Expect,
    mut expected_stderr: expect_test::Expect,
) {
    let mut shell = std::process::Command::new("/bin/sh");
    let shell = shell.arg("-c");
    let command = shell.arg(command);
    let output = command.output().unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();

    let stdout: String = stdout
        .lines()
        .map(|line| line.trim_end())
        .intersperse("\n")
        .collect();
    let stderr: String = stderr
        .lines()
        .map(|line| line.trim_end())
        .intersperse("\n")
        .collect();

    expected_stdout.indent(false);
    expected_stderr.indent(false);

    expected_stdout.assert_eq(&stdout);
    expected_stderr.assert_eq(&stderr);
}

#[test]
fn cli_no_args() {
    check(
        PION,
        expect![[""]],
        expect![[r#"
Usage: pion <COMMAND>

Commands:
  check
  eval
  help   Print this message or the help of the given subcommand(s)

Options:
  -h, --help  Print help"#]],
    );
}

#[test]
fn cli_incorrect_args() {
    check(
        &format!("{PION} check"),
        expect![[""]],
        expect![[r#"
error: the following required arguments were not provided:
  <PATH>

Usage: pion check <PATH>

For more information, try '--help'."#]],
    );
    check(
        &format!("{PION} eval"),
        expect![[""]],
        expect![[r#"
error: the following required arguments were not provided:
  <PATH>

Usage: pion eval <PATH>

For more information, try '--help'."#]],
    );
}

#[test]
fn consts() {
    check(
        &format!("{PION} check <(echo true)"),
        expect!["true : Bool"],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo false)"),
        expect!["false : Bool"],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo 5)"),
        expect!["5 : Int"],
        expect![""],
    );
}

#[test]
fn prims() {
    check(
        &format!("{PION} check <(echo Type)"),
        expect!["Type : Type"],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo Int)"),
        expect!["Int : Type"],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo Bool)"),
        expect!["Bool : Type"],
        expect![""],
    );
}

#[test]
fn fun_arrow() {
    check(
        &format!("{PION} check <(echo 'Int -> Bool')"),
        expect!["(Int -> Bool) : Type"],
        expect![""],
    );
}

#[test]
fn fun_type() {
    check(
        &format!("{PION} check <(echo 'forall(x: Int) -> Bool')"),
        expect!["(Int -> Bool) : Type"],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo 'forall (A: Type) -> A -> A')"),
        expect!["(forall(A: Type) -> A -> A) : Type"],
        expect![""],
    );
}

#[test]
fn fun_lit() {
    check(
        &format!("{PION} check <(echo 'fun(x: Int) => x')"),
        expect!["(fun(x: Int) => x) : Int -> Int"],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo 'fun x => x')"),
        expect!["(fun(x: ?0) => x) : ?0 -> ?0"],
        expect![[r#"
error: Unsolved metavariable: ?0
  ┌─ /dev/fd/63:1:5
  │
1 │ fun x => x
  │     ^ could not infer type of variable `x`
"#]],
    );
    check(
        &format!("{PION} check <(echo '(fun x => x) : Int -> Int')"),
        expect!["(fun(x: Int) => x) : Int -> Int"],
        expect![""],
    );
}

#[test]
fn fun_app() {
    check(
        &format!("{PION} check <(echo '(fun x => x) 1')"),
        expect!["((fun(x: Int) => x) 1) : Int"],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo '(fun x => x) 1 2 3')"),
        expect!["#error : #error"],
        expect![[r#"
error: Expected function, found `Int`
  ┌─ /dev/fd/63:1:1
  │
1 │ (fun x => x) 1 2 3
  │ ^^^^^^^^^^^^^^
"#]],
    );
}

#[test]
fn r#let() {
    check(
        &format!("{PION} check <(echo 'let f = fun x => x; f false')"),
        expect![[r#"
(let f: Bool -> Bool = fun(x: Bool) => x;
f false) : Bool"#]],
        expect![""],
    );
    check(
        &format!("{PION} check <(echo 'let f: Bool -> Bool = fun x => x; f false')"),
        expect![[r#"
(let f: Bool -> Bool = fun(x: Bool) => x;
f false) : Bool"#]],
        expect![""],
    );
}
