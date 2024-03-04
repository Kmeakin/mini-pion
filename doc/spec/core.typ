= Syntax

#let klet = $sans("let")$
#let kin = $sans("in")$
#let ktrue = $sans("true")$
#let kfalse = $sans("false")$
#let kif = $sans("if")$
#let kthen = $sans("then")$
#let kelse = $sans("else")$

#let let-in(x, t, e1, e2) = $klet #x : #t = #e1 kin #e2$
#let if-then-else(c, t, e) = $kif #c kthen #t kelse #e$
#let fun-app(f, a) = $#f med #a$
#let fun-lit(x, t, e) = $lambda (#x : #t) . e$
#let fun-type(x, t, e) = $forall (#x : #t) . e$

#let grammar(g, debug_stroke: none) = {
    let cells = ()
    for rule in g {
        let name = if "name" in rule {
            if rule.name != none {
                rect(stroke: debug_stroke, strong(rule.name + ":"))
            }
        };
        let symbols = if type(rule.symbol) == "array" {
            rule.symbol.join($,$)
        } else {
            rule.symbol
        };
        let lhs = $#symbols ::= $;
        let productions = if type(rule.productions) == "array" {
            rule.productions
        } else {
            (rule.productions,)
        };
        for row in productions {
            cells.push(align(horizon, name))
            cells.push(align(right + horizon, rect(stroke: debug_stroke, lhs)));
            let row = if type(row) == "array" {
                row.join(rect(stroke: debug_stroke, $ | $))
            } else {
                row
            }
            cells.push(align(horizon, rect(stroke: debug_stroke, $#row$)));
            lhs = $|$;
            name = none;
        }
    }
    grid(columns: 3, ..cells)
}

The `pion` core language is divided into following syntactic categories:
#let pion-grammar = (
    (
        name: "Terms",
        symbol: ($t$, $e$),
        productions: (
          (),
          ( $x$ ),
          ( $?m$ ),
          ( $c$ ),
          ( $p$ ),
          ( let-in($x$, $t$, $e_1$, $e_2$) ),
          ( if-then-else($e_1$, $e_2$, $e_3$) ),
          ( fun-app($e_1$, $e_2$) ),
          ( fun-lit($x$, $t$, $e$) ),
          ( fun-type($x$, $t$, $e$) ),
        ),
    ),
    (
        name: "Constants",
        symbol: ($c$),
        productions: (
          (),
          ( $ktrue$, $kfalse$ ),
          ( $0$, $1$, $2$, $...$, ),
        ),
    ),
    (
        name: "Primitives",
        symbol: ($p$),
        productions: (
          (),
          ( $sans("Type")$ ),
          ( $sans("Bool")$ ),
          ( $sans("Int")$ ),
          ( $sans("add")$, $sans("sub")$, $sans("mul")$ ),
          ( $sans("eq")$, $sans("ne")$, $sans("lt")$, $sans("gt")$, $sans("lte")$, $sans("gte")$ ),
          ( $sans("fix")$ ),
        ),
    )
);
#grammar(pion-grammar)

= Typing
#let has-type(local-env, e, t) = $#local-env tack #e : #t$

#has-type($$, $sans("Type")$, $sans("Type")$)

#has-type($$, $sans("Bool")$, $sans("Type")$)

#has-type($$, $sans("Int")$, $sans("Type")$)

#has-type($$, $ktrue$, $sans("Bool")$)

#has-type($$, $kfalse$, $sans("Bool")$)

= Reduction
