# Syntax

```text
n                               // Natural numbers

x, y                            // Variables

t :=                            // Terms
    | x                         // Variable
    | n                         // Natural number literal
    | true | false              // Boolean literal
    | let x : t1 = t2 ; t3      // let-in
    | if t1 then t2 else t3     // if-then-else
    | fun (x : t1) => t2        // Function literal
    | forall (x : t1) -> t2     // Function type
    | t1 t2                     // Function application
```

# Normalization

Values are expressions in normal form (in particular, weak normal form):
```text
v :=                            // Values
    | n                         // Natural number literal
    | true | false              // Boolean literal
    | fun (x : v1) => e1        // Function literal
    | forall (x : v1) -> e1     // Function type
```
