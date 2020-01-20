# bidi-higher-rank-poly
Didactic implementation of the type checker described in "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" written in OCaml.

# Building
```text
cd bidi-higher-rank-poly/
dune build repl   (Build the REPL)
dune build test   (Build the tests)
```

# Using the REPL
```text
rlwrap ./_build/default/repl/Main.exe
> exit;;          (Exit the REPL)
> context;;       (Print the current context)
> x => x;;        (Evaluate a input term and print it's result)
```

# Running the tests
```text
./_build/default/test/Main.exe
```
