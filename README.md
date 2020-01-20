# bidi-higher-rank-poly
Didactic implementation of the type checker described in "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" written in OCaml.

# Notable detours from the paper
Added the empty program and type explicitly in order to have a better handle on them during random program generation for testing. The reason is there are many different terms that represent the empty type in System F (e.g. ∀a.a), however in general it is undecidable whether a type term is inhabited or not. Therefore generating random polymorphic type terms is not very useful for testing, since some of them will represent the empty type and there is no way to tell. The chosen strategy for testing therefore became; generate random monomorphic type terms (these are always inhabited), generalise these type terms by randomly substituting their subterms with existential variables (the results are still inhabited, and should sometimes implicitly turn into polymorphic type terms); from these type terms generate random typed programs.

# Frontend syntax
```text
// Type terms
nothing           (Empty type)
unit              (Singleton type)
x                 (Variables)
s -> t            (Arrow type)
x => t            (Universally quantified type)

// Programs
undefined         (Empty program)
unit              (Singleton value)
x                 (Variables)
x => e            (Abstractions)
f x               (Applications)
```

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
> x => x;;        (Evaluate an input term and print its result)
```

# Running the tests
```text
./_build/default/test/Main.exe
```
