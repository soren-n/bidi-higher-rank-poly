# bidi-higher-rank-poly
Didactic implementation of the type checker described in "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" written in OCaml.

# Notable detours from the paper
Added the empty program and type explicitly in order to have a better handle on them during random program generation for testing. The reason is there are many different terms that represent the empty type in System F (e.g. ∀a.a), however in general it is undecidable whether a type term is inhabited or not. Therefore generating random polymorphic type terms is not very useful for testing, since some of them will represent the empty type and there is no way to tell. The chosen strategy for testing therefore became; generate random monomorphic type terms (these are always inhabited), generalise these type terms by randomly substituting their subterms with existential variables (the results are still inhabited, and should sometimes implicitly create polymorphic type terms); from these type terms generate random typed programs.

# Testing strategy
This project uses Property Based Testing through the QCheck module for OCaml. Code has been written that allows for the random generation of typed programs, and as well as type directed shrinking of said generated programs. This made it very easy to hone in on bugs in e.g. the type checker, type synthesis and interpreter.

# Language feature additions
Computing only with abstractions and units is a little inconvenient, as such additional language features will be added over time to this language playground.

Added features so far:
- Empty types and programs
- Statements

# Frontend syntax
```text
// Types - t
nothing           (Empty type)
unit              (Singleton type)
x                 (Type variable)
s -> t            (Arrow type)
x => t            (Universally quantified type)

// Statements - s
x : t. s          (Variable declaration followed by statement)
x = e. s          (Variable definition followed by statement)
e                 (Statement terminal)

// Expressions - e
undefined         (Empty program)
unit              (Singleton value)
x                 (Variables)
x => s            (Abstractions)
f x               (Applications)
(e : t)           (Type annotation)
```

# Building
```text
cd bidi-higher-rank-poly/
dune build repl/bin   (Build the REPL)
dune build util/test  (Build the util tests)
dune build back/test  (Build the backend tests)
dune build front/test (Build the frontend tests)
```

Or build all artefacts at once with
```Text
dune build
```

# Testing
```text
_build/default/util/test/Tests.exe   (Run the util tests)
_build/default/back/test/Tests.exe   (Run the backend tests)
_build/default/front/test/Tests.exe  (Run the frontend tests)
```

Or run all tests at once with
```Text
dune runtest
```

# Using the REPL
```text
rlwrap ./_build/default/repl/bin/Main.exe
> exit;;          (Exit the REPL)
> context;;       (Print the current context)
> x => x;;        (Evaluate an input term and print its result)
```
