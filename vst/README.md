[Verified Software Toolchain (VST)](https://vst.cs.princeton.edu/) refers to a modular ecosystem for developing certified software programs.

## Building

First, install [CompCert](https://github.com/AbsInt/CompCert).

Then, install VST in a sibling directory. Instructions are found [here](https://github.com/PrincetonUniversity/VST/blob/master/BUILD_ORGANIZATION.md).

The programs have been tested with Coq 8.11.1, CompCert 3.7, and VST 2.6.

## Toolchain overview

- At the base level is **CompCert C**, the program language, which is a subset of C in which programs can be written. **CompCert** is the certified compiler that correctly compiles down CompCert C code into assembly with respect to the source language's operational semantics. The compiler transforms the CompCert C code into a series of intermediate representations, first by removing side effects from expressions (**C light**) and then allocating variables to the stack (**C minor**), etc.
- **Core Verifiable C** is a separation logic whose soundness has been proved with respect to CompCert C's operational semantics.
- **Verifiable C** is a separation logic derived from Core Verifiable C that supports proof automation.
- **Floyd** is a proof automation system/library that is used to reason with the properties of Verifiable C programs.

## Proof automation with VST

[This reference manual](https://vst.cs.princeton.edu/download/VC.pdf) outlines the steps to produce a correctness proof of a C program using VST. In summary, the steps are:

1. Translate the C program into abstract syntax trees (ASTs) of the Clight intermediate language using [`clightgen`](https://github.com/AbsInt/CompCert/tree/master/exportclight).
2. Use Floyd to declare the functional model and API specifications for each function in the program.
3. Use Floyd to prove that each function body satisfies $$its specification declared in the previous step.

### 1. Translate into C light AST with `Clightgen`

`Clightgen` is CompCert's front-end tool that produces a C-light abstract syntax data structure (a `.v` file), given a C program (a `.c` file). This consists of two steps: a parser from source to CompCert C (unverified); and a translator from CompCert C to abstract syntax trees of C light (verified).

Example:

```bash
<PATH_TO_COMPCERT>/clightgen -normalize /path/to/file.c
```

### 2. Declare functional model and API specification

The functional model is a purely mathematical model consisting of definitions and lemmas. It should be independent of the C program.

The API specification is a series of `funspec`s where each one corresponds to a function in the C program.

### 3. Prove that function bodies meet specifications

The proof proceeds by forward execution.

## Using `coqc` and Proof General outside the VST directory

To verify the C programs in this directory, do the following.

1. Copy the file `_CoqProject-export` from the root of your `VST` installation to this directory and rename it to `_CoqProject`.
2. Use `clightgen` from the root of your `CompCert` installation to generate the `.v` file which contains the AST.
3. Compile the `.v` file into a `.vo` file using `coqc`. When doing so, pass the `-R` and `-Q` arguments contained in `_CoqProject`. (e.g., `coqc $(cat _CoqProject) swap.v`)
4. The files prefixed with `verif_` are the verification scripts. Open it with Proof General. It should recognized the compiled AST from step 3 as a module when you `Require Import` it.

