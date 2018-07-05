## Artifact

This artifact comprises the Coq implementation of supporting proofs of
the material in the ICFP'18 paper titled 'Static Interpretation of
Higher-Order Modules in Futhark'.

## Assumptions

These files have been tested with the The Coq Proof Assistant, version
8.6 (March 2018) under Mac and under Linux.

## Compiling the files

To compile the files, run `make`.

To clean-up, run `make clean`

## Step-by-Step Guide

In this section, we give a short description of the development of the
module system formalisation. We outline the file structure of the
project and describe the content of the source files with the
references to the paper text.

Throughout our development, we assume axioms of functional
extensionality and proof-irrelevance. The main development is fully
formalised and does not contain admitted theorems. Parts of the
material in the `Experimental` folder contain admitted lemmas,
but these parts serve as direction for further improvement.

### Main development

    Basics.v : Definitions and notations for identifiers.  Properties
      of equality for the proofs involving dependent types.

    Syntax.v : Syntax for the source language (core language and
    modules) --- Section 2.

    Target.v : Target language syntax and semantics --- Section 5.1.

    SemObjects.v : Semantic objects definition (Section 4, Figure 4),
      enrichment relation (Section 4.1).

    ElabCore.v : Elaboration rules for core-level types, expressions
      and declarations; examples --- Section 4.4, Figure 6.

    MiniElab.v : Elaboration rules for modules --- Section 4.5,
      Figures 7 and 8.

    CompCore.v : Compilation rules for core-level expressions and
      declarations --- Section 5.4, Figure 10.

    IntObjects.v : Interpretation objects, interpretation erasure,
      environment filtering --- Sections 5.2, 5.3 and 5.5.

    MiniInt.v : Static interpretation relation (Section 5.6,
      Figure 12), type consistency logical relation (Section 6,
      Figure 13), and the proof of termination (Section 6,
      normalisation part of Proposition 6.1).

### Finite maps and sets

    SetExt.v : Finite sets with extensionality.

    EnvExt.v : Environments (finite maps) with
      extensionality. Includes an isomorphic (to the one form the Coq
      standard library) and a representation of environments used to
      overcome some issues with the strict-positivity checker --- see
      Section 9.

### Nominal techniques

    NomEnv.v : Nominal set of semantic objects and interpretation
      objects.

    Nom.v : Basic definitions of nominal sets and a nominal set of
      finite sets of atoms. This part of the development is generic
      and can be used in different contexts.

    CpdtTactics.v : Some tactics from CPDT.

    CustomTactics.v : Selected tactics from Pierce et al.; some custom
      tactics.

### Supplementary examples

    stlc.v : Proof of termination of simply-typed lambda calculus.

    Example.v : Examples showing that Coq can reject certain strictly
      positive inductive definitions. We provide workarounds for this
      issue for simple examples.  In our development, we use similar
      techniques to define semantic objects.

### Experimental development (future work)

    Experimental/MiniElab1.v : Elaboration rules with
      alpha-equivalence. An example, showing when alpha-equivalence is
      important for the elaboration.
