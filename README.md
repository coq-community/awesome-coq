Awesome Coq
===========

> _**Everything you'll ever need on the road to mastering Coq.**_

A curated list of references to awesome Coq libraries, plugins, tools, and verification projects. Also includes learning resources such as books.

Is your favorite project not listed? Fork and [create a Pull Request](https://github.com/coq-community/awesome-coq/edit/master/README.md) to add it!

## Contents

- [Community](#community)
- [Books](#books)
- [User Interface](#user-interface)
- [Libraries](#libraries)
- [Package Management](#package-management)
- [Plugins](#plugins)
- [Tools](#tools)
- [Type Theory and Mathematics](#type-theory-and-mathematics)
- [Verified Software](#verified-software)

* * *

## Community

- [Official Coq Website](https://coq.inria.fr)
- [Coq Discourse Web Forum](https://coq.discourse.group)
- [Coq Gitter Chat](https://gitter.im/coq/coq)
- [Official Coq-Club Mailing List](https://sympa.inria.fr/sympa/arc/coq-club)
- [Coq SubReddit](https://www.reddit.com/r/coq/)

## Books

- [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/) by Yves Bertot and Pierre Castéran (2004, Chinese version in 2009) – The first book dedicated to Coq; only the French version and the exercises can be downloaded for free, an English version is available via [Springer's website](https://link.springer.com/book/10.1007/978-3-662-07964-5).
- [Software Foundations](https://softwarefoundations.cis.upenn.edu) by Benjamin Pierce et al. (2007) – Series of Coq-based textbooks on logic, functional programming, and foundations of programming languages, much acclaimed for being accessible to beginners, but mostly oriented towards computer scientists.
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) by Adam Chlipala (2008) – Textbook about practical engineering with Coq which teaches advanced practical tricks and a very specific style of proof.
- [Program Logics for Certified Compilers](https://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/program-logics-certified-compilers) by Andrew W. Appel et al (2014) – Book that explains how to construct powerful and expressive program logics using the theory of separation logic, accompanied by a formal model in Coq, the [Verified Software Toolchain](https://vst.cs.princeton.edu), which is applied to the C light programming language and other examples.
- [Formal Reasoning About Programs](http://adam.chlipala.net/frap/) by Adam Chlipala (2017) – Book that simultaneously provides a general introduction to formal logical reasoning about the correctness of programs and to using Coq for this purpose.
- [Programs and Proofs](https://ilyasergey.net/pnp/) by Ilya Sergey (2017) – Book that gives a brief and practically-oriented introduction to the basic concepts of interactive theorem proving using Coq; emphasizes the computational nature of inductive reasoning about decidable propositions via a small set of primitives from the SSreflect proof language.
- [Computer Arithmetic and Formal Proofs](http://iste.co.uk/book.php?id=1238) by Sylvie Boldo and Guillaume Melquiond (2017) – Book that gives a comprehensive view of how to formally specify and verify tricky floating-point algorithms with Coq using the Flocq library.
- [The Mathematical Components book](https://math-comp.github.io/mcb/) by Assia Mahboubi and Enrico Tassi (2018) – Book that is more oriented towards mathematically inclined users, to dive into Coq with the SSReflect proof language, and the Mathematical Components library.

## User Interface

- [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) — The Coq Integrated Development Environment is a standalone graphical tool for interacting with Coq.
- [ProofGeneral](https://proofgeneral.github.io/) — Generic interface for proof assistants based on the extensible, customizable text editor Emacs.
- [Company-Coq](https://github.com/cpitclaudel/company-coq) — IDE extensions for Proof General's Coq mode.
- [VSCoq](https://github.com/coq-community/vscoq) – Visual Studio Code extension for Coq.

## Libraries

- [Mathematical Components](http://math-comp.github.io) – Formalization of mathematical theories, focusing in particular on group theory.
- [Flocq](http://flocq.gforge.inria.fr) – Formalization of floating-point computations.
- [TLC](http://www.chargueraud.org/softs/tlc/) – Non-constructive alternative to Coq's standard library.
- [ExtLib](https://github.com/coq-community/coq-ext-lib) – Collection of theories and plugins that may be useful in other Coq developments.
- [CoLoR](http://color.inria.fr) – Library on rewriting theory, lambda-calculus and termination, with sub-libraries on common data structures extending the Coq standard library (especially on vectors).
- [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp) – Extended "Standard Library" for Coq.

## Package Management

- **Distribution**:
  - [OPAM](https://opam.ocaml.org) – Flexible Git-friendly package manager with multiple compiler support.

- **Build Tools**:
  - [coq_makefile](https://coq.inria.fr/refman/practical-tools/utilities.html) – Tool distributed by Coq and based on generating a makefile.
  - [dune](https://github.com/ocaml/dune) – Composable and opinionated build system for Coq and OCaml (former jbuilder).

## Plugins

- [CoqHammer](https://github.com/lukaszcz/coqhammer) – General-purpose automated reasoning hammer tool for Coq that combines learning from previous proofs with the translation of problems to the logics of automated systems and the reconstruction of successfully found proofs.

## Tools

- [Ott](https://github.com/ott-lang/ott) – Tool for writing definitions of programming languages and calculi that can be exported to Coq.

## Type Theory and Mathematics

- [Four Color Theorem](https://github.com/math-comp/fourcolor) – Formal proof of the Four Color Theorem, a landmark result of graph theory.
- [Homotopy Type Theory](https://github.com/HoTT/HoTT) – Development of homotopy-theoretic ideas in Coq.
- [Odd Order Theorem](https://github.com/math-comp/odd-order) – Formal proof of the Odd Order Theorem, a landmark result of finite group theory.

## Verified Software

- [CompCert](http://compcert.inria.fr) – High-assurance compiler for almost all of the C language (ISO C99), generating efficient code for the PowerPC, ARM, RISC-V and x86 processors.

* * *

_Inspired by awesome projects line. Discover [more awesomeness](https://github.com/bayandin/awesome-awesomeness) :sparkles:._
