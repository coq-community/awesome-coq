# Awesome Coq [![Awesome](https://cdn.rawgit.com/sindresorhus/awesome/d7305f38d29fed78fa85652e3a63e154dd8e8829/media/badge.svg)](https://github.com/sindresorhus/awesome)

The Coq proof assistant provides a formal language to write mathematical definitions, executable algorithms, and theorems, together with an environment for semi-interactive development of machine-checked proofs.

## Contents

- [Projects](#projects)
  - [Frameworks](#frameworks)
  - [User Interfaces](#user-interfaces)
  - [Libraries](#libraries)
  - [Package Management](#package-management)
  - [Plugins](#plugins)
  - [Tools](#tools)
  - [Type Theory and Mathematics](#type-theory-and-mathematics)
  - [Verified Software](#verified-software)
- [Resources](#resources)
  - [Community](#community)
  - [Blogs](#blogs)
  - [Books](#books)
  - [Tutorials and Hints](#tutorials-and-hints)
- [Contributing](#contributing)

---

## Projects

### Frameworks

- [Fiat](https://github.com/mit-plv/fiat) - Mostly automated synthesis of correct-by-construction programs.
- [Iris](https://iris-project.org) - Higher-order concurrent separation logic framework.
- [Verdi](https://github.com/uwplse/verdi) - Framework for formally verifying distributed systems implementations.
- [VST](https://vst.cs.princeton.edu) - Toolchain for verifying C code inside Coq in a higher-order concurrent, impredicative separation logic that is sound w.r.t. the Clight language of the CompCert compiler.

### User Interfaces

- [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) - Standalone graphical tool for interacting with Coq.
- [Coqtail](https://github.com/whonore/Coqtail) - Interface for Coq based on the Vim text editor.
- [Proof General](https://proofgeneral.github.io/) - Generic interface for proof assistants based on the extensible, customizable text editor Emacs.
- [Company-Coq](https://github.com/cpitclaudel/company-coq) - IDE extensions for Proof General's Coq mode.
- [jsCoq](https://github.com/ejgallego/jscoq) - Port of Coq to JavaScript, which enables running Coq projects in a browser.
- [VSCoq](https://github.com/coq-community/vscoq) - Visual Studio Code extension for Coq.

### Libraries

- [Bignums](https://github.com/coq/bignums) - Library of arbitrary large numbers.
- [CoLoR](http://color.inria.fr) - Library on rewriting theory, lambda-calculus and termination, with sub-libraries on common data structures extending the Coq standard library.
- [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp) - Extended alternative standard library for Coq.
- [ExtLib](https://github.com/coq-community/coq-ext-lib) - Collection of theories and plugins that may be useful in other Coq developments.
- [FCSL-PCM](https://github.com/imdea-software/fcsl-pcm) - Formalization of partial commutative monoids as used in verification of pointer-manipulating programs.
- [Flocq](http://flocq.gforge.inria.fr) - Formalization of floating-point computations.
- [Mathematical Components](http://math-comp.github.io) - Formalization of mathematical theories, focusing in particular on group theory.
- [Paco](http://plv.mpi-sws.org/paco/) - Library for parameterized coinduction.
- [Relation Algebra](https://github.com/damien-pous/relation-algebra) - Modular formalization of algebras with heterogeneous binary relations as models.
- [TLC](http://www.chargueraud.org/softs/tlc/) - Non-constructive alternative to Coq's standard library.

### Package Management

- **Distribution**:
  - [OPAM](https://opam.ocaml.org) - Flexible git-friendly package manager with multiple compiler support.
  - [Coq Package Index](https://coq.inria.fr/packages.html) - OPAM-based collection of Coq packages.

- **Build Tools**:
  - [coq_makefile](https://coq.inria.fr/refman/practical-tools/utilities.html) - Tool distributed by Coq and based on generating a makefile.
  - [dune](https://github.com/ocaml/dune) - Composable and opinionated build system for Coq and OCaml (former jbuilder).

### Plugins

- [AAC Tactics](https://github.com/coq-community/aac-tactics) - Plugin providing tactics for rewriting universally quantified equations, modulo associativity and commutativity of some operator.
- [Coq-Elpi](https://github.com/LPCIC/coq-elpi) - Plugin for the Embeddable Lambda Prolog Interpreter.
- [CoqHammer](https://github.com/lukaszcz/coqhammer) - General-purpose automated reasoning hammer tool that combines learning from previous proofs with the translation of problems to automated provers and the reconstruction of found proofs.
- [Equations](https://github.com/mattam82/Coq-Equations) - Function definition package for Coq.
- [Gappa](https://gitlab.inria.fr/gappa/coq) - Coq tactic for discharging goals about floating-point arithmetic and round-off errors.
- [MetaCoq](https://github.com/MetaCoq/metacoq) - Project formalizing Coq in Coq and providing tools for manipulating Coq terms and developing certified plugins.
- [Mtac2](https://github.com/Mtac2/Mtac2) - Plugin adding Typed Tactics for Backward Reasoning in Coq.
- [Paramcoq](https://github.com/coq-community/paramcoq) - Plugin to generate parametricity translations of Coq terms.
- [QuickChick](https://github.com/QuickChick/QuickChick) - Plugin for randomized property-based testing.
- [Unicoq](https://github.com/unicoq/unicoq) - Plugin that replaces the existing unification algorithm with an enhanced one.

### Tools

- [coq-dpdgraph](https://github.com/Karmaki/coq-dpdgraph) - Tool for building dependency graphs between Coq objects.
- [CoqOfOCaml](https://github.com/clarus/coq-of-ocaml) - Tool for generating idiomatic Coq from OCaml code.
- [Cosette](https://github.com/uwdb/Cosette) - Automated solver for reasoning about SQL equivalences.
- [Ott](https://www.cl.cam.ac.uk/~pes20/ott/) - Tool for writing definitions of programming languages and calculi that can be translated to Coq.
- [SerAPI](https://github.com/ejgallego/coq-serapi) - Library and tool for serialization of Coq code to JSON or S-expressions.
- [Menhir](http://gallium.inria.fr/~fpottier/menhir/) - Parser generator that can output Coq code for verified parsers.

### Type Theory and Mathematics

- [category-theory](https://github.com/jwiegley/category-theory) - Axiom-free formalization of category theory in Coq for personal study and practical work.
- [CoRN](https://github.com/coq-community/corn) - Library of constructive real analysis and algebra.
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot) - Formalization of real analysis compatible with the standard library and focusing on usability.
- [Four Color Theorem](https://github.com/math-comp/fourcolor) - Formal proof of the Four Color Theorem, a landmark result of graph theory.
- [GeoCoq](https://github.com/GeoCoq/GeoCoq) - Formalization of geometry based on Tarski's axiom system.
- [Homotopy Type Theory](https://github.com/HoTT/HoTT) - Development of homotopy-theoretic ideas.
- [Math Classes](https://github.com/coq-community/math-classes) - Abstract interfaces for mathematical structures based on type classes.
- [Odd Order Theorem](https://github.com/math-comp/odd-order) - Formal proof of the Odd Order Theorem, a landmark result of finite group theory.
- [UniMath](https://github.com/UniMath/UniMath) - Library which aims to formalize a substantial body of mathematics using the univalent point of view.

### Verified Software

- [CompCert](http://compcert.inria.fr) - High-assurance compiler for almost all of the C language (ISO C99), generating efficient code for the PowerPC, ARM, RISC-V and x86 processors.
- [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) - Cryptographic primitive code generation.
- [lambda-rust](https://gitlab.mpi-sws.org/iris/lambda-rust) - Formal model of a Rust core language and type system, a logical relation for the type system, and safety proofs for some Rust libraries.
- [Verdi Raft](https://github.com/uwplse/verdi-raft) - Implementation of the Raft distributed consensus protocol, verified in Coq using the Verdi framework.

## Resources

### Community

- [Official Coq website](https://coq.inria.fr)
- [Official Coq Discourse forum](https://coq.discourse.group)
- [Official Coq Gitter chat](https://gitter.im/coq/coq)
- [Official Coq-Club mailing list](https://sympa.inria.fr/sympa/arc/coq-club)
- [Coq-community package maintainance project](https://github.com/coq-community/manifesto)
- [Coq subreddit](https://www.reddit.com/r/coq/)
- [StackOverflow Coq tag](https://stackoverflow.com/questions/tagged/coq)

### Blogs

- [Poleiro: a Coq blog by Arthur Azevedo de Amorim](http://poleiro.info)
- [Guillaume Claret's blog](http://coq-blog.clarus.me)
- [Gagallium](http://gallium.inria.fr/blog)
- [Ralf Jung's blog posts on Coq](https://www.ralfj.de/blog/categories/coq.html)
- [Joachim Breitner's Coq posts](http://www.joachim-breitner.de/blog/tag/Coq)
- [Gregory Malecha's blog](https://gmalecha.github.io)
- [Coq Exchange: ideas and experiment reports about Coq](https://project.inria.fr/coqexchange/news/)

### Books

- [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/) by Yves Bertot and Pierre Castéran (2004, Chinese version in 2009) - The first book dedicated to Coq.
- [Software Foundations](https://softwarefoundations.cis.upenn.edu) by Benjamin Pierce et al. (2007) - Series of Coq-based textbooks on logic, functional programming, and foundations of programming languages, much acclaimed for being accessible to beginners, but mostly oriented towards computer scientists.
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) by Adam Chlipala (2008) - Textbook about practical engineering with Coq which teaches advanced practical tricks and a very specific style of proof.
- [Program Logics for Certified Compilers](https://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/program-logics-certified-compilers) by Andrew W. Appel et al (2014) - Book that explains how to construct powerful and expressive program logics using the theory of separation logic, accompanied by a formal model in Coq which is applied to the Clight programming language and other examples.
- [Formal Reasoning About Programs](http://adam.chlipala.net/frap/) by Adam Chlipala (2017) - Book that simultaneously provides a general introduction to formal logical reasoning about the correctness of programs and to using Coq for this purpose.
- [Programs and Proofs](https://ilyasergey.net/pnp/) by Ilya Sergey (2017) - Book that gives a brief and practically-oriented introduction to the basic concepts of interactive theorem proving using Coq; emphasizes the computational nature of inductive reasoning about decidable propositions via a small set of primitives from the SSreflect proof language.
- [Computer Arithmetic and Formal Proofs](http://iste.co.uk/book.php?id=1238) by Sylvie Boldo and Guillaume Melquiond (2017) - Book that gives a comprehensive view of how to formally specify and verify tricky floating-point algorithms with Coq using the Flocq library.
- [The Mathematical Components book](https://math-comp.github.io/mcb/) by Assia Mahboubi and Enrico Tassi (2018) - Book that is more oriented towards mathematically inclined users, to dive into Coq with the SSReflect proof language and the Mathematical Components library.

### Tutorials and Hints

- [coq-tricks](https://github.com/tchajed/coq-tricks) - Tricks you wish the Coq manual told you.

# Contributing

Contributions welcome! Read the [contribution guidelines](CONTRIBUTING.md) first.
