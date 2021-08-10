# Awesome Coq [![Awesome](https://awesome.re/badge.svg)](https://awesome.re)

[<img src="coq-logo.svg" align="right" width="100" title="Awesome Coq is a coq-community project">](https://github.com/coq-community/manifesto)

> A curated list of awesome Coq libraries, plugins, tools, and resources.

The [Coq proof assistant](https://coq.inria.fr) provides a formal language to write mathematical definitions, executable algorithms, and theorems, together with an environment for semi-interactive development of machine-checked proofs.

Contributions welcome! Read the [contribution guidelines](CONTRIBUTING.md) first.

## Contents

- [Projects](#projects)
  - [Frameworks](#frameworks)
  - [User Interfaces](#user-interfaces)
  - [Libraries](#libraries)
  - [Package and Build Management](#package-and-build-management)
  - [Plugins](#plugins)
  - [Tools](#tools)
  - [Type Theory and Mathematics](#type-theory-and-mathematics)
  - [Verified Software](#verified-software)
- [Resources](#resources)
  - [Community](#community)
  - [Blogs](#blogs)
  - [Books](#books)
  - [Course Material](#course-material)
  - [Tutorials and Hints](#tutorials-and-hints)

---

## Projects

### Frameworks

- [CoqEAL](https://github.com/CoqEAL/CoqEAL) - Framework to ease change of data representations in proofs.
- [FCF](https://github.com/adampetcher/fcf) - Framework for proofs of cryptography.
- [Fiat](https://github.com/mit-plv/fiat) - Mostly automated synthesis of correct-by-construction programs.
- [FreeSpec](https://github.com/ANSSI-FR/FreeSpec) - Framework for modularly verifying programs with effects and effect handlers.
- [Iris](https://iris-project.org) - Higher-order concurrent separation logic framework.
- [Q\*cert](https://querycert.github.io) - Platform for implementing and verifying query compilers.
- [Verdi](https://github.com/uwplse/verdi) - Framework for formally verifying distributed systems implementations.
- [VST](https://vst.cs.princeton.edu) - Toolchain for verifying C code inside Coq in a higher-order concurrent, impredicative separation logic that is sound w.r.t. the Clight language of the CompCert compiler.

### User Interfaces

- [CoqIDE](https://coq.inria.fr/refman/practical-tools/coqide.html) - Standalone graphical tool for interacting with Coq.
- [Coqtail](https://github.com/whonore/Coqtail) - Interface for Coq based on the Vim text editor.
- [Proof General](https://proofgeneral.github.io) - Generic interface for proof assistants based on the extensible, customizable text editor Emacs.
- [Company-Coq](https://github.com/cpitclaudel/company-coq) - IDE extensions for Proof General's Coq mode.
- [jsCoq](https://github.com/ejgallego/jscoq) - Port of Coq to JavaScript, which enables running Coq projects in a browser.
- [Jupyter kernel for Coq](https://github.com/EugeneLoy/coq_jupyter) - Coq support for the Jupyter Notebook web environment.
- [VSCoq](https://github.com/coq-community/vscoq) - Extension for the Visual Studio Code editor.

### Libraries

- [ALEA](https://github.com/coq-community/alea) - Library for reasoning on randomized algorithms.
- [Bignums](https://github.com/coq/bignums) - Library of arbitrary large numbers.
- [CoLoR](http://color.inria.fr) - Library on rewriting theory, lambda-calculus and termination, with sub-libraries on common data structures extending the Coq standard library.
- [coq-haskell](https://github.com/jwiegley/coq-haskell) - Library smoothing the transition to Coq for Haskell users.
- [Coq record update](https://github.com/tchajed/coq-record-update) - Library which provides a generic way to update Coq record fields.
- [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp) - Extended alternative standard library for Coq.
- [ExtLib](https://github.com/coq-community/coq-ext-lib) - Collection of theories and plugins that may be useful in other Coq developments.
- [FCSL-PCM](https://github.com/imdea-software/fcsl-pcm) - Formalization of partial commutative monoids as used in verification of pointer-manipulating programs.
- [Flocq](http://flocq.gforge.inria.fr) - Formalization of floating-point computations.
- [Formalised Undecidable Problems](https://github.com/uds-psl/coq-library-undecidability) - Library of undecidable problems and reductions between them.
- [Hahn](https://github.com/vafeiadis/hahn) - Library for reasoning on lists and binary relations.
- [Metalib](https://github.com/plclub/metalib) - Library for programming language metatheory using locally nameless variable binding representations.
- [Monae](https://github.com/affeldt-aist/monae) - Monadic effects and equational reasoning.
- [Paco](http://plv.mpi-sws.org/paco/) - Library for parameterized coinduction.
- [Regular Language Representations](https://github.com/coq-community/reglang) - Translations between different definitions of regular languages, including regular expressions and automata.
- [Relation Algebra](https://github.com/damien-pous/relation-algebra) - Modular formalization of algebras with heterogeneous binary relations as models.
- [Simple IO](https://github.com/Lysxia/coq-simple-io) - Input/output monad with user-definable primitive operations.
- [TLC](https://github.com/charguer/tlc) - Non-constructive alternative to Coq's standard library.

### Package and Build Management

- [coq_makefile](https://coq.inria.fr/refman/practical-tools/utilities.html) - Build tool distributed with Coq and based on generating a makefile.
- [Coq Package Index](https://coq.inria.fr/packages.html) - OPAM-based collection of Coq packages.
- [Coq Platform](https://github.com/MSoegtropIMC/coq-platform) - Experimental curated collection of packages to support Coq use in industry, education, and research.
- [Coq-community Templates](https://github.com/coq-community/templates) - Templates for generating configuration files for Coq projects.
- [Docker-Coq](https://github.com/coq-community/docker-coq) - Docker images for many versions of Coq.
- [Docker-MathComp](https://github.com/math-comp/docker-mathcomp) - Docker images for many combinations of versions of Coq and the Mathematical Components library.
- [Docker-Coq-action](https://github.com/marketplace/actions/docker-coq-action) - GitHub container action that can be used with Docker-Coq or Docker-MathComp.
- [Dune](https://dune.build) - Composable and opinionated build system for Coq and OCaml (former jbuilder).
- [Nix](https://nixos.org/nix/) - Package manager for Linux and other Unix systems, supporting atomic upgrades and rollbacks.
- [Nix Coq packages](https://search.nixos.org/packages?channel=unstable&query=coqPackages) - Collection of Coq-related packages for Nix.
- [OPAM](https://opam.ocaml.org) - Flexible and Git-friendly package manager for OCaml with multiple compiler support.

### Plugins

- [AAC Tactics](https://github.com/coq-community/aac-tactics) - Tactics for rewriting universally quantified equations, modulo associativity and commutativity of some operator.
- [Coq-Elpi](https://github.com/LPCIC/coq-elpi) - Plugin for the Embeddable Lambda Prolog Interpreter.
- [CoqHammer](https://github.com/lukaszcz/coqhammer) - General-purpose automated reasoning hammer tool that combines learning from previous proofs with the translation of problems to automated provers and the reconstruction of found proofs.
- [Equations](https://github.com/mattam82/Coq-Equations) - Function definition package for Coq.
- [Gappa](https://gitlab.inria.fr/gappa/coq) - Tactic for discharging goals about floating-point arithmetic and round-off errors.
- [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) - Collection of commands for declaring Coq hierarchies based on packed classes.
- [Ltac2](https://coq.inria.fr/refman/proof-engine/ltac2.html) - Experimental typed tactic language similar to Coq's classic Ltac language.
- [MetaCoq](https://github.com/MetaCoq/metacoq) - Project formalizing Coq in Coq and providing tools for manipulating Coq terms and developing certified plugins.
- [Mtac2](https://github.com/Mtac2/Mtac2) - Plugin adding typed tactics for backward reasoning.
- [Paramcoq](https://github.com/coq-community/paramcoq) - Plugin to generate parametricity translations of Coq terms.
- [QuickChick](https://github.com/QuickChick/QuickChick) - Plugin for randomized property-based testing.
- [SMTCoq](https://github.com/smtcoq/smtcoq) - Tool that checks proof witnesses coming from external SAT and SMT solvers.
- [Unicoq](https://github.com/unicoq/unicoq) - Plugin that replaces the existing unification algorithm with an enhanced one.

### Tools

- [Alectryon](https://github.com/cpitclaudel/alectryon) - Collection of tools for writing technical documents that mix Coq code and prose.
- [CFML](https://gitlab.inria.fr/charguer/cfml2) - Tool for proving properties of OCaml programs in separation logic.
- [coq2html](https://github.com/xavierleroy/coq2html) - Alternative HTML documentation generator for Coq.
- [CoqOfOCaml](https://github.com/clarus/coq-of-ocaml) - Tool for generating idiomatic Coq from OCaml code.
- [coq-dpdgraph](https://github.com/Karmaki/coq-dpdgraph) - Tool for building dependency graphs between Coq objects.
- [coq-tools](https://github.com/JasonGross/coq-tools) - Scripts to help construct small reproducing examples of bugs, remove unneeded imports, etc.
- [Cosette](https://github.com/uwdb/Cosette) - Automated solver for reasoning about SQL query equivalences.
- [hs-to-coq](https://github.com/plclub/hs-to-coq) - Converter from Haskell code to equivalent Coq code.
- [lngen](https://github.com/plclub/lngen) - Tool for generating locally nameless Coq definitions and proofs.
- [Menhir](http://gallium.inria.fr/~fpottier/menhir/) - Parser generator that can output Coq code for verified parsers.
- [mCoq](https://github.com/EngineeringSoftware/mcoq) - Mutation analysis tool for Coq projects.
- [Ott](https://github.com/ott-lang/ott) - Tool for writing definitions of programming languages and calculi that can be translated to Coq.
- [Roosterize](https://github.com/EngineeringSoftware/roosterize) - Tool for suggesting lemma names in Coq projects.
- [SerAPI](https://github.com/ejgallego/coq-serapi) - Library and tools for (de)serialization of Coq code to and from JSON and S-expressions.

### Type Theory and Mathematics

- [Analysis](https://github.com/math-comp/analysis) - Library for classical real analysis compatible with Mathematical Components.
- [Category Theory in Coq](https://github.com/jwiegley/category-theory) - Axiom-free formalization of category theory.
- [Completeness and Decidability of Modal Logic Calculi](https://github.com/coq-community/comp-dec-modal) - Soundness, completeness, and decidability for the logics K, K*, CTL, and PDL.
- [CoqPrime](https://github.com/thery/coqprime) - Library for certifying primality using Pocklington and Elliptic Curve certificates.
- [CoRN](https://github.com/coq-community/corn) - Library of constructive real analysis and algebra.
- [Coqtail Math](https://github.com/coq-community/coqtail-math) - Library of mathematical results ranging from arithmetic to real and complex analysis.
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot) - Formalization of classical real analysis compatible with the standard library and focusing on usability.
- [Finmap](https://github.com/math-comp/finmap) - Extension of Mathematical Components with finite maps, sets, and multisets.
- [Four Color Theorem](https://github.com/math-comp/fourcolor) - Formal proof of the Four Color Theorem, a landmark result of graph theory.
- [Gaia](https://github.com/coq-community/gaia) - Implementation of books from Bourbaki's Elements of Mathematics, including set theory and number theory.
- [GeoCoq](https://github.com/GeoCoq/GeoCoq) - Formalization of geometry based on Tarski's axiom system.
- [Graph Theory](https://github.com/coq-community/graph-theory) - Formalized graph theory results.
- [Homotopy Type Theory](https://github.com/HoTT/HoTT) - Development of homotopy-theoretic ideas.
- [Infotheo](https://github.com/affeldt-aist/infotheo) - Formalization of information theory and linear error-correcting codes.
- [Mathematical Components](http://math-comp.github.io) - Formalization of mathematical theories, focusing in particular on group theory.
- [Math Classes](https://github.com/coq-community/math-classes) - Abstract interfaces for mathematical structures based on type classes.
- [Odd Order Theorem](https://github.com/math-comp/odd-order) - Formal proof of the Odd Order Theorem, a landmark result of finite group theory.
- [Puiseuxth](https://github.com/roglo/puiseuxth) - Proof of Puiseux's theorem and computation of roots of polynomials of Puiseux's series.
- [UniMath](https://github.com/UniMath/UniMath) - Library which aims to formalize a substantial body of mathematics using the univalent point of view.

### Verified Software

- [CompCert](http://compcert.inria.fr) - High-assurance compiler for almost all of the C language (ISO C99), generating efficient code for the PowerPC, ARM, RISC-V and x86 processors.
- [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto) - Cryptographic primitive code generation.
- [Incremental Cycles](https://gitlab.inria.fr/agueneau/incremental-cycles) - Verified OCaml implementation of an algorithm for incremental cycle detection in graphs.
- [JSCert](https://github.com/jscert/jscert) - Coq specification of ECMAScript 5 (JavaScript) with verified reference interpreter.
- [lambda-rust](https://gitlab.mpi-sws.org/iris/lambda-rust) - Formal model of a Rust core language and type system, a logical relation for the type system, and safety proofs for some Rust libraries.
- [Vélus](http://velus.inria.fr/) - Verified compiler for a Lustre/Scade-like dataflow synchronous language.
- [Verdi Raft](https://github.com/uwplse/verdi-raft) - Implementation of the Raft distributed consensus protocol, verified in Coq using the Verdi framework.

## Resources

### Community

- [Official Coq website](https://coq.inria.fr)
- [Official Coq manual](https://coq.inria.fr/refman/)
- [Official Coq standard library](https://coq.inria.fr/stdlib/)
- [Official Coq Discourse forum](https://coq.discourse.group)
- [Official Coq Zulip chat](https://coq.zulipchat.com)
- [Official Coq-Club mailing list](https://sympa.inria.fr/sympa/arc/coq-club)
- [Official Coq wiki](https://github.com/coq/coq/wiki)
- [Official Coq Twitter](https://twitter.com/CoqLang)
- [coq-community package maintenance project](https://github.com/coq-community/manifesto)
- [Coq subreddit](https://www.reddit.com/r/coq/)
- [Coq tag on Stack Overflow](https://stackoverflow.com/questions/tagged/coq)
- [Coq tag on Theoretical Computer Science Stack Exchange](https://cstheory.stackexchange.com/questions/tagged/coq)
- [Mathematical Components wiki](https://github.com/math-comp/math-comp/wiki)
- [Planet Coq link aggregator](https://coq.pl-a.net)

### Blogs

- [Coq Exchange: ideas and experiment reports about Coq](https://project.inria.fr/coqexchange/news/)
- [Gagallium](http://gallium.inria.fr/blog)
- [Gregory Malecha's blog](https://gmalecha.github.io)
- [Guillaume Claret's Coq blog](http://coq-blog.clarus.me)
- [Joachim Breitner's blog posts on Coq](http://www.joachim-breitner.de/blog/tag/Coq)
- [MIT PLV blog posts on Coq](https://plv.csail.mit.edu/blog/category/coq.html)
- [PLClub Blog](https://www.seas.upenn.edu/~plclub/blog/)
- [Poleiro: a Coq blog by Arthur Azevedo de Amorim](http://poleiro.info)
- [Ralf Jung's blog posts on Coq](https://www.ralfj.de/blog/categories/coq.html)
- [Thomas Letan's blog posts on Coq](https://soap.coffee/~lthms/#coq)

### Books

- [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/) - The first book dedicated to Coq.
- [Software Foundations](https://softwarefoundations.cis.upenn.edu) - Series of Coq-based textbooks on logic, functional programming, and foundations of programming languages, aimed at being accessible to beginners.
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) - Textbook about practical engineering with Coq which teaches advanced practical tricks and a very specific style of proof.
- [Program Logics for Certified Compilers](https://www.cs.princeton.edu/~appel/papers/plcc.pdf) - Book that explains how to construct program logics using separation logic, accompanied by a formal model in Coq which is applied to the Clight programming language and other examples.
- [Formal Reasoning About Programs](http://adam.chlipala.net/frap/) - Book that simultaneously provides a general introduction to formal logical reasoning about the correctness of programs and to using Coq for this purpose.
- [Programs and Proofs](https://ilyasergey.net/pnp/) - Book that gives a brief and practically-oriented introduction to interactive proofs in Coq which emphasizes the computational nature of inductive reasoning about decidable propositions via a small set of primitives from the SSReflect proof language.
- [Computer Arithmetic and Formal Proofs](http://iste.co.uk/book.php?id=1238) - Book that describes how to formally specify and verify floating-point algorithms in Coq using the Flocq library.
- [The Mathematical Components book](https://math-comp.github.io/mcb/) - Book oriented towards mathematically inclined users, focusing on the Mathematical Components library and the SSReflect proof language.

### Course Material

- [Foundations of Separation Logic](https://chargueraud.org/teach/verif/) - Introduction to using separation logic to reason about sequential imperative programs in Coq.
- [Introduction to Computational Logic](https://courses.ps.uni-saarland.de/icl_20/2/Resources) - Introduction to basic logic principles, constructive type theory, and interactive theorem proving with Coq.

### Tutorials and Hints

- [CodeWars' Coq kata](https://www.codewars.com/kata/search/coq) - Online proving challenges.
- [Coq'Art Exercises and Tutorials](https://github.com/coq-community/coq-art) - Coq code and exercises from the Coq'Art book, including additional tutorials.
- [Coq in a Hurry](http://cel.archives-ouvertes.fr/inria-00001173) - Introduction to how Coq can be used to define logical concepts and functions and reason about them.
- [Lemma Overloading](https://github.com/coq-community/lemma-overloading) - Demonstration of design patterns for programming and proving with canonical structures.
- [MathComp Tutorial Materials](https://github.com/math-comp/tutorial_material) - Source code for Mathematical Components tutorials.
- [Mike Nahas's Coq Tutorial](https://mdnahas.github.io/doc/nahas_tutorial.html) - Basics of using Coq to write formal proofs.
- [Tricks in Coq](https://github.com/tchajed/coq-tricks) - Tips, tricks, and features that are hard to discover.
