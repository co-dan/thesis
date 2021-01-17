Formalizations/Coq code for my thesis.

# About

This is a meta-repository for collecting the logics that I have
developed for my thesis.

- `lambdac`: λMC – monadic translation, and the corresponding logic,
  of a mini C fragment into HeapLang.
  See the overview paper [Semi-automated reasoning about non-determinism in C expressions](https://iris-project.org/pdfs/2019-esop-c.pdf). 
- `reloc`: ReLoC - a logic for proving contexutal refinements.
  See the overview paper [ReLoC Reloaded: A Mechanized Relational Logic for Fine-Grained Concurrency and Logical Atomicity](https://arxiv.org/abs/2006.13635).
- `seloc`: SeLoC - a logic for proving non-interference.
  See the overview paper [Compositional Non-Interference for Fine-Grained Concurrent Programs](https://arxiv.org/abs/1910.00905).


The folders `stdpp`, `iris`, and `autosubst` contain compatible versions of the dependencies.
The folder `prelim` contains the formalizations of the propositions from Chapter 2.

Please consult the `README.md` files in the subfolders for details.

# Compilation instructions

Requires [Coq](https://coq.inria.fr/) version >= 8.12 (but it might work with older versions as well).
You can also use `opam` for installing the packages.

Clone the repository with
```
git clone --recurse-submodules https://github.com/co-dan/thesis.git
```
Then compile and install the dependencies:

```bash
cd thesis/stdpp
make -j2
make install
cd ../iris
make -j2
make install
cd ../autosubst
make -j2
make install
cd ..
```

Then you can compile and work with the rest of the source code, e.g.
```bash
cd reloc
make -j2
```

To compile `seloc` you also need the [Equations](https://github.com/mattam82/Coq-Equations) plugin.
You can install it from opam:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.2.3+8.12     # pick a version number corresponding to your Coq version
```

## Installing dependencies with `opam`

Alterenatively you can try the following:

```
opam pin coq-stdpp.dev ./stdpp
opam pin coq-iris.dev ./iris
```
