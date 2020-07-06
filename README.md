Formalizations/Coq code for my thesis

# About

This is a meta-repository for collecting the logics that I have
developed for my thesis.

- `lambdac`: λMC – monadic translation, and the corresponding logic,
  of a mini C fragment into HeapLang.
  See the overview paper [Semi-automated reasoning about non-determinism in C expressions](http://cs.ru.nl/~dfrumin/wpc/iris-c-monad.pdf). 
- `reloc`: ReLoC - a logic for proving contexutal refinements.
  See the overview paper [ReLoC Reloaded: A Mechanized Relational Logic for Fine-Grained Concurrency and Logical Atomicity](https://arxiv.org/abs/2006.13635).
- `seloc`: SeLoC - a logic for proving non-interference.
  See the overview paper [Compositional Non-Interference for Fine-Grained Concurrent Programs](https://arxiv.org/abs/1910.00905).


The folders `stdpp` and `iris` contain compatible dependencies.
(Specifically, the std++ library and the Iris framework)

Please consult the `README.md` files in the subfolders.

# Cloning and compiling

Requires [Coq](https://coq.inria.fr/) version >= 8.11.0.

Clone the repository, and run

```
git submodule init
git submodule update
```

Then compile and install the dependencies:

```
cd stdpp
make -j2
make install
cd ../iris
make -j2
make install
```

Then you can compile and work with the rest of the source code.

To compile `seloc` you also need the [Equations](https://github.com/mattam82/Coq-Equations) plugin.
You can install it from opam:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.2.1+8.11
```
