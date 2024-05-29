`theories/realizability` : Toy realizability model prototype,
formalized with Iris: Affine lambda calculus ~~> HeapLang

`theories/resources` : Resource algebra for reference counting,
defined inductively as a proof of concept. Contains re-definition
of the agreement resource algebra, with a different non-empty list.

To install dependencies using `opam`:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

make builddep
```

It may be best to install these dependencies on a new "switch"
linked to this directory:
```
cd my-dir
opam switch create my-switch ocaml-base-compiler.4.14.1
opam switch link my-switch .
eval $(opam env)
```

Then, run `make` to build the Rocq project, recompiling after making
changes to any files that the current one depends on.