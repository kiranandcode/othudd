# OThudd - Ocaml Theorem Driven Development
Template for software development workflow using theorems instead of tests.

<TODO add synopsis>

## Requirements
 - Coq - 8.9
 - Ssreflect - 1.9
 - Ocaml
 - Dune
 - Core

## Setup
1. Clone this repository

```
git clone <site-name>/thudd.git
```

2. Edit dune file to name project to liking.

3. Run make

```
make
```

4. Verify it works with

```
make run
```

## Development Workflow

See `lib/examplecoq.ml`,`lib/examplecoqinst.ml` for concrete examples of the following.

1. For experimental library stuff, build it first in `src/` and figure out a good abstract interface for the core logic.
2. Construct an abstract version of this interface in `lib/` in Coq as a Module Type, capturing any pre/postconditions as axioms of the module type.
3. Implement and prove core logic given the preconditions/postconditions in abstract form,  taking a module conforming to the type specified in 2. as a parameter.
4. At the end of the file add `Extract "<file-name>" <abstract-module-name>`.
5. Run `make` to build an ocaml version of the code.
6. Define a concrete Ocaml module in the `lib/` directory that imports the constructed abstract core logic and instantiates it with a concrete type. 
7. Use verified module in `src/` and repeat.

Will add more if more comes up

## Note: Updates
 If you are reading this from micro$oft's github, then be advised that
 updates will be first pushed to the version hosted on Gitlab, and
 only then, maybe will they be pushed to micro$oft's github.
