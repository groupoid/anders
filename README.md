# Requirements

OCaml, ocamlbuild, ocamllex, Menhir and Make.

On Ubuntu 18.04 all this can be installed via:

```shell
$ apt install ocaml ocamlbuild menhir make
```

# Build

```shell
$ make
$ ./tt.native check experiments/test.tt
```
