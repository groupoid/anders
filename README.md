# Requirements

OCaml, ocamlbuild, ocamllex and Menhir.

On Ubuntu 18.04 all this can be installed via:

```shell
$ apt install ocaml ocamlbuild menhir
```

# Build

```shell
$ ocamlbuild -use-menhir tt.native
$ ./tt.native test.tt
```
