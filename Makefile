FLAGS = -I src/kernel -pkgs 'zarith' -use-ocamlfind -use-menhir -yaccflag "--explain" -ocamlc "ocamlc -w +a-4-29"
OPTFLAGS = -classic-display -ocamlopt "ocamlopt -O3"
NATIVEFLAGS = -ocamlopt "ocamlopt -O3"

default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild $(FLAGS) -lib dynlink anders.native $(NATIVEFLAGS)

release:
	ocamlbuild $(FLAGS) -lib dynlink anders.native $(OPTFLAGS)

byte:
	ocamlbuild $(FLAGS) -lib dynlink anders.byte -tag 'debug'

tactics:
	ocamlbuild $(FLAGS) -I src/tactics tactics.cmxs
