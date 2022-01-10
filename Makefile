FLAGS = -I src/kernel -pkgs 'zarith' -use-menhir -yaccflag "--explain" -ocamlc "ocamlc -w +a-4-29"
OPTFLAGS = -classic-display -ocamlopt "ocamlopt -O3"
NATIVEFLAGS = -ocamlopt "ocamlopt -O3"

default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild $(FLAGS) anders.native $(NATIVEFLAGS)

release:
	ocamlbuild $(FLAGS) anders.native $(OPTFLAGS)

byte:
	ocamlbuild $(FLAGS) anders.byte -tag 'debug'

profiler:
	ocamlbuild $(FLAGS) anders.d.byte
