FLAGS = -use-menhir -yaccflag "--explain"
OPTFLAGS = -classic-display -ocamlopt "ocamlopt -O3"

default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild $(FLAGS) anders.native

release:
	ocamlbuild $(FLAGS) anders.native $(OPTFLAGS)

byte:
	ocamlbuild $(FLAGS) anders.byte -tag 'debug'
