FLAGS = -use-menhir -yaccflag "--explain" -ocamlc "ocamlc -w +a-4-29"
OPTFLAGS = -classic-display -ocamlopt "ocamlopt -O3" -ccopt -static

default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild $(FLAGS) anders.native

release:
	ocamlbuild $(FLAGS) anders.native $(OPTFLAGS)

byte:
	ocamlbuild $(FLAGS) anders.byte -tag 'debug'
