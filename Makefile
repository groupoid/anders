default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild -use-menhir -yaccflag "--explain" anders.native

byte:
	ocamlbuild -use-menhir anders.byte -tag 'debug'
