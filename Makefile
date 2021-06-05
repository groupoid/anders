default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild -use-menhir anders.native

byte:
	ocamlbuild -use-menhir anders.byte -tag 'debug'
