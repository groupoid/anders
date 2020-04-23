default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild -use-menhir tt.native

byte:
	ocamlbuild -use-menhir tt.byte -tag 'debug'
