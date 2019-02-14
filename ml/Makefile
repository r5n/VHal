.PHONY: all clean utop

OCB_FLAGS = -tag bin_annot -use-menhir -use-ocamlfind
OCB = ocamlbuild $(OCB_FLAGS)

all: byte

clean:
	$(OCB) -clean

byte:
	$(OCB) main.byte

utop: byte
	utop
