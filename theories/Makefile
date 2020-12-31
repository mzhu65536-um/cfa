COQMFFLAGS := -Q . CFA

DEP := Coqlib.v Lang.v Ordered.v Ancilla.v
MORE := Analyse.v  Constraints.v Check.v
END := Reference.v Postscript.v

ALLVFILES :=  $(DEP) $(MORE) $(END)


build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	rm *.vok *.vo *.vos *.vio *.glob *.aux
Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

.PHONY: build clean
