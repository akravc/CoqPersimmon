COQC=coqc
COQDEP=coqdep

VFILES=calculus.v transitivity.v canonical.v

all: canonical.vo

%.vo: %.v
	$(COQC) $<

depend:
	$(COQDEP) $(VFILES) > .depend

clean:
	rm -f *.vo *.glob *.aux *.vok *.vos .*.aux

-include .depend