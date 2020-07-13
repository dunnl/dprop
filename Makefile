
# Makefile from https://github.com/coq-community/coqdocjs/blob/master/Makefile
EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 3 --latex --interpolate \
  --index indexpage --lib-subtitles --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
VS:=$(wildcard *.v)
VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

CRUFT_EXT=*.vo *.vos *.vok *.glob .*.aux
CRUFT:=$(foreach ext,$(CRUFT_EXT),$(wildcard $(ext)))

ifeq (,$(VS_IN_PROJ))
VS_OTHER := $(VS)
else
VS := $(VS_IN_PROJ)
endif

SEDHTML:=sed -i -e 's/\.\/toc\.html/\.\/index.html/g'
all: docs

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)
	-rm -f $(CRUFT)

purge: clean
	-rm -fr html docs
	-rm -f $(wildcard extracted/*.ml)
	-rm -f $(wildcard extracted/*.mli)

test:
	ls $(CRUFT)

docs: $(COQMAKEFILE) $(VS)
	-rm -fr html docs
	@$(MAKE) -f $(COQMAKEFILE) html 
	cp $(EXTRA_DIR)/resources/* html
	mv html/ docs/
	find docs/ -type f -exec $(SEDHTML) {} \;
	mv docs/toc.html docs/index.html


$(COQMAKEFILE): $(COQ_PROJ) $(VS)
		coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ) $(VS): ;

.PHONY: clean all force
