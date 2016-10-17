# OASIS_START
# DO NOT EDIT (digest: 4c293511860bb966e727ba6f0ecc8197)

SETUP = ./setup.exe

build: setup.data $(SETUP)
	$(SETUP) -build $(BUILDFLAGS)

doc: setup.data $(SETUP) build
	$(SETUP) -doc $(DOCFLAGS)

test: setup.data $(SETUP) build
	$(SETUP) -test $(TESTFLAGS)

all: $(SETUP)
	$(SETUP) -all $(ALLFLAGS)

install: setup.data $(SETUP)
	$(SETUP) -install $(INSTALLFLAGS)

uninstall: setup.data $(SETUP)
	$(SETUP) -uninstall $(UNINSTALLFLAGS)

reinstall: setup.data $(SETUP)
	$(SETUP) -reinstall $(REINSTALLFLAGS)

clean: $(SETUP)
	$(SETUP) -clean $(CLEANFLAGS)

distclean: $(SETUP)
	$(SETUP) -distclean $(DISTCLEANFLAGS)
	$(RM) $(SETUP)

setup.data: $(SETUP)
	$(SETUP) -configure $(CONFIGUREFLAGS)

configure: $(SETUP)
	$(SETUP) -configure $(CONFIGUREFLAGS)

setup.exe: setup.ml _oasis
	ocamlfind ocamlopt -o $@ -linkpkg -package oasis.dynrun setup.ml || ocamlfind ocamlc -o $@ -linkpkg -package oasis.dynrun setup.ml || true
	$(RM) setup.cmi setup.cmo setup.cmx setup.o

.PHONY: build doc test all install uninstall reinstall clean distclean configure

# OASIS_STOP

DONTTEST=myocamlbuild.ml setup.ml
QTESTABLE=$(filter-out $(DONTTEST), \
	$(wildcard src/core/*.ml) \
	$(wildcard src/core/*.mli) \
	$(wildcard src/parsers/*.ml) \
	$(wildcard src/parsers/*.mli) \
	$(wildcard src/transformations/*.ml) \
	$(wildcard src/transformations/*.mli) \
	$(wildcard src/random/*.ml) \
	$(wildcard src/random/*.mli) \
	)

qtest-clean:
	@rm -rf qtest/

QTEST_PREAMBLE='open Nunchaku_core;; '

qtest-gen:
	@mkdir -p qtest
	@if which qtest > /dev/null ; then \
		qtest extract --preamble $(QTEST_PREAMBLE) \
			-o qtest/run_qtest.ml \
			$(QTESTABLE) 2> /dev/null ; \
	else touch qtest/run_qtest.ml ; \
	fi

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make ; \
	done
