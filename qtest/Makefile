
QTEST_PREAMBLE='open Nunchaku_core;; open Nunchaku_random;; open Nunchaku_transformations;;'

DONTTEST=$(wildcard ../src/**/*.cppo.*)
QTESTABLE=$(filter-out $(DONTTEST), \
	$(wildcard ../src/core/*.ml) \
	$(wildcard ../src/core/*.mli) \
	$(wildcard ../src/transformations/*.ml) \
	$(wildcard ../src/transformations/*.mli) \
	$(wildcard ../src/random/*.ml) \
	$(wildcard ../src/random/*.mli) \
	)
	# $(wildcard ../src/backends/*.ml) \
	# $(wildcard ../src/backends/*.mli) \

qtest-gen:
	@if which qtest > /dev/null ; then \
	  	echo "generate qtest"; \
		qtest extract --preamble $(QTEST_PREAMBLE) \
			-o run_qtest.ml \
			$(QTESTABLE) 2> /dev/null ; \
	else touch run_qtest.ml ; \
	fi
