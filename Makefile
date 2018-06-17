
J?=3

all: build test

build:
	jbuilder build @install -j $J

clean:
	jbuilder clean

doc:
	jbuilder build @doc

test: build
	jbuilder runtest --no-buffer --force -j $J
	# ./tests/quick/all.sh # FIXME?

open_doc: doc
	xdg-open _build/default/_doc/index.html

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make all ; \
	done

ocp-indent:
	@which ocp-indent > /dev/null || { \
	  	echo 'ocp-indent not found; please run `opam install ocp-indent`'; \
		exit 1 ; \
	  }

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

.PHONY: reindent ocp-indent watch
