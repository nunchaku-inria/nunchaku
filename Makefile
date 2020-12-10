
J?=3

all: build test

build:
	@dune build @install -j $J

clean:
	@dune clean

doc:
	@dune build @doc

test: build
	@dune runtest --no-buffer --force -j $J
	# ./tests/quick/all.sh # FIXME?

install: build
	@dune install

watch:
	@dune build @all -w

ocp-indent:
	@which ocp-indent > /dev/null || { \
	  	echo 'ocp-indent not found; please run `opam install ocp-indent`'; \
		exit 1 ; \
	  }

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

.PHONY: reindent ocp-indent watch
