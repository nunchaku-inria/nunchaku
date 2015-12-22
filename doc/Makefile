
DOCS = $(wildcard *.adoc)
HTML_DOCS = $(patsubst %.adoc,%.html,$(DOCS))

all: $(HTML_DOCS)

%.html: %.adoc
	asciidoc $<

.PHONY: all
