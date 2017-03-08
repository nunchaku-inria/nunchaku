
%.html: %.adoc
	asciidoc $< > $@

TARGETS=$(subst .adoc,.html,$(shell find -name '*.adoc'))

all: $(TARGETS)

upload: all
	./upload_doc.sh *.html

.PHONY: all
