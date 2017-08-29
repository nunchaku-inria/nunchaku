
%.html: %.adoc
	asciidoctor $< > $@

TARGETS=$(subst .adoc,.html,$(shell find -name '*.adoc'))

all: $(TARGETS)

clean:
	rm $(TARGETS)

upload: all
	./upload_doc.sh *.html

.PHONY: all clean upload
