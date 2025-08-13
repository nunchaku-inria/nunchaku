JOBS ?= 8

bench:
	python3 gen-tasks.py
	benchexec --tool-dir ../../ --no-container -N $(JOBS) --no-hyperthreading config.xml

clean:
	rm -rf tasks/ results/

.PHONY: bench clean
