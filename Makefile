COQ_DIR := theories/
DOC_DIR := doc/

doc:
	cd $(DOC_DIR) && $(MAKE) doc

coq:
	cd $(COQ_DIR) && $(MAKE)

clean:
	cd $(COQ_DIR) && $(MAKE) clean

.PHONY: doc clean

all: coq doc
