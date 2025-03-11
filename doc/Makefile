COQDOCJS_DIR ?= ../doc
EXTRA_DIR = $(COQDOCJS_DIR)/extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html \
	-d ../doc/
export COQDOCFLAGS
COQFILES_DIR ?= ../theories
COQMAKEFILE ?= $(COQFILES_DIR)/CoqMakefile
COQDOCJS_LN ?= false

remove-old:
	rm -rf html

coqdoc: $(COQMAKEFILE)
	cd $(COQFILES_DIR) && $(MAKE) html && mv html/ $(COQDOCJS_DIR)/
ifeq ($(COQDOCJS_LN),true)
	ln -sf ../$(EXTRA_DIR)/resources html
else
	cp -R $(EXTRA_DIR)/resources html
endif

create-index:
	cp html/toc.html html/index.html

doc: remove-old coqdoc create-index

.PHONY: remove-old coqdoc
