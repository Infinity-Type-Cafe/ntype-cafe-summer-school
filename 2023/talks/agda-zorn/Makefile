#
# Author: Jake Zimmerman <jake@zimmerman.io>
#
# ===== Usage ================================================================
#
# make                  Prepare docs/ folder (all markdown & assets)
# make docs/index.html  Recompile just docs/index.html
#
# make watch            Start a local HTTP server and rebuild on changes
# PORT=4242 make watch  Like above, but use port 4242
#
# make clean            Delete all generated files
#
# ============================================================================

DOCS = ../../resources/agda-zorn
SOURCES := $(shell find src -type f -name '*.lagda.md')
TARGETS := $(addprefix $(DOCS)/,$(subst /,.,$(patsubst src/%.lagda.md,%.html,$(SOURCES))))

.PHONY: all
all: $(DOCS)/.nojekyll $(TARGETS) final

.PHONY: clean
clean:
	rm -rf $(DOCS)

.PHONY: watch
watch:
	./tools/serve.sh --watch

$(DOCS)/.nojekyll: $(wildcard public/*) public/.nojekyll
	rm -vrf $(DOCS) && mkdir -p $(DOCS) && cp -vr public/.nojekyll public/* $(DOCS)

.PHONY: $(DOCS)
docs: $(DOCS)/.nojekyll

# Literate agda markdown to pandoc markdown
.SECONDEXPANSION:
$(DOCS)/%.md: src/$$(subst .,/,%).lagda.md
	agda --html --html-dir=$(DOCS) --highlight-occurrences --html-highlight=auto "$<"

# Generalized rule: how to build a .html file from each .md
# Note: you will need pandoc 2 or greater for this to work
$(DOCS)/%.html: $(DOCS)/%.md template.html5 Makefile tools/build.sh
	tools/build.sh "$<" "$@"

final:
	-rm $(DOCS)/*.md
