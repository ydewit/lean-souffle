# TODO Move this to lakefile, if possible
SOUFFLE_OUTPUTS_DIR=./outputs
SOUFFLE_FACTS_DIR=./facts
SOUFFLE_RULES_DIR=./rules

#SOUFFLE_FLAGS=--debug-report=a.html
# SOUFFLE_FLAGS=-t explain

.PHONY: souffle-static-analysis
souffle-static-analysis: #build
	@mkdir -p $(SOUFFLE_OUTPUTS_DIR)
	@mkdir -p $(SOUFFLE_FACTS_DIR)
	@mkdir -p $(SOUFFLE_RULES_DIR)
	souffle $(SOUFFLE_FLAGS) --include-dir=. --fact-dir=$(SOUFFLE_FACTS_DIR)/ --output-dir=$(SOUFFLE_OUTPUTS_DIR) ./rules/StaticAnalysis.dl

# .PHONY: souffle-reachingAnalysis
# souffle-reachingAnalysis: #build
# 	souffle $(SOUFFLE_FLAGS) --fact-dir=$(SOUFFLE_FACTS_DIR) --output-dir=$(SOUFFLE_OUTPUTS_DIR) ./dl/ReachingDefinitionsAnalysis.dl

# .PHONY: souffle-lcnf
# souffle-lcnf: #build
# 	souffle $(SOUFFLE_FLAGS) --fact-dir=$(SOUFFLE_FACTS_DIR) --output-dir=$(SOUFFLE_OUTPUTS_DIR) ./dl/ReachingDefinitionsAnalysis.dl

.PHONY: build
build:
	@mkdir -p $(SOUFFLE_OUTPUTS_DIR)
	@mkdir -p $(SOUFFLE_FACTS_DIR)
	lake build

clean:
	rm -f ./facts.dl
	rm -f ./facts/*.facts
	rm -f ./outputs/*
