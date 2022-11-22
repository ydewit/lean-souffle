# TODO Move this to lakefile, if possible
SOUFFLE_OUTPUTS_DIR=./build/outputs/
SOUFFLE_FACTS_DIR=./facts/

#SOUFFLE_FLAGS=--debug-report=a.html

.PHONY: souffle-reachingAnalysis
souffle-reachingAnalysis: build
	souffle $(SOUFFLE_FLAGS) --fact-dir=$(SOUFFLE_FACTS_DIR) --output-dir=$(SOUFFLE_OUTPUTS_DIR) ./dl/ReachingDefinitionsAnalysis.dl

.PHONY: souffle-lcnf
souffle-lcnf: build
	souffle $(SOUFFLE_FLAGS) --fact-dir=$(SOUFFLE_FACTS_DIR) --output-dir=$(SOUFFLE_OUTPUTS_DIR) ./dl/ReachingDefinitionsAnalysis.dl

.PHONY: build
build:
	@mkdir -p $(SOUFFLE_OUTPUTS_DIR)
	@mkdir -p $(SOUFFLE_FACTS_DIR)
	lake build

clean:
	rm -f ./dl/Lean.dl
	rm -f ./facts/*.facts
	rm -f ./build/outputs/*
