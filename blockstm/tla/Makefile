.DEFAULT_GOAL := tlc
.PHONY: tlc tlc-value tlc-version tlc-aba-value tlc-aba-version clean-states help check-tlc

JAVA ?= java
JAVA_OPTS ?= -XX:+UseParallelGC
TLA_MODULE ?= BlockSTM.tla

# Auto-detect tla2tools.jar from the VS Code TLA+ extension install.
TLA2TOOLS_JAR ?= $(shell ls -t "$$HOME"/.vscode/extensions/tlaplus.vscode-ide-*/tools/tla2tools.jar 2>/dev/null | head -n 1)

ifeq ($(strip $(TLA2TOOLS_JAR)),)
TLC ?= tlc2.TLC
else
TLC ?= $(JAVA) $(JAVA_OPTS) -cp "$(TLA2TOOLS_JAR)" tlc2.TLC
endif
TLC_OPTS ?= -deadlock -workers 1

CFGS := \
	BlockSTM_version.cfg \
	BlockSTM_value.cfg \
	BlockSTM_ABA_version.cfg \
	BlockSTM_ABA_value.cfg

help:
	@echo "Targets:"
	@echo "  make tlc            # run all configs"
	@echo "  make tlc-version     # run version-based config"
	@echo "  make tlc-value       # run value-based config"
	@echo "  make tlc-aba-version # run ABA scenario (version-based)"
	@echo "  make tlc-aba-value   # run ABA scenario (value-based)"
	@echo "  make clean-states    # remove TLC state cache"
	@echo ""
	@echo "Variables:"
	@echo "  TLA2TOOLS_JAR=<path> # override jar location (when tlc2.TLC not on PATH)"
	@echo "  TLC=<cmd>            # override TLC command (e.g. tlc2.TLC)"
	@echo "  TLC_OPTS='...'       # extra TLC flags"
	@echo "  TLA_MODULE=<file>    # module to check (default: BlockSTM.tla)"

check-tlc:
	@if [ "$(TLC)" = "tlc2.TLC" ]; then \
		command -v tlc2.TLC >/dev/null 2>&1 || { \
			echo "ERROR: tlc2.TLC not found on PATH, and TLA2TOOLS_JAR was not detected."; \
			echo "Fix one of:"; \
			echo "  - install TLA+ tools so tlc2.TLC is on PATH"; \
			echo "  - set TLA2TOOLS_JAR=<path/to/tla2tools.jar>"; \
			exit 2; \
		}; \
	fi

# Run all configs
tlc: check-tlc
	@set -e; \
	for cfg in $(CFGS); do \
		echo "==> $$cfg"; \
		$(TLC) $(TLC_OPTS) -config "$$cfg" $(TLA_MODULE); \
	done

# Individual configs
tlc-version: check-tlc
	$(TLC) $(TLC_OPTS) -config BlockSTM_version.cfg $(TLA_MODULE)

tlc-value: check-tlc
	$(TLC) $(TLC_OPTS) -config BlockSTM_value.cfg $(TLA_MODULE)

tlc-aba-version: check-tlc
	$(TLC) $(TLC_OPTS) -config BlockSTM_ABA_version.cfg $(TLA_MODULE)

tlc-aba-value: check-tlc
	$(TLC) $(TLC_OPTS) -config BlockSTM_ABA_value.cfg $(TLA_MODULE)

clean-states:
	@rm -rf ./states
