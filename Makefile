# Makefile for Toyprover testing (Cross-Platform v2)

TIMEOUT_SEC = 2
TEST_DIR = Toyprover/Test/Pelletier
EXE_PATH = .lake/build/bin/toyprover.exe
EXE_PATH_LINUX = .lake/build/bin/toyprover

.PHONY: build test

build:
	@lake build toyprover

test: build
ifeq ($(OS),Windows_NT)
	@echo "Starting tests with $(TIMEOUT_SEC) second timeout (Windows)..."
	@powershell -ExecutionPolicy Bypass -Command \
	"$$ErrorActionPreference = 'Stop'; \
	 $$total = 0; \
	 $$success = 0; \
	 $$timeout = 0; \
	 $$timeout_files = @(); \
	 $$files = @(Get-ChildItem -Path '$(TEST_DIR)' -Filter *.p); \
	 foreach ($$file in $$files) { \
		$$total++; \
		Write-Host -NoNewline \"Testing $$($$file.Name)... \"; \
		$$psi = New-Object System.Diagnostics.ProcessStartInfo; \
		$$psi.FileName = '$(EXE_PATH)'; \
		$$psi.Arguments = \"`\"$$($$file.FullName)`\"\"; \
		$$psi.UseShellExecute = $$false; \
		$$psi.CreateNoWindow = $$true; \
		$$psi.RedirectStandardOutput = $$true; \
		$$process = [System.Diagnostics.Process]::Start($$psi); \
		$$timedOut = $$false; \
		if (-not $$process.WaitForExit($(TIMEOUT_SEC)*1000)) { \
			$$process.Kill(); \
			$$timedOut = $$true; \
		} \
		$$output = $$process.StandardOutput.ReadToEnd().Trim(); \
		if ($$timedOut) { \
			Write-Host 'timeout'; \
			$$timeout++; \
			$$timeout_files += $$file.Name; \
		} elseif ($$output -match '^success') { \
			Write-Host 'success'; \
			$$success++; \
		} elseif ($$output -match 'timeout') { \
			Write-Host 'timeout'; \
			$$timeout++; \
			$$timeout_files += $$file.Name; \
		} else { \
			Write-Host \"failed ($$output)\"; \
		} \
	 } \
	 $$percentage = [math]::Round($$success/$$total*100, 2); \
	 Write-Host \"`nTest results:\"; \
	 Write-Host \"Total tests : $$total\"; \
	 Write-Host \"Success     : $$success ($$percentage%)\"; \
	 Write-Host \"Timeout     : $$timeout\"; \
	 if ($$timeout_files.Count -gt 0) { \
		Write-Host \"Timeout files: $$($$timeout_files -join ', ')\" \
	 }"
else
	@echo "Starting tests with $(TIMEOUT_SEC) second timeout (Linux/macOS)..."
	@bash -c '\
	TIMEOUT_SEC=$(TIMEOUT_SEC); \
	TEST_DIR="$(TEST_DIR)"; \
	EXE_PATH="$(EXE_PATH_LINUX)"; \
	total=0; \
	success=0; \
	timeout=0; \
	timeout_files=(); \
	shopt -s nullglob; \
	files=("$$TEST_DIR"/*.p); \
	for file in "$${files[@]}"; do \
		total=$$((total + 1)); \
		echo -n "Testing $$(basename "$$file")... "; \
		output=$$(timeout $$TIMEOUT_SEC $$EXE_PATH "$$file" 2>&1); \
		status=$$?; \
		if [ $$status -eq 124 ]; then \
			echo "timeout"; \
			timeout=$$((timeout + 1)); \
			timeout_files+=("$$(basename "$$file")"); \
		elif echo "$$output" | grep -q "^success"; then \
			echo "success"; \
			success=$$((success + 1)); \
		else \
			echo "failed ($$output)"; \
		fi; \
	done; \
	if [ $$total -eq 0 ]; then \
		echo "No test files found in $$TEST_DIR"; \
		exit 1; \
	fi; \
	percentage=$$(echo "scale=2; $$success / $$total * 100" | bc); \
	echo -e "\nTest results:"; \
	echo "Total tests : $$total"; \
	echo "Success     : $$success ($$percentage%)"; \
	echo "Timeout     : $$timeout"; \
	if [ $$timeout -gt 0 ]; then \
		IFS=, ; \
		echo "Timeout files: $${timeout_files[*]}"; \
	fi'
endif