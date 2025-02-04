# Makefile for Toyprover testing (Windows-PowerShell enhanced v2)

TIMEOUT_SEC = 2
TEST_DIR = Toyprover/Test/Pelletier
EXE_PATH = .lake/build/bin/toyprover.exe

.PHONY: build test

build:
	@lake build toyprover

test: build
	@echo "Starting tests with $(TIMEOUT_SEC) second timeout..."
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
	 Write-Host \"Success     : $$success ($$percentage)\"; \
	 Write-Host \"Timeout     : $$timeout\"; \
	 if ($$timeout_files.Count -gt 0) { \
		Write-Host \"Timeout files: $$($$timeout_files -join ', ')\" \
	 }"