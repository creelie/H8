# verify.ps1 -- run the whole verification on Windows (PowerShell 5 or 7).
#
#   powershell -ExecutionPolicy Bypass -File .\verify.ps1
#
# Runs the Python suite (exact arithmetic, about fifteen minutes) and then the Lean
# check: `lake build` of the package when lake is on the path, then the
# axiom report of `lean HodgeObstruction.lean` (about a minute each once the
# toolchain is installed).  Python 3 must
# be on the path as `python` or `python3`; numpy is needed by two scripts.  For
# the Lean step install elan from https://github.com/leanprover/elan and the
# toolchain named in lean\lean-toolchain; if `lean` is not on the path the
# step is skipped and reported.

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $MyInvocation.MyCommand.Path

$py = Get-Command python -ErrorAction SilentlyContinue
if (-not $py) { $py = Get-Command python3 -ErrorAction SilentlyContinue }
if (-not $py) { Write-Error "Python 3 was not found on the path."; exit 1 }

Write-Host "== Python suite (code\verify_all.py) =="
Push-Location (Join-Path $root "code")
& $py.Source "verify_all.py"
$pyStatus = $LASTEXITCODE
Pop-Location
if ($pyStatus -ne 0) { Write-Error "verify_all.py reported a failure (exit $pyStatus)."; exit $pyStatus }

Write-Host ""
Write-Host "== Lean check (lean\HodgeObstruction.lean) =="
$lean = Get-Command lean -ErrorAction SilentlyContinue
if (-not $lean) {
  Write-Host "lean is not on the path; skipping.  Install elan and run:"
  Write-Host "    cd lean; lean HodgeObstruction.lean"
  exit 0
}
Push-Location (Join-Path $root "lean")
$lake = Get-Command lake -ErrorAction SilentlyContinue
if ($lake) {
  & $lake.Source build
  if ($LASTEXITCODE -ne 0) { Pop-Location; Write-Error "lake build failed (exit $LASTEXITCODE)."; exit $LASTEXITCODE }
}
$out = & $lean.Source "HodgeObstruction.lean" 2>&1
$leanStatus = $LASTEXITCODE
$out | Out-File -Encoding ascii "axioms.txt"
Pop-Location
if ($leanStatus -ne 0) { Write-Error "lean exited with status $leanStatus."; exit $leanStatus }

$lines = @($out | Where-Object { $_ -match "axioms" })
$free  = @($out | Where-Object { $_ -match "does not depend on any axioms" }).Count
$prop  = @($out | Where-Object { $_ -match "\[propext\]" }).Count
$sorry = @($out | Where-Object { $_ -match "sorryAx" }).Count
Write-Host ("theorems: {0}  axiom-free: {1}  propext only: {2}  sorryAx: {3}" -f $lines.Count, $free, $prop, $sorry)
if ($lines.Count -ne 80 -or ($free + $prop) -ne 80 -or $sorry -ne 0) {
  Write-Error "the Lean report does not match the expected 80 theorems."; exit 1
}
Write-Host "overall: PASS"
