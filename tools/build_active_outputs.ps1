[CmdletBinding()]
param(
    [switch]$IncludeScratch,
    [switch]$ListOnly
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $PSScriptRoot
$outputDir = Join-Path $repoRoot "ToyApollo\Output"

if (-not (Test-Path -LiteralPath $outputDir)) {
    throw "Output directory not found: $outputDir"
}

$files = Get-ChildItem -LiteralPath $outputDir -Filter "*.lean" -File

if (-not $IncludeScratch) {
    $files = $files | Where-Object { $_.BaseName -notlike "HarvestRepair_*" }
}

$modules = $files |
    Sort-Object Name |
    ForEach-Object { "ToyApollo.Output.$($_.BaseName)" }

if (-not $modules -or $modules.Count -eq 0) {
    throw "No ToyApollo.Output modules found to build."
}

if ($ListOnly) {
    $modules
    exit 0
}

Write-Host "Building $($modules.Count) ToyApollo.Output modules"

Push-Location $repoRoot
try {
    & lake build @modules
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}
