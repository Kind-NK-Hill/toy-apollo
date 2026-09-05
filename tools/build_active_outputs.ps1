[CmdletBinding()]
param(
    [switch]$IncludeScratch,
    [switch]$ListOnly
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $PSScriptRoot
$outputDir = Join-Path $repoRoot "ProbabilityTheory"

if (-not (Test-Path -LiteralPath $outputDir)) {
    throw "Output directory not found: $outputDir"
}

$files = Get-ChildItem -LiteralPath $outputDir -Filter "*.lean" -File -Recurse

if (-not $IncludeScratch) {
    $files = $files | Where-Object { $_.BaseName -notlike "HarvestRepair_*" }
}

$modules = $files |
    Sort-Object FullName |
    ForEach-Object {
        $relative = $_.FullName.Substring($repoRoot.Length + 1)
        [IO.Path]::ChangeExtension($relative, $null).Replace("\", ".")
    }

if (-not $modules -or $modules.Count -eq 0) {
    throw "No ProbabilityTheory modules found to build."
}

if ($ListOnly) {
    $modules
    exit 0
}

Write-Host "Building $($modules.Count) ProbabilityTheory modules"

Push-Location $repoRoot
try {
    & lake build @modules
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}
