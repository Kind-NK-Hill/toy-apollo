[CmdletBinding()]
param(
    [switch]$IncludeScratch,
    [switch]$ListOnly
)

$ErrorActionPreference = "Stop"

$repoRoot = Split-Path -Parent $PSScriptRoot
$workspaceRoot = if ($env:TOY_APOLLO_WORKSPACE_ROOT) {
    [System.IO.Path]::GetFullPath($env:TOY_APOLLO_WORKSPACE_ROOT)
}
else {
    Split-Path -Parent $repoRoot
}
$matRepo = if ($env:TOY_APOLLO_MAT_REPO_ROOT) {
    if ([System.IO.Path]::IsPathRooted($env:TOY_APOLLO_MAT_REPO_ROOT)) {
        [System.IO.Path]::GetFullPath($env:TOY_APOLLO_MAT_REPO_ROOT)
    }
    else {
        [System.IO.Path]::GetFullPath((Join-Path $workspaceRoot $env:TOY_APOLLO_MAT_REPO_ROOT))
    }
}
else {
    Join-Path $workspaceRoot "MAT3280-formalization-output"
}
$outputDir = Join-Path $matRepo "ProbabilityTheory"

if (-not (Test-Path -LiteralPath $outputDir)) {
    throw "Output directory not found: $outputDir"
}

$files = Get-ChildItem -LiteralPath $outputDir -Filter "*.lean" -File -Recurse

if (-not $IncludeScratch) {
    $scratchDir = Join-Path $outputDir "Scratch"
    $files = $files | Where-Object { -not $_.FullName.StartsWith($scratchDir, [System.StringComparison]::OrdinalIgnoreCase) }
}

$modules = $files |
    Sort-Object FullName |
    ForEach-Object {
        $relative = [System.IO.Path]::GetRelativePath($matRepo, $_.FullName)
        $withoutExtension = $relative.Substring(0, $relative.Length - ".lean".Length)
        $withoutExtension.Replace("\", ".").Replace("/", ".")
    }

if (-not $modules -or $modules.Count -eq 0) {
    throw "No MAT ProbabilityTheory modules found to build."
}

if ($ListOnly) {
    $modules
    exit 0
}

Write-Host "Building the MAT ProbabilityTheory library ($($modules.Count) source modules)"

Push-Location $matRepo
try {
    & lake build
    exit $LASTEXITCODE
}
finally {
    Pop-Location
}
