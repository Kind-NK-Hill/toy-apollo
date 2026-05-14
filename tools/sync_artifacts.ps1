param(
    [Parameter(Mandatory = $true)]
    [ValidateSet("push", "pull")]
    [string]$Mode,

    [string]$ArtifactsRepoPath = "..\toy-apollo-artifacts",
    [string]$MainRepoPath = "."
)

$ErrorActionPreference = "Stop"

function Copy-ArtifactPath {
    param(
        [string]$SourceRoot,
        [string]$DestRoot,
        [string]$RelativePath
    )
    $src = Join-Path $SourceRoot $RelativePath
    $dst = Join-Path $DestRoot $RelativePath

    if (-not (Test-Path $src)) {
        Write-Host "SKIP $RelativePath (missing at source)"
        return
    }

    $dstParent = Split-Path -Parent $dst
    if ($dstParent -and -not (Test-Path $dstParent)) {
        New-Item -ItemType Directory -Path $dstParent | Out-Null
    }

    if (Test-Path $src -PathType Container) {
        New-Item -ItemType Directory -Path $dst -Force | Out-Null
        robocopy $src $dst /E /NFL /NDL /NJH /NJS /NC /NS | Out-Null
    } else {
        Copy-Item -LiteralPath $src -Destination $dst -Force
    }
    Write-Host "SYNC $RelativePath"
}

$artifactPaths = @(
    "output_lean_files",
    "formalized_chapters",
    "reports",
    "error_logs",
    "error_logs_1",
    "aristotle_outbox",
    "aristotle_archives",
    "aristole-example-outputs",
    "mathlib_index.faiss",
    "mathlib_corpus.json",
    "project_ledger.json",
    "lab_notebook.json"
)

$main = Resolve-Path $MainRepoPath
if (-not (Test-Path $ArtifactsRepoPath)) {
    if ($Mode -eq "push") {
        New-Item -ItemType Directory -Path $ArtifactsRepoPath | Out-Null
    } else {
        throw "Artifacts repository path not found: $ArtifactsRepoPath"
    }
}
$artifacts = Resolve-Path $ArtifactsRepoPath

if ($Mode -eq "push") {
    Write-Host "PUSH main -> artifacts"
    foreach ($path in $artifactPaths) {
        Copy-ArtifactPath -SourceRoot $main -DestRoot $artifacts -RelativePath $path
    }
} else {
    Write-Host "PULL artifacts -> main"
    foreach ($path in $artifactPaths) {
        Copy-ArtifactPath -SourceRoot $artifacts -DestRoot $main -RelativePath $path
    }
}
