#Requires -Version 5.1
<#
.SYNOPSIS
  One-time setup to register JaCoP as a MiniZinc solver backend.
.DESCRIPTION
  Idempotent script: checks if JaCoP is already registered and skips if so.
  - Copies JaCoP MiniZinc library files into MiniZinc's share directory
  - Creates the org.jacop.msc solver configuration
  - Creates fzn-jacop.bat wrapper script
  - Reads version from pom.xml to build correct classpath
.PARAMETER JacopRoot
  Root directory of the JaCoP repository. Defaults to 4 levels up from this script.
.PARAMETER MinizincHome
  MiniZinc installation directory. Auto-detected if not specified.
#>
param(
    [string]$JacopRoot,
    [string]$MinizincHome
)

$ErrorActionPreference = "Stop"

# --- Self-elevate if not running as admin (needed for C:\Program Files) ---
$currentPrincipal = New-Object Security.Principal.WindowsPrincipal([Security.Principal.WindowsIdentity]::GetCurrent())
if (-not $currentPrincipal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)) {
    Write-Host "Requesting admin privileges (needed to write to MiniZinc directory)..."
    $resolvedRoot = if ($JacopRoot) { $JacopRoot } else { (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\.." )).Path }
    $args = @("-ExecutionPolicy", "Bypass", "-File", "`"$PSCommandPath`"", "-JacopRoot", "`"$resolvedRoot`"")
    if ($MinizincHome) { $args += @("-MinizincHome", "`"$MinizincHome`"") }
    Start-Process powershell -Verb RunAs -ArgumentList ($args -join " ") -Wait
    exit $LASTEXITCODE
}

# --- Resolve JaCoP root ---
if (-not $JacopRoot) {
    $JacopRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..\.." )).Path
}
if (-not (Test-Path (Join-Path $JacopRoot "pom.xml"))) {
    Write-Error "Cannot find pom.xml in JaCoP root: $JacopRoot"
    exit 1
}

# --- Resolve MiniZinc home ---
if (-not $MinizincHome) {
    $candidates = @(
        "C:\Program Files\MiniZinc",
        "C:\Program Files (x86)\MiniZinc",
        "$env:LOCALAPPDATA\Programs\MiniZinc"
    )
    foreach ($c in $candidates) {
        if (Test-Path (Join-Path $c "minizinc.exe")) {
            $MinizincHome = $c
            break
        }
    }
    if (-not $MinizincHome) {
        $found = Get-Command minizinc -ErrorAction SilentlyContinue
        if ($found) {
            $MinizincHome = Split-Path $found.Source
        }
    }
}
if (-not $MinizincHome -or -not (Test-Path (Join-Path $MinizincHome "minizinc.exe"))) {
    Write-Error "MiniZinc not found. Install it or pass -MinizincHome."
    exit 1
}
Write-Host "MiniZinc home: $MinizincHome"

$minizincExe = Join-Path $MinizincHome "minizinc.exe"
$shareDir = Join-Path $MinizincHome "share\minizinc"
$solversDir = Join-Path $shareDir "solvers"
$jacopLibDir = Join-Path $shareDir "jacop"

# --- Read version from pom.xml ---
[xml]$pom = Get-Content (Join-Path $JacopRoot "pom.xml")
$ns = New-Object Xml.XmlNamespaceManager($pom.NameTable)
$ns.AddNamespace("m", "http://maven.apache.org/POM/4.0.0")
$revision = $pom.SelectSingleNode("//m:properties/m:revision", $ns).'#text'
if (-not $revision) {
    Write-Error "Could not read <revision> from pom.xml"
    exit 1
}
Write-Host "JaCoP version: $revision"

# --- Detect installed version (if any) to check for version change ---
$fznBat = Join-Path $MinizincHome "fzn-jacop.bat"
$mscFile = Join-Path $solversDir "org.jacop.msc"
$installedVersion = $null
if (Test-Path $mscFile) {
    $mscJson = Get-Content $mscFile -Raw | ConvertFrom-Json
    $installedVersion = $mscJson.version
}

$solverList = & $minizincExe --solvers 2>&1 | Out-String
$isRegistered = $solverList -match "org\.jacop"
$versionChanged = $installedVersion -and ($installedVersion -ne $revision)

if ($isRegistered -and -not $versionChanged) {
    Write-Host "JaCoP $revision is already registered as a MiniZinc solver. Nothing to do."
    exit 0
}

if ($versionChanged) {
    Write-Host "Version changed: $installedVersion -> $revision. Updating configuration..."
}

# --- Copy MiniZinc library files ---
$srcLib = Join-Path $JacopRoot "jacop-flatzinc\src\main\minizinc\org\jacop\minizinc"
if (-not (Test-Path $srcLib)) {
    Write-Error "JaCoP MiniZinc library not found at: $srcLib"
    exit 1
}

if (-not (Test-Path $jacopLibDir)) {
    Write-Host "Copying JaCoP MiniZinc library to $jacopLibDir ..."
    Copy-Item -Path $srcLib -Destination $jacopLibDir -Recurse -Force
    Write-Host "  Done. Copied library files."
} else {
    Write-Host "JaCoP library directory already exists at $jacopLibDir"
}

# --- Helper: build fzn-jacop.bat content for a given version ---
function Build-FznBatContent {
    param([string]$Version)
    $modules = @("jacop-core", "jacop-floats", "jacop-sets", "jacop-sat", "jacop-flatzinc")
    $cpParts = @()
    foreach ($mod in $modules) {
        $cpParts += "`"$JacopRoot\$mod\target\$mod-$Version.jar`""
    }
    $depDir = Join-Path $JacopRoot "jacop-flatzinc\target\dependency"
    if (Test-Path $depDir) {
        $cpParts += "`"$depDir\*`""
    } else {
        $m2 = Join-Path $env:USERPROFILE ".m2\repository"
        $slf4jApi = Get-ChildItem "$m2\org\slf4j\slf4j-api" -Recurse -Filter "slf4j-api-*.jar" -ErrorAction SilentlyContinue | Select-Object -First 1
        $slf4jSimple = Get-ChildItem "$m2\org\slf4j\slf4j-simple" -Recurse -Filter "slf4j-simple-*.jar" -ErrorAction SilentlyContinue | Select-Object -First 1
        $lombok = Get-ChildItem "$m2\org\projectlombok\lombok" -Recurse -Filter "lombok-*.jar" -ErrorAction SilentlyContinue | Select-Object -First 1
        if ($slf4jApi) { $cpParts += "`"$($slf4jApi.FullName)`"" }
        if ($slf4jSimple) { $cpParts += "`"$($slf4jSimple.FullName)`"" }
        if ($lombok) { $cpParts += "`"$($lombok.FullName)`"" }
    }
    $classpath = $cpParts -join ";"
    return "@echo off`r`njava -XX:+UseSerialGC -server -Xmx8G -Xss100M -cp $classpath org.jacop.fz.Fz2jacop %*"
}

# --- Helper: build org.jacop.msc content for a given version ---
function Build-MscContent {
    param([string]$Version)
    return @"
{
    "id": "org.jacop",
    "name": "JaCoP",
    "description": "JaCoP FlatZinc solver",
    "mznlib": "$($jacopLibDir -replace '\\', '/')",
    "executable": "$($fznBat -replace '\\', '/')",
    "isGUIApplication": false,
    "mznlibVersion": 1,
    "needsMznExecutable": false,
    "needsPathsFile": false,
    "needsSolns2Out": true,
    "needsStdlibDir": false,
    "supportsFzn": true,
    "supportsMzn": false,
    "version": "$Version",
    "tags": ["cp", "int", "float", "set", "restart"],
    "stdFlags": ["-a", "-n", "-s", "-t", "-v", "-f", "-r"],
    "extraFlags": [
        ["-b", "Use bounds consistency whenever possible.", "bool", "false"],
        ["-cs", "Complementary search.", "bool", "false"],
        ["--precision", "Precision for floating operations.", "float", "1e-11"],
        ["-sat", "Use SAT solver for boolean constraints.", "bool", "false"],
        ["--decay", "Decay factor for AFC/activity heuristic.", "float", "0.99"],
        ["--restart", "Restart search type.", "opt:none:constant:linear:luby:geometric", "none"]
    ]
}
"@
}

# --- Create or update fzn-jacop.bat ---
$needsBat = (-not (Test-Path $fznBat)) -or $versionChanged
if ($needsBat) {
    $action = if (Test-Path $fznBat) { "Updating" } else { "Creating" }
    Write-Host "$action $fznBat ..."
    $batContent = Build-FznBatContent -Version $revision
    Set-Content -Path $fznBat -Value $batContent -Encoding ASCII
    Write-Host "  Done."
} else {
    Write-Host "fzn-jacop.bat already up to date at $fznBat"
}

# --- Create or update org.jacop.msc ---
$needsMsc = (-not (Test-Path $mscFile)) -or $versionChanged
if ($needsMsc) {
    $action = if (Test-Path $mscFile) { "Updating" } else { "Creating" }
    Write-Host "$action $mscFile ..."
    $mscContent = Build-MscContent -Version $revision
    [System.IO.File]::WriteAllText($mscFile, $mscContent, (New-Object System.Text.UTF8Encoding $false))
    Write-Host "  Done."
} else {
    Write-Host "org.jacop.msc already up to date at $mscFile"
}

# --- Verify registration ---
Write-Host ""
Write-Host "Verifying JaCoP registration..."
$verify = & $minizincExe --solvers 2>&1 | Out-String
if ($verify -match "org\.jacop") {
    Write-Host "SUCCESS: JaCoP is now registered as a MiniZinc solver."
} else {
    Write-Warning "JaCoP not found in solver list. Check the .msc file and paths."
    Write-Host $verify
    exit 1
}
