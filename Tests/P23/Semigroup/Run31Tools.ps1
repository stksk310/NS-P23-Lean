$ErrorActionPreference='Stop'
$root=(Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
$expected='NS_P23_LEAN_RUN31_RHO4_STRUCTURAL_REDUCTION_RESULT_20261004.zip'
foreach($name in @('package.ps1','audit-package.ps1')) {
  $source=Get-Content -Raw -LiteralPath (Join-Path $root "P23\Run31\$name")
  if(-not $source.Contains($expected)){throw "Run31 result filename contract failed: $name"}
  if($source.Contains('NS_P23_LEAN_RUN30_RHO4_STRUCTURAL_REDUCTION')){throw 'Stale RUN30 filename prefix'}
}
$frozen=@(Get-Content -LiteralPath (Join-Path $root 'P23\Run31\FROZEN_SHA256SUMS'))
if($frozen.Count -ne 84){throw 'Frozen table count contract failed'}
$crcSource=Get-Content -Raw -LiteralPath (Join-Path $root 'P23\Run31\audit-package.ps1')
$crcDefinition=[regex]::Match($crcSource,"(?s)Add-Type -TypeDefinition @'\r?\n(.*?)\r?\n'@")
if(-not $crcDefinition.Success){throw 'Missing actual archive CRC implementation'}
if(-not ('P23Run31Crc32' -as [type])){Add-Type -TypeDefinition $crcDefinition.Groups[1].Value}
if([P23Run31Crc32]::Compute([byte[]]@()) -ne 0){throw 'Empty CRC known vector failed'}
$crcVector=[Text.Encoding]::ASCII.GetBytes('123456789')
if([P23Run31Crc32]::Compute($crcVector).ToString('x8') -cne 'cbf43926'){
  throw 'CRC known-vector mismatch: actual archive implementation is not IEEE ZIP CRC32'
}
if([P23Run31Crc32]::Compute([Text.Encoding]::ASCII.GetBytes('123456788')).ToString('x8') -ceq 'cbf43926'){
  throw 'CRC changed-byte negative control failed'
}
Write-Host 'PASS actual archive CRC code: empty/123456789 known vectors and changed-byte negative control'
. (Join-Path $root 'P23\Run31\result-path-guard.ps1')
$prior=Join-Path $root 'NS_P23_LEAN_RUN30_RHO5_EXCLUSION_RESULT_20261003.zip'
if(-not (Test-Path -LiteralPath $prior)){$prior=Join-Path $root 'lakefile.toml'}
$before=(Get-FileHash -Algorithm SHA256 -LiteralPath $prior).Hash
$rejected=$false
try { Assert-Run31NewResultPath $prior } catch {
  if($_.Exception.Message -notmatch 'Preserving existing'){throw}; $rejected=$true
}
if(-not $rejected -or (Get-FileHash -Algorithm SHA256 -LiteralPath $prior).Hash -cne $before){throw 'Overwrite guard contract failed'}
$package=Get-Content -Raw -LiteralPath (Join-Path $root 'P23\Run31\package.ps1')
if($package.IndexOf('Assert-Run31NewResultPath') -lt 0 -or
    $package.IndexOf('Assert-Run31NewResultPath') -gt $package.IndexOf('[IO.File]::WriteAllLines')){throw 'Overwrite guard must precede packaging side effects'}
Write-Host 'PASS Run31 tools: exact result filename and 84-target frozen-table contracts'
Write-Host "PASS Run31 overwrite guard: existing $([IO.Path]::GetFileName($prior)) refused and SHA256 unchanged"
