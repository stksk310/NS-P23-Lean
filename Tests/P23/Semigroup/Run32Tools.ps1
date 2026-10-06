$ErrorActionPreference='Stop'
$root=(Resolve-Path (Join-Path $PSScriptRoot '..\..\..')).Path
. (Join-Path $root 'P23/Run32/tools.ps1')
function MustReject([scriptblock]$action,[string]$label){
  $rejected=$false;try {& $action} catch {$rejected=$true}
  if(-not $rejected){throw "Negative control accepted: $label"}
  Write-Host "PASS negative: $label"
}
Test-Run32Frozen
$list=Join-Path $root 'Tests/P23/Semigroup/AxiomCheckRun32.lean'
$names=@(Get-Content $list|Where-Object {$_ -match '^#print axioms '}|ForEach-Object {$_ -replace '^#print axioms\s+',''})
$public=@(Get-Run32PublicTheorems)
if(@(Compare-Object $public $names).Count){throw 'Exact public axiom inventory failed'}
$valid=($names|ForEach-Object {"'$_' depends on axioms: [propext, Classical.choice, Quot.sound]"}) -join "`n"
Test-Run32AxiomOutput $list $valid
MustReject {Test-Run32AxiomOutput $list ($valid -replace [regex]::Escape("'$($names[0])' depends on axioms: [propext, Classical.choice, Quot.sound]"),'')} 'missing public axiom report'
MustReject {Test-Run32AxiomOutput $list ($valid+"`n'$($names[0])' depends on axioms: []")} 'duplicate public axiom report'
MustReject {Test-Run32AxiomOutput $list ($valid.Replace('propext','projectBadAxiom'))} 'unexpected axiom dependency'
$relative=Join-Path $root 'P23/Run32/AXIOM_RELATIVE_REQUESTS.fixture'
$relativeText="'P23.Semigroup.FourGeneratedNumericalSemigroup.mem_Gamma_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`n'P23.Semigroup.semigroupToAperyAlg_ker' depends on axioms: [propext, Classical.choice, Quot.sound]"
Test-Run32AxiomOutput $relative $relativeText
MustReject {Test-Run32AxiomOutput $relative ($relativeText.Replace('P23.Semigroup.semigroupToAperyAlg_ker','Wrong.Namespace.semigroupToAperyAlg_ker'))} 'unopened namespace cannot spoof relative axiom name'
$old=Join-Path $root 'NS_P23_LEAN_RUN31_RHO4_STRUCTURAL_REDUCTION_RESULT_20261004.zip'
$hash=Get-Run32Hash $old
MustReject {Assert-Run32NewResultPath $old} 'existing result overwrite'
if((Get-Run32Hash $old) -cne $hash){throw 'Existing result changed'}
$scratch=Join-Path ([IO.Path]::GetTempPath()) ('p23-run32-unit-'+[Guid]::NewGuid().ToString('N'))
New-Item -ItemType Directory $scratch|Out-Null
try {
  $manifest=Join-Path $scratch 'SHA256SUMS'
  $one='lean-toolchain';$line=(Get-Run32Hash (Join-Path $root $one))+'  '+$one
  [IO.File]::WriteAllLines($manifest,@($line))
  Test-Run32Manifest $manifest @($one)
  MustReject {Test-Run32Manifest $manifest @($one,'lakefile.toml')} 'manifest missing target'
  [IO.File]::WriteAllLines($manifest,@($line,$line))
  MustReject {Test-Run32Manifest $manifest @($one)} 'manifest duplicate target'
  [IO.File]::WriteAllLines($manifest,@(('0'*64)+'  '+$one))
  MustReject {Test-Run32Manifest $manifest @($one)} 'manifest wrong bytes'
} finally {
  $checked=(Resolve-Path -LiteralPath $scratch).Path
  $prefix=[IO.Path]::GetFullPath([IO.Path]::GetTempPath()).TrimEnd('\')+'\'
  if(-not $checked.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or (Split-Path -Leaf $checked) -notmatch '^p23-run32-unit-[a-f0-9]{32}$'){throw 'Unsafe unit temporary cleanup'}
  Remove-Item -LiteralPath $checked -Recurse
}
foreach($file in @('package.ps1','audit-package.ps1')){
  if(-not (Get-Content -Raw (Join-Path $root "P23/Run32/$file")).Contains('NS_P23_LEAN_RUN32_RHO4_LOCAL_THREE_BORDER_RESULT_20261004.zip')){throw 'Wrong Run32 result filename'}
}
Write-Host "PASS Run32 tool units: public=$($public.Count), accepted frozen88, manifest negatives, overwrite protection"
