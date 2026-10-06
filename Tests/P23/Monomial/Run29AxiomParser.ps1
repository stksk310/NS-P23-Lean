$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot '..\..\..\P23\Run29\axiom-report-parser.ps1')
$fixture = @"
'Example.ordinary' depends on axioms: [propext]
'Example.primed'' depends on axioms: [propext,
 Classical.choice, Quot.sound]
'Example.noAxioms' does not depend on any axioms
"@
$reports = @(Get-Run29AxiomReports $fixture)
if ($reports.Count -ne 3) { throw 'Expected three complete axiom reports, including primed declaration' }
$names = @($reports | ForEach-Object { $_.Groups[1].Value })
if ($names[0] -cne 'Example.ordinary' -or $names[1] -cne "Example.primed'" -or
    $names[2] -cne 'Example.noAxioms') { throw 'Axiom parser truncated or altered declaration names' }
Write-Host 'PASS Run29 axiom parser: primed names, multiline dependencies, no-axiom form'
