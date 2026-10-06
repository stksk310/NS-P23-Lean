param([int]$MaxDegree = 80)

$ErrorActionPreference = 'Stop'

function Get-Factorizations([int[]]$Generators, [int]$Degree) {
  $out = [System.Collections.Generic.List[object]]::new()
  for ($a = 0; $a * $Generators[0] -le $Degree; $a++) {
    for ($b = 0; $a * $Generators[0] + $b * $Generators[1] -le $Degree; $b++) {
      for ($c = 0; $a * $Generators[0] + $b * $Generators[1] + $c * $Generators[2] -le $Degree; $c++) {
        $used = $a * $Generators[0] + $b * $Generators[1] + $c * $Generators[2]
        $rest = $Degree - $used
        if ($rest -ge 0 -and $rest % $Generators[3] -eq 0) {
          $out.Add([pscustomobject]@{ E = [int[]]@($a, $b, $c, [int]($rest / $Generators[3])) })
        }
      }
    }
  }
  return $out.ToArray()
}

function Get-Components([object[]]$Factorizations) {
  $seen = [System.Collections.Generic.HashSet[int]]::new()
  $components = [System.Collections.Generic.List[object]]::new()
  for ($start = 0; $start -lt $Factorizations.Count; $start++) {
    if ($seen.Contains($start)) { continue }
    $queue = [System.Collections.Generic.Queue[int]]::new()
    $component = [System.Collections.Generic.List[int]]::new()
    $queue.Enqueue($start)
    $null = $seen.Add($start)
    while ($queue.Count -gt 0) {
      $u = $queue.Dequeue()
      $component.Add($u)
      for ($v = 0; $v -lt $Factorizations.Count; $v++) {
        if ($seen.Contains($v)) { continue }
        $overlap = $false
        for ($j = 0; $j -lt 4; $j++) {
          if ($Factorizations[$u].E[$j] -gt 0 -and $Factorizations[$v].E[$j] -gt 0) {
            $overlap = $true
          }
        }
        if ($overlap) {
          $null = $seen.Add($v)
          $queue.Enqueue($v)
        }
      }
    }
    $components.Add([pscustomobject]@{ Indices = [int[]]$component.ToArray() })
  }
  return $components.ToArray()
}

$fixtures = @(
  [int[]]@(4,5,6,7),
  [int[]]@(5,6,7,8),
  [int[]]@(5,7,8,9),
  [int[]]@(6,7,9,10),
  [int[]]@(7,8,9,11)
)

$totalBetti = 0
$totalChecks = 0
$partitionNames = [System.Collections.Generic.HashSet[string]]::new()
foreach ($generators in $fixtures) {
  $budget = @(0,0,0,0)
  $singletonDegree = @{}
  $bettiCount = 0
  for ($d = 1; $d -le $MaxDegree; $d++) {
    $factors = @(Get-Factorizations $generators $d)
    if ($factors.Count -lt 2) { continue }
    $components = @(Get-Components $factors)
    if ($components.Count -lt 2) { continue }
    $bettiCount++
    $totalBetti++
    $supports = @()
    foreach ($component in $components) {
      $support = [System.Collections.Generic.HashSet[int]]::new()
      foreach ($index in $component.Indices) {
        for ($j = 0; $j -lt 4; $j++) {
          if ($factors[$index].E[$j] -gt 0) { $null = $support.Add($j) }
        }
      }
      $supports += ,$support
    }
    for ($x = 0; $x -lt $supports.Count; $x++) {
      for ($y = $x + 1; $y -lt $supports.Count; $y++) {
        foreach ($j in $supports[$x]) {
          if ($supports[$y].Contains($j)) { throw "component supports overlap" }
        }
      }
    }
    $combined = [System.Collections.Generic.HashSet[int]]::new()
    $ell = 0
    $partition = @()
    foreach ($support in $supports) {
      foreach ($j in $support) { $null = $combined.Add($j) }
      $partition += $support.Count
      if ($support.Count -eq 1) {
        $ell++
        $j = @($support)[0]
        if ($singletonDegree.ContainsKey($j) -and $singletonDegree[$j] -ne $d) {
          throw "singleton degree uniqueness failed"
        }
        $singletonDegree[$j] = $d
      }
    }
    $partition = @($partition | Sort-Object)
    $null = $partitionNames.Add(($partition -join '+'))
    $c = $components.Count
    $v = $combined.Count
    if ((4 - $v) * ($c - 1) -gt $ell) { throw "local support inequality failed" }
    for ($i = 0; $i -lt 4; $i++) {
      if (-not $combined.Contains($i)) { $budget[$i] += $c - 1 }
    }
    $totalChecks++
  }
  $sumBudget = ($budget | Measure-Object -Sum).Sum
  if ($sumBudget -gt 4) { throw "four-base budget failed" }
  Write-Host ("fixture <{0}>: Betti={1}, B=[{2}], sum={3}" -f
    ($generators -join ','), $bettiCount, ($budget -join ','), $sumBudget)
}

Write-Host ("partitions observed: {0}" -f ((@($partitionNames) | Sort-Object) -join ', '))
Write-Host "PASS: Run23 concrete exploration; fixtures=$($fixtures.Count), Betti=$totalBetti, checked=$totalChecks, maxDegree=$MaxDegree"
