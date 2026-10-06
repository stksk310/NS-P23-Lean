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
          $out.Add([int[]]@($a, $b, $c, [int]($rest / $Generators[3])))
        }
      }
    }
  }
  return $out.ToArray()
}

function Get-Components([object[]]$Factors) {
  $seen = [System.Collections.Generic.HashSet[int]]::new()
  $out = [System.Collections.Generic.List[object]]::new()
  for ($start = 0; $start -lt $Factors.Count; $start++) {
    if ($seen.Contains($start)) { continue }
    $queue = [System.Collections.Generic.Queue[int]]::new()
    $part = [System.Collections.Generic.List[int]]::new()
    $queue.Enqueue($start); $null = $seen.Add($start)
    while ($queue.Count -gt 0) {
      $u = $queue.Dequeue(); $part.Add($u)
      for ($v = 0; $v -lt $Factors.Count; $v++) {
        if ($seen.Contains($v)) { continue }
        $adj = $false
        for ($j = 0; $j -lt 4; $j++) {
          if ($Factors[$u][$j] -gt 0 -and $Factors[$v][$j] -gt 0) { $adj = $true }
        }
        if ($adj) { $null = $seen.Add($v); $queue.Enqueue($v) }
      }
    }
    $out.Add([int[]]$part.ToArray())
  }
  return $out.ToArray()
}

function Get-Rank([int[][]]$Columns, [int]$Rows, [int]$Prime) {
  if ($Columns.Count -eq 0) { return 0 }
  $m = New-Object 'int[,]' $Rows,$Columns.Count
  for ($c = 0; $c -lt $Columns.Count; $c++) {
    for ($r = 0; $r -lt $Rows; $r++) { $m[$r,$c] = (($Columns[$c][$r] % $Prime) + $Prime) % $Prime }
  }
  $rank = 0
  for ($c = 0; $c -lt $Columns.Count -and $rank -lt $Rows; $c++) {
    $pivot = $rank
    while ($pivot -lt $Rows -and $m[$pivot,$c] -eq 0) { $pivot++ }
    if ($pivot -eq $Rows) { continue }
    for ($j = $c; $j -lt $Columns.Count; $j++) {
      $tmp = $m[$rank,$j]; $m[$rank,$j] = $m[$pivot,$j]; $m[$pivot,$j] = $tmp
    }
    $inv = if ($Prime -eq 2 -or $m[$rank,$c] -eq 1) { 1 } else { 2 }
    for ($j = $c; $j -lt $Columns.Count; $j++) { $m[$rank,$j] = ($m[$rank,$j] * $inv) % $Prime }
    for ($r = 0; $r -lt $Rows; $r++) {
      if ($r -eq $rank) { continue }
      $factor = $m[$r,$c]
      for ($j = $c; $j -lt $Columns.Count; $j++) {
        $m[$r,$j] = (($m[$r,$j] - $factor * $m[$rank,$j]) % $Prime + $Prime) % $Prime
      }
    }
    $rank++
  }
  return $rank
}

$fixtures = @(
  [int[]]@(4,5,6,7), [int[]]@(5,6,7,8), [int[]]@(5,7,8,9),
  [int[]]@(6,7,9,10), [int[]]@(7,8,9,11)
)
$betti = 0; $rankChecks = 0; $edgeChecks = 0
foreach ($generators in $fixtures) {
  for ($d = 1; $d -le $MaxDegree; $d++) {
    $factors = @(Get-Factorizations $generators $d)
    if ($factors.Count -lt 2) { continue }
    $components = @(Get-Components $factors)
    if ($components.Count -lt 2) { continue }
    $betti++
    $componentOf = @{}
    for ($c = 0; $c -lt $components.Count; $c++) {
      foreach ($u in $components[$c]) { $componentOf[$u] = $c }
    }
    for ($u = 0; $u -lt $factors.Count; $u++) {
      for ($v = $u + 1; $v -lt $factors.Count; $v++) {
        $overlap = $false
        for ($j = 0; $j -lt 4; $j++) {
          if ($factors[$u][$j] -gt 0 -and $factors[$v][$j] -gt 0) { $overlap = $true }
        }
        if ($overlap) {
          $edgeChecks++
          if ($componentOf[$u] -ne $componentOf[$v]) { throw 'overlap edge survived component quotient' }
        }
      }
    }
    $columns = [System.Collections.Generic.List[int[]]]::new()
    for ($c = 1; $c -lt $components.Count; $c++) {
      $column = [int[]]::new($components.Count)
      $column[0] = 1; $column[$c] = -1
      $columns.Add($column)
    }
    foreach ($prime in @(2,3)) {
      $rank = Get-Rank $columns.ToArray() $components.Count $prime
      if ($rank -ne $components.Count - 1) { throw "connector rank mismatch in GF($prime)" }
      $rankChecks++
    }
  }
}

Write-Host "PASS: Run24 concrete matrix exploration; fixtures=$($fixtures.Count), Betti=$betti, rankChecks=$rankChecks, overlapEdges=$edgeChecks, maxDegree=$MaxDegree"
