param([int]$MaxDegree = 80)

$ErrorActionPreference = 'Stop'

function Get-Key([int[]]$u) { return ($u -join ',') }

function Get-Factorizations([int[]]$Generators, [int]$Degree) {
  $out = [System.Collections.Generic.List[object]]::new()
  for ($a = 0; $a * $Generators[0] -le $Degree; $a++) {
    for ($b = 0; $a * $Generators[0] + $b * $Generators[1] -le $Degree; $b++) {
      for ($c = 0; $a * $Generators[0] + $b * $Generators[1] + $c * $Generators[2] -le $Degree; $c++) {
        $used = $a * $Generators[0] + $b * $Generators[1] + $c * $Generators[2]
        $rest = $Degree - $used
        if ($rest -ge 0 -and $rest % $Generators[3] -eq 0) {
          $out.Add([int[]]@($a,$b,$c,[int]($rest / $Generators[3])))
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

function Get-Rank([object[]]$Columns, [int]$Rows, [int]$Prime) {
  if ($Columns.Count -eq 0) { return 0 }
  $m = New-Object 'int[,]' $Rows,$Columns.Count
  for ($c = 0; $c -lt $Columns.Count; $c++) {
    for ($r = 0; $r -lt $Rows; $r++) {
      $m[$r,$c] = (($Columns[$c][$r] % $Prime) + $Prime) % $Prime
    }
  }
  $rank = 0
  for ($c = 0; $c -lt $Columns.Count -and $rank -lt $Rows; $c++) {
    $pivot = $rank
    while ($pivot -lt $Rows -and $m[$pivot,$c] -eq 0) { $pivot++ }
    if ($pivot -eq $Rows) { continue }
    for ($j = $c; $j -lt $Columns.Count; $j++) {
      $tmp=$m[$rank,$j]; $m[$rank,$j]=$m[$pivot,$j]; $m[$pivot,$j]=$tmp
    }
    $inv = if ($Prime -eq 2 -or $m[$rank,$c] -eq 1) { 1 } else { 2 }
    for ($j = $c; $j -lt $Columns.Count; $j++) { $m[$rank,$j]=($m[$rank,$j]*$inv)%$Prime }
    for ($r = 0; $r -lt $Rows; $r++) {
      if ($r -eq $rank) { continue }
      $factor=$m[$r,$c]
      for ($j = $c; $j -lt $Columns.Count; $j++) {
        $m[$r,$j]=(($m[$r,$j]-$factor*$m[$rank,$j])%$Prime+$Prime)%$Prime
      }
    }
    $rank++
  }
  return $rank
}

$fixtures=@(
  [int[]]@(4,5,6,7), [int[]]@(5,6,7,8), [int[]]@(5,7,8,9),
  [int[]]@(6,7,9,10), [int[]]@(7,8,9,11)
)
$betti=0; $comparisons=0; $lowerColumns=0; $twoComponent=0; $threeComponent=0
foreach($generators in $fixtures) {
  $cache=@{}
  for($d=0;$d -le $MaxDegree;$d++){$cache[$d]=@(Get-Factorizations $generators $d)}
  for($d=1;$d -le $MaxDegree;$d++) {
    $factors=@($cache[$d]); if($factors.Count -lt 2){continue}
    $components=@(Get-Components $factors); if($components.Count -lt 2){continue}
    $betti++
    if($components.Count -eq 2){$twoComponent++}
    if($components.Count -eq 3){$threeComponent++}
    $index=@{}; $componentOf=@{}
    for($i=0;$i -lt $factors.Count;$i++){$index[(Get-Key $factors[$i])]=$i}
    for($c=0;$c -lt $components.Count;$c++){foreach($i in $components[$c]){$componentOf[$i]=$c}}
    $columns=[System.Collections.Generic.List[object]]::new()
    $seenColumns=[System.Collections.Generic.HashSet[string]]::new()
    for($e=0;$e -lt $d;$e++) {
      $low=@($cache[$e]); if($low.Count -lt 2){continue}
      $shifts=@($cache[$d-$e]); if($shifts.Count -eq 0){continue}
      for($i=0;$i -lt $low.Count;$i++) {
        for($j=$i+1;$j -lt $low.Count;$j++) {
          foreach($w in $shifts) {
            $left=[int[]]::new(4); $right=[int[]]::new(4)
            for($t=0;$t -lt 4;$t++){$left[$t]=$low[$i][$t]+$w[$t];$right[$t]=$low[$j][$t]+$w[$t]}
            $li=$index[(Get-Key $left)]; $ri=$index[(Get-Key $right)]
            if($componentOf[$li] -ne $componentOf[$ri]){throw 'lower multiple crossed components'}
            $key="$li,$ri"; if(-not $seenColumns.Add($key)){continue}
            $col=[int[]]::new($factors.Count); $col[$li]=1; $col[$ri]=-1
            $columns.Add($col); $lowerColumns++
          }
        }
      }
    }
    $target=$factors.Count-$components.Count
    foreach($prime in @(2,3)) {
      $rank=Get-Rank $columns.ToArray() $factors.Count $prime
      if($rank -ne $target){throw "actual lower rank mismatch: generators=$generators d=$d GF($prime) rank=$rank target=$target"}
      $comparisons++
    }
  }
}

if($twoComponent -eq 0 -or $threeComponent -eq 0){throw 'missing required concrete two-/three-component Betti fibers'}

Write-Host "PASS: Run24R actual-lower matrix regression; fixtures=$($fixtures.Count), Betti=$betti, twoComponent=$twoComponent, threeComponent=$threeComponent, comparisons=$comparisons, lowerColumns=$lowerColumns, maxDegree=$MaxDegree"
