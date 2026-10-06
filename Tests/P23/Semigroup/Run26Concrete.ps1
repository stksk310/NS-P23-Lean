param([int]$MaxDegree = 120)

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


# Non-load-bearing exploration; no production theorem imports this script.
$fixtures = @([int[]]@(4,5,6,7), [int[]]@(5,6,7,8), [int[]]@(5,7,8,9),
  [int[]]@(6,7,9,10), [int[]]@(7,8,9,11), [int[]]@(7,9,10,12))
$tags=0; $internal=0; $external=0; $three=0; $mixedRepresentatives=0
$budgets=[Collections.Generic.HashSet[int]]::new()
foreach($n in $fixtures) {
  $b=[int[]]@(0,0,0,0); $rho=0; $intTags=[int[]]@(0,0,0,0)
  for($d=1;$d -le $MaxDegree;$d++){
    $f=@(Get-Factorizations $n $d); if($f.Count -lt 2){continue}
    $parts=@(Get-Components $f); if($parts.Count -lt 2){continue}
    $rho+=$parts.Count-1
    if($parts.Count -ge 3){$three++}
    for($i=0;$i -lt 4;$i++){
      $using=@(0..($f.Count-1) | Where-Object {$f[$_][$i] -gt 0})
      $isInternal=$using.Count -eq 0; $root=0; $rootFactor=$parts[0][0]
      if(-not $isInternal){
        $roots=@(0..($parts.Count-1) | Where-Object {
          @($parts[$_] | Where-Object {$f[$_][$i] -gt 0}).Count -gt 0 })
        if($roots.Count -ne 1){throw 'base support component not unique'}
        $root=$roots[0]; $rootFactor=$using[0]
        if($parts[$root] -notcontains $rootFactor){throw 'witness outside root component'}
        $free=@($parts[$root] | Where-Object {$f[$_][$i] -eq 0})
        if($free.Count -gt 0){$mixedRepresentatives++}
      } else {
        $b[$i]+=$parts.Count-1
        $r=$d-$n[$i]
        if($r -ge 0 -and @(Get-Factorizations $n $r).Count -gt 0){throw 'internal degree not Apery'}
      }
      $tails=@(0..3 | Where-Object {$_ -ne $i})
      $local=0
      for($c=0;$c -lt $parts.Count;$c++){
        if($c -eq $root){continue}
        $target=$parts[$c][0]; $local++; $tags++
        if($f[$target][$i] -ne 0){throw 'target uses base'}
        if(-not $isInternal){
          if($f[$rootFactor][$i] -le 0){throw 'external root does not use base'}
          $external++
        } else {
          $internal++; $intTags[$i]++
          $u=@($tails | ForEach-Object {$f[$rootFactor][$_]})
          $v=@($tails | ForEach-Object {$f[$target][$_]})
          $su=@(0..2 | Where-Object {$u[$_] -gt 0})
          $sv=@(0..2 | Where-Object {$v[$_] -gt 0})
          if($su.Count -eq 0 -or $sv.Count -eq 0){throw 'empty binomial support'}
          if(@($su | Where-Object {$sv -contains $_}).Count -gt 0){throw 'non-disjoint supports'}
          if($su.Count -ne 1 -and $sv.Count -ne 1){throw 'no pure side'}
          if(($u -join ',') -eq ($v -join ',')){throw 'zero binomial'}
          $du=0;$dv=0
          for($j=0;$j -lt 3;$j++){$du+=$u[$j]*$n[$tails[$j]];$dv+=$v[$j]*$n[$tails[$j]]}
          if($du -ne $d -or $dv -ne $d){throw 'term degree transport failed'}
        }
      }
      if($local -ne $parts.Count-1){throw 'incorrect star count'}
    }
  }
  for($i=0;$i -lt 4;$i++){
    if($intTags[$i] -ne $b[$i]){throw 'internal budget count mismatch'}
    if($rho-$intTags[$i] -lt 0){throw 'external count mismatch'}
    $null=$budgets.Add($b[$i])
  }
  Write-Host "fixture <$($n -join ',')>: rho=$rho B=[$($b -join ',')]"
}
if(-not $budgets.Contains(0) -or -not $budgets.Contains(1) -or -not @($budgets | Where-Object {$_ -gt 1}).Count){
 throw 'missing B=0/1/>1 controls'
}
if($three -eq 0 -or $mixedRepresentatives -eq 0){throw 'missing multi-component or base-free-root-representative control'}
Write-Host "PASS Run26 concrete: fixtures=$($fixtures.Count) bases=$($fixtures.Count*4) tags=$tags internal=$internal external=$external threeComponent=$three mixedBaseRepresentatives=$mixedRepresentatives maxDegree=$MaxDegree"
