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



# Independent test-only normalization. No production proof reads this script.
function Normalize([int[]]$v,[int]$a,[int]$b,[int]$c) {
  $turn=[int][Math]::Floor($v[0]/$a)
  return [int[]]@(($v[0]%$a),($v[1]+$turn*$b),($v[2]+$turn*$c))
}
function Key([int[]]$v){ return ($v -join ',') }
$fixtures=@([int[]]@(4,5,6,7),[int[]]@(5,6,7,8),[int[]]@(5,7,8,9),
  [int[]]@(6,7,9,10),[int[]]@(7,8,9,11),[int[]]@(7,9,10,12),
  [int[]]@(6,8,9,11),[int[]]@(8,10,11,13))
$cases=0;$mixed=0;$pure=0;$nonprimitive=0;$negativeOrientations=0
foreach($n in $fixtures){
  $fibers=@{};$parts=@{};$sg=[bool[]]::new($MaxDegree+1);$rho=0
  for($d=0;$d -le $MaxDegree;$d++){
    $f=@(Get-Factorizations $n $d);$fibers[$d]=$f;$sg[$d]=$f.Count -gt 0
    if($f.Count -gt 1){$cs=@(Get-Components $f);if($cs.Count -gt 1){$parts[$d]=$cs;$rho+=$cs.Count-1}}
  }
  foreach($d in (($MaxDegree-($n|Measure-Object -Maximum).Maximum+1)..$MaxDegree)){
    if(-not $sg[$d]){throw 'degree cap has not passed conductor'}
  }
  for($i=0;$i -lt 4;$i++){
    $internal=[Collections.Generic.List[object]]::new()
    $external=[Collections.Generic.List[object]]::new()
    $tails=@(0..3|Where-Object {$_ -ne $i})
    foreach($d in @($parts.Keys|Sort-Object)){
      $f=$fibers[$d];$cs=$parts[$d]
      $using=@(0..($f.Count-1)|Where-Object {$f[$_][$i] -gt 0})
      if($using.Count -eq 0){$root=0;$rf=$cs[0][0]}
      else {
        $root=@(0..($cs.Count-1)|Where-Object {@($cs[$_]|Where-Object {$f[$_][$i] -gt 0}).Count -gt 0})[0]
        $rf=$using[0]
      }
      for($j=0;$j -lt $cs.Count;$j++){
        if($j -eq $root){continue}
        $tf=$cs[$j][0]
        $v=[int[]]@($tails|ForEach-Object {$f[$tf][$_]})
        if($using.Count -eq 0){
          $u=[int[]]@($tails|ForEach-Object {$f[$rf][$_]})
          $internal.Add(@{u=$u;v=$v;degree=$d})
        }else{$external.Add($v)}
      }
    }
    if($internal.Count -ne 1){continue}
    $u=$internal[0].u;$v=$internal[0].v
    $su=@(0..2|Where-Object {$u[$_] -gt 0});$sv=@(0..2|Where-Object {$v[$_] -gt 0})
    if($su.Count -ne 1){$tmp=$u;$u=$v;$v=$tmp;$su=$sv;$negativeOrientations++}
    if($su.Count -ne 1){throw 'no singleton tie side'}
    $x=$su[0];$y=@(0..2|Where-Object {$v[$_] -gt 0})[0]
    $z=@(0..2|Where-Object {$_ -ne $x -and $_ -ne $y})[0]
    $perm=@($x,$y,$z);$a=$u[$x];$b=$v[$y];$c=$v[$z]
    if($a -lt 2 -or $b -lt 1 -or ($c -eq 0 -and $b -lt 2)){throw 'bad live domain'}
    if($c -eq 0){$pure++}else{$mixed++}
    if($a%2 -eq 0 -and $b%2 -eq 0 -and $c%2 -eq 0){$nonprimitive++}
    $weights=[int[]]@($perm|ForEach-Object {$n[$tails[$_]]})
    $normGenerators=[Collections.Generic.HashSet[string]]::new()
    foreach($v0 in $external){
      $ren=[int[]]@($perm|ForEach-Object {$v0[$_]})
      $key=Key (Normalize $ren $a $b $c)
      if(-not $normGenerators.Add($key)){throw 'normalization collision'}
      if($key -eq '0,0,0'){throw 'unit generator'}
    }
    if($normGenerators.Count -ne $rho-1){throw 'incorrect normalized cardinality'}
    $survivors=[Collections.Generic.Dictionary[string,object]]::new()
    $universe=[Collections.Generic.Dictionary[string,object]]::new()
    for($d=0;$d -le $MaxDegree;$d++){
      $ap=$sg[$d] -and ($d -lt $n[$i] -or -not $sg[$d-$n[$i]])
      foreach($f in $fibers[$d]){
        if($f[$i] -ne 0){continue}
        $v0=[int[]]@($perm|ForEach-Object {$f[$tails[$_]]})
        $q=Normalize $v0 $a $b $c;$key=Key $q
        $universe[$key]=$q
        if($ap){$survivors[$key]=$q}
      }
    }
    foreach($key in @('0,0,0','1,0,0','0,1,0','0,0,1',"0,$b,$c")){
      if(-not $survivors.ContainsKey($key)){throw "required survivor missing $key"}
    }
    if($survivors.Count -ne $n[$i]){throw 'Apéry cardinal mismatch'}
    $candidates=[Collections.Generic.Dictionary[string,object]]::new()
    $roots=[Collections.Generic.List[string]]::new()
    foreach($q in $survivors.Values){
      $isRoot=$true
      for($j=0;$j -lt 3;$j++){
        $q1=[int[]]$q.Clone();$q1[$j]++;$g=Normalize $q1 $a $b $c;$key=Key $g
        if($survivors.ContainsKey($key)){$isRoot=$false}else{$candidates[$key]=$g}
      }
      if($isRoot){$roots.Add((Key $q))}
    }
    $border=[Collections.Generic.HashSet[string]]::new()
    foreach($g in $candidates.Values){
      $minimal=$true
      for($j=0;$j -lt 3;$j++){
        foreach($q in $universe.Values){
          $v0=[int[]]$q.Clone();$v0[$j]++
          if((Key (Normalize $v0 $a $b $c)) -eq (Key $g) -and -not $survivors.ContainsKey((Key $q))){
            $minimal=$false;break
          }
        }
      }
      if($minimal){$null=$border.Add((Key $g))}
    }
    if(-not $border.SetEquals($normGenerators)){throw "exact border mismatch <$($n -join ',')> base=$($n[$i])"}
    $cases++
    Write-Host "B=1 <$($n -join ',')> base=$($n[$i]): tie=($a,$b,$c) rho=$rho roots=$($roots.Count) border=$($border.Count)"
  }
}
if($cases -lt 3 -or $mixed -eq 0 -or $pure -eq 0){throw 'missing required mixed/pure B=1 coverage'}
Write-Host "PASS Run28 concrete: cases=$cases mixed=$mixed pure=$pure nonprimitive=$nonprimitive reversed=$negativeOrientations maxDegree=$MaxDegree"

