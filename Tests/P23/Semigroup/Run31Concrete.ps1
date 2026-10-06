$ErrorActionPreference='Stop'
# Audit-only bounded controls. No production theorem imports these computations.
function Reachable([int[]]$gens,[int]$limit) {
  $set=[Collections.Generic.HashSet[int]]::new(); [void]$set.Add(0)
  for($h=1;$h -le $limit;$h++) {
    foreach($g in $gens) { if($h -ge $g -and $set.Contains($h-$g)) { [void]$set.Add($h); break } }
  }
  return ,$set
}
function Run31Factors([int[]]$gens,[int]$degree) {
  $out=[Collections.Generic.List[object]]::new()
  function Visit([int]$j,[int]$left,[int[]]$u) {
    if($j -eq $gens.Count-1){
      if($left % $gens[$j] -eq 0){$u[$j]=[int]($left/$gens[$j]);$out.Add([pscustomobject]@{E=$u.Clone()})}
      return
    }
    for($a=0;$a*$gens[$j] -le $left;$a++){$u[$j]=$a;Visit ($j+1) ($left-$a*$gens[$j]) $u}
  }
  Visit 0 $degree ([int[]]::new($gens.Count))
  return $out.ToArray()
}
function Run31Components([object[]]$factors) {
  $seen=[Collections.Generic.HashSet[int]]::new();$out=[Collections.Generic.List[object]]::new()
  for($s=0;$s -lt $factors.Count;$s++){
    if($seen.Contains($s)){continue}
    $queue=[Collections.Generic.Queue[int]]::new();$queue.Enqueue($s);[void]$seen.Add($s)
    $support=[Collections.Generic.HashSet[int]]::new()
    while($queue.Count){
      $u=$queue.Dequeue()
      for($j=0;$j -lt 4;$j++){if($factors[$u].E[$j] -gt 0){[void]$support.Add($j)}}
      for($v=0;$v -lt $factors.Count;$v++){
        if($seen.Contains($v)){continue}
        $overlap=$false
        for($j=0;$j -lt 4;$j++){if($factors[$u].E[$j] -gt 0 -and $factors[$v].E[$j] -gt 0){$overlap=$true}}
        if($overlap){[void]$seen.Add($v);$queue.Enqueue($v)}
      }
    }
    $out.Add([pscustomobject]@{Support=$support})
  }
  return $out.ToArray()
}
$fixtures=@(@(4,5,6,7),@(5,6,7,8),@(5,7,8,9),@(6,7,9,10),@(7,8,9,11),@(7,9,10,12))
$expectedPF=@(@(1,2,3),@(9),@(11),@(3,8,11),@(10,12,13),@(11,13,15))
$expectedNG=@($true,$true,$true,$true,$false,$false)
$expectedRho=@(6,5,5,6,4,6)
$expectedBudgets=@(@(0,0,0,1),@(1,1,1,1),@(1,1,1,1),@(0,1,1,2),@(0,1,1,1),@(0,1,1,1))
$classified=0;$rhoFourBases=0;$rhoFourRejected=0;$ngVectorRelations=0;$ngVectorSources=0;$actualTopPatterns=0
$relations=0; $factorizations=0; $multiple=0; $fullMinimality=0
foreach($gens in $fixtures) {
  $gamma=Reachable $gens 180
  $gaps=@(0..(180-($gens|Measure-Object -Maximum).Maximum)|Where-Object {-not $gamma.Contains($_)})
  $frobenius=($gaps|Measure-Object -Maximum).Maximum
  # A reachable block of length max(generator) proves this bounded PF search covers all gaps.
  for($n=$frobenius+1;$n -le $frobenius+($gens|Measure-Object -Maximum).Maximum;$n++){
    if(-not $gamma.Contains($n)){throw 'PF search has not reached a conductor block'}
  }
  $pf=@($gaps|Where-Object {$f=$_;@($gens|Where-Object {-not $gamma.Contains($f+$_)}).Count -eq 0})
  if(($pf -join ',') -cne ($expectedPF[$classified] -join ',')){throw 'Actual PF set mismatch'}
  $vector=@();$ng=$true
  foreach($n in $gens){
    $candidates=@($pf|Where-Object {$f=$_;@($pf|Where-Object {-not $gamma.Contains($n+$f-$_)}).Count -eq 0})
    if(-not $candidates.Count){$ng=$false;$vector+=,$null}else{$vector+=,$candidates[0]}
  }
  if($ng -ne $expectedNG[$classified]){throw 'PF-NG vector classification mismatch'}
  if($ng){foreach($j in 0..3){foreach($g in $pf){
    if(-not $gamma.Contains($gens[$j]+$vector[$j]-$g)){throw 'Explicit NG-vector relation fails'}
    $ngVectorRelations++
  }}}
  # Actual factorization graph, not the synthetic partition fixture below.
  # Degree80 is an audit bound; the literal rho/budgets are the accepted small controls.
  $rho=0;$budgets=@(0,0,0,0);$observedPartitions=[Collections.Generic.HashSet[string]]::new()
  foreach($d in 1..80){
    $components=@(Run31Components @(Run31Factors $gens $d))
    if($components.Count -lt 2){continue}
    $rho+=$components.Count-1
    for($j=0;$j -lt 4;$j++){
      if(@($components|Where-Object {$_.Support.Contains($j)}).Count -eq 0){$budgets[$j]+=$components.Count-1}
    }
    [void]$observedPartitions.Add((@($components|ForEach-Object {$_.Support.Count}|Sort-Object)-join '+'))
  }
  if($rho -ne $expectedRho[$classified] -or ($budgets -join ',') -cne ($expectedBudgets[$classified] -join ',')){
    throw 'Actual bounded Betti rho/budgets mismatch'
  }
  if($rho -eq 4){
    $rhoFourBases+=4
    foreach($j in 0..3){if($budgets[$j] -eq 0){
      if($pf.Count -eq 3 -and $ng){throw 'Budget-zero type-three PF-NG rho-four control survives'}
      $rhoFourRejected++
    }}
    if($pf.Count -eq 3 -and $ng){
      if(@($budgets|Where-Object {$_ -ne 1}).Count){throw 'Combined-hypothesis rho-four budgets not all one'}
      foreach($p in $observedPartitions){if($p -notin @('1+1','1+2','2+2')){throw 'Combined-hypothesis support partition fails'}}
    }
  }
  Write-Host "PF/NG fixture classification: gens=$($gens -join ',') PF=$($pf -join ',') type=$($pf.Count) NG=$ng vector=$($vector -join ',') rho80=$rho budgets=$($budgets -join ',') partitions=$(@($observedPartitions|Sort-Object)-join ',')"
  for($i=0;$i -lt 4;$i++) {
    $q=$gens[$i]; $tails=@(0..3 | Where-Object {$_ -ne $i} | ForEach-Object {$gens[$_]})
    $hset=Reachable $tails 180
    if($hset.Contains($q)){throw 'Original base is tail-generated'}
    $kset=[Collections.Generic.HashSet[int]]::new()
    foreach($h in $hset){if($h -ge $q -and $gamma.Contains($h-$q)){[void]$kset.Add($h)}}
    # Check the source lemma from the actual PF top pattern and an explicit NG vector.
    # No unrelated cardinality bijection or assumed combined-hypothesis fixture.
    if($pf.Count -eq 3){foreach($a in 0..2){foreach($b in 0..2){
      if($a -eq $b){continue};$c=3-$a-$b;$pfByTail=@($pf[$a],$pf[$b],$pf[$c])
      $tops=@(0..2|ForEach-Object {$pfByTail[$_]+$q+$tails[$_]})
      if(@($tops|Sort-Object -Unique).Count -ne 1){continue};$actualTopPatterns++
      if(-not $ng){continue}
      $selected=[array]::IndexOf($pfByTail,$vector[$i])
      if($selected -lt 0){throw 'Explicit NG witness absent from actual PF/socle pattern'}
      foreach($t in 0..2){
        if($t -eq $selected){continue};$d=$q+$tails[$t];$w=$q+$vector[$i]-$pfByTail[$t]
        if($d -ne $tails[$selected]+$w -or -not $gamma.Contains($w)){throw 'NG/top additive source equation fails'}
        if(-not $kset.Contains($d)){throw 'Explicit NG-vector source not in K'}
        foreach($h in $hset){if($h -gt 0 -and $d -ge $h -and $kset.Contains($d-$h)){throw 'Explicit NG-vector source has full H predecessor'}}
        $exact=@(Run31Factors $tails $d)
        if(-not @($exact|Where-Object {$_.E[$selected] -gt 0}).Count){throw 'Explicit NG-vector source lacks selected-tail factorization'}
        $ngVectorSources++
      }
    }}}
    foreach($d in $kset){
      $one=$true; foreach($t in $tails){if($d -ge $t -and $kset.Contains($d-$t)){$one=$false}}
      $full=$true; foreach($r in $hset){if($r -gt 0 -and $d -ge $r -and $kset.Contains($d-$r)){$full=$false;break}}
      if($one -ne $full){throw 'One-tail/full source minimality mismatch'}; $fullMinimality++
    }
    for($s=0;$s -lt 3;$s++){for($t=0;$t -lt 3;$t++){
      if($s -eq $t){continue}; $d=$q+$tails[$t]; $g=$d-$tails[$s]
      if($g -lt 0 -or -not $gamma.Contains($g)){continue}
      if(-not $kset.Contains($d)){throw 'NG relation source not in K'}
      foreach($a in $tails){if($d -ge $a -and $kset.Contains($d-$a)){throw 'NG relation source has K predecessor'}}
      if($g -ge $q -and $gamma.Contains($g-$q)){throw 'Gamma witness not base-free'}
      $found=$false; $count=0
      for($x=0;$x*$tails[0] -le $d;$x++){for($y=0;$x*$tails[0]+$y*$tails[1] -le $d;$y++){
        $rest=$d-$x*$tails[0]-$y*$tails[1]
        if($rest % $tails[2] -ne 0){continue}; $z=[int]($rest/$tails[2]); $u=@($x,$y,$z)
        if($u[$s] -gt 0){$found=$true}
        for($j=0;$j -lt 3;$j++){if($u[$j] -gt 0 -and $kset.Contains($d-$tails[$j])){throw 'Source factorization not exponent-minimal'}}
        $count++;$factorizations++
      }}
      if(-not $found){throw 'No exact factorization containing selected tail'}
      if($count -gt 1){$multiple++};$relations++
    }}
  }
  $classified++
}
if($classified -ne 6 -or $rhoFourBases -ne 4 -or $rhoFourRejected -ne 1 -or
   $ngVectorSources -ne 4 -or $actualTopPatterns -ne 3){throw 'Incomplete PF/NG/source controls'}
Write-Host "PASS Run31 PF/NG fixture classification: fixtures=$classified rhoFourBases=$rhoFourBases budgetZeroRejected=$rhoFourRejected; <7,8,9,11> lacks base7 NG witness; actual bounded Betti inspection degree<=80"
Write-Host "PASS Run31 explicit NG-vector sources: vectorRelations=$ngVectorRelations actualTopPatterns=$actualTopPatterns sourceChecks=$ngVectorSources; combined type3/NG/rho4 fixtures=0 (not asserted to exist)"
# Synthetic nonempty disjoint support-card fixtures, not claimed actual rho-four semigroups.
$partitionChecks=0; $allowed=[Collections.Generic.HashSet[string]]::new()
foreach($c in 2..4){
  foreach($a in 1..4){foreach($b in 1..4){foreach($e in 0..4){foreach($f in 0..4){
    if(($c -eq 2 -and ($e -ne 0 -or $f -ne 0)) -or ($c -eq 3 -and $f -ne 0)){continue}
    $sizes=if($c -eq 2){@($a,$b)}elseif($c -eq 3){@($a,$b,$e)}else{@($a,$b,$e,$f)}
    if(@($sizes | Where-Object {$_ -eq 0}).Count){continue}
    $v=($sizes | Measure-Object -Sum).Sum; if($v -gt 4){continue}
    $ell=@($sizes | Where-Object {$_ -eq 1}).Count
    if((4-$v)*($c-1) -ne $ell){continue}
    if($c -ne 2){throw 'Saturated partition has more than two components'}
    $key=(@($sizes|Sort-Object) -join '+')
    if($key -notin @('1+1','1+2','2+2')){throw "Forbidden saturated partition $key"}
    [void]$allowed.Add($key);$partitionChecks++
  }}}}
}
if($allowed.Count -ne 3 -or $relations -eq 0 -or $multiple -eq 0){throw 'Incomplete controls'}
Write-Host "PASS Run31 audit-only sources: fixtures=$($fixtures.Count) bases=24 relations=$relations factorizations=$factorizations multipleFactorizations=$multiple fullMinimality=$fullMinimality"
Write-Host "PASS Run31 synthetic saturated supports: checked=$partitionChecks partitions=$(@($allowed|Sort-Object) -join ',') no1+3=PASS; not actual combined-hypothesis semigroup fixtures"
