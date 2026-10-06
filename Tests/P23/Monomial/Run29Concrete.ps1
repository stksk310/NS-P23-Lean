$ErrorActionPreference='Stop'
# Independent exploration only. Neither outputs nor bounded tables enter Lean.
if(-not ('P23Run29PlainControls' -as [type])) {
Add-Type -TypeDefinition @'
using System;
using System.Collections.Generic;
public static class P23Run29PlainControls {
  static int[] V(int n,int side) { return new[]{n/(side*side),(n/side)%side,n%side}; }
  static bool Le(int[] p,int[] q) {return p[0]<=q[0]&&p[1]<=q[1]&&p[2]<=q[2];}
  static bool Standard(int[] p,int[][] roots) {foreach(var r in roots)if(Le(p,r))return true;return false;}
  static bool Centres(int[][] roots) {
    for(int j=0;j<3;j++) {
      bool found=false;
      foreach(var c in roots) {
        bool ok=true;
        foreach(var s in roots)if(s[j]>0) {var p=(int[])s.Clone();p[j]--;if(!Le(p,c))ok=false;}
        if(ok){found=true;break;}
      }
      if(!found)return false;
    }
    return true;
  }
  static int Border(int[][] roots,int side) {
    int card=0;
    for(int n=0;n<side*side*side;n++) {
      var p=V(n,side); if(Standard(p,roots))continue;
      bool ok=true;
      for(int j=0;j<3;j++)if(p[j]>0){var q=(int[])p.Clone();q[j]--;if(!Standard(q,roots))ok=false;}
      if(ok)card++;
    }
    return card;
  }
  public static string Run() {
    int checkedModels=0,triangle=0,plane=0,dominant=0;
    for(int a=0;a<64;a++)for(int b=a+1;b<64;b++)for(int c=b+1;c<64;c++) {
      var roots=new[]{V(a,4),V(b,4),V(c,4)};
      bool anti=true;
      for(int u=0;u<3;u++)for(int v=0;v<3;v++)if(u!=v&&Le(roots[u],roots[v]))anti=false;
      if(!anti)continue;
      bool live=true;
      for(int j=0;j<3;j++){var e=new int[3];e[j]=1;if(!Standard(e,roots))live=false;}
      if(!live||!Centres(roots))continue;
      int card=Border(roots,5); checkedModels++;
      if(card==4)triangle++;else if(card==6)plane++;else if(card==7)dominant++;
      else throw new Exception("Corrected centre cover mismatch: "+a+","+b+","+c+" border="+card);
    }
    var bad=new[]{new[]{2,0,0},new[]{1,1,0},new[]{0,2,0}};
    if(!Centres(bad)||Border(bad,4)!=5||Standard(new[]{0,0,1},bad))
      throw new Exception("Inactive-variable negative control mismatch");
    if(checkedModels==0||triangle==0||plane==0||dominant==0)throw new Exception("Missing control coverage");
    return "PASS independent plain controls: models="+checkedModels+" border4="+triangle+
      " border6="+plane+" border7="+dominant+" inactive-variable negative=PASS";
  }
}
'@
}
[P23Run29PlainControls]::Run()
function Get-FactorizationsOracle([int[]]$Generators, [int]$Degree) {
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

function Get-ComponentsOracle([object[]]$Factors) {
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




# Actual small chosen-base budget-zero controls, independently reconstructed.
if (-not ('P23Run29ChosenControls' -as [type])) {
  Add-Type -TypeDefinition @'
public static class P23Run29ChosenControls {
  public static int[][] Factors(int[] n, int d) {
    var rows = new System.Collections.Generic.List<int[]>();
    for (int a=0; a*n[0]<=d; a++)
      for (int b=0; a*n[0]+b*n[1]<=d; b++)
        for (int c=0; a*n[0]+b*n[1]+c*n[2]<=d; c++) {
          int rest=d-a*n[0]-b*n[1]-c*n[2];
          if (rest>=0 && rest%n[3]==0) rows.Add(new int[]{a,b,c,rest/n[3]});
        }
    return rows.ToArray();
  }
  public static int[][] Components(object[] factors) {
    var seen = new bool[factors.Length];
    var rows = new System.Collections.Generic.List<int[]>();
    for (int start=0; start<factors.Length; start++) {
      if (seen[start]) continue;
      var queue = new System.Collections.Generic.Queue<int>();
      var part = new System.Collections.Generic.List<int>();
      queue.Enqueue(start); seen[start]=true;
      while (queue.Count>0) {
        int u=queue.Dequeue(); part.Add(u);
        for (int v=0; v<factors.Length; v++) {
          if (seen[v]) continue;
          bool adjacent=false;
          for (int j=0; j<4; j++)
            if (((int[])factors[u])[j]>0 && ((int[])factors[v])[j]>0) adjacent=true;
          if (adjacent) {seen[v]=true;queue.Enqueue(v);}
        }
      }
      rows.Add(part.ToArray());
    }
    return rows.ToArray();
  }
}
'@
}
function Get-Factorizations([int[]]$Generators, [int]$Degree) {
  return [P23Run29ChosenControls]::Factors($Generators,$Degree)
}
function Get-Components([object[]]$Factors) {
  return [P23Run29ChosenControls]::Components($Factors)
}
$run29Fixtures=@([int[]]@(4,5,6,7),[int[]]@(5,6,7,8),[int[]]@(5,7,8,9),
  [int[]]@(6,7,9,10),[int[]]@(7,8,9,11),[int[]]@(7,9,10,12),
  [int[]]@(6,8,9,11),[int[]]@(8,10,11,13))
$run29ZeroCases=0
$run29NgTypeThree=0
$run29Bound=160
$run29OracleComparisons=0
foreach($run29N in $run29Fixtures) {
  for($run29D=0;$run29D -le 32;$run29D++) {
    $run29Old=@(Get-FactorizationsOracle $run29N $run29D)
    $run29New=@(Get-Factorizations $run29N $run29D)
    if((($run29Old|ForEach-Object {$_ -join ','}) -join ';') -ne
       (($run29New|ForEach-Object {$_ -join ','}) -join ';')) {
      throw 'Native factorization helper differs from retained PowerShell oracle'
    }
    $run29OldC=@(Get-ComponentsOracle $run29Old)
    $run29NewC=@(Get-Components $run29New)
    if((($run29OldC|ForEach-Object {$_ -join ','}) -join ';') -ne
       (($run29NewC|ForEach-Object {$_ -join ','}) -join ';')) {
      throw 'Native BFS helper differs from retained PowerShell oracle'
    }
    $run29OracleComparisons++
  }
}
Write-Host "PASS test-helper parity: native factorization/BFS equals retained PowerShell oracle in $run29OracleComparisons fibers"
foreach($run29N in $run29Fixtures){
  $run29Fibers=@{};$run29Sg=[bool[]]::new($run29Bound+1)
  $run29Budget=[int[]]::new(4);$run29Rho=0
  for($run29D=0;$run29D -le $run29Bound;$run29D++){
    $run29F=@(Get-Factorizations $run29N $run29D)
    $run29Fibers[$run29D]=$run29F;$run29Sg[$run29D]=$run29F.Count -gt 0
    $run29C=@(Get-Components $run29F)
    if($run29C.Count -gt 1){
      $run29Rho+=$run29C.Count-1
      for($run29I=0;$run29I -lt 4;$run29I++){
        $run29Used=$false
        foreach($run29V in $run29F){if($run29V[$run29I] -gt 0){$run29Used=$true}}
        if(-not $run29Used){$run29Budget[$run29I]+=$run29C.Count-1}
      }
    }
  }
  $run29Pf=[Collections.Generic.List[int]]::new()
  for($run29D=1;$run29D -le $run29Bound-($run29N|Measure-Object -Maximum).Maximum;$run29D++){
    if($run29Sg[$run29D]){continue}
    $run29Good=$true
    foreach($run29Gen in $run29N){if(-not $run29Sg[$run29D+$run29Gen]){$run29Good=$false}}
    if($run29Good){$run29Pf.Add($run29D)}
  }
  $run29Ng=$true
  foreach($run29Gen in $run29N){
    $run29Witness=$false
    foreach($run29P in $run29Pf){
      $run29Good=$true
      foreach($run29Q in $run29Pf){
        $run29Value=$run29Gen+$run29P-$run29Q
        if($run29Value -lt 0 -or -not $run29Sg[$run29Value]){$run29Good=$false}
      }
      if($run29Good){$run29Witness=$true}
    }
    if(-not $run29Witness){$run29Ng=$false}
  }
  for($run29I=0;$run29I -lt 4;$run29I++){
    if($run29Budget[$run29I] -ne 0){continue}
    $run29Std=[Collections.Generic.HashSet[string]]::new()
    for($run29D=0;$run29D -le $run29Bound;$run29D++){
      if(-not $run29Sg[$run29D]){continue}
      if($run29D -ge $run29N[$run29I] -and $run29Sg[$run29D-$run29N[$run29I]]){continue}
      $run29F=@($run29Fibers[$run29D])
      if($run29F.Count -ne 1){throw 'Budget-zero surviving degree has multiple tail factorizations'}
      $run29V=$run29F[0]
      if($run29V[$run29I] -ne 0){throw 'Apery factorization uses base'}
      $run29Tail=@(0..3|Where-Object{$_ -ne $run29I}|ForEach-Object{$run29V[$_]})
      $null=$run29Std.Add($run29Tail -join ',')
    }
    if($run29Std.Count -ne $run29N[$run29I]){throw 'Apery cardinality control failed'}
    foreach($run29J in 0..2){
      $run29E=[int[]]::new(3);$run29E[$run29J]=1
      if(-not $run29Std.Contains($run29E -join ',')){throw 'Chosen-base tail survival control failed'}
    }
    $run29Candidates=[Collections.Generic.HashSet[string]]::new()
    foreach($run29Key in $run29Std){
      $run29V=[int[]]@($run29Key.Split(',')|ForEach-Object{[int]$_})
      foreach($run29J in 0..2){
        $run29W=[int[]]$run29V.Clone();$run29W[$run29J]++
        if(-not $run29Std.Contains($run29W -join ',')){$null=$run29Candidates.Add($run29W -join ',')}
      }
    }
    $run29Border=0
    foreach($run29Key in $run29Candidates){
      $run29V=[int[]]@($run29Key.Split(',')|ForEach-Object{[int]$_});$run29Good=$true
      foreach($run29J in 0..2){
        if($run29V[$run29J] -gt 0){
          $run29W=[int[]]$run29V.Clone();$run29W[$run29J]--
          if(-not $run29Std.Contains($run29W -join ',')){$run29Good=$false}
        }
      }
      if($run29Good){$run29Border++}
    }
    if($run29Border -ne $run29Rho){throw 'Actual budget-zero monomial border/rho mismatch'}
    $run29ZeroCases++
    if($run29Ng -and $run29Pf.Count -eq 3){
      if($run29Border -eq 5){throw 'Type-three NG budget-zero five-generator control failed'}
      $run29NgTypeThree++
    }
  }
}
if($run29ZeroCases -eq 0){throw 'Missing genuine budget-zero control'}
Write-Host "PASS independent chosen-base controls: budgetZero=$run29ZeroCases typeThreeNG=$run29NgTypeThree border=rho tailsSurvive=PASS"

