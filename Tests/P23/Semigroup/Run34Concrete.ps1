$ErrorActionPreference='Stop'
# Audit-only bounded controls; no generated fact enters the Lean proof DAG.
Add-Type -TypeDefinition @'
using System;
using System.Collections.Generic;
using System.Linq;
public static class Run34Controls {
  record P(int x,int y,int z);
  static bool Div(P p,P q,int b,int c) => p.y<=q.y && p.z<=q.z &&
    (p.x<=q.x || p.y+b<=q.y && p.z+c<=q.z);
  static HashSet<P> Std(P[] roots,int a,int b,int c) {
    var s=new HashSet<P>();
    for(int x=0;x<a;x++)for(int y=0;y<=roots.Max(p=>p.y);y++)
      for(int z=0;z<=roots.Max(p=>p.z);z++) {
        var p=new P(x,y,z);if(roots.Any(q=>Div(p,q,b,c)))s.Add(p);
      }
    return s;
  }
  static HashSet<P> Border(P[] roots,int a,int b,int c) {
    var s=Std(roots,a,b,c);var cand=new HashSet<P>();
    foreach(var p in s) {
      cand.Add(p.x+1<a?new P(p.x+1,p.y,p.z):new P(0,p.y+b,p.z+c));
      cand.Add(new P(p.x,p.y+1,p.z));cand.Add(new P(p.x,p.y,p.z+1));
    }
    return cand.Where(p=>!s.Contains(p) &&
      (p.x==0||s.Contains(new P(p.x-1,p.y,p.z))) &&
      (p.y==0||s.Contains(new P(p.x,p.y-1,p.z))) &&
      (p.z==0||s.Contains(new P(p.x,p.y,p.z-1))) &&
      (p.x!=0||p.y<b||p.z<c||s.Contains(new P(a-1,p.y-b,p.z-c)))).ToHashSet();
  }
  static void Assert(bool ok,string msg){if(!ok)throw new Exception(msg);}
  public static string Run() {
    int plain=0,fixture=0,live=0,two=0;
    // Ordinary pure powers: hand-specified box root and literal axis border.
    for(int A=2;A<=5;A++)for(int B=2;B<=5;B++)for(int C=2;C<=5;C++) {
      var s=new HashSet<P>();for(int x=0;x<A;x++)for(int y=0;y<B;y++)for(int z=0;z<C;z++)s.Add(new P(x,y,z));
      var roots=s.Where(p=>!s.Contains(new P(p.x+1,p.y,p.z)) &&
        !s.Contains(new P(p.x,p.y+1,p.z)) && !s.Contains(new P(p.x,p.y,p.z+1))).ToArray();
      Assert(roots.Length==1 && roots[0]==new P(A-1,B-1,C-1),"plain singleton");
      var cand=s.SelectMany(p=>new[]{new P(p.x+1,p.y,p.z),new P(p.x,p.y+1,p.z),new P(p.x,p.y,p.z+1)}).ToHashSet();
      var bd=cand.Where(p=>!s.Contains(p) && (p.x==0||s.Contains(new P(p.x-1,p.y,p.z))) &&
        (p.y==0||s.Contains(new P(p.x,p.y-1,p.z))) && (p.z==0||s.Contains(new P(p.x,p.y,p.z-1)))).ToHashSet();
      Assert(bd.SetEquals(new[]{new P(A,0,0),new P(0,B,0),new P(0,0,C)}),"plain triple");plain++;
    }
    Assert(Border(new[]{new P(1,2,2)},2,1,1).SetEquals(new[]{new P(0,3,0),new P(0,0,3)}),"mixed fixture");fixture++;
    Assert(Border(new[]{new P(1,3,1)},2,2,0).SetEquals(new[]{new P(0,4,0),new P(0,0,2)}),"pure last fixture");fixture++;
    Assert(Border(new[]{new P(0,3,1)},2,2,0).SetEquals(new[]{new P(1,2,0),new P(0,0,2)}),"pure below fixture");fixture++;
    // All root antichains of size1..3 in each small normal box, not only principals.
    for(int a=2;a<=3;a++)for(int b=1;b<=2;b++)for(int c=0;c<=1;c++) {
      if(c==0&&b<2)continue;
      var pts=new List<P>();for(int x=0;x<a;x++)for(int y=0;y<=3;y++)for(int z=0;z<=2;z++)pts.Add(new P(x,y,z));
      for(int n=1;n<=3;n++)for(int i=0;i<pts.Count;i++)
        for(int j=n>=2?i+1:pts.Count;j<=pts.Count;j++) {
          if(n>=2&&j==pts.Count)continue;
          for(int k=n==3?j+1:pts.Count;k<=pts.Count;k++) {
            if(n==3&&k==pts.Count)continue;
            var r=n==1?new[]{pts[i]}:n==2?new[]{pts[i],pts[j]}:new[]{pts[i],pts[j],pts[k]};
            if(r.Any(p=>r.Any(q=>p!=q&&Div(p,q,b,c))))continue;
            var std=Std(r,a,b,c);
            if(!std.Contains(new P(1,0,0))||!std.Contains(new P(0,1,0))||!std.Contains(new P(0,0,1))||!std.Contains(new P(0,b,c)))continue;
            live++;var bd=Border(r,a,b,c);Assert(bd.Count>=2,"live at least two");
            if(bd.Count==2){two++;Assert(r.Length==1,"two border implies one root");}
          }
        }
    }
    return $"PASS audit-only Run34: plain triples={plain}; literal mixed/pure fixtures={fixture}; live antichains={live}; exact two-border cases={two}; failures=0";
  }
}
'@
[Run34Controls]::Run()
