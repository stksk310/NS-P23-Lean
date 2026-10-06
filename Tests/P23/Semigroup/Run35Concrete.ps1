$ErrorActionPreference='Stop'
# Audit-only reconstructed sets. These computations are not Lean proof inputs.
Add-Type -TypeDefinition @'
using System;
using System.Collections.Generic;
using System.Linq;
public static class Run35Controls {
  record P(int x,int y,int z);
  static bool Div(P p,P q,int b,int c) => p.y<=q.y && p.z<=q.z &&
    (p.x<=q.x || p.y+b<=q.y && p.z+c<=q.z);
  static bool PD(P p,P q) => p.x<=q.x && p.y<=q.y && p.z<=q.z;
  static P Pred(P p,int j,int a,int b,int c) {
    if(j==0)return p.x>0?new P(p.x-1,p.y,p.z):p.y>=b&&p.z>=c?new P(a-1,p.y-b,p.z-c):null;
    if(j==1)return p.y>0?new P(p.x,p.y-1,p.z):null;
    return p.z>0?new P(p.x,p.y,p.z-1):null;
  }
  static HashSet<P> Std(P[] roots,int a,int b,int c,bool plain=false) {
    var s=new HashSet<P>();
    for(int x=0;x<(plain?roots.Max(p=>p.x)+1:a);x++)
      for(int y=0;y<=roots.Max(p=>p.y);y++)for(int z=0;z<=roots.Max(p=>p.z);z++) {
        var p=new P(x,y,z);if(roots.Any(q=>plain?PD(p,q):Div(p,q,b,c)))s.Add(p);
      }
    return s;
  }
  static HashSet<P> Border(HashSet<P> s,int a,int b,int c,bool plain=false) {
    var cand=new HashSet<P>();
    foreach(var p in s) {
      cand.Add(plain||p.x+1<a?new P(p.x+1,p.y,p.z):new P(0,p.y+b,p.z+c));
      cand.Add(new P(p.x,p.y+1,p.z));cand.Add(new P(p.x,p.y,p.z+1));
    }
    return cand.Where(p=>!s.Contains(p) && Enumerable.Range(0,3).All(j=> {
      var q=Pred(p,j,plain?100:a,plain?100:b,plain?100:c);return q==null||s.Contains(q);
    })).ToHashSet();
  }
  static bool DC(P[] roots,int a,int b,int c,bool plain=false) =>
    Enumerable.Range(0,3).All(j=>roots.Any(s=>roots.All(r=> {
      var q=Pred(r,j,plain?100:a,plain?100:b,plain?100:c);
      return q==null||(plain?PD(q,s):Div(q,s,b,c));
    })));
  static bool Dom(P[] roots,HashSet<P> std,int b,int c,bool plain=false) =>
    roots.Any(s=>std.All(p=>roots.Contains(p)||(plain?PD(p,s):Div(p,s,b,c))));
  static void Assert(bool ok,string msg){if(!ok)throw new Exception(msg);}
  public static string Run() {
    int n2=0,n3=0,p2=0,p3=0,p7=0,wrapped=0;
    for(int a=2;a<=3;a++)for(int b=1;b<=2;b++)for(int c=0;c<=1;c++) {
      if(c==0&&b<2)continue;
      var pts=new List<P>();for(int x=0;x<a;x++)for(int y=0;y<=3;y++)for(int z=0;z<=2;z++)pts.Add(new P(x,y,z));
      for(int n=2;n<=3;n++)for(int i=0;i<pts.Count;i++)for(int j=i+1;j<pts.Count;j++)
        for(int k=n==3?j+1:pts.Count;k<=pts.Count;k++) {
          if(n==3&&k==pts.Count)continue;
          var r=n==2?new[]{pts[i],pts[j]}:new[]{pts[i],pts[j],pts[k]};
          if(r.Any(p=>r.Any(q=>p!=q&&Div(p,q,b,c))))continue;
          var s=Std(r,a,b,c);
          if(!new[]{new P(1,0,0),new P(0,1,0),new P(0,0,1),new P(0,b,c)}.All(s.Contains))continue;
          if(!DC(r,a,b,c)||Dom(r,s,b,c))continue;
          var bd=Border(s,a,b,c);Assert(bd.Count<=n+2,"one-tie no-dominant bound");
          if(n==2)n2++;else n3++;
          wrapped+=bd.Count(p=>p.x==0&&p.y>=b&&p.z>=c);
        }
    }
    var plainPts=new List<P>();for(int x=0;x<=2;x++)for(int y=0;y<=2;y++)for(int z=0;z<=2;z++)plainPts.Add(new P(x,y,z));
    for(int n=2;n<=3;n++)for(int i=0;i<plainPts.Count;i++)for(int j=i+1;j<plainPts.Count;j++)
      for(int k=n==3?j+1:plainPts.Count;k<=plainPts.Count;k++) {
        if(n==3&&k==plainPts.Count)continue;
        var r=n==2?new[]{plainPts[i],plainPts[j]}:new[]{plainPts[i],plainPts[j],plainPts[k]};
        if(r.Any(p=>r.Any(q=>p!=q&&PD(p,q))))continue;
        var s=Std(r,100,100,100,true);var bd=Border(s,100,100,100,true);
        if(n==2){Assert(bd.Count<=5,"plain pair bound");p2++;continue;}
        if(!new[]{new P(1,0,0),new P(0,1,0),new P(0,0,1)}.All(s.Contains)||!DC(r,100,100,100,true))continue;
        Assert(bd.Count==4||bd.Count==6||bd.Count==7,"plain frontier");p3++;
        if(bd.Count==7){
          var positive=r.Single(p=>p.x>0&&p.y>0&&p.z>0);
          Assert(s.All(p=>r.Contains(p)||PD(p,positive)),"plain seven positive-root dominance");p7++;
        }
      }
    Assert(n2>0&&n3>0&&p2>0&&p3>0&&p7>0&&wrapped>0,"nonempty audit coverage");
    return $"Run35 audit-only PASS: one-tie2={n2}; one-tie3={n3}; wrapped={wrapped}; plain2={p2}; plain3={p3}; plain7={p7}; failures=0";
  }
}
'@
[Run35Controls]::Run()
