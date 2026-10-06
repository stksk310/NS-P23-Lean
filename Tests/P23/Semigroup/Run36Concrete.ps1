$ErrorActionPreference='Stop'
# Independent audit controls only. No generated object is a Lean proof input.
Add-Type -TypeDefinition @'
using System;
using System.Collections.Generic;
using System.Linq;
public static class Run36Controls {
  record P(int x,int y,int z);
  static void Check(bool ok,string msg){if(!ok)throw new Exception(msg);}
  static bool Div(P p,P s)=>p.y<=s.y&&p.z<=s.z&&(p.x<=s.x||p.y+1<=s.y&&p.z+1<=s.z);
  static int[] Apery(int[] gens,int q){
    var d=Enumerable.Repeat(1000000,q).ToArray();d[0]=0;
    var todo=new PriorityQueue<int,int>();todo.Enqueue(0,0);
    while(todo.TryDequeue(out int r,out int v)){
      if(d[r]!=v)continue;
      foreach(int n in gens){int t=(r+n)%q,w=v+n;if(w<d[t]){d[t]=w;todo.Enqueue(t,w);}}
    }
    Check(d.All(v=>v<1000000),"cofinite fixture residues");return d;
  }
  public static string Run(){
    long triples=0,complete=0;
    for(int A=2;A<=5;A++)for(int B=2;B<=5;B++)for(int C=2;C<=5;C++){
      int q=A*B*C+2;var marks=new int[q];int stamp=0;
      for(int X=0;X<q;X++)for(int Y=0;Y<q;Y++)for(int Z=0;Z<q;Z++){
        triples++;stamp++;int r=A*X%q,s=B*Y%q;
        if(r==s)continue;marks[r]=stamp;marks[s]=stamp;bool valid=true;
        for(int x=0;x<A&&valid;x++)for(int y=0;y<B&&valid;y++)for(int z=0;z<C;z++){
          int v=(x*X+y*Y+z*Z)%q;
          if(marks[v]==stamp){valid=false;break;}marks[v]=stamp;
        }
        if(valid)complete++;
      }
    }
    Check(complete==0,"complete box-plus-two residue counterexample");
    int bases=0,residues=0,dominance=0,wrapped=0;
    var fixtures=new[]{new[]{4,5,6,7},new[]{5,6,7,8},new[]{6,7,8,9},new[]{7,8,9,10}};
    foreach(var gens in fixtures)foreach(int q in gens){
      var ap=Apery(gens,q);bases++;
      Check(ap.Select(v=>v%q).Distinct().Count()==q,"Apéry residue completeness");
      foreach(int v in ap){Check(ap[v%q]==v,"residue inverse");residues++;}
    }
    // Exact synthetic canonical/actual interfaces, including wrapped x divisors.
    for(int fixture=0;fixture<2;fixture++){
      int[] gens=fixtures[fixture];int q=gens[0],X=gens[2],Y=gens[1],Z=gens[3];
      var ap=Apery(gens,q);var gamma=new bool[500];gamma[0]=true;
      for(int v=0;v<500;v++)if(gamma[v])foreach(int n in gens)if(v+n<500)gamma[v+n]=true;
      P[] roots=fixture==0?new[]{new P(1,0,0),new P(0,1,0),new P(0,0,1)}:new[]{new P(0,1,1)};
      var standard=new List<P>();
      for(int x=0;x<2;x++)for(int y=0;y<=1;y++)for(int z=0;z<=1;z++){
        var p=new P(x,y,z);if(roots.Any(s=>Div(p,s)))standard.Add(p);
      }
      int Degree(P p)=>p.x*X+p.y*Y+p.z*Z;
      Check(standard.Select(Degree).ToHashSet().SetEquals(ap),"canonical/actual Apéry exact image");
      Check(standard.Select(Degree).Distinct().Count()==standard.Count,"fixture surviving basis injectivity");
      bool Socle(int w)=>gens.Skip(1).All(n=>!ap.Contains(w+n));
      foreach(var center in roots){
        if(!standard.All(p=>roots.Contains(p)||Div(p,center)))continue;
        int c=Degree(center);Check(Socle(c),"root to actual socle");
        foreach(var p in standard){
          int w=Degree(p);bool divides=w<=c&&gamma[c-w];
          Check(!divides==(Socle(w)&&w!=c),"exact actual dominance decomposition");
          if(Div(p,center)&&p.x>center.x)wrapped++;
          dominance++;
        }
      }
    }
    Check(dominance>0&&wrapped>0,"dominance/wrapped controls nonvacuous");
    return $"Run36 controls PASS: cyclic ABC=2..5 triples={triples}, complete={complete}; Apéry bases={bases}, residue checks={residues}; actual dominance={dominance}, wrapped={wrapped}. Audit-only.";
  }
}
'@
[Run36Controls]::Run() | Write-Host
