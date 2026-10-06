$ErrorActionPreference='Stop'
# Independent integer audit controls; no generated value is a production proof input.
Add-Type -TypeDefinition @'
using System;
using System.Linq;
using System.Collections.Generic;
public static class Run37Controls {
  static void Check(bool p,string s){if(!p)throw new Exception(s);}
  static int Gcd(int a,int b){while(b!=0){int t=a%b;a=b;b=t;}return a;}
  static int[] Apery(int[] ns,int q){
    var d=Enumerable.Repeat(int.MaxValue,q).ToArray();d[0]=0;
    var todo=new PriorityQueue<int,int>();todo.Enqueue(0,0);
    while(todo.TryDequeue(out int r,out int v)){
      if(d[r]!=v)continue;
      foreach(int n in ns){int t=(r+n)%q,w=v+n;if(w<d[t]){d[t]=w;todo.Enqueue(t,w);}}
    }
    Check(d.All(x=>x<int.MaxValue),"cofinite");return d;
  }
  static bool Minimal(int[] ns){
    for(int j=0;j<4;j++){
      var hit=new bool[ns[j]+1];hit[0]=true;
      for(int x=1;x<=ns[j];x++)for(int k=0;k<4;k++)
        if(k!=j&&x>=ns[k]&&hit[x-ns[k]])hit[x]=true;
      if(hit[ns[j]])return false;
    }return true;
  }
  public static string Run(){
    int models=0,bases=0,pfChecks=0,gapChecks=0,divChecks=0,pivots=0,repeated=0,AS=0,notAS=0;
    var types=new HashSet<int>();
    for(int a=4;a<=15;a++)for(int b=a+1;b<=18;b++)
    for(int c=b+1;c<=20;c++)for(int d=c+1;d<=22;d++){
      int[] ns={a,b,c,d};if(Gcd(Gcd(a,b),Gcd(c,d))!=1||!Minimal(ns))continue;
      models++;var ap0=Apery(ns,a);
      Func<int,bool> gamma=x=>x>=0&&x>=ap0[x%a];
      int F=ap0.Max()-a;
      var gaps=Enumerable.Range(0,F+1).Where(x=>!gamma(x)).ToArray();int G=gaps.Length;
      var pf=gaps.Where(f=>ns.All(n=>gamma(f+n))).ToArray();int t=pf.Length;
      types.Add(t);Check(gaps.Length>0&&gaps.Max()==F,"max gap");
      Check(pf.Contains(F),"F in PF");
      foreach(int f in pf){Check(f>0&&f<=F&&!gamma(f),"PF naturalization");pfChecks++;}
      var doubleGaps=gaps.Where(x=>!gamma(F-x)).ToArray();
      foreach(int x in doubleGaps){Check(doubleGaps.Contains(F-x),"reflection");gapChecks++;}
      Check(2*G==F+1+doubleGaps.Length,"double gap identity");
      Check(pf.Where(x=>x!=F).All(doubleGaps.Contains),"non-F PF inclusion");
      Check(F+t<=2*G,"genus lower bound");
      bool isAS=doubleGaps.All(pf.Contains);
      Check(isAS==(2*G==F+t),"standard AS iff genus");if(isAS)AS++;else notAS++;
      var centres=new List<(int q,int h)>();
      foreach(int q in ns){
        bases++;var ap=Apery(ns,q);var set=ap.ToHashSet();
        var socles=ap.Where(s=>ns.All(n=>!set.Contains(s+n))).ToArray();
        Check(socles.Order().SequenceEqual(pf.Select(f=>f+q).Order()),"PF socle equivalence");
        int sumQuot=0;
        for(int r=0;r<q;r++){
          Check(ap[r]%q==r,"residue inverse");int K=ap[r]/q;sumQuot+=K;
          for(int k=0;k<=K+1;k++)Check((!gamma(r+q*k))==(k<K),"gap quotient iff");
        }
        Check(sumQuot==G,"gap count by residue");
        Check(2*q*G==2*ap.Sum()-q*(q-1),"Apéry genus");
        foreach(int s in socles){
          var div=ap.Where(w=>gamma(s-w)).ToArray();
          var complement=ap.Except(div).Order().ToArray();
          if(!complement.SequenceEqual(socles.Where(w=>w!=s).Order()))continue;
          int h=s-q;centres.Add((q,h));
          Check(div.Length==q-t+1,"dominant complement card");
          foreach(int w in div){Check(set.Contains(s-w)&&div.Contains(s-w),"actual divisor reflection");divChecks++;}
          Check(2*div.Sum()==div.Length*s,"reflection sum");
          Check(complement.Sum()==pf.Sum()-h+(t-1)*q,"exceptional PF sum");
          Check(q*(2*G-h-t)==2*pf.Sum()-(t+1)*h,"dominant pivot");pivots++;
        }
      }
      for(int x=0;x<centres.Count;x++)for(int y=x+1;y<centres.Count;y++){
        var u=centres[x];var v=centres[y];if(u.q==v.q||u.h!=v.h)continue;
        Check(2*G==u.h+t&&u.h==F&&isAS,"repeated centre rigidity");repeated++;
      }
      if((t==2||t==3)&&ns.All(q=>centres.Any(x=>x.q==q)))
        Check(isAS,"four dominant centres AS");
    }
    Check(models>=200&&pivots>0&&repeated>0&&AS>0&&notAS>0,"substantial nonvacuous controls");
    return $"Run37 independent controls PASS: models={models}, bases={bases}, types={string.Join(",",types.Order())}, PF={pfChecks}, double-gap={gapChecks}, reflection={divChecks}, pivots={pivots}, repeated-centres={repeated}, AS={AS}, not-AS={notAS}";
  }
}
'@
[Run37Controls]::Run()
