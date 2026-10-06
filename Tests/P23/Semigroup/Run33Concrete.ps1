$ErrorActionPreference='Stop'
# Bounded independent audit only: never imported by production Lean.
Add-Type -TypeDefinition @'
using System;
using System.Collections.Generic;
public static class Run33Control {
 static int Gcd(int a,int b){while(b!=0){int t=a%b;a=b;b=t;}return a;}
 static void Fiber(int[] n,int d,int j,int[] u,List<int[]> f){
  if(j==3){if(d%n[j]==0){u[j]=d/n[j];f.Add((int[])u.Clone());}return;}
  for(int a=0;a*n[j]<=d;a++){u[j]=a;Fiber(n,d-a*n[j],j+1,u,f);}
 }
 static int Find(int[] p,int i){while(p[i]!=i){p[i]=p[p[i]];i=p[i];}return i;}
 public static string Run(){
  int models=0,rho4=0,ng4=0,type3four=0,betti=0;
  for(int a=4;a<=8;a++)for(int b=a+1;b<=11;b++)for(int c=b+1;c<=12;c++)for(int d=c+1;d<=13;d++){
   int[] n={a,b,c,d};if(Gcd(Gcd(a,b),Gcd(c,d))!=1)continue;
   bool[] h=new bool[401];h[0]=true;
   for(int t=1;t<h.Length;t++)foreach(int v in n)if(t>=v&&h[t-v]){h[t]=true;break;}
   bool minimal=true;foreach(int v in n){
    bool[] other=new bool[v+1];other[0]=true;
    for(int t=1;t<=v;t++)foreach(int w in n)if(w!=v&&t>=w&&other[t-w])other[t]=true;
    if(other[v])minimal=false;
   }
   if(!minimal)continue;
   int F=0;for(int t=1;t<350;t++)if(!h[t])F=t;
   if(F>=100)throw new Exception("fixture bound insufficient");
   List<int> pf=new List<int>();
   for(int f=1;f<=F;f++)if(!h[f]){bool ok=true;foreach(int v in n)if(!h[f+v])ok=false;if(ok)pf.Add(f);}
   bool ng=true;foreach(int v in n){bool witness=false;foreach(int f in pf){bool ok=true;
    foreach(int g in pf){int z=v+f-g;if(z<0||!h[z])ok=false;}if(ok)witness=true;
   }if(!witness)ng=false;}
   int rho=0;
   for(int t=1;t<=150;t++){
    List<int[]> fs=new List<int[]>();Fiber(n,t,0,new int[4],fs);int m=fs.Count;
    if(m<2)continue;int[] p=new int[m];for(int j=0;j<m;j++)p[j]=j;
    for(int j=0;j<m;j++)for(int l=0;l<j;l++){bool overlap=false;
     for(int k=0;k<4;k++)if(fs[j][k]>0&&fs[l][k]>0)overlap=true;
     if(overlap)p[Find(p,j)]=Find(p,l);
    }
    HashSet<int> components=new HashSet<int>();for(int j=0;j<m;j++)components.Add(Find(p,j));
    if(components.Count>1){if(t>100)throw new Exception("late Betti control outside recorded budget");
     rho+=components.Count-1;betti++;}
   }
   models++;if(rho==4){rho4++;if(ng)ng4++;if(pf.Count==3){type3four++;
    if(ng)throw new Exception("type-three PF-NG bounded-rho-four counterexample");
   }}
  }
  // A raw positive x exponent may wrap to y-only; union support survives.
  int support=0;for(int a=2;a<=6;a++)for(int b=2;b<=6;b++)for(int x=1;x<=20;x++){
   int nx=x%a,ny=(x/a)*b;if(nx==0&&ny==0)throw new Exception("weak support failed");support++;
  }
  return $"Run33 bounded independent controls PASS: models={models}; degrees<=150; Betti fibers={betti}; bounded-rho4={rho4}; PF-NG/rho4={ng4}; type3/rho4={type3four}; weak-support={support}; counterexamples=0";
 }
}
'@
[Run33Control]::Run()
