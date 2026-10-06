$ErrorActionPreference='Stop'
# Audit-only computations: no production declaration consumes this file.
# Canonical maps are solved one monoid-homogeneous degree at a time over F2.
# Each positive variable-source solution is checked on every algebra basis scalar.
Add-Type -TypeDefinition @'
using System;
using System.Collections.Generic;
public static class Run32Control {
  struct P : IEquatable<P> {
    public int x,y,z;
    public P(int X,int Y,int Z){x=X;y=Y;z=Z;}
    public bool Equals(P p){return x==p.x&&y==p.y&&z==p.z;}
    public override bool Equals(object o){return o is P && Equals((P)o);}
    public override int GetHashCode(){return HashCode.Combine(x,y,z);}
  }
  sealed class Model {
    public int a,b,c; public List<P> O=new List<P>();
    public Dictionary<P,int> ix=new Dictionary<P,int>();
    public int[,] mul; public int[] vars; public List<int> roots=new List<int>();
    public P N(P p){int n=p.x/a;return new P(p.x%a,p.y+n*b,p.z+n*c);}
    public P Product(P p,P q){return N(new P(p.x+q.x,p.y+q.y,p.z+q.z));}
    bool Dvd(P p,P q){return p.y<=q.y&&p.z<=q.z&&(p.x<=q.x||(p.y+b<=q.y&&p.z+c<=q.z));}
    public Model(int A,int B,int C,int Y,int Z,P[] killed){
      a=A;b=B;c=C;
      for(int x=0;x<a;x++)for(int y=0;y<Y;y++)for(int z=0;z<Z;z++){
        P p=new P(x,y,z);bool ok=true;foreach(P g in killed)if(Dvd(g,p)){ok=false;break;}
        if(ok){ix[p]=O.Count;O.Add(p);}
      }
      int n=O.Count;mul=new int[n,n];
      for(int i=0;i<n;i++)for(int j=0;j<n;j++){int k;mul[i,j]=ix.TryGetValue(Product(O[i],O[j]),out k)?k:-1;}
      vars=new int[]{ix[new P(1,0,0)],ix[new P(0,1,0)],ix[new P(0,0,1)]};
      for(int i=0;i<n;i++){bool soc=true;foreach(int v in vars)if(mul[v,i]>=0){soc=false;break;}if(soc)roots.Add(i);}
    }
    int Find(int[] p,int i){while(p[i]!=i){p[i]=p[p[i]];i=p[i];}return i;}
    bool Source(int s,int target,bool validate){
      int n=O.Count;P top=Product(O[s],O[target]);int[] dest=new int[n];
      int[] parent=new int[n];bool[] forbidden=new bool[n];
      for(int p=0;p<n;p++){
        parent[p]=p;dest[p]=-1;
        for(int t=0;t<n;t++)if(Product(O[p],O[t]).Equals(top)){
          if(dest[p]>=0)throw new Exception("cancellativity failure");dest[p]=t;
        }
      }
      Action<int,int> eq=(p,q)=>{int x=Find(parent,p),y=Find(parent,q);if(x!=y){parent[y]=x;forbidden[x]|=forbidden[y];}};
      Action<int> zero=p=>{if(p>=0)forbidden[Find(parent,p)]=true;};
      foreach(int v in vars)for(int p=0;p<n;p++){
        int q=-1;for(int t=0;t<n;t++)if(mul[v,t]==p){q=t;break;}
        int lhs=q>=0?dest[q]:-1;
        int rhs=dest[p]>=0?mul[v,dest[p]]:-1;
        if(lhs>=0&&rhs>=0&&lhs==rhs)eq(p,q);
        else {if(lhs>=0)zero(q);if(rhs>=0)zero(p);}
      }
      int root=Find(parent,s);if(dest[s]!=target||forbidden[root])return false;
      if(validate){
        int[] image=new int[n];for(int p=0;p<n;p++)image[p]=dest[p]>=0&&Find(parent,p)==root?dest[p]:-1;
        if(image[s]!=target)throw new Exception("source image mismatch");
        for(int m=0;m<n;m++)for(int p=0;p<n;p++){
          int q=-1;for(int t=0;t<n;t++)if(mul[m,t]==p){q=t;break;}
          int lhs=q>=0?image[q]:-1;
          int rhs=image[p]>=0?mul[m,image[p]]:-1;
          if(lhs!=rhs)throw new Exception("full basis canonical-map A-linearity failure");
          mapChecks++;
        }
        witnesses++;
      }
      return true;
    }
    public bool NG(){
      // Type>1 root images must have zero constant coefficients; independently test it.
      int one=ix[new P(0,0,0)];
      if(roots.Count>1)foreach(int s in roots)if(Source(s,one,false))throw new Exception("unexpected unit root image");
      foreach(int v in vars){bool ok=false;foreach(int s in roots)if(Source(s,v,true)){ok=true;break;}if(!ok)return false;}
      return true;
    }
  }
  static long mixed,pure,residual,witnesses,mapChecks;
  public static string Run(){
    for(int a=2;a<=4;a++)for(int b=1;b<=3;b++)for(int c=1;c<=3;c++)
    for(int r=1;r<a;r++)for(int B=b+1;B<=b+2;B++)for(int C=c+2;C<=c+3;C++)for(int v=1;v<C-c;v++){
      Model M=new Model(a,b,c,B,C,new P[]{new P(0,B,0),new P(0,0,C),new P(r,0,v)});
      if(M.roots.Count!=3||M.NG())throw new Exception("mixed three-border mismatch");mixed++;
    }
    for(int a=2;a<=4;a++)for(int b=2;b<=4;b++)for(int u=1;u<=2;u++)for(int C=2;C<=3;C++)
    for(int r=1;r<a;r++)for(int v=1;v<u+b;v++)for(int w=1;w<C;w++){
      Model M=new Model(a,b,0,u+b,C,new P[]{new P(r,u,0),new P(0,0,C),new P(0,v,w)});
      if(M.roots.Count!=2+(v>u?1:0))throw new Exception("pure type formula mismatch");
      if(M.roots.Count==3&&M.NG()&&(r!=1||v!=u+b-1||w!=C-1))throw new Exception("pure endpoint mismatch");pure++;
    }
    for(int a=2;a<=4;a++)for(int b=2;b<=4;b++)for(int u=1;u<=3;u++)for(int C=2;C<=4;C++){
      Model M=new Model(a,b,0,u+b,C,new P[]{new P(1,u,0),new P(0,0,C),new P(0,u+b-1,C-1)});
      if(M.roots.Count!=3||!M.NG())throw new Exception("mandatory positive residual NG control failed");residual++;
    }
    return "Run32 audit controls PASS: mixed="+mixed+", pure="+pure+", positive residual="+residual+", explicit canonical-map witnesses="+witnesses+", full basis A-linearity checks="+mapChecks;
  }
}
'@
[Run32Control]::Run()
