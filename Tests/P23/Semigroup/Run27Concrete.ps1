param([int]$MaxDegree = 80)
$ErrorActionPreference = 'Stop'
# Independent audit-only linear algebra: production Lean never imports this file.
if (-not ('P23Run27Ranks' -as [type])) {
Add-Type -TypeDefinition @'
using System;
using System.Linq;
using System.Collections.Generic;
public static class P23Run27Ranks {
  static List<int[]> Factors(int[] n,int d) {
    var r=new List<int[]>();
    if(d<0)return r;
    void Go(int j,int left,int[] u) {
      if(j==n.Length-1){if(left%n[j]==0){u[j]=left/n[j];r.Add((int[])u.Clone());}return;}
      for(int a=0;a*n[j]<=left;a++){u[j]=a;Go(j+1,left-a*n[j],u);}
    }
    Go(0,d,new int[n.Length]);return r;
  }
  static string Key(int[] u)=>string.Join(",",u);
  static int[] Components(List<int[]> f) {
    var c=Enumerable.Repeat(-1,f.Count).ToArray();int next=0;
    for(int s=0;s<f.Count;s++)if(c[s]<0){var q=new Queue<int>();q.Enqueue(s);c[s]=next;
      while(q.Count>0){int u=q.Dequeue();for(int v=0;v<f.Count;v++)if(c[v]<0 &&
        Enumerable.Range(0,4).Any(j=>f[u][j]>0&&f[v][j]>0)){c[v]=next;q.Enqueue(v);}}
      next++;
    }return c;
  }
  static int Mod(int x,int p)=>(x%p+p)%p;
  static int Rank(List<int[]> cols,int rows,int p) {
    var a=new int[rows,cols.Count];for(int r=0;r<rows;r++)for(int c=0;c<cols.Count;c++)a[r,c]=Mod(cols[c][r],p);
    int k=0;
    for(int j=0;j<cols.Count&&k<rows;j++){
      int s=k;while(s<rows&&a[s,j]==0)s++;if(s==rows)continue;
      for(int c=0;c<cols.Count;c++){int t=a[k,c];a[k,c]=a[s,c];a[s,c]=t;}
      int inv=1;while(Mod(inv*a[k,j],p)!=1)inv++;
      for(int c=j;c<cols.Count;c++)a[k,c]=Mod(a[k,c]*inv,p);
      for(int r=0;r<rows;r++)if(r!=k){int z=a[r,j];for(int c=j;c<cols.Count;c++)a[r,c]=Mod(a[r,c]-z*a[k,c],p);}
      k++;
    }return k;
  }
  static List<int[]> KernelBasis(List<int[]> f,bool killed) {
    var b=new List<int[]>();for(int j=0;j<f.Count;j++){
      if(!killed&&j==0)continue;var v=new int[f.Count];v[j]=1;if(!killed)v[0]=-1;b.Add(v);
    }return b;
  }
  public static string Check(int max) {
    int[][] ns={new[]{4,5,6,7},new[]{5,6,7,8},new[]{5,7,8,9},new[]{6,7,9,10},new[]{7,8,9,11},new[]{7,9,10,12}};
    int[] rho={6,5,5,6,4,6};
    int[][] budgets={new[]{0,0,0,1},new[]{1,1,1,1},new[]{1,1,1,1},new[]{0,1,1,2},new[]{0,1,1,1},new[]{0,1,1,1}};
    long mjChecks=0,kronecker=0;int cases=0,degrees=0,internalTags=0,externalTags=0;
    for(int model=0;model<ns.Length;model++){
      int[] n=ns[model];var full=new List<int[]>[max+1];var comp=new int[max+1][];
      for(int d=0;d<=max;d++){full[d]=Factors(n,d);comp[d]=Components(full[d]);}
      for(int i=0;i<4;i++){
        int[] tails=Enumerable.Range(0,4).Where(j=>j!=i).ToArray();int[] tn=tails.Select(j=>n[j]).ToArray();
        var tf=new List<int[]>[max+1];var kb=new List<int[]>[max+1];
        for(int d=0;d<=max;d++){tf[d]=Factors(tn,d);bool killed=d>=n[i]&&full[d-n[i]].Count>0;kb[d]=KernelBasis(tf[d],killed);}
        int[] sums=new int[2];int tagTotal=0,intTotal=0;
        for(int d=0;d<=max;d++){
          var f=tf[d];var dict=f.Select((u,j)=>new{u,j}).ToDictionary(x=>Key(x.u),x=>x.j);
          var mj=new List<int[]>();
          for(int j=0;j<3;j++)if(d>=tn[j]){
            int e=d-tn[j];foreach(var b in kb[e]){
              var v=new int[f.Count];for(int u=0;u<tf[e].Count;u++)if(b[u]!=0){var w=(int[])tf[e][u].Clone();w[j]++;v[dict[Key(w)]]+=b[u];}mj.Add(v);
            }
          }
          var tags=new List<int[]>();var detectors=new List<int[]>();
          int cc=comp[d].Length==0?0:comp[d].Max()+1;
          if(cc>1){
            int baseVertex=full[d].FindIndex(u=>u[i]>0);int root=baseVertex<0?0:comp[d][baseVertex];
            int rv=baseVertex<0?Array.FindIndex(comp[d],c=>c==root):baseVertex;
            for(int target=0;target<cc;target++)if(target!=root){
              int tv=Array.FindIndex(comp[d],c=>c==target);if(full[d][tv][i]!=0)throw new Exception("target uses base");
              var v=new int[f.Count];v[dict[Key(tails.Select(j=>full[d][tv][j]).ToArray())]]=-1;
              if(baseVertex<0){v[dict[Key(tails.Select(j=>full[d][rv][j]).ToArray())]]++;intTotal++;internalTags++;}else externalTags++;
              tags.Add(v);tagTotal++;
              var det=new int[f.Count];for(int u=0;u<f.Count;u++){
                var w=new int[4];for(int j=0;j<3;j++)w[tails[j]]=f[u][j];int ix=full[d].FindIndex(x=>Key(x)==Key(w));
                if(comp[d][ix]==target)det[u]=-1;
              }detectors.Add(det);
            }
          }
          for(int pi=0;pi<2;pi++){
            int p=pi==0?2:3;int mr=Rank(mj,f.Count,p);int jr=Rank(kb[d],f.Count,p);
            if(Rank(mj.Concat(kb[d]).ToList(),f.Count,p)!=jr)throw new Exception("mJ not subset J");
            if(jr-mr!=tags.Count)throw new Exception("actual quotient dimension != connectors");
            if(Rank(mj.Concat(tags).ToList(),f.Count,p)!=jr)throw new Exception("classes not independent/spanning actual quotient");
            sums[pi]+=jr-mr;degrees++;
            for(int t=0;t<detectors.Count;t++){
              foreach(var v in mj){if(Mod(detectors[t].Zip(v,(a,b)=>a*b).Sum(),p)!=0)throw new Exception("detector mJ failure");mjChecks++;}
              for(int h=0;h<tags.Count;h++){if(Mod(detectors[t].Zip(tags[h],(a,b)=>a*b).Sum(),p)!=(t==h?1:0))throw new Exception("Kronecker failure");kronecker++;}
            }
          }
        }
        if(tagTotal!=rho[model]||intTotal!=budgets[model][i]||sums.Any(x=>x!=rho[model]))throw new Exception("literal rho/budget control mismatch");
        cases+=2;
      }
    }
    return $"PASS Run27 independent actual J/mJ ranks: field-base cases={cases} degrees={degrees} mJ detector checks={mjChecks} Kronecker checks={kronecker} internal={internalTags} external={externalTags} maxDegree={max}; audit-only";
  }
}
'@
}
[P23Run27Ranks]::Check($MaxDegree)
