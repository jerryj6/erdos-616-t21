/* REFEREE (independent) pairwise conflict checker. Written from the lemma statements; shares no code with w14_*.
   Input 1 (states): lines "var b o0 o1 o2 o3" (my own enumerated states, var = authors' CNF variable).
   Input 2: a DIMACS CNF; every binary clause "-x -y 0" is a claimed CONF clause; we test it.
   A pair of distinct non-base edges F (b1,o1,u1), F' (b2,o2,u2) is COMPATIBLE if some state pair and some integer
   overlap vector z_q = |F&F'&O_q| (max(0,o1+o2-|O_q|)..min), zU = |F&F'&U| (0..min(u1,u2)) satisfies ALL of:
     A    |F&F'| >= 5
     F1   for each q: F&F'&P_q nonempty
     SAME if F,F' are singles of base pair (i,j) of different types: no common point outside P_i u P_j (S(a)),
          a=|F&F'&(P_i\P_j)|>=2, c>=2 (W7-I), a+c>=5 (S(b))
     L    every set X of >=2 base edges with (cap X)&F&F' empty: |U X u F u F'| >= 61
     D1   (P_k,F) with |F&P_k|=5 and F&P_k not inside F': |F'&(P_k u F)| <= 9; and with F,F' swapped.
   Output: number of binary clauses checked, and every clause that is NOT a conflict (disagreement). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int MEMB[16][4];
static const char *NM[16]={"v","w","al0","al1","g0","g1","g2","m0","m1","m2","a3_0","a3_1","a4_0","a4_1","c3","c4"};
static int P[4], OSZ[4];
typedef struct { int b, o[4], u; } St;
static St *ST; static int *first, *cnt; static int NV;
static int pc(int x){ return __builtin_popcount(x); }
static void setup(void){
  /* regions by triple membership */
  for(int a=0;a<16;a++){ for(int q=0;q<4;q++) MEMB[a][q]=0;
    const char*s=NM[a]; int m[4]={0,0,0,0};
    if(!strcmp(s,"v")){m[0]=m[1]=m[2]=1;} else if(!strcmp(s,"w")){m[0]=m[1]=m[3]=1;}
    else if(!strncmp(s,"al",2)){m[0]=m[2]=m[3]=1;} else if(s[0]=='g'){m[1]=m[2]=m[3]=1;}
    else if(s[0]=='m'){m[0]=m[1]=1;} else if(!strncmp(s,"a3",2)){m[0]=m[2]=1;} else if(!strncmp(s,"a4",2)){m[0]=m[3]=1;}
    else if(!strcmp(s,"c3")){m[1]=m[2]=1;} else if(!strcmp(s,"c4")){m[1]=m[3]=1;}
    for(int q=0;q<4;q++) MEMB[a][q]=m[q]; }
  for(int q=0;q<4;q++){ P[q]=0; for(int a=0;a<16;a++) if(MEMB[a][q]) P[q]|=1<<a; OSZ[q]=21-pc(P[q]); }
  if(OSZ[0]!=10||OSZ[1]!=11||OSZ[2]!=12||OSZ[3]!=12){fprintf(stderr,"bad base\n");exit(1);}
}
static int feasible(const St*s1,const St*s2){
  int I=s1->b & s2->b;
  int lo[4],hi[4],z[4];
  for(int q=0;q<4;q++){ lo[q]=s1->o[q]+s2->o[q]-OSZ[q]; if(lo[q]<0)lo[q]=0; hi[q]=s1->o[q]<s2->o[q]?s1->o[q]:s2->o[q]; if(lo[q]>hi[q]) return 0; }
  int uh = s1->u<s2->u?s1->u:s2->u;
  /* SAME pairs */
  int samei[6],samej[6],ns=0;
  for(int i=0;i<4;i++)for(int j=i+1;j<4;j++){ int N=P[i]&P[j]; int x=s1->b&N,y=s2->b&N; if(pc(x)==1&&pc(y)==1&&x!=y){samei[ns]=i;samej[ns]=j;ns++;} }
  for(z[0]=lo[0];z[0]<=hi[0];z[0]++)for(z[1]=lo[1];z[1]<=hi[1];z[1]++)for(z[2]=lo[2];z[2]<=hi[2];z[2]++)for(z[3]=lo[3];z[3]<=hi[3];z[3]++)
  for(int zu=0;zu<=uh;zu++){
    int ok=1, zs=z[0]+z[1]+z[2]+z[3];
    if(pc(I)+zs+zu<5) ok=0;
    for(int q=0;ok&&q<4;q++) if(!(I&P[q]) && z[q]==0) ok=0;
    for(int t=0;ok&&t<ns;t++){ int i=samei[t],j=samej[t];
      if(I & ~(P[i]|P[j]) & 0xffff) ok=0;
      for(int q=0;q<4;q++) if(q!=i&&q!=j&&z[q]) ok=0;
      if(zu) ok=0;
      int a=pc(I&P[i]&~P[j])+z[i], c=pc(I&P[j]&~P[i])+z[j];
      if(a<2||c<2||a+c<5) ok=0; }
    for(int X=1;ok&&X<16;X++){ if(pc(X)<2) continue;
      int cap=0xffff,cup=0,ux=0; for(int q=0;q<4;q++) if(X>>q&1){cap&=P[q];cup|=P[q];ux+=OSZ[q];}
      if(cap&I) continue;
      ux+=pc(cup);
      int f1=pc(s1->b&~cup)+s1->u, f2=pc(s2->b&~cup)+s2->u, ov=pc(I&~cup)+zu;
      for(int q=0;q<4;q++) if(!(X>>q&1)){f1+=s1->o[q];f2+=s2->o[q];ov+=z[q];}
      if(ux+f1+f2-ov<61) ok=0; }
    for(int sw=0;ok&&sw<2;sw++){ const St*A=sw?s2:s1,*B=sw?s1:s2;
      for(int k=0;ok&&k<4;k++){ if(pc(A->b&P[k])+A->o[k]!=5) continue;
        int inside = ((A->b&P[k]&~B->b)==0) && z[k]==A->o[k];
        if(inside) continue;
        int val=pc(B->b&P[k])+B->o[k] + pc(I&~P[k]) + zu; for(int q=0;q<4;q++) if(q!=k) val+=z[q];
        if(val>9) ok=0; } }
    if(ok) return 1;
  }
  return 0;
}
int main(int argc,char**argv){
  setup();
  FILE*f=fopen(argv[1],"r"); int nst=0,cap=1<<17; ST=malloc(sizeof(St)*cap); int *var=malloc(sizeof(int)*cap); int maxv=0;
  int vv,b,o0,o1,o2,o3;
  while(fscanf(f,"%d %d %d %d %d %d",&vv,&b,&o0,&o1,&o2,&o3)==6){ if(nst==cap){cap*=2;ST=realloc(ST,sizeof(St)*cap);var=realloc(var,sizeof(int)*cap);}
    St s; s.b=b;s.o[0]=o0;s.o[1]=o1;s.o[2]=o2;s.o[3]=o3; s.u=21-pc(b)-o0-o1-o2-o3; ST[nst]=s; var[nst]=vv; nst++; if(vv>maxv)maxv=vv; }
  fclose(f); NV=maxv; first=calloc(NV+2,sizeof(int)); cnt=calloc(NV+2,sizeof(int));
  for(int i=0;i<nst;i++){ if(i>0 && var[i]<var[i-1]){fprintf(stderr,"unsorted\n");return 1;} if(!cnt[var[i]]) first[var[i]]=i; cnt[var[i]]++; }
  FILE*g=fopen(argv[2],"r"); char line[1<<20]; long nb=0,bad=0,other=0,novar=0;
  while(fgets(line,sizeof line,g)){ if(line[0]=='p'||line[0]=='c') continue;
    int l[4],k=0; char*p=line; char*e; long x;
    while(k<4){ x=strtol(p,&e,10); if(e==p) break; p=e; if(x==0) break; l[k++]=(int)x; }
    if(k!=2 || l[0]>0 || l[1]>0){ other++; continue; }
    int a=-l[0], c=-l[1]; nb++;
    if(a==c){ printf("SELF %d\n",a); bad++; continue; }
    if(a>NV||c>NV||!cnt[a]||!cnt[c]){ novar++; continue; }   /* a trace with no state in my universe: clause vacuous for me */
    int comp=0;
    for(int i=0;i<cnt[a]&&!comp;i++)for(int j=0;j<cnt[c]&&!comp;j++) comp=feasible(&ST[first[a]+i],&ST[first[c]+j]);
    if(comp){ bad++; printf("DISAGREE %d %d\n",a,c); }
    if(nb%200000==0){ fprintf(stderr,"%ld binary checked, bad %ld\n",nb,bad); }
  }
  printf("binary %ld bad %ld nonbinary %ld vacuous(no-state var) %ld\n",nb,bad,other,novar);
  return 0;
}
