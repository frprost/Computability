/* Number h(n) of Radó tables with n states (n = 1, 2, 3) that halt,
   starting on a tape of 0s in state A.
   Each transition (state, symbol read) has 4(n+1) choices:
   symbol written (0 or 1), move (L or R), next state (A.. or H).
   An n-state machine that halts does so in at most S(n) steps
   (S(1)=1, S(2)=6, S(3)=21, values proved in the busy beaver chapter):
   so we simulate S(n) steps and conclude.
   Compilation: cc -O2 castor_omega.c -o castor_omega */
#include <stdio.h>
#include <string.h>
int main(void){
  const int S[4]={0,1,6,21};
  for(int n=1;n<=3;n++){
    int k=4*(n+1), nt=2*n;
    long long total=1; for(int i=0;i<nt;i++) total*=k;
    long long h=0;
    int ch[6];
    for(long long m=0;m<total;m++){
      long long r=m; for(int i=0;i<nt;i++){ch[i]=r%k; r/=k;}
      unsigned char tape[64]; memset(tape,0,64);
      int pos=32, q=0, halted=0;
      for(int t=0;t<S[n];t++){
        int c=ch[2*q+tape[pos]];
        tape[pos]=c&1; pos+= (c&2)?1:-1;
        int nq=c>>2;               /* 0 = H, 1..n = states A.. */
        if(nq==0){halted=1;break;}
        q=nq-1;
      }
      h+=halted;
    }
    printf("n=%d  tables=%lld  halting=%lld\n",n,total,h);
  }
  return 0;
}
