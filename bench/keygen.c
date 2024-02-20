#define _XOPEN_SOURCE

#include <getopt.h>
#include <inttypes.h>
#include <stdio.h>
#include <time.h> 
#include <pari/pari.h>

#include "precomputed.h"
#include "sqisign.h"

static __inline__ uint64_t rdtsc(void)
{
    uint32_t hi, lo;
    __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
    return lo | (uint64_t) hi << 32;
}

int main(int argc, char **argv) {
  int samples = 8, seed = 1;
  
  int opt;
  while ((opt = getopt(argc, argv, "s:r:h")) != -1) {
    switch (opt) {
    case 's':
      samples = atoi(optarg);
      break;
    case 'r':
      seed = atoi(optarg);
      break;
    default:
      fprintf(stderr,
	      "Usage: %s [-s samples] [-r seed]\n",
	      argv[0]);
      exit(-1);
    }
  }
  
  pari_init(800000000, 1<<18);
  init_precomputations();
  
  setrand(mkintn(1, seed));
  srand48(seed);

  printf("### Keygen\n");
  printf("# cycles\tms\n");
  for (int i = 0; i < samples; i++) {
    //public_key pk;
    //secret_key sk;

    uintbig ID;
    uintbig_set(&ID,2022);

    public_key mpk;
    secret_key msk;
    two_walk_long sigma1;
    two_walk_long sigma2;
    proj E1;
    proj E2;
    proj E3;
    user_sk usk;
    user_pk upk;

    clock_t t = -clock();
    uint64_t c = -rdtsc();

    CLI_keygen(&mpk, &msk);

    set_secret_val(&sigma1, &E1, &mpk);

    partial_key_ext(&sigma2, &E2, &E3, &mpk, &msk, &ID, &E1);

    set_user_key(&usk, &upk, &sigma2, &E2, &E3, &sigma1, &E1);

    c += rdtsc();
    t += clock();

    printf("%" PRIu64 "\t%.3lf\n", c, 1000. * t / CLOCKS_PER_SEC);   
  }
    
  return 0;
}
