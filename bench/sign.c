#define _XOPEN_SOURCE

#include <getopt.h>
#include <inttypes.h>
#include <stdio.h>
#include <time.h>
#include <pari/pari.h>

#include "precomputed.h"
#include "sqisign.h"
#include "constants.h"

static __inline__ uint64_t rdtsc(void)
{
    uint32_t hi, lo;
    __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
    return lo | (uint64_t) hi << 32;
}

int main(int argc, char **argv) {
  int keys = 2, samples = 4, seed = 1;

  int opt;
  while ((opt = getopt(argc, argv, "k:s:r:h")) != -1) {
    switch (opt) {
    case 'k':
      keys = atoi(optarg);
      break;
    case 's':
      samples = atoi(optarg);
      break;
    case 'r':
      seed = atoi(optarg);
      break;
    default:
      fprintf(stderr,
	      "Usage: %s [-k keys] [-s samples] [-r seed]\n",
	      argv[0]);
      exit(-1);
    }
  }

  pari_init(800000000, 1<<18);
  init_precomputations();

  setrand(mkintn(1, seed));
  srand48(seed);

  printf("### Sign\n");
  printf("# key\tcycles\t\tms\t\tlength\n");
  for (int k = 0; k < keys; k++) {
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

    CLI_keygen(&mpk, &msk);
    set_secret_val(&sigma1, &E1, &mpk);
    partial_key_ext(&sigma2, &E2, &E3, &mpk, &msk, &ID, &E1);
    set_user_key(&usk, &upk, &sigma2, &E2, &E3, &sigma1, &E1);

    for (int i = 0; i < samples; i++) {
      // signature Sigma;
      //compressed_signature comp_sigma;
      //init_compressed_sig(&comp_sigma);
      //uintbig m;
      //randombytes(m.c, 32);

      id_sig SIG[CLI_round];
      uint64_t m[CLI_round];
      int th;
      for (th = 0; th < CLI_round; ++th) {
        randombytes(&(m[th]), 32);
      }
      

      clock_t t = -clock();
      uint64_t c = -rdtsc();

      //sign(&comp_sigma ,&sk, &pk, &m);
      sig_sign(SIG, &usk, &upk, &mpk, m);

      c += rdtsc();
      t += clock();

      //free_compressed_sig(&comp_sigma);

  //     int len = 0;
  //     for (int j = 0; j < Sigma.sigma.len; j++)
	// len += Sigma.sigma.phi[j].len;

      printf("%d\t%" PRIu64 "\t%.3lf\t%ld\n", k, c, 1000. * t / CLOCKS_PER_SEC, signing_length);
    }
  }

  return 0;
}
