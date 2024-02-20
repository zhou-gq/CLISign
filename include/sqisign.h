
#ifndef SQISIGN_H
#define SQISIGN_H

#include <pari/pari.h>
#include "idiso.h"

typedef struct public_key {
  proj E;
} public_key;

typedef struct secret_key {
  GEN I_large_prime;
  GEN I_two;
  GEN I_T;
  special_isogeny phi_T;
  two_walk_long phi_two;
} secret_key;

typedef struct signature {
  proj E_com;
  two_walk_long sigma;
} signature;

typedef struct compressed_signature {
  proj E_com;
  uint64_t *zip;
} compressed_signature;

typedef struct user_sk
{
  two_walk_long sigma1;
  two_walk_long sigma2;
} user_sk;

typedef struct user_pk
{
  proj E1;
  proj E2;
  proj E3;
} user_pk;

typedef struct id_com
{
  odd_isogeny_long eta;
  proj F;

  two_walk_long sigma1;
  odd_isogeny_long eta1;
  proj F1;

  two_walk_long sigma2;
  odd_isogeny_long eta2;
  proj F2;
} id_com;

typedef struct id_res
{
  two_walk_long res1;
  two_walk_long res2;
  odd_isogeny_long res3;
  odd_isogeny_long res4;
} id_res;

typedef struct id_sig
{
  proj F;
  proj F1;
  proj F2;
  two_walk_long res1;
  two_walk_long res2;
  odd_isogeny_long res3;
  odd_isogeny_long res4;
} id_sig;





void init_compressed_sig(compressed_signature *comp_sigma);
void free_compressed_sig(compressed_signature *comp_sigma);
void keygen(public_key *pk, secret_key *sk);
void commitment(GEN *coeff, GEN *I, odd_isogeny *phi_com);
void challenge(proj *E_cha, const uintbig *m, const proj *E_com, const proj *basis_plus, const proj *basis_minus, GEN *dlog, proj *basis_two);
void response(two_walk_long *sigma, uint64_t *zip, GEN coeff_ker_challenge_commitment, const secret_key *sk, const proj *basis_two, const proj *E_cha);
void sign(compressed_signature *comp_sigma, const secret_key *sk, const public_key *pk, const uintbig *m);
void decompress(two_walk *walk, proj *A, const uint64_t *zip, long len,long last_step);
bool verif(compressed_signature *comp_sigma, const public_key *pk,const uintbig *m);

//msk is an secret isogeny from E0, mpk is the codomain EA of msk.
void CLI_keygen(public_key *mpk, secret_key *msk);

//sigma1 is an isogeny from EA of degree 2^1000, E1 is the codomain of sigma1.
// 包含初始化 sigma1
// need: pari_sp ltop = avma ?
void set_secret_val(two_walk_long *sigma1, proj *E1, const public_key *mpk);

// sigma2 is an isogeny from EA to E_cha of degree 2^1000, E3 = E_com, E2 = E_cha.
//不需要初始化sigma2
// need: pari_sp ltop = avma ?
void partial_key_ext(two_walk_long *sigma2, proj *E2, proj *E3, const public_key *mpk, const secret_key *msk,  const uintbig *ID, const proj *E1);
void set_user_key(user_sk *usk, user_pk *upk, const two_walk_long *sigma2, const proj *E2, const proj *E3, const two_walk_long *sigma1, const proj *E1);

void SIDH(proj *E_tar, two_walk_long *sigma1, odd_isogeny_long *eta1, const two_walk_long *sigma, const odd_isogeny_long *eta);
void id_commitment(id_com *com, const user_sk *usk, const public_key *mpk);
void id_challenge(long *cha);
void id_response(id_res *res, const id_com *com, const long *cha);
bool id_verify(const id_res *res, const id_com *com, const long *cha, const user_pk *upk, const public_key *mpk);
bool identification(const user_sk *usk, const user_pk *upk, const public_key *mpk);

void sig_sign(id_sig *SIG, const user_sk *usk, const user_pk *upk, const public_key *mpk, const uint64_t *m);
bool sig_verify(const id_sig *SIG, const user_pk *upk, const public_key *mpk, const uint64_t *m);

#endif
