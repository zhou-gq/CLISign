#define _XOPEN_SOURCE

#include <stdint.h>
//#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <pari/pari.h>
#include <assert.h>


#include "ideal.h"
#include "idiso.h"
#include "constants.h"
#include "precomputed.h"
#include "tedwards.h"
#include "isogenies.h"
#include "klpt.h"
#include "toolbox.h"
#include "sqisign.h"
// #include "isomorphism.h"
// #include "uintbig.h"


void init_compressed_sig(compressed_signature *comp_sigma) {
  comp_sigma->zip=malloc(sizeof(uint64_t)*signing_length_two_tors_height_step);
}

void free_compressed_sig(compressed_signature *comp_sigma) {
  free(comp_sigma->zip);
}

void keygen(public_key *pk, secret_key *sk) {

    unsigned int length_NI = security_level/2;
    unsigned int e_tau = (double)security_level*2;
    GEN NI = NULL;
    GEN NJ = powiu(gen_2, e_tau);

    do {
        NI = randomprime(powiu(gen_2, length_NI));
    } while (Fp_issquare(gen_2,NI));

    GEN gamma = NULL;
    while (!gamma) {
        // parity option is 1 so the 2-walk is not backtracking
        gamma = norm_equation_special(global_setup.p, gmul(NI,NJ), 1, true);
    }
    gamma = gtrans(gamma);

    sk->I_large_prime = lideal_create(global_setup.B, global_setup.O0, gamma, NI);
    sk->I_two = lideal_create(global_setup.B, global_setup.O0, alg_conj(global_setup.B, gamma), NJ);

    init_trivial_two_walk_long(&sk->phi_two);
    ideal_to_isogeny_O0_two_long(&sk->phi_two, &sk->I_T, &sk->phi_T, sk->I_two, true);


    if (!sk->phi_T.phi2_set) {
        assert(sk->phi_T.phi2_dual_set);
        sk->phi_T.phi2 = sk->phi_T.phi2_dual;
        sk->phi_T.middle = sk->phi_T.target;
        dual(&sk->phi_T.middle, &sk->phi_T.phi2);
        sk->phi_T.phi2_set = true;
    }

    if (!sk->phi_T.phi2_dual_set) {
        assert(sk->phi_T.phi2_set);
        sk->phi_T.phi2_dual = sk->phi_T.phi2;
        sk->phi_T.target = sk->phi_T.middle;
        dual(&sk->phi_T.target, &sk->phi_T.phi2_dual);
        sk->phi_T.phi2_dual_set = true;
    }

    pk->E = sk->phi_T.target;

}

void commitment(GEN *coeff, GEN *I, odd_isogeny *phi_com){
    pari_sp ltop = avma;

    GEN coeff_plus_1 = cgetg(p_plus_len+1, t_VEC);
    GEN coeff_plus_2 = cgetg(p_plus_len+1, t_VEC);
    GEN coeff_minus_1 = cgetg(p_minus_len+1, t_VEC);
    GEN coeff_minus_2 = cgetg(p_minus_len+1, t_VEC);

    for (int i = 0; i < p_plus_len; ++i) {
        gel(coeff_plus_1,i+1) = powuu(p_plus_fact[i], p_plus_mult[i] - p_plus_mult_com[i]);
        gel(coeff_plus_2,i+1) = randomi(powuu(p_plus_fact[i],p_plus_mult_com[i]));
        gel(coeff_plus_2,i+1) = gmul(gel(coeff_plus_2,i+1), gel(coeff_plus_1,i+1));

        gel(coeff_plus_1,i+1) = gmod(gel(coeff_plus_1,i+1), powuu(p_plus_fact[i],p_plus_mult[i]));
        gel(coeff_plus_2,i+1) = gmod(gel(coeff_plus_2,i+1), powuu(p_plus_fact[i],p_plus_mult[i]));
    }

    for (int i = 0; i < p_minus_len; ++i) {
        gel(coeff_minus_1,i+1) = powuu(p_minus_fact[i], p_minus_mult[i] - p_minus_mult_com[i]);;
        gel(coeff_minus_2,i+1) = randomi(powuu(p_minus_fact[i],p_minus_mult_com[i]));
        gel(coeff_minus_2,i+1) = gmul(gel(coeff_minus_2,i+1), gel(coeff_minus_1,i+1));

        gel(coeff_minus_1,i+1) = gmod(gel(coeff_minus_1,i+1), powuu(p_minus_fact[i],p_minus_mult[i]));
        gel(coeff_minus_2,i+1) = gmod(gel(coeff_minus_2,i+1), powuu(p_minus_fact[i],p_minus_mult[i]));
    }

    GEN coeff_plus = mkvec2(coeff_plus_1, coeff_plus_2);
    GEN coeff_minus = mkvec2(coeff_minus_1, coeff_minus_2);
    *coeff = mkvec2(coeff_plus, coeff_minus);

    *I = kernel_to_ideal_O0_T(*coeff);


    proj ker = coeff_to_E0(gel(*coeff,1), false);
    proj ker_twist = coeff_to_E0(gel(*coeff,2), true);
    isog_degree deg, deg_twist;
    famat_to_degree(&deg, &deg_twist, Z_factor(lideal_norm(*I)));

    phi_com->kernel_plus = ker;
    phi_com->kernel_minus = ker_twist;
    phi_com->deg_plus = deg;
    phi_com->deg_minus = deg_twist;

    gerepileall(ltop, 2, I, coeff);
}



void deterministic_point(proj *P, proj const *A, long ell, long e, bool twist, GEN seed) {
    pari_sp ltop = avma;
    GEN rand_state = getrand();
    setrand(seed);

    unsigned short newseed[3] = {1,2,3};
    unsigned short *oldptr = seed48(newseed);

    uintbig cofactor;
    uintbig_add3(&cofactor, &p, &uintbig_1);
    uintbig ell_big;
    uintbig_set(&ell_big, ell);
    for (int i = 0; i < e; ++i) {
        uintbig_div3_64(&cofactor, &cofactor, ell);
    }
    proj Z;

    while (1) {
        fp2_random(&P->x); fp2_random(&P->z);
        if (twist == is_on_curve(P, A)) continue;
        xMUL(P, A, P, &cofactor);
        Z = *P;
        for (int i = 0; i < e-1; ++i) {
            xMUL(&Z, A, &Z, &ell_big);
        }
        if (!fp2_iszero(&Z.z)) {
            // a final test
            xMUL(&Z, A, &Z, &ell_big);
            assert(fp2_iszero(&Z.z));
            return;
        }
    }

    setrand(rand_state);
    seed48(oldptr);
    avma = ltop;
}


void deterministic_basis(point *P1_ted, point *P2_ted, proj const *A, long ell, long e, bool twist) {
    proj P1, P2;
    point P1_mul, P2_mul, tmp;
    uintbig ell_big;
    uintbig_set(&ell_big, ell);
    fp2 weil;

    proj E;
    mont_to_ted(&E, A, twist);

    GEN seed = gen_1;

    deterministic_point(&P1, A, ell, e, twist, seed);

    seed = gadd(seed, gen_1);

    mont_to_ted_point(P1_ted, A, &P1);
    P1_mul = *P1_ted;
    for (int i = 0; i < e-1; ++i) {
        ted_mul(&P1_mul, &P1_mul, &E, &ell_big);
    }

    assert(ted_is_on_curve(&P1_mul,&E));
    assert(!ted_iszero(&P1_mul));
    ted_mul(&tmp, &P1_mul, &E, &ell_big);
    assert(ted_iszero(&tmp));

    do {
        deterministic_point(&P2, A, ell, e, twist, seed);
        mont_to_ted_point(P2_ted, A, &P2);
        P2_mul = *P2_ted;
        for (int i = 0; i < e-1; ++i) {
            ted_mul(&P2_mul, &P2_mul, &E, &ell_big);
        }
        assert(ted_is_on_curve(&P2_mul,&E));
        assert(!ted_iszero(&P2_mul));
        ted_mul(&tmp, &P2_mul, &E, &ell_big);
        assert(ted_iszero(&tmp));

        ted_weil(&weil, &E, &P1_mul, &P2_mul, &ell_big);
        fp2_sub2(&weil, &fp2_1);
        seed = gadd(seed, gen_1);
    } while (fp2_iszero(&weil));
}




bool mont_dlp(GEN *a, GEN *b, const proj *A, const proj *P, const proj *P1,
    const proj *P2, const proj *P1plusP2, long ell, long e, bool twist) {
    proj Q;
    proj E;
    point basis_ted[3], P_ted;
    mont_to_ted(&E, A, twist);

    mont_to_ted_point(&P_ted, A, P);
    mont_to_ted_point(&basis_ted[0], A, P1);
    mont_to_ted_point(&basis_ted[1], A, P2);

    ted_add(&basis_ted[2], &E, &basis_ted[0], &basis_ted[1]);
    ted_to_mont_point(&Q, &basis_ted[2]);
    if (!mont_equal(&Q, P1plusP2)) { ted_neg(&basis_ted[1], &basis_ted[1]); }
    ted_add(&basis_ted[2], &E, &basis_ted[0], &basis_ted[1]);
    ted_to_mont_point(&Q, &basis_ted[2]);
    assert(mont_equal(&Q, P1plusP2));

    return ted_bidim_log(a, b, &E, &P_ted, &basis_ted[0], &basis_ted[1], ell, e);
}


//in fact only work for ell=2
bool mont_power_dlp(uint64_t *a,const proj *A, const proj *Q, const proj *P,const proj *PQ,long e) {
  return mont_two_DLP(a,A,Q,P,PQ,e);
}


// PRF to generate points
static void hash(proj *P, int i) {
  uintbig_set(&P->x.re.x, 3 * i + 13);
  uintbig_set(&P->z.re.x, 5 * i * i + 17);
  uintbig_set(&P->x.im.x, 7 * i * i * i + 19);
  uintbig_set(&P->z.im.x, 11 * i * i * i + 23);
}

// Find a basis of the 2-torsion of A, deterministically
//
// Outputs x(P), x(Q) and x(P-Q) of a basis (P,Q) such that [2^(n-1)]P
// = (0,0).
//
// Assumes the curve A has order p+1
static void find_basis(proj *P, proj *Q, proj *PQ, proj *A) {
  bool oncurve = class_mod_4 == 3;
  proj P2, Q2, tmp;
  long cnt = 1;

    //normalize for deterministic computation
    normalize_proj(A);

  // Get first point
  while (true) {
    hash(P, cnt++);
    if (is_on_curve(P, A) != oncurve)
      continue;
    // multiply by cofactor
    xMUL(P, A, P, &p_even_cofactor);
    // check it has maximal order
    P2 = *P;
    for (int i = 1; i < two_tors_height; i++)
      xDBL(&P2, A, &P2);
    if (!mont_iszero(&P2))
      break;
  }

  // Get linearly independent point
  while (true) {
    hash(Q, cnt++);
    if (is_on_curve(Q, A) != oncurve)
      continue;
    // multiply by cofactor
    xMUL(Q, A, Q, &p_even_cofactor);
    // check it has maximal order
    Q2 = *Q;
    for (int i = 1; i < two_tors_height; i++)
      xDBL(&Q2, A, &Q2);
    if (!mont_iszero(&Q2) && !mont_equal(&Q2, &P2))
      break;
  }

  // Compute P-Q
  xBILIFT(PQ, &tmp, P, Q, A);

  // Shuffle to satisfy constraint
  if (fp2_iszero(&P2.x)) {
  } else if (fp2_iszero(&Q2.x)) {
    fp2_cswap(&P->x, &Q->x, true);
    fp2_cswap(&P->z, &Q->z, true);
  } else {
    fp2_cswap(&P->x, &PQ->x, true);
    fp2_cswap(&P->z, &PQ->z, true);
  }
}


//renormalize the two walk into a walk of step having length two_tors_height
long normalized_walk(two_walk *w,uint64_t *zip, long *n) {
  long tot = 0;
  for (int i=0;i<*n;i++) {
    tot+=w[i].len;
  }
  long step= tot / two_tors_height;
  long add_step=1;
  if (tot == step*two_tors_height) {
    add_step=0;
  }
  long index_w = 0;
  two_walk norm_walk[step+add_step];
  // proj Pc[step+add_step],Qc[step+add_step],PQc[step+add_step],Ac[step+add_step];
  while ( w[index_w].len == two_tors_height ) {
    norm_walk[index_w]=w[index_w];
    //this computes a basis <P,Q> and the value log such that the kernel is generated by
    // P + log*Q
    // currently the algorithm is pushing the basis through and computing a DLP
    // for this one we already have the kernel but doing a bidimensionnal DLP appears difficult
    // as we would need some extra point (the difference between the kernel and the points of the basis ?)
    proj P1,P2,P3,dummy_A;
    find_basis(&P1,&P2,&P3,&w[index_w].A);
    proj push_points[3];
    push_points[0]=P2;
    push_points[1]=P1;
    push_points[2]=P3;
    eval_walk_mult(&w[index_w],&dummy_A,push_points,3);
    // what we do when P is the kernel generator ?
    bool dlp=mont_power_dlp(&(zip[index_w]),&dummy_A,&(push_points[0]),&(push_points[1]),&(push_points[2]),two_tors_height);
    zip[index_w]=pow(2,two_tors_height) - zip[index_w];
    assert(dlp);

    index_w++;
    isomorphism isom;
    mont_isom(&isom,&w[index_w].A,&dummy_A);
    mont_isom_apply(&isom,&w[index_w].ker);
  }

  proj A = w[index_w].A;
  proj P = w[index_w].ker;
  long order_P = w[index_w].len;
  assert(mont_equal(&A,&w[index_w].A));


  for (int index=index_w; index < step; index++ ){
    norm_walk[index].A=A;
    norm_walk[index].len=two_tors_height;
    proj P1,P2,P3;
    proj dummy_A;
    find_basis(&P1,&P2,&P3,&A);
    #ifndef NDEBUG
    proj test_order;
    test_order=P1;
    for (int i=1;i<two_tors_height; i++) {
      xDBL(&test_order,&A,&test_order);
    }
    assert(!mont_iszero(&test_order));
    xDBL(&test_order,&A,&test_order);
    assert(mont_iszero(&test_order));
    uint64_t a;
    assert(!mont_power_dlp(&a,&A,&P2,&P1,&P3,two_tors_height));
    uintbig log_test;
    long mult_fac=55;
    uint64_t x_test;
    uintbig_set(&log_test,mult_fac);
    proj test_point,test_pt2;
    xMUL(&test_point,&A,&P1,&log_test);
    uintbig_set(&log_test,mult_fac+1);
    xMUL(&test_pt2,&A,&P1,&log_test);

    assert(mont_power_dlp(&x_test,&A,&test_point,&P1,&test_pt2,two_tors_height));
    #endif

    long w_step=1;
    long remain_step = order_P;
    while (remain_step+w[index_w + w_step].len <two_tors_height) {
      remain_step+=w[index_w+w_step].len;
      w_step++;
    }
    two_walk loc_phi[w_step+1];
    loc_phi[0].A = A;
    loc_phi[0].ker=P;
    loc_phi[0].len =order_P;


    if (w_step > 1) {
      for (int i=1; i < w_step ;i++){
        loc_phi[i] = w[index_w+i];
      }
    }
    remain_step = two_tors_height - remain_step;

    if (remain_step == w[index_w+w_step].len) {
        loc_phi[w_step] = w[index_w+w_step];
        index_w += w_step+1;
        order_P = w[index_w].len;
        P = w[index_w].ker;
    }
    else {
      loc_phi[w_step].A = w[index_w+w_step].A;
      loc_phi[w_step].len=remain_step;
      xDBL(&loc_phi[w_step].ker,&w[index_w+w_step].A,&w[index_w+w_step].ker);
      for (int i=0; i < w[index_w+w_step].len - remain_step -1 ; i++ ) {
        xDBL(&loc_phi[w_step].ker,&w[index_w+w_step].A,&loc_phi[w_step].ker);
      }
      index_w += w_step;
      order_P = w[index_w].len - remain_step;
      P=w[index_w].ker;
      isomorphism isom;
      eval_walk_isom_mult(&isom,&(loc_phi[w_step]), &dummy_A,&(loc_phi[w_step]),&P,1);
    }
    proj push_points[3];
    push_points[0]=P2;push_points[1]=P1;push_points[2]=P3;

    for (int i=0; i < w_step +1 ;i ++) {
      long log;
      isomorphism isom;
      eval_walk_isom_mult(&isom,&(loc_phi[i]),&A,&(loc_phi[i]),push_points,3);
      if (i != w_step) {
        isomorphism isom;
        mont_isom(&isom,&loc_phi[i+1].A,&A);
        mont_isom_apply(&isom,&loc_phi[i+1].ker);
        loc_phi[i+1].A=A;
      }
      if (i == w_step) {
        isomorphism isom;
        mont_isom(&isom,&dummy_A,&A);
        mont_isom_apply(&isom,&P);
      }
    }
    uintbig x,y;

    if (mont_iszero(&(push_points[0])) ) {
      uintbig_set(&x,1);
      uintbig_set(&y,0);
    }
    if (mont_iszero(&(push_points[1])) ){
      uintbig_set(&x,0);
      uintbig_set(&y,1);
    }
    else {
      uintbig_set(&x,1);
      bool dlp =mont_power_dlp(&(zip[index]),&A,&(push_points[0]),&(push_points[1]),&(push_points[2]),two_tors_height );
      zip[index]=pow(2,two_tors_height) - zip[index];
      uintbig_set(&y,zip[index]);
      assert(dlp);
      #ifndef NDEBUG
      proj verif_dlp;
      verif_dlp=push_points[1];
      xMUL(&verif_dlp,&A,&verif_dlp,&y);
      assert(mont_equal(&verif_dlp,&(push_points[0])));
      #endif
    }

    xBIDIM(&norm_walk[index].ker,&(loc_phi[0].A),&P2,&x,&P1,&y,&P3);
    isomorphism isom;
    proj A_target;
    eval_walk_isom(&isom,&norm_walk[index],&A_target,NULL,&norm_walk[index],NULL);
    #ifndef NDEBUG
    proj verif=P;
    for (int i=1; i < order_P; i++) {
      xDBL(&verif,&A,&verif);
    }
    assert(!mont_iszero(&verif));
    xDBL(&verif,&A,&verif);
    assert(mont_iszero(&verif));
    proj proj_tmp = {fp2_1, fp2_0};
    proj j1,j2;
    jinv256(&j1,&A);
    jinv256(&j2,&A_target);
    assert(mont_equal(&j1, &j2));
    #endif

  }

  if (add_step == 1){
    norm_walk[step].A=A;
    norm_walk[step].ker=P;
    norm_walk[step].len=order_P;

    //compute the compression coeff for the last one
    isomorphism isom;

    proj P1,P2,P3,A_target;
    find_basis(&P1,&P2,&P3,&A);
    two_walk phi_test;
    phi_test.A=A;
    phi_test.len=order_P;
    proj push_points[3];
    push_points[0]=P2;
    push_points[1]=P1;
    push_points[2]=P3;
    for (int i=0;i < two_tors_height - order_P; i++) {
      for (int j=0; j<3; j++){
        xDBL(&(push_points[j]),&A,&(push_points[j]));
      }
    }
    P1=push_points[1];
    P2=push_points[0];
    P3=push_points[2];
    eval_walk_isom_mult(&isom,&norm_walk[step],&A_target,&norm_walk[step],push_points,3);
    //what we do when P1 is the kernel generator ?
    bool dlp=mont_power_dlp(&zip[step],&A_target,&(push_points[0]),&(push_points[1]),&(push_points[2]),order_P);
    zip[step]= pow(2,order_P) - zip[step];
    assert(dlp);
    #ifndef NDEBUG
    proj A_test;
    uintbig a;
    uintbig_set(&a,zip[step]);
    xBIDIM(&phi_test.ker,&phi_test.A,&P1,&a,&P2,&uintbig_1,&P3);
    isomorphism isom2;
    eval_walk_isom(&isom2,&phi_test,&A_test,NULL,&phi_test,NULL);
    proj j1,j2;
    jinv256(&j1,&A_target);
    jinv256(&j2,&A_test);
    assert(mont_equal(&j1,&j2));
    #endif

  }

  for ( int i=0; i<step+add_step; i++){
    w[i]=norm_walk[i];
  }
  *n=step+add_step;

  #ifndef NDEBUG
  uintbig a;
  proj Q, PQ;
  A=w[0].A;
  two_walk walk[step+add_step];
  for (int i = 0; i < step; i++) {
    uintbig_set(&a, zip[i] );
    // get the next kernel
    find_basis(&P, &Q, &PQ, &A);  // TODO: use point Q from previous step + hint

    xBIDIM(&(walk[i].ker), &A, &P, &a, &Q, &uintbig_1, &PQ);
    walk[i].A = A;
    walk[i].len = two_tors_height;
    // take the next step
    isomorphism isom;
    eval_walk_isom(&isom,&walk[i], &A, NULL,&walk[i],NULL);
    proj j1,j2;
    jinv256(&j1,&A);
    jinv256(&j2,&w[i+1].A);
    assert(mont_equal(&j1,&j2));
  }
  #endif

  return order_P;

}



void challenge(proj *E_cha, const uintbig *m, const proj *E_com, const proj *basis_plus, const proj *basis_minus, GEN *dlog, proj *basis_two){
    pari_sp ltop = avma;

    odd_isogeny phi;
    proj A = *E_com;
    long index;
    bool twist;
    uintbig k;
    long ell;
    proj H, P, Z;

    uintbig_set(&H.x.re.x, m->c[0]);
    uintbig_set(&H.x.im.x, m->c[1]);
    uintbig_set(&H.z.re.x, m->c[2]);
    uintbig_set(&H.z.im.x, m->c[3]);


    /*
    uintbig k1,k2,k3;
    //k1 = 2^33
    uintbig_set(&k1, (uint64_t)pow(2,33));
    //k2 = 5^20
    uintbig_set(&k2, (uint64_t)pow(5,20));
    //k3 = 5^21
    uintbig_set(&k3, (uint64_t)pow(5,21));
    //set p_minus_2_3 = 2 * 3^53
    uintbig p_minus_2_3;
    uintbig_set(&p_minus_2_3, 2*(uint64_t)pow(3,26));
    uintbig_mul3_64(&p_minus_2_3,&p_minus_2_3, (uint64_t)pow(3,27));
    //set p_minus_2_3_cofactor 
    uintbig p_minus_2_3_cofactor={1,0,0,0};
    for (int i = 1; i < p_minus_len; ++i) {
        ell = p_minus_fact[i];
        for (int j=0; j < p_minus_mult[i]; ++j) {
            uintbig_mul3_64(&p_minus_2_3_cofactor,&p_minus_2_3_cofactor, ell);
        }
    }

    uintbig p_plus_2_5_cofactor={1,0,0,0};
    for (int i = 1; i < p_plus_len; ++i) {
        ell = p_plus_fact[i];
        for (int j=0; j < p_plus_mult[i]; ++j) {
            uintbig_mul3_64(&p_plus_2_5_cofactor,&p_plus_2_5_cofactor, ell);
        }
    }
    */



    uintbig cofactor_plus = {1,0,0,0}, cofactor_minus = {1,0,0,0};
    uintbig order_plus = {1,0,0,0}, order_minus = {1,0,0,0};
    isog_degree deg;
    degree_one(&deg);


    // compute cofactor and degree of the 'plus' part
    for (int i = 0; i < p_plus_len; ++i) {
        ell = p_plus_fact[i];
        for (int j = 0; j < p_plus_mult[i] - p_plus_mult_cha[i]; ++j){
            uintbig_mul3_64(&cofactor_plus, &cofactor_plus, ell);
        }
        for (int j = 0; j < p_plus_mult_cha[i]; ++j){
            uintbig_mul3_64(&order_plus, &order_plus, ell);
            index = ell_to_index(p_plus_fact[i], &twist);
            degree_set(&deg, index, p_plus_mult_cha[i]);
        }

    }

    bool bad;


    // find the 'plus' part of the kernel
    while (1) {
        fp_add2(&H.z.re, &fp_1);
        if (!is_on_curve(&H, E_com)) continue;

        /*
        Z=H;
        xMUL(&Z, &E_com, &Z, &p_minus_2_3);
        xMUL(&Z, &E_com, &Z, &p_minus_2_3_cofactor);
        xMUL(&Z, &E_com, &Z, &p_plus_2_5_cofactor);
        xMUL(&Z, &E_com, &Z, &k1); //k1=2^33
        xMUL(&Z, &E_com, &Z, &k3); //k3=5^21
        if (mont_iszero(&Z)) {
             printf("[p^2-1] P = O !\n");
            break;
        }
        else {
            printf("???\n");
            break;
        }
        */

        xMUL(&P, E_com, &H, &cofactor_plus);
        xMUL(&P, E_com, &P, &p_plus_odd_cofactor);

        bad = false;
        for (int i = 0; i < p_plus_len; ++i) {
            if (p_plus_mult_cha[i] > 0) {
                ell = p_plus_fact[i];
                Z = P;
                uintbig_div3_64(&k, &order_plus, ell);

                xMUL(&Z, E_com, &Z, &k);
                if (mont_iszero(&Z)) { bad = true; break; }

                #ifndef NDEBUG
		            uintbig ell_big;
                uintbig_set(&ell_big, ell);
                xMUL(&Z, E_com, &Z, &ell_big);
                assert(mont_iszero(&Z));
                #endif
            }
        }
        if (bad) continue;
        else break;

    }

    GEN dlog_plus = NULL;
    if (basis_plus) {
        long len = p_plus_len;
        GEN coeff_1 = cgetg(len+1, t_VEC);
        GEN coeff_2 = cgetg(len+1, t_VEC);
        proj Q;
        for (int i = 0; i < len; ++i) {

            gel(coeff_1,i+1) = gen_0;
            gel(coeff_2,i+1) = gen_0;

            if (0 < p_plus_mult_cha[i]) {
                GEN a,b;
                bool dlp = mont_dlp(&a, &b, &A, &P, &basis_plus[0], &basis_plus[1], &basis_plus[2],
                    p_plus_fact[i], p_plus_mult_cha[i], false);
                assert(dlp);
                gel(coeff_1,i+1) = a;
                gel(coeff_2,i+1) = b;
            }
        }

        dlog_plus = mkvec2(coeff_1, coeff_2);

        GEN dlog_plus_composed = torsion_crt_compose(dlog_plus, false);

        uintbig a_big, b_big;
        gentobig(&a_big, gel(dlog_plus_composed, 1));
        gentobig(&b_big, gel(dlog_plus_composed, 2));
        xBIDIM(&Q, &A, &basis_plus[0], &a_big, &basis_plus[1], &b_big, &basis_plus[2]);
        assert(mont_equal(&Q,&P));

    }




    phi.kernel_plus = P;
    phi.kernel_minus.x = fp2_1;
    phi.kernel_minus.z = fp2_0;
    phi.deg_plus = deg;
    phi.deg_minus.val = 0;


    long len_points = (basis_plus) ? 3 : 1;
    if (basis_two) len_points += 3;

    proj points[len_points];
    points[0] = P;

    if (basis_minus) {
        points[0] = basis_minus[0];
        points[1] = basis_minus[1];
        points[2] = basis_minus[2];
    }
    if (basis_two) {
        points[3] = basis_two[0];
        points[4] = basis_two[1];
        points[5] = basis_two[2];
    }


    eval_mult(&A, &phi, points, len_points);


    // compute cofactor and degree of the 'minus' part
    for (int i = 0; i < p_minus_len; ++i) {
        ell = p_minus_fact[i];
        for (int j = 0; j < p_minus_mult[i] - p_minus_mult_cha[i]; ++j){
            uintbig_mul3_64(&cofactor_minus, &cofactor_minus, ell);
        }
        for (int j = 0; j < p_minus_mult_cha[i]; ++j){
            uintbig_mul3_64(&order_minus, &order_minus, ell);
            index = ell_to_index(p_minus_fact[i], &twist);
            degree_set(&deg, index, p_minus_mult_cha[i]);
        }

    }

    // find the 'minus' part of the kernel
    while (1) {
        fp_add2(&H.x.re, &fp_1);
        if (is_on_curve(&H, &A)) continue;
        xMUL(&P, &A, &H, &cofactor_minus);
        xMUL(&P, &A, &P, &p_minus_odd_cofactor);


        bad = false;
        for (int i = 0; i < p_minus_len; ++i) {
            if (p_minus_mult_cha[i] > 0) {
                ell = p_minus_fact[i];
                Z = P;
                uintbig_div3_64(&k, &order_minus, ell);

                xMUL(&Z, &A, &Z, &k);
                if (mont_iszero(&Z)) { bad = true; break; }

                #ifndef NDEBUG
		uintbig ell_big;
                uintbig_set(&ell_big, ell);
                xMUL(&Z, &A, &Z, &ell_big);
                assert(mont_iszero(&Z));
                #endif
            }
        }
        if (bad) continue;
        else break;
    }


    GEN dlog_minus = NULL;
    if (basis_minus) {
        long len = p_minus_len;
        GEN coeff_1 = cgetg(len+1, t_VEC);
        GEN coeff_2 = cgetg(len+1, t_VEC);
        proj Q;
        for (int i = 0; i < len; ++i) {

            gel(coeff_1,i+1) = gen_0;
            gel(coeff_2,i+1) = gen_0;

            if (0 < p_minus_mult_cha[i]) {
                GEN a,b;


                bool dlp = mont_dlp(&a, &b, &A, &P, &points[0], &points[1], &points[2],
                    p_minus_fact[i], p_minus_mult_cha[i], true);
                assert(dlp);
                gel(coeff_1,i+1) = a;
                gel(coeff_2,i+1) = b;
            }
        }



        dlog_minus = mkvec2(coeff_1, coeff_2);

        GEN dlog_minus_composed = torsion_crt_compose(dlog_minus, true);

        uintbig a_big, b_big;
        gentobig(&a_big, gel(dlog_minus_composed, 1));
        gentobig(&b_big, gel(dlog_minus_composed, 2));
        xBIDIM(&Q, &A, &points[0], &a_big, &points[1], &b_big, &points[2]);
        assert(mont_equal(&Q,&P));

    }


    len_points = (basis_two) ? 3 : 1;

    if (basis_two) {
        points[0] = points[3];
        points[1] = points[4];
        points[2] = points[5];
    }

    phi.kernel_minus = P;
    phi.kernel_plus.x = fp2_1;
    phi.kernel_plus.z = fp2_0;
    phi.deg_minus = deg;
    phi.deg_plus.val = 0;
    eval_mult(&A, &phi, points, len_points);

    if (basis_two) {
        basis_two[0] = points[0];
        basis_two[1] = points[1];
        basis_two[2] = points[2];
    }

    *E_cha = A;

    if (dlog) { *dlog = gerepilecopy(ltop, mkvec2(dlog_plus, dlog_minus)); }

    //seed48(oldptr);
    //avma = ltop;
}

//function to test the decompression
void decompress(two_walk *walk, proj *A, const uint64_t *zip, long len,long last_step) {
  long mask = (1 << two_tors_height) - 1;
  long hint_mask = (0xf << two_tors_height);
  uintbig a;
  proj P, Q, PQ;
  for (int i = 0; i < len-1; i++) {
    // printf("zip %ld ",zip[i]);

    uintbig_set(&a, zip[i]);
    long hint = (zip[i] & hint_mask) >> two_tors_height;
    // get the next kernel
    find_basis(&P, &Q, &PQ, A);  // TODO: use point Q from previous step + hint
    xBIDIM(&(walk[i].ker), A, &P, &a, &Q, &uintbig_1, &PQ);
    walk[i].A = *A;
    walk[i].len = two_tors_height;
    // take the next step
    isomorphism isom;
    eval_walk_isom(&isom,&walk[i], A, NULL,&walk[i],NULL);
  }
  //last step of smaller size
  uintbig_set(&a, zip[len-1]);
  long hint = (zip[len-1] & hint_mask) >> two_tors_height;
  // get the next kernel
  find_basis(&P, &Q, &PQ, A);
  for (int i=0; i < two_tors_height - last_step ; i++){
    xDBL(&P,A,&P);
    xDBL(&Q,A,&Q);
    xDBL(&PQ,A,&PQ);
  }
  xBIDIM(&walk[len-1].ker, A, &P, &a, &Q, &uintbig_1, &PQ);
  walk[len-1].A = *A;
  walk[len-1].len = last_step;
  isomorphism isom;
  eval_walk_isom(&isom,&walk[len-1],A,NULL,&walk[len-1], NULL);
}

// basis_two is the image of the basis of the two torsion through phi_com and phi_cha
void response(two_walk_long *sigma, uint64_t *zip,  GEN coeff_ker_challenge_commitment, const secret_key *sk, const proj *basis_two, const proj *E_cha){
    pari_sp ltop = avma;
    GEN A = global_setup.B;
    GEN order = global_setup.O0;

    GEN I = sk->I_large_prime;
    GEN I_two = sk->I_two;

    // STEP 1: compute the ideal of phi_challenge_commitment
    GEN I_phipsi = kernel_to_ideal_O0_T(coeff_ker_challenge_commitment);
    // STEP 2: find J of norm a power of two such that J inter I is equivalent to I_phipsi
    GEN beta = lideal_isom(I_two, I); // I_two*beta = I
    GEN alpha = gmul(beta, lideal_norm(I_two)); // n(alpha) = n(I)
    GEN gamma = lideal_generator_coprime(I_phipsi, gmul(gen_2, lideal_norm(I)));
    GEN generator = algmul(A, gamma, alpha);
    GEN norm = gmul(lideal_norm(I_two), lideal_norm(I_phipsi));
    GEN K = lideal_create(A, order, generator, norm);

    assert(lideal_isom(I_phipsi, lideal_inter(K,I))); // K inter I is equivalent to I_phipsi


    GEN J;
    GEN n;
    do{
        J = klpt_general_power(I, K, gen_2); // J inter I is equivalent to I_phipsi
        alg_primitive(&n, A, order, algmul(A, lideal_generator(J), lideal_generator(I_two)));

        // backtracking?
    } while(gcmp(n,gen_1) != 0);

    // STEP 3: compute L of norm n(J) such that L inter sk->I_T is equivalent to I_phipsi

    GEN L = lideal_inter(J,I);
    assert(lideal_isom(I_phipsi, L));

    beta = lideal_isom(I, sk->I_T); // I*beta = I_T;

    L = lideal_mul(L,beta);

    assert(lideal_isom(I_phipsi, L));
    assert(gcmp(lideal_norm(L), gmul(lideal_norm(sk->I_T), lideal_norm(J))) == 0);


    GEN dummy_ideal;
    special_isogeny dummy_isogeny;

    // STEP 4: convert to an isogeny


    #ifndef NDEBUG
    alg_primitive(&n, A, order, algmul(A, lideal_generator(L), lideal_generator(sk->I_two)));
    assert(gcmp(n,gen_1) == 0);
    #endif

    long delta = 14;
    long len_tail = two_tors_height + delta;
    GEN L_cut = lideal_create(A, order, lideal_generator(L), shifti(lideal_norm(L), -len_tail));

    ideal_to_isogeny_two(sigma, &dummy_ideal, &dummy_isogeny, L_cut, sk->I_T, sk->I_two, &sk->phi_T, &sk->phi_two, false);

    GEN gen_tail = lideal_isom(L, I_phipsi); // L*gen_tail = I_phipsi;
    gen_tail = gmul(gen_tail, lideal_norm(L));
    GEN L_tail = lideal_create(A, order, gen_tail, powuu(2,two_tors_height));

    two_walk phi_tail_dual;
    phi_tail_dual.A = *E_cha;
    phi_tail_dual.len = two_tors_height;

    GEN v_tail = ideal_to_kernel_O0_ell(L_tail, 2);
    uintbig x, y;
    gentobig(&x, gel(v_tail,1));
    gentobig(&y, gel(v_tail,2));

    xBIDIM(&phi_tail_dual.ker, &phi_tail_dual.A, &basis_two[0], &x, &basis_two[1], &y, &basis_two[2]);


    isomorphism isom;
    proj L_cut_target, phi_tail_dual_target, proj_tmp = {fp2_1, fp2_0};
    eval_walk(&sigma->phi[sigma->len-1], &L_cut_target, &proj_tmp);

    eval_walk_isom(&isom, &phi_tail_dual, &phi_tail_dual_target, NULL, &phi_tail_dual, NULL);

    two_walk eta;

    bool done;

    proj from = L_cut_target;
    proj to = phi_tail_dual_target; // phi_2 source

    done = MITM(&eta, &from, &to, delta);
    assert(done);

    two_walk phi_tail = phi_tail_dual;
    dual_walk(&phi_tail);

    two_walk_composition_sl(sigma, &eta, sigma);
    two_walk_composition_sl(sigma, &phi_tail, sigma);

    normalized_walk(sigma->phi,zip,&(sigma->len));

    avma = ltop;
}


bool simple_check_signature(const two_walk_long *sigma, const uint64_t *zip, const public_key *pk, proj *E_cha) {
    proj j1,j2,j3;
    jinv256(&j1, &pk->E);
    jinv256(&j2, &sigma->phi[0].A);
    assert(mont_equal(&j1, &j2));

    proj sigma_target = sigma->phi[0].A, proj_tmp = {fp2_1, fp2_0};
    for (int i = 0; i < sigma->len; ++i) {
        jinv256(&j1, &sigma_target);
        jinv256(&j2, &sigma->phi[i].A);
        if (!mont_equal(&j1, &j2)) return false;
        sigma_target = sigma->phi[i].A;
        eval_walk(&sigma->phi[i], &sigma_target, &proj_tmp);
    }

    jinv256(&j1, &sigma_target);
    jinv256(&j2, E_cha);
    normalize_proj(&j2);
    proj A_target=(sigma->phi)[0].A;
    two_walk check[sigma->len];
    long last_step= sigma->phi[sigma->len-1].len;
    decompress(check,&A_target,zip,(sigma->len),last_step);
    jinv256(&j3, &A_target);
    return (mont_equal(&j1, &j2) && mont_equal(&j1,&j3));
}




void sign(compressed_signature *comp_sigma, const secret_key *sk, const public_key *pk, const uintbig *m) {
    pari_sp ltop = avma;

    GEN coeff_com, I_com;
    odd_isogeny phi_com;
    proj E_cha;


    commitment(&coeff_com, &I_com, &phi_com);

    comp_sigma->E_com = global_setup.E0;


    // compute the image of a basis of the torsion used for the challenge

    proj points[9];
    points[0] = torsion_basis_sum[0];
    points[1] = torsion_basis_sum[1];
    points[2] = torsion_basis_sum[2];
    points[3] = torsion_basis_twist_sum[0];
    points[4] = torsion_basis_twist_sum[1];
    points[5] = torsion_basis_twist_sum[2];
    points[6] = torsion_basis_two[0];
    points[7] = torsion_basis_two[1];
    points[8] = torsion_basis_two[2];

    eval_mult(&comp_sigma->E_com, &phi_com, points, 9);

    proj basis_plus[3], basis_minus[3], basis_two[3];
    basis_plus[0] = points[0];
    basis_plus[1] = points[1];
    basis_plus[2] = points[2];
    basis_minus[0] = points[3];
    basis_minus[1] = points[4];
    basis_minus[2] = points[5];
    basis_two[0] = points[6];
    basis_two[1] = points[7];
    basis_two[2] = points[8];

    uintbig ell_big;
    for (int i = 0; i < p_plus_len; ++i) {
        uintbig_set(&ell_big, p_plus_fact[i]);
        for (int j = 0; j < p_plus_mult[i] - p_plus_mult_cha[i]; ++j){
            for (int l = 0; l < 3; ++l) {
                xMUL(&basis_plus[l], &comp_sigma->E_com, &basis_plus[l], &ell_big);
            }
        }
    }

    for (int i = 0; i < p_minus_len; ++i) {
        uintbig_set(&ell_big, p_minus_fact[i]);
        for (int j = 0; j < p_minus_mult[i] - p_minus_mult_cha[i]; ++j){
            for (int l = 0; l < 3; ++l) {
                xMUL(&basis_minus[l], &comp_sigma->E_com, &basis_minus[l], &ell_big);
            }
        }
    }


    GEN dlog;

    challenge(&E_cha, m, &comp_sigma->E_com, basis_plus, basis_minus, &dlog, basis_two);

    GEN coeff_ker_challenge_commitment = gadd(coeff_com,dlog);


    #ifndef NDEBUG

    odd_isogeny phi_test;
    GEN I = kernel_to_ideal_O0_T(coeff_ker_challenge_commitment);
    proj ker = coeff_to_E0(gel(coeff_ker_challenge_commitment,1), false);
    proj ker_twist = coeff_to_E0(gel(coeff_ker_challenge_commitment,2), true);
    isog_degree deg, deg_twist;
    famat_to_degree(&deg, &deg_twist, Z_factor(lideal_norm(I)));

    phi_test.kernel_plus = ker;
    phi_test.kernel_minus = ker_twist;
    phi_test.deg_plus = deg;
    phi_test.deg_minus = deg_twist;

    proj A = global_setup.E0, H = {fp2_1, fp2_0};
    eval(&A, &phi_test, &H);

    assert(mont_equal(&A, &E_cha));

    #endif


    uint64_t zip[signing_length_two_tors_height_step];
    two_walk_long sigma;
    init_trivial_two_walk_long(&sigma);

    response(&sigma, comp_sigma->zip, coeff_ker_challenge_commitment, sk, basis_two, &E_cha);




    assert(simple_check_signature(&sigma,comp_sigma->zip, pk, &E_cha));

    free_two_walk_long(&sigma);

    avma = ltop;
}



bool verif(compressed_signature *comp_sigma, const public_key *pk,const uintbig *m){
    proj A_chall = comp_sigma->E_com;
    challenge(&A_chall, m, &A_chall, NULL, NULL, NULL, NULL);
    proj A_check=pk->E;
    two_walk walk_check[signing_length_two_tors_height_step];


    decompress(walk_check,&A_check,comp_sigma->zip,signing_length_two_tors_height_step,last_step_length);

    proj j1,j2;
    jinv256(&j1,&A_chall);
    normalize_proj(&j1);
    jinv256(&j2,&A_check);
    normalize_proj(&j2);
    return mont_equal(&j1,&j2);
}




//msk is an secret isogeny from E0, mpk is the codomain of msk.
void CLI_keygen(public_key *mpk, secret_key *msk){
    keygen(mpk,msk);
}



//sigma1 is an isogeny from EA of degree 2^1000, E1 is the codomain of sigma1.
// 包含初始化 sigma1
// need: pari_sp ltop = avma ?
void set_secret_val(two_walk_long *sigma1, proj *E1, const public_key *mpk){
    int i,j,index;
    proj P,Z;
    bool find;
    two_walk phi_temp;
    two_walk_long res;

    //inti_two_walk_long(&res,31);
    inti_two_walk_long(&res,8);
    
    *E1 = mpk->E;

    index = 0;
    while (index < res.len) {
        fp_random(&P.x.re);
        fp_random(&P.x.im);
        fp_random(&P.z.re);
        fp_random(&P.z.im);

        i=0; find = false;
        while(i<100) {
            fp_add2(&P.x.re, &fp_1);
            if (!is_on_curve(&P, E1)) {
                ++i;
                continue;
            }

            //[p-1]P = O ?
            Z=P;
            xMUL(&Z, E1, &Z, &p_minus_2_3);
            xMUL(&Z, E1, &Z, &p_minus_2_3_cofactor);

            if (mont_iszero(&Z)) {
                --index;
                *E1 = res.phi[index].A;
                break;
            }

            xMUL(&P, E1, &P, &p_even_cofactor);

            xMUL(&Z, E1, &P, &pow_2_32);
            if (!mont_iszero(&Z)) {
                if (index == res.len-1) xMUL(&P, E1, &P, &pow_2_8);
                find = true;
                break;
            }

            else ++i;


            /*
            xMUL(&Z, E1, &P, &pow_2_33);
            if (mont_iszero(&Z)) {
                xMUL(&Z, E1, &P, &pow_2_32);
                if (!mont_iszero(&Z)) {
                    if (index == 30) xMUL(&P, E1, &P, &pow_2_23);
                    find = true;
                    break;
                }
                else ++i;
            }
            else printf("#curve is wrong in secret value !\n");
            */
        }
                
        if (find) {
            phi_temp.A = *E1;
            phi_temp.ker = P;
            if (index == res.len-1) phi_temp.len = 25;
            else phi_temp.len = two_tors_height;

            res.phi[index] = phi_temp;

            eval_walk(&phi_temp, E1, &P);

            //assert(mont_iszero(&P));
            //if (!mont_iszero(&P)) printf("error in sec_val isogeny\n");

            ++index;
        }
    }

    //free_two_walk_long(sigma1);
    *sigma1 = res;
}


// sigma2 is an isogeny from EA to E_cha of degree 2^1000, E3 = E_com, E2 = E_cha.
//不需要初始化sigma2
// need: pari_sp ltop = avma ?
void partial_key_ext(two_walk_long *sigma2, proj *E2, proj *E3, const public_key *mpk, const secret_key *msk,  const uintbig *ID, const proj *E1){
    //pari_sp ltop = avma;

    uintbig m;
    compressed_signature comp_sigma;
    init_compressed_sig(&comp_sigma);

    uintbig_add3(&m,ID,&(E1->x.re.x));
    uintbig_add3(&m, &m, &(E1->x.im.x));
    uintbig_add3(&m, &m, &(E1->z.re.x));
    uintbig_add3(&m, &m, &(E1->z.im.x));

    //copied from sign()

    GEN coeff_com, I_com;
    odd_isogeny phi_com;
    //proj E_cha;


    commitment(&coeff_com, &I_com, &phi_com);

    comp_sigma.E_com = global_setup.E0;


    // compute the image of a basis of the torsion used for the challenge

    proj points[9];
    points[0] = torsion_basis_sum[0];
    points[1] = torsion_basis_sum[1];
    points[2] = torsion_basis_sum[2];
    points[3] = torsion_basis_twist_sum[0];
    points[4] = torsion_basis_twist_sum[1];
    points[5] = torsion_basis_twist_sum[2];
    points[6] = torsion_basis_two[0];
    points[7] = torsion_basis_two[1];
    points[8] = torsion_basis_two[2];

    eval_mult(&comp_sigma.E_com, &phi_com, points, 9);

    proj basis_plus[3], basis_minus[3], basis_two[3];
    basis_plus[0] = points[0];
    basis_plus[1] = points[1];
    basis_plus[2] = points[2];
    basis_minus[0] = points[3];
    basis_minus[1] = points[4];
    basis_minus[2] = points[5];
    basis_two[0] = points[6];
    basis_two[1] = points[7];
    basis_two[2] = points[8];

    uintbig ell_big;
    for (int i = 0; i < p_plus_len; ++i) {
        uintbig_set(&ell_big, p_plus_fact[i]);
        for (int j = 0; j < p_plus_mult[i] - p_plus_mult_cha[i]; ++j){
            for (int l = 0; l < 3; ++l) {
                xMUL(&basis_plus[l], &comp_sigma.E_com, &basis_plus[l], &ell_big);
            }
        }
    }

    for (int i = 0; i < p_minus_len; ++i) {
        uintbig_set(&ell_big, p_minus_fact[i]);
        for (int j = 0; j < p_minus_mult[i] - p_minus_mult_cha[i]; ++j){
            for (int l = 0; l < 3; ++l) {
                xMUL(&basis_minus[l], &comp_sigma.E_com, &basis_minus[l], &ell_big);
            }
        }
    }

    GEN dlog;

    //challenge(&E_cha, m, &comp_sigma->E_com, basis_plus, basis_minus, &dlog, basis_two);
    challenge(E2, &m, &comp_sigma.E_com, basis_plus, basis_minus, &dlog, basis_two);

    GEN coeff_ker_challenge_commitment = gadd(coeff_com,dlog);


    #ifndef NDEBUG

    odd_isogeny phi_test;
    GEN I = kernel_to_ideal_O0_T(coeff_ker_challenge_commitment);
    proj ker = coeff_to_E0(gel(coeff_ker_challenge_commitment,1), false);
    proj ker_twist = coeff_to_E0(gel(coeff_ker_challenge_commitment,2), true);
    isog_degree deg, deg_twist;
    famat_to_degree(&deg, &deg_twist, Z_factor(lideal_norm(I)));

    phi_test.kernel_plus = ker;
    phi_test.kernel_minus = ker_twist;
    phi_test.deg_plus = deg;
    phi_test.deg_minus = deg_twist;

    proj A0 = global_setup.E0, H = {fp2_1, fp2_0};
    eval(&A0, &phi_test, &H);

    //assert(mont_equal(&A, &E_cha));
    assert(mont_equal(&A0, E2));

    #endif


    uint64_t zip[signing_length_two_tors_height_step];

    two_walk_long sigma;
    init_trivial_two_walk_long(&sigma);
    //init_trivial_two_walk_long(sigma2);

    //response(sigma2, comp_sigma->zip, coeff_ker_challenge_commitment, msk, basis_two, &E_cha);
    response(&sigma, comp_sigma.zip, coeff_ker_challenge_commitment, msk, basis_two, E2);

    assert(simple_check_signature(&sigma,comp_sigma.zip, mpk, E2));

    *E3 = comp_sigma.E_com;

    //new sigma2 and E2
    inti_two_walk_long(sigma2,8);

    for(int i=0; i<7;++i) sigma2->phi[i] = sigma.phi[i];

    proj P,A;
    A = sigma.phi[7].A;
    P = sigma.phi[7].ker;
    xMUL(&P, &A, &P, &pow_2_8);
    sigma2->phi[7].A = A;
    sigma2->phi[7].ker = P;
    sigma2->phi[7].len = 25;

    eval_walk(&(sigma2->phi[7]), E2, &P);

    //avma = ltop;
}


void set_user_key(user_sk *usk, user_pk *upk, const two_walk_long *sigma2, const proj *E2, const proj *E3, const two_walk_long *sigma1, const proj *E1) {
    usk->sigma1 = *sigma1;
    usk->sigma2 = *sigma2;
    upk->E1 = *E1;
    upk->E2 = *E2;
    upk->E3 = *E3;
}

void SIDH(proj *E_tar, two_walk_long *sigma1, odd_isogeny_long *eta1, const two_walk_long *sigma, const odd_isogeny_long *eta) {
    long i,j,row,col;
    proj A0,N,E1,E2,j1,j2;
    isog_degree deg;

    degree_one(&deg);
    degree_set(&deg,0,21);
    for (i=1;i<p_plus_len;++i) degree_unset(&deg,i);

    col = sigma->len;
    row = eta->len;

    //store the inside isogeny 
    two_walk table_2[row+1][col];
    odd_isogeny table_odd[row][col];

    //the first row of table_2 is sigma
    for(j=0;j<col;++j) {
        table_2[0][j] = (sigma->phi)[j];
    }

    /*
    E1 = sigma->phi[0].A;
    E2 = eta->phi[0].A;
    //assert(mont_equal(&E1,&E2));
    if (!mont_equal(&E1,&E2)) printf("different starting curves in SIDH\n");
    */

    //generate the table
    for(i=0;i<row;++i) {
        N = (eta->phi)[i].kernel_plus;
        A0 = (eta->phi)[i].A;
        for(j=0;j<col;++j) {
            E1 = table_2[i][j].A;
            eval_walk(&(table_2[i][j]), &A0, &N);
            table_odd[i][j].A = A0;
            table_odd[i][j].kernel_plus = N;
            table_odd[i][j].kernel_minus.x = fp2_1;
            table_odd[i][j].kernel_minus.z = fp2_0;
            table_odd[i][j].deg_plus = deg;
            table_odd[i][j].deg_minus.val = 0;
        }

        N = table_2[i][0].ker;
        A0 = (eta->phi)[i].A;
        eval(&A0, &((eta->phi)[i]), &N);
        table_2[i+1][0].A = A0;
        table_2[i+1][0].ker = N;
        table_2[i+1][0].len = table_2[i][0].len;

        for(j=1;j<col;++j) {
            A0 = table_odd[i][j-1].A;
            N = table_2[i][j].ker;
            eval(&A0, &(table_odd[i][j-1]), &N);
            table_2[i+1][j].A = A0;
            table_2[i+1][j].ker = N;
            table_2[i+1][j].len = table_2[i][j].len;
        }
    }

    //verify the equality of the domains of two walks  
    E1 = table_odd[row-1][col-1].A;
    N = table_odd[row-1][col-1].kernel_plus;
    eval(&E1, &(table_odd[row-1][col-1]), &N);

    //assert(mont_iszero(&N));
    //if (!mont_iszero(&N)) printf("error1 in SIDH isogeny\n");

    E2 = table_2[row][col-1].A;
    N = table_2[row][col-1].ker;
    eval_walk(&(table_2[row][col-1]), &E2, &N);

    //assert(mont_iszero(&N));
    //if (!mont_iszero(&N)) printf("error2 in SIDH isogeny\n");

    //assert(mont_equal(&E1,&E2));
    jinv256(&j1,&E1);
    jinv256(&j2,&E2);
    if(!mont_equal(&j1, &j2)) printf("SIDH is wrong!\n");
    

    *E_tar = E1;

    for(j=0;j<col;++j) {
        (sigma1->phi)[j] = table_2[row][j];
    }

    for(i=0;i<row;++i) {
        (eta1->phi)[i] = table_odd[i][col-1];
    }
}



//包含初始化
void id_commitment(id_com *com, const user_sk *usk, const public_key *mpk){
    int i,j,t;
    proj P,Z;
    bool find;
    odd_isogeny eta_temp;
    isog_degree deg;
    degree_one(&deg);

    /*
    uintbig p_plus_2_5_cofactor={517434778561,0,0,0};
    uintbig_mul3_64(&p_plus_2_5_cofactor,&p_plus_2_5_cofactor, 26602537156291);
    for (i = 1; i < p_plus_len; ++i) {
        ell = p_plus_fact[i];
        for (j=0; j < p_plus_mult[i]; ++j) {
            uintbig_mul3_64(&p_plus_2_5_cofactor,&p_plus_2_5_cofactor, ell);
        }
    }
    */

    //compute t-th commitment.
    for(t=0; t< CLI_round ; ++t) {
        inti_odd_isogeny_long(&(com[t].eta),3);
        inti_odd_isogeny_long(&(com[t].eta1),3);
        inti_odd_isogeny_long(&(com[t].eta2),3);
        inti_two_walk_long(&(com[t].sigma1),(usk->sigma1).len);
        inti_two_walk_long(&(com[t].sigma2),(usk->sigma2).len);

        //construct random isogeny eta and the codomain F.
        com[t].F = mpk->E;
        j=0;
        while(j < 3) {
            fp_random(&P.x.re);
            fp_random(&P.x.im);
            fp_random(&P.z.re);
            fp_random(&P.z.im);

            i=0; find = false;

            while(i<100) {
                fp_add2(&P.x.re, &fp_1);
                if (!is_on_curve(&P, &(com[t].F))) {
                    //++i;
                    continue;
                }

                //[p-1]P = O ?
                Z=P;
                xMUL(&Z, &(com[t].F), &Z, &p_minus_2_3);
                xMUL(&Z, &(com[t].F), &Z, &p_minus_2_3_cofactor);

                if (mont_iszero(&Z)) {
                    --j;
                    com[t].F = (com[t].eta.phi)[j].A;
                    find = false;
                    break;
                }
                
                xMUL(&P, &(com[t].F), &P, &p_plus_5_cofactor);

                xMUL(&Z, &(com[t].F), &P, &pow_5_20);
                if (!mont_iszero(&Z)) {
                    find = true;
                    break;
                }
                else ++i;

                /*
                xMUL(&Z, &(com[t].F), &P, &pow_5_21); //k3=5^21
                if (mont_iszero(&Z)) {
                    xMUL(&Z, &(com[t].F), &P, &pow_5_20);
                    if (!mont_iszero(&Z)) {
                        find = true;
                        break;
                    }
                    else ++i;
                }

                else printf("j=%d,#curve is wrong in commitment!\n",j);
                */
            }

            if (find) {
                eta_temp.A = com[t].F;
                eta_temp.kernel_plus = P;
                eta_temp.kernel_minus.x = fp2_1;
                eta_temp.kernel_minus.z = fp2_0;
                eta_temp.deg_minus.val = 0;

                degree_set(&deg,0,21);
                for (i=1;i<p_plus_len;++i) degree_unset(&deg,i);
                eta_temp.deg_plus = deg;

                (com[t].eta.phi)[j] = eta_temp;

                eval(&(com[t].F), &eta_temp, &P);

                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error in id_commitment isogeny.\n");

                ++j;
            }
        }

        //use SIDH to compute eta1,F1,eta2,F2.
        SIDH(&(com[t].F1), &(com[t].sigma1), &(com[t].eta1), &(usk->sigma1), &(com[t].eta));
        SIDH(&(com[t].F2), &(com[t].sigma2), &(com[t].eta2), &(usk->sigma2), &(com[t].eta));
    }
}

void id_challenge(long *cha) {
    int i;

    for(i=0;i<CLI_round;++i) {
        cha[i] = random_Fl(3);
        //cha[i] = random_Fl(2);
    }
}

//包含初始化
/*
void id_response(id_res *res, const id_com *com, const long *cha) {
    int t;

    for(t=0;t<CLI_round;++t) {
        if(cha[t]==0) {
            inti_two_walk_long(&(res[t].res1),com[t].sigma1.len);
            inti_two_walk_long(&(res[t].res2),com[t].sigma2.len);
            res[t].res1 = com[t].sigma1;
            res[t].res2 = com[t].sigma2;
        }

        else if(cha[t] == 1) {
            inti_odd_isogeny_long(&(res[t].res3),com[t].eta.len);
            inti_odd_isogeny_long(&(res[t].res4),com[t].eta1.len);
            res[t].res3 = com[t].eta;
            res[t].res4 = com[t].eta1;
        }

        else {
            inti_odd_isogeny_long(&(res[t].res3),com[t].eta.len);
            inti_odd_isogeny_long(&(res[t].res4),com[t].eta2.len);
            res[t].res3 = com[t].eta;
            res[t].res4 = com[t].eta2;
        }
    }
}

bool id_verify(const id_res *res, const id_com *com, const long *cha, const user_pk *upk, const public_key *mpk) {
    int i,t;
    proj N,P,j1,j2;

    for(t=0;t<CLI_round;++t) {
        if(cha[t]==0) {
            N = com[t].F;
            for(i=0;i<(res[t].res1).len;++i) {
                P = (res[t].res1.phi)[i].ker;
                eval_walk(&((res[t].res1.phi)[i]), &N, &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error1 in id_verify isogeny.\n");
                //printf("c=0,res1\n");
            }
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F1));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res1, ", cha[t]);
                return false;
            }

            N = com[t].F;
            for(i=0;i<(res[t].res2).len;++i) {
                P = (res[t].res2.phi)[i].ker;                
                eval_walk(&((res[t].res2.phi)[i]), &N, &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error2 in id_verify isogeny.\n");
                //printf("c=0,res2\n");
            }
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F2));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res2, ", cha[t]);
                return false;
            }
        }

        else if(cha[t] == 1) {
            N = mpk->E;
            for(i=0;i<(res[t].res3).len;++i) {
                P = (res[t].res3.phi)[i].kernel_plus;
                eval(&N, &((res[t].res3.phi)[i]), &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error3 in id_verify isogeny.\n");
                //printf("c=1,res1\n");
            }
            
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res1, ", cha[t]);
                return false;
            }
            
            //if(!mont_equal(&N, &com[t].F)) return false;

            N = upk->E1;
            for(i=0;i<(res[t].res4).len;++i) {
                P = (res[t].res4.phi)[i].kernel_plus;
                eval(&N, &((res[t].res4.phi)[i]), &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error4 in id_verify isogeny.\n");
                //printf("c=1,res2\n");
            }
            
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F1));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res2, ", cha[t]);
                return false;
            }
            
            //if(!mont_equal(&N, &com[t].F2)) return false;
        }

        else {
            N = mpk->E;
            for(i=0;i<(res[t].res3).len;++i) {
                P = (res[t].res3.phi)[i].kernel_plus;
                eval(&N, &((res[t].res3.phi)[i]), &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error5 in id_verify isogeny.\n");
                //printf("c=2,res1\n");
            }
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res1, ", cha[t]);
                return false;
            }

            N = upk->E2;
            for(i=0;i<(res[t].res4).len;++i) {
                P = (res[t].res4.phi)[i].kernel_plus;
                eval(&N, &((res[t].res4.phi)[i]), &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error6 in id_verify isogeny.\n");
                //printf("c=2,res2\n");
            }
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F2));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res2, ", cha[t]);
                return false;
            }
        }
    }

    return true;
}
*/

void id_response(id_res *res, const id_com *com, const long *cha) {
    int t;

    for(t=0;t<CLI_round;++t) {
        if(cha[t]==0) {
            inti_two_walk_long(&(res[t].res1),com[t].sigma1.len);
            inti_two_walk_long(&(res[t].res2),com[t].sigma2.len);
            res[t].res1 = com[t].sigma1;
            res[t].res2 = com[t].sigma2;
        }

        else {
            inti_odd_isogeny_long(&(res[t].res3),com[t].eta1.len);
            inti_odd_isogeny_long(&(res[t].res4),com[t].eta2.len);
            res[t].res3 = com[t].eta1;
            res[t].res4 = com[t].eta2;
        }
    }
}

bool id_verify(const id_res *res, const id_com *com, const long *cha, const user_pk *upk, const public_key *mpk) {
    int i,t;
    proj N,P,j1,j2;

    for(t=0;t<CLI_round;++t) {
        if(cha[t]==0) {
            N = com[t].F;
            for(i=0;i<(res[t].res1).len;++i) {
                P = (res[t].res1.phi)[i].ker;
                eval_walk(&((res[t].res1.phi)[i]), &N, &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error1 in id_verify isogeny.\n");
                //printf("c=0,res1\n");
            }
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F1));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res1, ", cha[t]);
                return false;
            }

            N = com[t].F;
            for(i=0;i<(res[t].res2).len;++i) {
                P = (res[t].res2.phi)[i].ker;                
                eval_walk(&((res[t].res2.phi)[i]), &N, &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error2 in id_verify isogeny.\n");
                //printf("c=0,res2\n");
            }
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F2));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res2, ", cha[t]);
                return false;
            }
        }

        else {
            N = upk->E1;
            for(i=0;i<(res[t].res3).len;++i) {
                P = (res[t].res3.phi)[i].kernel_plus;
                eval(&N, &((res[t].res3.phi)[i]), &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error3 in id_verify isogeny.\n");
                //printf("c=1,res1\n");
            }
            
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F1));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res1, ", cha[t]);
                return false;
            }
            
            //if(!mont_equal(&N, &com[t].F)) return false;

            N = upk->E2;
            for(i=0;i<(res[t].res4).len;++i) {
                P = (res[t].res4.phi)[i].kernel_plus;
                eval(&N, &((res[t].res4.phi)[i]), &P);
                //assert(mont_iszero(&P));
                //if (!mont_iszero(&P)) printf("error4 in id_verify isogeny.\n");
                //printf("c=1,res2\n");
            }
            
            jinv256(&j1,&N);
            jinv256(&j2,&(com[t].F2));
            if(!mont_equal(&j1, &j2)) {
                printf("c = %ld, res2, ", cha[t]);
                return false;
            }
            
            //if(!mont_equal(&N, &com[t].F2)) return false;
        }
    }

    return true;
}

bool identification(const user_sk *usk, const user_pk *upk, const public_key *mpk){
    id_com COM[CLI_round];
    id_commitment(COM, usk, mpk);

    long CHA[CLI_round];
    id_challenge(CHA);

    id_res RES[CLI_round];
    id_response(RES, COM, CHA);

    return id_verify(RES,COM,CHA,upk,mpk);
}

//这里不需要再初始化
void sig_sign(id_sig *SIG, const user_sk *usk, const user_pk *upk, const public_key *mpk, const uint64_t *m) {
    int t;

    id_com COM[CLI_round];
    id_commitment(COM, usk, mpk);

    // c = H(m,upk,COM)
    long CHA[CLI_round];
    for(t=0;t<CLI_round;++t) {
        //CHA[t] = (long)(m[t]%3 + (upk->E1.x.re.x.c[0])%3 + (upk->E2.x.re.x.c[0])%3 + (upk->E3.x.re.x.c[0])%3 + (COM[t].F.x.re.x.c[0])%3)%3;
        CHA[t] = (long)(m[t]%2 + (upk->E1.x.re.x.c[0])%2 + (upk->E2.x.re.x.c[0])%2 + (upk->E3.x.re.x.c[0])%2 + (COM[t].F.x.re.x.c[0])%2)%2;
        //CHA[t] = 2;
    }

    id_res RES[CLI_round];
    id_response(RES, COM, CHA);

    for(t=0;t<CLI_round;++t) {
        SIG[t].F = COM[t].F;
        SIG[t].F1 = COM[t].F1;
        SIG[t].F2 = COM[t].F2;
        SIG[t].res1 = RES[t].res1;
        SIG[t].res2 = RES[t].res2;
        SIG[t].res3 = RES[t].res3;
        SIG[t].res4 = RES[t].res4;
    }
}

bool sig_verify(const id_sig *SIG, const user_pk *upk, const public_key *mpk, const uint64_t *m) {
    int t;

    id_res RES[CLI_round];
    for(t=0;t<CLI_round;++t) {
        RES[t].res1 = SIG[t].res1;
        RES[t].res2 = SIG[t].res2;
        RES[t].res3 = SIG[t].res3;
        RES[t].res4 = SIG[t].res4;
    }

    id_com COM[CLI_round];
    for(t=0;t<CLI_round;++t) {
        COM[t].F = SIG[t].F;
        COM[t].F1 = SIG[t].F1;
        COM[t].F2 = SIG[t].F2;
    }

    long CHA[CLI_round];
    for(t=0;t<CLI_round;++t) {
        //CHA[t] = (long)(m[t]%3 + (upk->E1.x.re.x.c[0])%3 + (upk->E2.x.re.x.c[0])%3 + (upk->E3.x.re.x.c[0])%3 + (COM[t].F.x.re.x.c[0])%3)%3;
        CHA[t] = (long)(m[t]%2 + (upk->E1.x.re.x.c[0])%2 + (upk->E2.x.re.x.c[0])%2 + (upk->E3.x.re.x.c[0])%2 + (COM[t].F.x.re.x.c[0])%2)%2;
        //CHA[t] = 2;
    }

    return id_verify(RES,COM,CHA,upk,mpk);
}