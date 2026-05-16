require import AllCore Distr.

(** A more mature proof would rely on libraries of definitions-generic
    definitions have a lot more parameters than what we'd like to
    expose a tutorial reader to.

    Instead, we inline (and specialise) the definitions we care about.
**)

(* Given sets of public keys, secret keys, plaintexts, DEM keys, KEM
   ciphertexts and DEM ciphertexts ... *)
type pkey, skey, pt, key, kct, dct.

(* ... and the uniform distribution over the DEM key space *)
op [lossless full uniform] dkey : key distr.

(** A KEM is a triple of (potentially probabilistic and stateful)
    algorithms:
**)
module type KEM = {
  proc keygen(): pkey * skey
  proc enc(pk : pkey): key * kct
  proc dec(sk : skey, k : kct): key option
}.

module type KEM_CCA_Oracles = {
  proc dec(k : kct): key option
}.

(** A CCA adversary against the KEM is an algorithm: **)
module type KEM_CCA_Adv (O : KEM_CCA_Oracles) = {
  proc distinguish(pk : pkey, k : key, c : kct): bool
}.

(** And we define the advantage of a CCA adversary A against a KEM E
    as
      `|   Pr[KEM_CCA_Exp(E, A).run(false) @ &m: res]
         - Pr[KEM_CCA_Exp(E, A).run(true) @ &m: res]  |
    where KEM_CCA_Exp is the experiment:
**)
module KEM_CCA_Exp (E : KEM) (A : KEM_CCA_Adv) = {
  var sk : skey
  var c : kct

  module O = {
    proc dec(c0 : kct) = {
      var r <- None;

      if (c <> c0) {
        r <@ E.dec(sk, c0);
      }
      return r;
    }
  }
        
  proc run(b : bool) = {
    var pk, k0, k1, k, r;

    (pk, sk) <@ E.keygen();
    (k0, c) <@ E.enc(pk);
    k1 <$ dkey;
    k <- if b then k1 else k0;
    r <@ A(O).distinguish(pk, k, c);
    return r;
  }
}.

(** For CCA security, we also need to assume correctness of the
    KEM.
**)
module KEM_Correctness (E : KEM) = {
  proc run() = {
    var sk, pk, c, k, k';

    (pk, sk) <@ E.keygen();
    (k, c) <@ E.enc(pk);
    k' <@ E.dec(sk, c);
    return k' = Some k;
  }
}.

(** For the proof, we actually want it to be expressed as follows.
    TODO: prove the generic implication we need.
**)
module KEM_Correctness_b (E : KEM) (A : KEM_CCA_Adv) = {
  var b0 : bool
  var sk : skey
  var c0 : kct
  var k0 : key

  module O = {
    proc dec(c) = {
      var r;

      if (b0 /\ c = c0) {
        r <- Some k0;
      } else {
        r <@ E.dec(sk, c);
      }
      return r;
    }
  }

  proc run(b) = {
    var pk, r;

    b0 <- b;
    (pk, sk) <@ E.keygen();
    (k0, c0) <@ E.enc(pk);
    r <@ A(O).distinguish(pk, k0, c0);
    return r;
  }
}.

(** A DEM is a pair of algorithms: **)
module type DEM = {
  (* We force key generation to be sampling in `dkey` *)
  proc enc(k : key, m : pt): dct
  proc dec(k : key, c : dct): pt
}.

module type DEM_CCA_Oracles = {
  proc dec(c : dct): pt option
}.

(** A passive/eavesdropping DEM adversary is a pair of algorithms: **)
module type DEM_CCA_Adv (O : DEM_CCA_Oracles) = {
  proc choose(): pt * pt
  proc distinguish(c : dct): bool
}.

(** And we define the advantage of a passive adversary A against a DEM
    as
      `|   Pr[DEM_PAS_Exp(E, A).run(false) @ &m: res]
         - Pr[DEM_PAS_Exp(E, A).run(true) @ &m: res]  |
    where DEM_PAS_Exp is the experiment:
**)
module DEM_CCA_Exp (E : DEM) (A : DEM_CCA_Adv) = {
  var k0 : key
  var c0 : dct option

  module O = {
    proc dec(c) = {
      var m;
      var r <- None;

      if (c0 <> Some c) {
        m <@ E.dec(k0, c);
        r <- Some m;
      }
      return r;
    }
  }

  proc run(b : bool) = {
    var m0, m1, c, r;

    c0 <- None;
    k0 <$ dkey;
    (m0, m1) <@ A(O).choose();
    c <@ E.enc(k0, if b then m1 else m0);
    c0 <- Some c;
    r <@ A(O).distinguish(c);
    return r;
  }
}.

(** We have defined our assumptions, we can now define our
    constructive goal.

    A public key encryption scheme (with structured ciphertexts!) is a
    triple of algorithms:
**)
module type PKE = {
  proc keygen(): pkey * skey
  proc enc(pk : pkey, m : pt): kct * dct
  proc dec(sk : skey, c : kct * dct): pt option
}.

module type PKE_CCA_Oracles = {
  proc dec(c : kct * dct): pt option
}.

(** A CCA adversary against a PKE is a pair of algorithms: **)
module type PKE_CCA_Adv (O : PKE_CCA_Oracles) = {
  proc choose(pk : pkey): pt * pt
  proc distinguish(c : kct * dct): bool
}.

(** The advantage of a CCA adversary A against a PKE E is
      `|   Pr[PKE_CCA_Exp(E, A).run(false) @ &m: res]
         - Pr[PKE_CCA_Exp(E, A).run(true) @ &m: res]  |
    where PKE_CCA_Exp is the experiment:
**)
module PKE_CCA_Exp (E : PKE) (A : PKE_CCA_Adv) = {
  var sk : skey
  var c0 : (kct * dct) option

  module O = {
    proc dec(c) = {
      var r <- None;

      if (c0 <> Some c) {
        r <@ E.dec(sk, c);
      }
      return r;
    }
  }

  proc run(b : bool) = {
    var pk, c, r, m0, m1;

    c0 <- None;
    (pk, sk) <@ E.keygen();
    (m0, m1) <@ A(O).choose(pk);
    c <@ E.enc(pk, if b then m1 else m0);
    c0 <- Some c;
    r <@ A(O).distinguish(c);
    return r;
  }
}.

(* (* Note: instead of defining a specialised notion of PKE with
      structured ciphertexts, we could have obtained very similar
      definitions by _instantiating_ a library definition.

      However, note that the humongous variety of ways in which CCA
      security for PKEs can be expressed makes developing such a
      library a tricky proposition.
   *)
require PKE.
clone PKE as KEM_Based_PKE with
  type pkey <= pkey,
  type skey <= skey,
  type plaintext <= pt,
  type ciphertext <= kct * dct.

print KEM_Based_PKE.Scheme.
*)

(** Finally, we can define our KEM/DEM composition **)
module KEMDEM (E_kem : KEM) (E_s : DEM): PKE = {
  proc keygen = E_kem.keygen

  proc enc(pk : pkey, m : pt): kct * dct = {
    var k, kc, c;

    (k, kc) <@ E_kem.enc(pk);
    c <@ E_s.enc(k, m);
    return (kc, c);
  }

  proc dec(sk : skey, c : kct * dct): pt option = {
    var kc, dc, r, k, m;

    (kc, dc) <- c;
    r <- None;
    k <@ E_kem.dec(sk, kc);
    if (k <> None) {
      m <@ E_s.dec(oget k, dc);
      r <- Some m;
    }
    return r;
  }
}.

module B_cor_b (E_s : DEM) (A : PKE_CCA_Adv) (O : KEM_CCA_Oracles) = {
  var b_lor : bool
  var c0 : (kct * dct) option

  module O_PKE = {
    proc dec(kc, dc) = {
      var k, m;
      var r <- None;

      if (c0 <> Some (kc, dc)) {
        k <@ O.dec(kc);
        if (k <> None) {
          m <@ E_s.dec(oget k, dc);
          r <- Some m;
        }
      }
      return r;
    }
  }

  proc distinguish(pk, k, c) = {
    var m0, m1, c', r;

    c0 <- None;
    (m0, m1) <@ A(O_PKE).choose(pk);
    c' <@ E_s.enc(k, if b_lor then m1 else m0);
    c0 <- Some (c, c');
    r <@ A(O_PKE).distinguish(c, c');
    return r;
  }
}.

module (B_cor_0 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_CCA_Adv) (O : KEM_CCA_Oracles) = {
  proc distinguish(pk, k, c) = {
    var b;

    B_cor_b.b_lor <- false;
    b <@ B_cor_b(E_s, A, O).distinguish(pk, k, c);
    return b;
  }
}.

module (B_cor_1 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_CCA_Adv) (O : KEM_CCA_Oracles) = {
  proc distinguish(pk, k, c) = {
    var b;

    B_cor_b.b_lor <- true;
    b <@ B_cor_b(E_s, A, O).distinguish(pk, k, c);
    return b;
  }
}.

module B_kem_b (E_s : DEM) (A : PKE_CCA_Adv) (O : KEM_CCA_Oracles) = {
  var b_lor : bool
  var c0 : (kct * dct) option
  var k0 : key
  var kc0 : kct

  module O_PKE = {
    proc dec(kc, dc) = {
      var k, m;
      var r <- None;

      if (c0 <> Some (kc, dc)) {
        if (kc0 = kc) {
          k <- Some k0;
        } else {
          k <@ O.dec(kc);
        }
        if (k <> None) {
          m <@ E_s.dec(oget k, dc);
          r <- Some m;
        }
      }
      return r;
    }
  }

  proc distinguish(pk, k, c) = {
    var m0, m1, c', r;

    c0 <- None;
    k0 <- k;
    kc0 <- c;
    (m0, m1) <@ A(O_PKE).choose(pk);
    c' <@ E_s.enc(k, if b_lor then m1 else m0);
    c0 <- Some (c, c');
    r <@ A(O_PKE).distinguish(c, c');
    return r;
  }
}.

module (B_kem_0 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_CCA_Adv) (O : KEM_CCA_Oracles) = {
  proc distinguish(pk, k, c) = {
    var b;

    B_kem_b.b_lor <- false;
    b <@ B_kem_b(E_s, A, O).distinguish(pk, k, c);
    return b;
  }
}.

module (B_kem_1 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_CCA_Adv) (O : KEM_CCA_Oracles) = {
  proc distinguish(pk, k, c) = {
    var b;

    B_kem_b.b_lor <- true;
    b <@ B_kem_b(E_s, A, O).distinguish(pk, k, c);
    return b;
  }
}.

module (B_s (E_kem : KEM) (E_s : DEM) (A : PKE_CCA_Adv) : DEM_CCA_Adv) (O : DEM_CCA_Oracles) = {
  var sk : skey
  var c0 : (kct * dct) option
  var kc0 : kct

  module O_PKE = {
    proc dec(c) = {
      var k, kc, dc, m;
      var r <- None;

      (kc, dc) <- c;
      if (c0 <> Some (kc, dc)) {
        if (kc = kc0) {
          r <@ O.dec(dc);
        } else {
          k <@ E_kem.dec(sk, kc);
          if (k <> None) {
            m <@ E_s.dec(oget k, dc);
            r <- Some m;
          }
        }
      }
      return r;
    }
  }

  proc choose() = {
    var pk, k, m0, m1;

    c0 <- None;
    (pk, sk) <@ E_kem.keygen();
    (k, kc0) <@ E_kem.enc(pk);
    (m0, m1) <@ A(O_PKE).choose(pk);
    return (m0, m1);
  }

  proc distinguish(c) = {
    var r;

    c0 <- Some (kc0, c);
    r <@ A(O_PKE).distinguish(kc0, c);
    return r;
  }
}.

section.
(* For every KEM E_kem *)
declare module E_kem <: KEM { -KEM_Correctness_b, -KEM_CCA_Exp, -DEM_CCA_Exp, -PKE_CCA_Exp, -B_cor_b, -B_kem_b, -B_s }.
(* For every DEM E_s *)
declare module E_s   <: DEM { -KEM_Correctness_b, -KEM_CCA_Exp, -DEM_CCA_Exp, -PKE_CCA_Exp, -B_cor_b, -B_kem_b, -B_s, -E_kem }.
(* and for every CCA adversary against the PKE KEMDEM(E_kem, E_s) *)
declare module A     <: PKE_CCA_Adv { -KEM_Correctness_b, -KEM_CCA_Exp, -DEM_CCA_Exp, -PKE_CCA_Exp, -B_cor_b, -B_kem_b, -B_s, -E_kem, -E_s }.
(* we have
        Adv^{CCA}_{KEMDEM(E_kem, E_s)}(A)
     <=   Adv^{cor}_{E_kem}(B_cor_0(E_s, A))
        + Adv^{CCA}_{E_kem}(B_kem_0(E_s, A))
        + Adv^{CCA}_{E_s}(B_s(E_s, E_kem, A))
        + Adv^{CCA}_{E_kem}(B_kem_1(E_s, A))
        + Adv^{cor}_{E_kem}(B_cor_1(E_s, A))
*)

(** This is a proof artefact allowing us to express our minimal
    assumption on the KEM; ideally we would not need to define it. But
    we do. **)
module KEMC (E : KEM) = {
  proc enc_dec(pk, sk, c) = {
    var kc', k';

    kc' <@ E.enc(pk);
    k' <@ E.dec(sk, c);
    return (k', kc');
  }

  proc dec_enc(pk, sk, c) = {
    var kc', k';

    k' <@ E.dec(sk, c);
    kc' <@ E.enc(pk);
    return (k', kc');
  }
}.

declare axiom kemC:
  equiv [KEMC(E_kem).enc_dec ~ KEMC(E_kem).dec_enc: ={glob E_kem, arg} ==> ={glob E_kem, res}].

(** First, we start by doing the challenge encapsulation, before
    letting the adversary run. For this exercise, we want to stay as
    generic as possible: it is possible that the KEM is stateful, or
    uses an RO that we model as stateful.

    This proof only requires that (independent) encapsulation and
    decapsulation can equivalently be done in any order.
**)
local module Game0 = {
  var sk : skey
  var c0 : (kct * dct) option

  module O = {
    proc dec(c) = {
      var r <- None;

      if (c0 <> Some c) {
        r <@ KEMDEM(E_kem, E_s).dec(sk, c);
      }
      return r;
    }
  }

  proc run(b : bool) = {
    var pk, k, kc, c, r, m0, m1;

    c0 <- None;
    (pk, sk) <@ E_kem.keygen();
    (k, kc) <@ E_kem.enc(pk);
    (m0, m1) <@ A(O).choose(pk);
    c <@ E_s.enc(k, if b then m1 else m0);
    c0 <- Some (kc, c);
    r <@ A(O).distinguish(kc, c);
    return r;
  }
}.

(** The eager tactic requires us to offload some things to global
    state. Don't ask me why: I don't know. **)
local module WAT = {
  var pk : pkey
  var kc : key * kct

  proc challenge() = {
    kc <@ E_kem.enc(pk);
  }
}.

(** Encapsulation swaps with the CCA adversary's run **)
local lemma swap_challenge:
  eager [WAT.challenge();, A(PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).O).choose
       ~ A(PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).O).choose, WAT.challenge();:
    ={glob E_kem, glob E_s, glob A, glob PKE_CCA_Exp, WAT.pk, WAT.kc, arg}
    ==> ={glob E_kem, glob E_s, glob A, glob PKE_CCA_Exp, WAT.kc, res} ].
proof.
eager proc (={glob PKE_CCA_Exp, glob E_kem, glob E_s, WAT.pk, WAT.kc})=> |>.
+ call (: ={glob E_kem, WAT.pk, WAT.kc} ==> ={glob E_kem, WAT.pk, WAT.kc})=> //.
  by sim.
+ eager proc; inline WAT.challenge.
  case: ((PKE_CCA_Exp.c0 = Some c){1}).
  + rcondf {1} 3; 1:by auto; call (: true); auto.
    rcondf {2} 2; 1:by auto.
    by auto; call (: true); auto.
  rcondt {1} 3; 1:by auto; call (: true); auto.
  rcondt {2} 2; 1:by auto.
  inline KEMDEM(E_kem, E_s).dec.
  swap {2} 10 -3; swap {1} 1 5.
  outline {1} [6..7] ~ KEMC(E_kem).enc_dec.
  rewrite equiv [{1} 6 kemC].
  inline KEMC(E_kem).dec_enc.
  by sim.
+ by sim.
+ by sim.
qed.

(* And now in context *)
local lemma pke_game0 b &m:
    Pr[PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run(b) @ &m: res]
  = Pr[Game0.run(b) @ &m: res].
proof.
byequiv (: ={glob A, glob E_kem, glob E_s, arg} ==> ={res})=> //.
proc; inline {1} ^c<@.
wp; call (: ={glob E_s, glob E_kem}
         /\ ={c0, sk}(PKE_CCA_Exp, Game0)).
+ by sim.
wp; call (: true).
swap {1} ^m<- 1. swap {1} ^pk0<- -1.
seq 3 2: (#pre
       /\ ={c0, sk}(PKE_CCA_Exp, Game0)
       /\ ={pk}
       /\ pk{1} = pk0{1}).
+ by auto; call (: true); auto.
wp; conseq (: ={glob A, glob E_kem, glob E_s, k, kc, m0, m1}
           /\ ={c0, sk}(PKE_CCA_Exp, Game0))=> />.
symmetry.
transitivity {1} {
  WAT.pk <- pk;
  WAT.kc <- witness;
  WAT.challenge();
  (m0, m1) <@ A(PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).O).choose(pk);
  (k, kc) <- WAT.kc;
} (   ={glob A, glob E_kem, glob E_s, pk}
   /\ ={c0, sk}(Game0, PKE_CCA_Exp)
   ==> ={glob A, glob E_kem, glob E_s, k, kc, m0, m1})
  (   ={glob A, glob E_kem, glob E_s, glob PKE_CCA_Exp, pk}
   /\ pk{2} = pk0{2}
   ==> ={glob A, glob E_kem, glob E_s, k, kc, m0, m1})=> [/#|//||].
+ by inline *; swap {2} -1 -1; sim; wp; call (: true); auto.
transitivity {1} {
  WAT.pk <- pk;
  WAT.kc <- witness;
  (m0, m1) <@ A(PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).O).choose(pk);
  WAT.challenge();
  (k, kc) <- WAT.kc;
} (   ={glob A, glob E_kem, glob E_s, glob PKE_CCA_Exp, pk}
   ==> ={glob A, glob E_kem, glob E_s, k, kc, m0, m1})
  (   ={glob A, glob E_kem, glob E_s, glob PKE_CCA_Exp, pk}
   /\ pk{2} = pk0{2}
   ==> ={glob A, glob E_kem, glob E_s, k, kc, m0, m1})=> [/#|//||].
+ by wp; sp; eager call swap_challenge; auto=> />.
inline *; wp; call (: true); sp.
conseq (: ={glob A, glob E_kem, glob E_s, m0, m1})=> />.
by sim.
qed.

local lemma adv_pke_game0 &m:
    `|  Pr[PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
      - Pr[PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run(true)  @ &m: res]|
  = `|  Pr[Game0.run(false) @ &m: res]
      - Pr[Game0.run(true)  @ &m: res]|.
proof. by rewrite !(pke_game0 _ &m). qed.

(** In Game1, we no longer decapsulate in the decryption oracle if
    the first half of the ciphertext is that used in the challenge;
    instead, we recover the key by correctness.
**)
local module Game1 = {
  var sk : skey
  var c0 : (kct * dct) option
  var kc0 : kct
  var k0 : key

  module O = {
    proc dec(c) = {
      var k, kc, dc, m;
      var r <- None;

      (kc, dc) <- c;
      if (c0 <> Some (kc, dc)) {
        if (kc = kc0) {
          k <- Some k0;
        } else {
          k <@ E_kem.dec(sk, kc);
        }
        if (k <> None) {
          m <@ E_s.dec(oget k, dc);
          r <- Some m;
        }
      }
      return r;
    }
  }

  proc run(b : bool) = {
    var pk, c, r, m0, m1;

    c0 <- None;
    (pk, sk) <@ E_kem.keygen();
    (k0, kc0) <@ E_kem.enc(pk);
    (m0, m1) <@ A(O).choose(pk);
    c <@ E_s.enc(k0, if b then m1 else m0);
    c0 <- Some (kc0, c);
    r <@ A(O).distinguish(kc0, c);
    return r;
  }
}.

local equiv game0_cor0_dec:
  Game0.O.dec ~ B_cor_b(E_s, A, KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).O).O_PKE.dec:
       ={glob E_kem, glob E_s}
    /\ arg{1} = (kc, dc){2}
    /\ ={sk}(Game0, KEM_Correctness_b)
    /\ ={c0}(Game0, B_cor_b)
    /\ !KEM_Correctness_b.b0{2}
    ==>    ={glob E_kem, glob E_s, res}
        /\ ={sk}(Game0, KEM_Correctness_b)
        /\ ={c0}(Game0, B_cor_b)
        /\ !KEM_Correctness_b.b0{2}.
proof.
proc; inline *; sp; if=> //.
rcondf {2} 2; 1:by auto=> />.
sp; seq 1 1: (#pre /\ k{1} = r0{2}).
+ by call (: true).
sp; if=> //; auto.
by wp; call (: true).
qed.

local equiv game0_cor0:
  Game0.run ~ KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A} /\ !b{2} /\ b{1} = B_cor_b.b_lor{2}
    ==> ={res}.
proof.
proc; inline {2} ^r<@.
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk}(Game0, KEM_Correctness_b)
         /\ ={c0}(Game0, B_cor_b)
         /\ !KEM_Correctness_b.b0{2}).
+ by conseq game0_cor0_dec=> />.
wp; call (: true).
call (: ={glob E_s, glob E_kem}
     /\ ={sk}(Game0, KEM_Correctness_b)
     /\ ={c0}(Game0, B_cor_b)
     /\ !KEM_Correctness_b.b0{2}).
+ conseq game0_cor0_dec=> />.
by wp; call (: true); call (: true); auto=> />.
qed.

local equiv game1_cor1_dec:
  Game1.O.dec ~ B_cor_b(E_s, A, KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).O).O_PKE.dec:
       ={glob E_kem, glob E_s}
    /\ arg{1} = (kc, dc){2}
    /\ ={sk, k0}(Game1, KEM_Correctness_b)
    /\ Game1.kc0{1} = KEM_Correctness_b.c0{2}
    /\ ={c0}(Game1, B_cor_b)
    /\ KEM_Correctness_b.b0{2}
    ==>    ={glob E_kem, glob E_s, res}
        /\ ={sk, k0}(Game1, KEM_Correctness_b)
        /\ Game1.kc0{1} = KEM_Correctness_b.c0{2}
        /\ ={c0}(Game1, B_cor_b)
        /\ KEM_Correctness_b.b0{2}.
proof.
proc; inline *; sp; if=> //.
seq 1 3: (#pre /\ ={k}).
+ sp; if; auto.
  by call (: true).
by if=> //; auto; call (: true).
qed.

local equiv game1_cor1:
  Game1.run ~ KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A} /\ b{2} /\ b{1} = B_cor_b.b_lor{2}
    ==> ={res}.
proof.
proc; inline {2} ^r<@.
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk, k0}(Game1, KEM_Correctness_b) /\ Game1.kc0{1} = KEM_Correctness_b.c0{2}
         /\ ={c0}(Game1, B_cor_b)
         /\ KEM_Correctness_b.b0{2})=> //.
+ by conseq game1_cor1_dec.
wp; call (: true).
call (: ={glob E_s, glob E_kem}
     /\ ={sk, k0}(Game1, KEM_Correctness_b) /\ Game1.kc0{1} = KEM_Correctness_b.c0{2}
     /\ ={c0}(Game1, B_cor_b)
     /\ KEM_Correctness_b.b0{2})=> //.
+ by conseq game1_cor1_dec.
by auto; call (: true); call (: true); auto=> />.
qed.

local lemma game0_game1_cor0 &m:
    `|  Pr[Game0.run(false) @ &m: res]
      - Pr[Game1.run(false) @ &m: res]|
  = `|  Pr[KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run(true) @ &m: res]|.
proof.
do !congr.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} ==> ={res})=> //.
  transitivity
    KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ !B_cor_b.b_lor{2} ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ !B_cor_b.b_lor{1} ==> ={res})=> [/#|//||].
  + by conseq game0_cor0=> />.
  proc; inline {2} ^r<@.
  swap {2} ^B_cor_b.b_lor<- @ 1; sp 0 2.
  by sim />=> /#.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ !b{1} /\ b{2} ==> ={res})=> //.
  transitivity
    KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ b{2} /\ !B_cor_b.b_lor{2} ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ !B_cor_b.b_lor{1} ==> ={res})=> [/#|//||].
  + by conseq game1_cor1=> />.
  proc; inline {2} ^r<@.
  swap {2} ^B_cor_b.b_lor<- @ 1; sp 0 2.
  by sim />=> /#.
qed.

local lemma game0_game1_cor1 &m:
    `|  Pr[Game0.run(true) @ &m: res]
      - Pr[Game1.run(true) @ &m: res]|
  = `|  Pr[KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run(true) @ &m: res]|.
proof.
do !congr.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} ==> ={res})=> //.
  transitivity
    KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} /\ B_cor_b.b_lor{2} ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ B_cor_b.b_lor{1} ==> ={res})=> [/#|//||].
  + by conseq game0_cor0=> />.
  proc; inline {2} ^r<@.
  swap {2} ^B_cor_b.b_lor<- @ 1; sp 0 2.
  by sim />=> /#.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} ==> ={res})=> //.
  transitivity
    KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ B_cor_b.b_lor{2} ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ B_cor_b.b_lor{1} ==> ={res})=> [/#|//||].
  + by conseq game1_cor1=> />.
  proc; inline {2} ^r<@.
  swap {2} ^B_cor_b.b_lor<- @ 1; sp 0 2.
  by sim />=> /#.
qed.

(** In Game 2, we use a random key in the challenge DEM encryption.
**)
local module Game2 = {
  var sk : skey
  var c0 : (kct * dct) option
  var kc0 : kct
  var k0 : key

  module O = {
    proc dec(c) = {
      var k, kc, dc, m;
      var r <- None;

      (kc, dc) <- c;
      if (c0 <> Some (kc, dc)) {
        if (kc = kc0) {
          k <- Some k0;
        } else {
          k <@ E_kem.dec(sk, kc);
        }
        if (k <> None) {
          m <@ E_s.dec(oget k, dc);
          r <- Some m;
        }
      }
      return r;
    }
  }

  proc run(b : bool) = {
    var pk, c, r, m0, m1;

    c0 <- None;
    (pk, sk) <@ E_kem.keygen();
    (k0, kc0) <@ E_kem.enc(pk);
    k0 <$ dkey;
    (m0, m1) <@ A(O).choose(pk);
    c <@ E_s.enc(k0, if b then m1 else m0);
    c0 <- Some (kc0, c);
    r <@ A(O).distinguish(kc0, c);
    return r;
  }
}.

local equiv game1_kem0_dec:
  Game1.O.dec ~ B_kem_b(E_s, A, KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).O).O_PKE.dec:
       ={glob E_s, glob E_kem}
    /\ arg{1} = (kc, dc){2}
    /\ ={sk}(Game1, KEM_CCA_Exp) /\ Game1.kc0{1} = KEM_CCA_Exp.c{2}
    /\ ={c0, k0, kc0}(Game1, B_kem_b)
    ==>    ={glob E_s, glob E_kem, res}
        /\ ={sk}(Game1, KEM_CCA_Exp) /\ Game1.kc0{1} = KEM_CCA_Exp.c{2}
        /\ ={c0, k0, kc0}(Game1, B_kem_b).
proof.
proc; sp; if; auto.
seq 1 1: (#pre /\ ={k})=> />.
+ if; auto.
  inline {2} ^k<@.
  rcondt {2} 3; 1:by auto=> /#.
  by wp; call (: true); auto.
if; auto.
by call (: true).
qed.

local equiv game1_kem0:
  Game1.run ~ KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run:
    ={glob A, glob E_s, glob E_kem} /\ b{1} = B_kem_b.b_lor{2} /\ !b{2}
    ==> ={res}.
proof.
proc; inline {2} ^r<@.
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk}(Game1, KEM_CCA_Exp) /\ Game1.kc0{1} = KEM_CCA_Exp.c{2}
         /\ ={c0, k0, kc0}(Game1, B_kem_b)).
+ by conseq game1_kem0_dec.    
auto; call (: true).
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk}(Game1, KEM_CCA_Exp) /\ Game1.kc0{1} = KEM_CCA_Exp.c{2}
         /\ ={c0, k0, kc0}(Game1, B_kem_b)).
+ by conseq game1_kem0_dec.    
by auto; call (: true); call (: true); auto=> />.
qed.

local equiv game2_kem1_dec:
  Game2.O.dec ~ B_kem_b(E_s, A, KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).O).O_PKE.dec:
       ={glob E_s, glob E_kem}
    /\ arg{1} = (kc, dc){2}
    /\ ={sk}(Game2, KEM_CCA_Exp) /\ Game2.kc0{1} = KEM_CCA_Exp.c{2}
    /\ ={c0, k0, kc0}(Game2, B_kem_b)
    ==>    ={glob E_s, glob E_kem, res}
        /\ ={sk}(Game2, KEM_CCA_Exp) /\ Game2.kc0{1} = KEM_CCA_Exp.c{2}
        /\ ={c0, k0, kc0}(Game2, B_kem_b).
proof.
proc; sp; if; auto.
seq 1 1: (#pre /\ ={k}).
+ if; auto.
  inline {2} ^k<@.
  rcondt {2} 3; 1:by auto=> /#.
  by wp; call (: true); auto.
if; auto.
by call (: true).
qed.

local equiv game2_kem1:
  Game2.run ~ KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run:
    ={glob A, glob E_s, glob E_kem} /\ b{1} = B_kem_b.b_lor{2} /\ b{2}
    ==> ={res}.
proof.
proc; inline {2} ^r<@.
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk}(Game2, KEM_CCA_Exp) /\ Game2.kc0{1} = KEM_CCA_Exp.c{2}
         /\ ={c0, k0, kc0}(Game2, B_kem_b)).
+ by conseq game2_kem1_dec.
auto; call (: true).
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk}(Game2, KEM_CCA_Exp) /\ Game2.kc0{1} = KEM_CCA_Exp.c{2}
         /\ ={c0, k0, kc0}(Game2, B_kem_b)).
+ by conseq game2_kem1_dec.
by auto; call (: true); call (: true); auto=> />.
qed.

local lemma game1_game2_kem0 &m:
    `|  Pr[Game1.run(false) @ &m: res]
      - Pr[Game2.run(false) @ &m: res]|
  = `|  Pr[KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res]|.
proof.
do !congr.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} ==> ={res})=> //.
  transitivity
    KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ !B_kem_b.b_lor{2}
     ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ !B_kem_b.b_lor{1}
     ==> ={res})=> [/#|//||].
  + by conseq game1_kem0=> />.
  proc; inline *; sim />.
  by wp; sim />.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ !b{1} /\ b{2} ==> ={res})=> //.
  transitivity
    KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ b{2} /\ !B_kem_b.b_lor{2}
     ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ !B_kem_b.b_lor{1}
     ==> ={res})=> [/#|//||].
  + by conseq game2_kem1=> />.
  proc; inline *; sim />.
  by wp; sim />.
qed.

local lemma game1_game2_kem1 &m:
    `|  Pr[Game1.run(true) @ &m: res]
      - Pr[Game2.run(true) @ &m: res]|
  = `|  Pr[KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res]|.
proof.
do !congr.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} ==> ={res})=> //.
  transitivity
    KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} /\ B_kem_b.b_lor{2}
     ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ B_kem_b.b_lor{1}
     ==> ={res})=> [/#|//||].
  + by conseq game1_kem0=> />.
  proc; inline *; sim />.
  by wp; sim />.
+ byequiv (: ={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} ==> ={res})=> //.
  transitivity
    KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ B_kem_b.b_lor{2}
     ==> ={res})
    (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ B_kem_b.b_lor{1}
     ==> ={res})=> [/#|//||].
  + by conseq game2_kem1=> />.
  proc; inline *; sim />.
  by wp; sim />.
qed.

local equiv game2_dem:
  Game2.run ~ DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run:
    ={glob E_s, glob E_kem, glob A, b} ==> ={res}.
proof.
proc; inline {2} ^r<@; inline {2} 3.
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk, c0, kc0}(Game2, B_s)
         /\ ={k0}(Game2, DEM_CCA_Exp)
         /\ omap fst Game2.c0{1} = Some Game2.kc0{1}
         /\ omap snd Game2.c0{1} = DEM_CCA_Exp.c0{2}).
+ proc; sp; if; auto.
  if; auto.
  + rcondt {1} 2; 1:by auto.
    inline {2} ^r<@.
    rcondt {2} 3; 1:by auto=> /#.
    by wp; call (: true); auto.
  + seq 1 1: (#pre /\ ={k}); 1:by call (: true).
    by conseq />; sim.
wp; call (: true); wp.
wp; call (: ={glob E_s, glob E_kem}
         /\ ={sk, c0, kc0}(Game2, B_s)
         /\ ={k0}(Game2, DEM_CCA_Exp)
         /\ Game2.c0{1} = None
         /\ DEM_CCA_Exp.c0{2} = None).
+ proc.
  rcondt {1} 3; 1:by auto.
  rcondt {2} 3; 1:by auto.
  sp; if; auto.
  + inline {2} ^r<@.
    rcondt {1} 2; 1:by auto.
    rcondt {2} 3; 1:by auto.
    by wp; call (: true); auto.
  seq 1 1: (#pre /\ ={k}); 1:by call (: true).
  by if; auto; call (: true).
by swap {2} 2 3; auto; call (: true); call (: true); auto.
qed.

local lemma game2_game2_dem &m:
    `|  Pr[Game2.run(false) @ &m: res]
      - Pr[Game2.run(true) @ &m: res]|
  = `|  Pr[DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run(false) @ &m: res]
      - Pr[DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run(true) @ &m: res]|.
proof. by do !congr; byequiv game2_dem. qed.

lemma security_of_kem_dem &m:
     `|  Pr[PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
       - Pr[PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run(true)  @ &m: res]|
  <=   `|  Pr[KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run(false) @ &m: res]
         - Pr[KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run(true)  @ &m: res]|
     + `|  Pr[KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
         - Pr[KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run(true)  @ &m: res]|
     + `|  Pr[DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run(false) @ &m: res]
         - Pr[DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run(true)  @ &m: res]|
     + `|  Pr[KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res]
         - Pr[KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run(true)  @ &m: res]|
     + `|  Pr[KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run(false) @ &m: res]
         - Pr[KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run(true)  @ &m: res]|.
proof.
smt(pke_game0 game0_game1_cor0 game1_game2_kem0 game2_game2_dem game1_game2_kem1 game0_game1_cor1).
qed.

end section.

print security_of_kem_dem.
