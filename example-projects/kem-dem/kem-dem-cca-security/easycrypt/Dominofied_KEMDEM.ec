require import AllCore Distr.

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
  proc kemgen(): pkey
  proc encaps(): (kct * key) option
  proc decaps(c : kct): key option 
}.

(** A CCA adversary against the KEM is an algorithm: **)
module type KEM_CCA_Adv (O : KEM_CCA_Oracles) = {
  proc distinguish(): bool
}.

module KEM_CCA_Game (E: KEM) : KEM_CCA_Oracles = {
  var pk : pkey option
  var sk : skey option
  var c : kct option
  var b: bool

  proc kemgen() = {
    var pk_, sk_;
    if (pk = None) {
      (pk_, sk_) <@ E.keygen();
      pk <- Some pk_;
      sk <- Some sk_;
    }
    return oget pk;
  }

  proc encaps() = {
    var r <- None;
    var k_, c_;
    if (pk <> None /\ c = None) {
      (k_, c_) <@ E.enc(oget pk);
      c <- Some c_;
      if (b) {
        k_ <$ dkey;
      }
      r <- Some (c_, k_);
    }
    return r;
  }

  proc decaps(c_: kct) = {
    var r <- None;
    if (sk <> None /\ c <> None /\ Some c_ <> c) {
      r <@ E.dec(oget sk, c_);
    }
    return r;
  }
}.

(** And we define the advantage of a CCA adversary A against a KEM E
    as
      `|   Pr[KEM_CCA_Exp(E, A).run(false) @ &m: res]
         - Pr[KEM_CCA_Exp(E, A).run(true) @ &m: res]  |
    where KEM_CCA_Exp is the experiment:
**)
module KEM_CCA_Exp (E: KEM) (A : KEM_CCA_Adv) = {
  proc run(b : bool) = {
    var r;
    KEM_CCA_Game.pk <- None;
    KEM_CCA_Game.sk <- None;
    KEM_CCA_Game.c <- None;
    KEM_CCA_Game.b <- b;
    r <@ A(KEM_CCA_Game(E)).distinguish();
    return r;
  }
}.

module type KEM_Correctness_Oracles = {
  proc corr_gen(): pkey
  proc corr_encaps(): (kct * key) option
  proc corr_decaps(c : kct): key option
}.

module type KEM_Correctness_Adv (O : KEM_Correctness_Oracles) = {
  proc distinguish(): bool
}.

module KEM_Correctness_Game (E : KEM) : KEM_Correctness_Oracles = {
  var b : bool
  var pk : pkey option
  var sk : skey option
  var c : kct option
  var k : key option

  proc corr_gen() = {
    var pk_, sk_;
    if (pk = None) {
      (pk_, sk_) <@ E.keygen();
      pk <- Some pk_;
      sk <- Some sk_;
    }
    return oget pk;
  }

  proc corr_encaps() = {
    var r <- None;
    var k_, c_;
    if (pk <> None /\ c = None) {
      (k_, c_) <@ E.enc(oget pk);
      c <- Some c_;
      k <- Some k_;
      r <- Some (c_, k_);
    }
    return r;
  }

  proc corr_decaps(c_ : kct) = {
    var r <- None;
    if (sk <> None /\ c <> None) {
      if (b /\ c = Some c_) {
        r <- k;
      } else {
        r <@ E.dec(oget sk, c_);
      }
    }
    return r;
  }
}.

module KEM_Correctness_b (E : KEM) (A : KEM_Correctness_Adv) = {
  proc run(b) = {
    var r;
    KEM_Correctness_Game.pk <- None;
    KEM_Correctness_Game.sk <- None;
    KEM_Correctness_Game.c <- None;
    KEM_Correctness_Game.k <- None;
    KEM_Correctness_Game.b <- b;
    r <@ A(KEM_Correctness_Game(E)).distinguish();
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
  proc enc(m0 : pt, m1 : pt): dct option
  proc dec(c : dct): pt option
}.

(** A passive/eavesdropping DEM adversary is a pair of algorithms: **)
module type DEM_CCA_Adv (O : DEM_CCA_Oracles) = {
  proc distinguish(): bool
}.

(** And we define the advantage of a passive adversary A against a DEM
    as
      `|   Pr[DEM_PAS_Exp(E, A).run(false) @ &m: res]
         - Pr[DEM_PAS_Exp(E, A).run(true) @ &m: res]  |
    where DEM_PAS_Exp is the experiment:
**)
module DEM_CCA_Game (E : DEM) : DEM_CCA_Oracles = {
  var b : bool
  var k : key option
  var c : dct option

  proc enc(m0 : pt, m1 : pt) = {
    var c_, k_;
    var r <- None;
    if (k = None) {
      k_ <$ dkey;
      k <- Some k_;
      c_ <@ E.enc(k_, if b then m1 else m0);
      c <- Some c_;
      r <- c;
    }
    return r;
  }

  proc dec(c_ : dct) = {
    var m;
    var r <- None;

    if (k <> None /\ c <> Some c_) {
      m <@ E.dec(oget k, c_);
      r <- Some m;
    }
    return r;
  }
}.

module DEM_CCA_Exp (E : DEM) (A : DEM_CCA_Adv) = {
  proc run(b : bool) = {
    var r;

    DEM_CCA_Game.b <- b;
    DEM_CCA_Game.k <- None;
    DEM_CCA_Game.c <- None;
    r <@ A(DEM_CCA_Game(E)).distinguish();
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
  proc pkgen(): pkey
  proc pkenc(m0 : pt, m1 : pt): (kct * dct) option
  proc pkdec(c : kct * dct): pt option
}.

(** A CCA adversary against a PKE is a pair of algorithms: **)
module type PKE_CCA_Adv (O : PKE_CCA_Oracles) = {
  proc distinguish(): bool
}.

(** The advantage of a CCA adversary A against a PKE E is
      `|   Pr[PKE_CCA_Exp(E, A).run(false) @ &m: res]
         - Pr[PKE_CCA_Exp(E, A).run(true) @ &m: res]  |
    where PKE_CCA_Exp is the experiment:
**)
module PKE_CCA_Game (E : PKE) : PKE_CCA_Oracles = {
  var b : bool
  var pk : pkey option
  var sk : skey option
  var c : (kct * dct) option

  proc pkgen() = {
    var pk_, sk_;
    if (pk = None) {
      (pk_, sk_) <@ E.keygen();
      pk <- Some pk_;
      sk <- Some sk_;
    }
    return oget pk;
  }

  proc pkenc(m0 : pt, m1 : pt) = {
    var c_;
    var r <- None;
    if (pk <> None /\ c = None) {
      c_ <@ E.enc(oget pk, if b then m1 else m0);
      c <- Some c_;
      r <- c;
    }
    return r;
  }

  proc pkdec(c_ : kct * dct) = {
    var r <- None;

    if (sk <> None /\ c <> None /\ c <> Some c_) {
      r <@ E.dec(oget sk, c_);
    }
    return r;
  }
}.

module PKE_CCA_Exp (E : PKE) (A : PKE_CCA_Adv) = {
  proc run(b : bool) = {
    var r;

    PKE_CCA_Game.b <- b;
    PKE_CCA_Game.pk <- None;
    PKE_CCA_Game.sk <- None;
    PKE_CCA_Game.c <- None;
    r <@ A(PKE_CCA_Game(E)).distinguish();
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

module B_cor_b (E_s : DEM) (A : PKE_CCA_Adv) (O : KEM_Correctness_Oracles) = {
  var b_lor : bool
  var pk : pkey option
  var c : (kct * dct) option

  module O_PKE = {
    proc pkgen() = {
      var pk_;

      pk_ <@ O.corr_gen();
      pk <- Some pk_;
      return pk_;
    }

    proc pkenc(m0 : pt, m1 : pt) = {
      var kc, k, dc;
      var okc;
      var r <- None;

      if (pk <> None /\ c = None) {
        okc <@ O.corr_encaps();
        if (okc <> None) {
          (kc, k) <- oget okc;
          dc <@ E_s.enc(k, if b_lor then m1 else m0);
          c <- Some (kc, dc);
          r <- c;
        }
      }
      return r;
    }

    proc pkdec(c_ : kct * dct) = {
      var k, kc, dc, m;
      var r <- None;

      (kc, dc) <- c_;
      if (c <> None /\ c <> Some c_) {
        k <@ O.corr_decaps(kc);
        if (k <> None) {
          m <@ E_s.dec(oget k, dc);
          r <- Some m;
        }
      }
      return r;
    }
  }

	  proc distinguish() = {
	    var r;
	
	    pk <- None;
	    c <- None;
	    r <@ A(O_PKE).distinguish();
	    return r;
	  }
	}.

module (B_cor_0 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_Correctness_Adv) (O : KEM_Correctness_Oracles) = {
  proc distinguish() = {
    var b;

    B_cor_b.b_lor <- false;
    b <@ B_cor_b(E_s, A, O).distinguish();
    return b;
  }
}.

module (B_cor_1 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_Correctness_Adv) (O : KEM_Correctness_Oracles) = {
  proc distinguish() = {
    var b;

    B_cor_b.b_lor <- true;
    b <@ B_cor_b(E_s, A, O).distinguish();
    return b;
  }
}.

module B_kem_b (E_s : DEM) (A : PKE_CCA_Adv) (O : KEM_CCA_Oracles) = {
  var b_lor : bool
  var pk : pkey option
  var c : (kct * dct) option
  var k : key option

  module O_PKE = {
    proc pkgen() = {
      var pk_;

      pk_ <@ O.kemgen();
      pk <- Some pk_;
      return pk_;
    }

    proc pkenc(m0 : pt, m1 : pt) = {
      var kc, dc, okc, k_;
      var r <- None;

      if (pk <> None /\ c = None) {
        okc <@ O.encaps();
        if (okc <> None) {
          (kc, k_) <- oget okc;
          k <- Some k_;
          dc <@ E_s.enc(k_, if b_lor then m1 else m0);
          c <- Some (kc, dc);
          r <- c;
        }
      }
      return r;
    }

    proc pkdec(c_ : kct * dct) = {
      var m, kc, dc, kc_, dc_, k_;
      var r <- None;

      (kc_, dc_) <- c_;
      if (c <> None /\ c <> Some c_) {
        (kc, dc) <- oget c;
        if (kc_ = kc) {
          k_ <- k;
        } else {
          k_ <@ O.decaps(kc_);
        }
        if (k_ <> None) {
          m <@ E_s.dec(oget k_, dc_);
          r <- Some m;
        }
      }
      return r;
    }
  }

  proc distinguish() = {
    var r;

	    pk <- None;
	    c <- None;
	    k <- None;
	    r <@ A(O_PKE).distinguish();
	    return r;
	  }
}.

module (B_kem_0 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_CCA_Adv) (O : KEM_CCA_Oracles) = {
  proc distinguish() = {
    var b;

    B_kem_b.b_lor <- false;
    b <@ B_kem_b(E_s, A, O).distinguish();
    return b;
  }
}.

module (B_kem_1 (E_s : DEM) (A : PKE_CCA_Adv) : KEM_CCA_Adv) (O : KEM_CCA_Oracles) = {
  proc distinguish() = {
    var b;

    B_kem_b.b_lor <- true;
    b <@ B_kem_b(E_s, A, O).distinguish();
    return b;
  }
}.

module (B_s (E_kem : KEM) (E_s : DEM) (A : PKE_CCA_Adv) : DEM_CCA_Adv) (O : DEM_CCA_Oracles) = {
  var sk : skey option
  var c : (kct * dct) option
  var pk : pkey option

  module O_PKE = {
    proc pkgen() = {
      var pk_, sk_;

      if (pk = None) {
        (pk_, sk_) <@ E_kem.keygen();
        pk <- Some pk_;
        sk <- Some sk_;
      }
      return oget pk;
    }

    proc pkenc(m0 : pt, m1 : pt) = {
      var k, kc, c_;
      var r <- None;
      if (pk <> None /\ c = None) {
        (k, kc) <@ E_kem.enc(oget pk);
        c_ <@ O.enc(m0, m1);
        c <- Some (kc, oget c_);
        r <- c;
      }
      return r;
    }

    proc pkdec(c_ : kct * dct) = {
      var k, kc, dc, m, kc_, dc_;
      var r <- None;

      (kc_, dc_) <- c_;
      if (sk <> None /\ c <> None /\ c <> Some (kc_, dc_)) {
        (kc, dc) <- oget c;
        if (kc = kc_) {
          r <@ O.dec(dc_);
        } else {
          k <@ E_kem.dec(oget sk, kc_);
          if (k <> None) {
            m <@ E_s.dec(oget k, dc_);
            r <- Some m;
          }
        }
      }
      return r;
    }
  }

  proc distinguish() = {
    var r;

    c <- None;
    pk <- None;
    sk <- None;
    r <@ A(O_PKE).distinguish();
    return r;
  }
}.

section.

declare module E_kem <: KEM {
  -KEM_Correctness_Game, -KEM_Correctness_b, -KEM_CCA_Game, -KEM_CCA_Exp,
  -DEM_CCA_Game, -DEM_CCA_Exp, -PKE_CCA_Game, -PKE_CCA_Exp,
  -B_cor_b, -B_kem_b, -B_s
}.

declare module E_s <: DEM {
  -KEM_Correctness_Game, -KEM_Correctness_b, -KEM_CCA_Game, -KEM_CCA_Exp,
  -DEM_CCA_Game, -DEM_CCA_Exp, -PKE_CCA_Game, -PKE_CCA_Exp,
  -B_cor_b, -B_kem_b, -B_s, -E_kem
}.

declare module A <: PKE_CCA_Adv {
  -KEM_Correctness_Game, -KEM_Correctness_b, -KEM_CCA_Game, -KEM_CCA_Exp,
  -DEM_CCA_Game, -DEM_CCA_Exp, -PKE_CCA_Game, -PKE_CCA_Exp,
  -B_cor_b, -B_kem_b, -B_s, -E_kem, -E_s
}.

local equiv pke_cor0:
  PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run ~
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run:
       ={glob E_kem, glob E_s, glob A}
    /\ b{1} = B_cor_b.b_lor{2}
    /\ !b{2}
    ==> ={res}.
proof.
proc; inline {2} ^r<@.
wp; call (:   ={glob E_kem, glob E_s}
            /\ ={pk, sk}(PKE_CCA_Game, KEM_Correctness_Game)
            /\ PKE_CCA_Game.pk{1} = B_cor_b.pk{2}
            /\ ={c}(PKE_CCA_Game, B_cor_b)
            /\ KEM_Correctness_Game.c{2} = omap fst B_cor_b.c{2}
            /\ PKE_CCA_Game.b{1} = B_cor_b.b_lor{2}
            /\ !KEM_Correctness_Game.b{2}).
+ proc; inline *; sp.
  if; 1: by auto=> /> /#.
  + by wp; call (: true); auto.
  + by auto=> /> /#.
+ proc; inline *; sp.
  if; 1: by auto=> />.
  + rcondt {2} 2; 1: by auto=> />.
    seq 3 5: (   ={glob E_kem, glob E_s, m0, m1}
               /\ k{1} = k_{2}
               /\ kc{1} = c_{2}
               /\ r{1} = r{2}
               /\ r0{2} = Some (kc{1}, k{1})
               /\ m{1} = (if B_cor_b.b_lor{2} then m1{2} else m0{2})
               /\ ={pk, sk}(PKE_CCA_Game, KEM_Correctness_Game)
               /\ PKE_CCA_Game.pk{1} = B_cor_b.pk{2}
               /\ PKE_CCA_Game.c{1} = None
               /\ B_cor_b.c{2} = None
               /\ KEM_Correctness_Game.c{2} = Some kc{1}
               /\ PKE_CCA_Game.b{1} = B_cor_b.b_lor{2}
               /\ !KEM_Correctness_Game.b{2}).
    + by wp; call (: true); auto=> /> /#.
    sp 0 1.
    rcondt {2} 1; 1: by auto=> />.
    sp 0 1.
    seq 1 1: (#pre /\ c{1} = dc{2}).
    + by wp; call (: true); auto=> /> /#.
    by auto=> />.
  + by auto=> />.
+ proc; inline *; sp.
  if{1}.
  + rcondt {2} 1; 1: by auto=> />.
    rcondt {2} 3; 1: by auto=> /> /#.
    rcondf {2} 3; 1: by auto=> />.
    seq 5 4: (#pre /\ k{1} = k{2} /\ dc{1} = dc{2} /\ r0{1} = r{2}).
    + by wp; call (: true); auto=> />.
    if; 1: by auto=> />.
    + by wp; call (: true); auto=> />.
    + by auto=> />.
  + if{2}.
    + rcondf {2} 3; 1: by auto=> /> /#.
      rcondf {2} 4; 1: by auto=> />.
      by auto=> />.
    + by auto=> />.
by auto=> />.
qed.

local equiv cor1_kem0:
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run ~
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run:
       ={glob E_kem, glob E_s, glob A}
    /\ B_cor_b.b_lor{1} = B_kem_b.b_lor{2}
    /\ b{1}
    /\ !b{2}
    ==> ={res}.
proof.
proc; inline {1} ^r<@; inline {2} ^r<@.
wp; call (:   ={glob E_kem, glob E_s}
            /\ ={pk, sk}(KEM_Correctness_Game, KEM_CCA_Game)
            /\ (KEM_CCA_Game.pk{2} <> None => KEM_CCA_Game.sk{2} <> None)
            /\ KEM_Correctness_Game.c{1} = KEM_CCA_Game.c{2}
            /\ (KEM_CCA_Game.c{2} <> None => KEM_CCA_Game.sk{2} <> None)
            /\ B_cor_b.pk{1} = KEM_Correctness_Game.pk{1}
            /\ B_kem_b.pk{2} = KEM_CCA_Game.pk{2}
            /\ ={c}(B_cor_b, B_kem_b)
            /\ KEM_CCA_Game.c{2} = omap fst B_kem_b.c{2}
            /\ KEM_Correctness_Game.k{1} = B_kem_b.k{2}
            /\ B_cor_b.b_lor{1} = B_kem_b.b_lor{2}
            /\ KEM_Correctness_Game.b{1}
            /\ !KEM_CCA_Game.b{2}).
+ proc; inline *; sp.
  if; 1: by auto=> />.
  + by wp; call (: true); auto.
  + by auto=> /> /#.
+ proc; inline *; sp.
  if; 1: by auto=> />.
  + rcondt {1} 2; 1: by auto=> />.
    rcondt {2} 2; 1: by auto=> />.
    rcondf {2} 4; 1: by auto=> />.
    seq 5 4: (   ={glob E_kem, glob E_s, m0, m1, r0}
               /\ r0{1} <> None
               /\ ={pk, sk}(KEM_Correctness_Game, KEM_CCA_Game)
               /\ (KEM_CCA_Game.pk{2} <> None => KEM_CCA_Game.sk{2} <> None)
               /\ KEM_Correctness_Game.c{1} = KEM_CCA_Game.c{2}
               /\ KEM_CCA_Game.c{2} = omap fst r0{2}
               /\ (KEM_CCA_Game.c{2} <> None => KEM_CCA_Game.sk{2} <> None)
               /\ KEM_Correctness_Game.k{1} = omap snd r0{1}
               /\ B_cor_b.pk{1} = KEM_Correctness_Game.pk{1}
               /\ B_kem_b.pk{2} = KEM_CCA_Game.pk{2}
               /\ B_cor_b.c{1} = None
               /\ B_kem_b.c{2} = None
               /\ B_cor_b.b_lor{1} = B_kem_b.b_lor{2}
               /\ KEM_Correctness_Game.b{1}
               /\ !KEM_CCA_Game.b{2}).
    + by wp; call (: true); auto=> />.
    sp 1 1.
    rcondt {1} 1; 1: by auto=> />.
    rcondt {2} 1; 1: by auto=> />.
    sp 1 2.
    seq 1 1: (#pre /\ dc{1} = dc{2}).
    + by wp; call (: true); auto=> /> /#.
    by auto=> /> /#.
  + by auto=> />.
+ proc; inline *; sp.
  if; 1: by auto=> />.
  + sp 2 0.
    rcondt {1} 1; 1: by auto=> /> /#.
    sp 0 1.
    if; 1: by auto=> /> /#.
    + by sim />.
    + rcondt {2} 3; 1: by auto=> /> /#.
      seq 1 4: (   ={glob E_kem, glob E_s, r0, r}
                 /\ k_{2} = r0{2}
                 /\ dc{1} = dc_{2}
                 /\ ={pk, sk}(KEM_Correctness_Game, KEM_CCA_Game)
                 /\ (KEM_CCA_Game.pk{2} <> None => KEM_CCA_Game.sk{2} <> None)
                 /\ KEM_Correctness_Game.c{1} = KEM_CCA_Game.c{2}
                 /\ (KEM_CCA_Game.c{2} <> None => KEM_CCA_Game.sk{2} <> None)
                 /\ B_cor_b.pk{1} = KEM_Correctness_Game.pk{1}
                 /\ B_kem_b.pk{2} = KEM_CCA_Game.pk{2}
                 /\ ={c}(B_cor_b, B_kem_b)
                 /\ KEM_CCA_Game.c{2} = omap fst B_kem_b.c{2}
                 /\ KEM_Correctness_Game.k{1} = B_kem_b.k{2}
                 /\ B_cor_b.b_lor{1} = B_kem_b.b_lor{2}
                 /\ KEM_Correctness_Game.b{1}
                 /\ !KEM_CCA_Game.b{2}).
      + by wp; call (: true); auto=> /> /#.
      sp 1 0.
      if; 1: by auto=> /> /#.
      + by wp; call (: true); auto=> /> /#.
      + by auto=> /> /#.
    + by auto=> /> /#.
  + by auto=> />.
qed.

local equiv kem1_dem:
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run ~
  DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run:
       ={glob E_kem, glob E_s, glob A}
    /\ B_kem_b.b_lor{1} = b{2}
    /\ b{1}
    ==> ={res}.
proof.
proc; inline {1} ^r<@; inline {2} ^r<@.
wp; call (:   ={glob E_kem, glob E_s}
            /\ B_kem_b.pk{1} = KEM_CCA_Game.pk{1}
            /\ B_s.pk{2} = KEM_CCA_Game.pk{1}
            /\ B_s.sk{2} = KEM_CCA_Game.sk{1}
            /\ (KEM_CCA_Game.pk{1} <> None => KEM_CCA_Game.sk{1} <> None)
            /\ (KEM_CCA_Game.c{1} <> None => KEM_CCA_Game.sk{1} <> None)
            /\ ={c}(B_kem_b, B_s)
            /\ KEM_CCA_Game.c{1} = omap fst B_kem_b.c{1}
            /\ DEM_CCA_Game.c{2} = omap snd B_s.c{2}
            /\ B_kem_b.k{1} = DEM_CCA_Game.k{2}
            /\ (B_kem_b.c{1} = None => B_kem_b.k{1} = None)
            /\ B_kem_b.b_lor{1} = DEM_CCA_Game.b{2}
            /\ KEM_CCA_Game.b{1}).
+ proc; inline *; sp.
  if; 1: by auto=> />.
  + by wp; call (: true); auto.
  + by auto=> /> /#.
+ proc; inline *; sp.
  if; 1: by auto=> />.
  + rcondt {1} 2; 1: by auto=> />.
    rcondt {1} 4; 1: by auto=> />.
	    rcondt {2} 5.
	    + move=> &m.
	      wp.
	      call (: DEM_CCA_Game.k = None).
	      by auto=> /> /#.
    seq 3 1: (   ={glob E_kem, glob E_s, m0, m1}
               /\ B_kem_b.pk{1} = KEM_CCA_Game.pk{1}
	               /\ B_s.pk{2} = KEM_CCA_Game.pk{1}
	               /\ B_s.sk{2} = KEM_CCA_Game.sk{1}
	               /\ KEM_CCA_Game.pk{1} <> None
	               /\ (KEM_CCA_Game.pk{1} <> None => KEM_CCA_Game.sk{1} <> None)
	               /\ c_{1} = kc{2}
	               /\ KEM_CCA_Game.c{1} = Some kc{2}
	               /\ B_kem_b.c{1} = None
	               /\ B_kem_b.k{1} = None
	               /\ B_s.c{2} = None
	               /\ DEM_CCA_Game.k{2} = None
	               /\ DEM_CCA_Game.c{2} = None
               /\ B_kem_b.b_lor{1} = DEM_CCA_Game.b{2}
               /\ KEM_CCA_Game.b{1}).
    + by wp; call (: true); auto=> />.
    sp 0 3.
	    seq 1 1: (#pre /\ k_0{1} = k_{2}).
	    + by rnd.
	    sp 2 1.
	    rcondt {1} 1; 1: by auto=> />.
	    sp 2 0.
	    seq 1 1: (   ={glob E_kem, glob E_s, m0, m1}
	               /\ k_{1} = k_{2}
	               /\ kc{1} = kc{2}
	               /\ dc{1} = c_0{2}
	               /\ B_kem_b.pk{1} = KEM_CCA_Game.pk{1}
	               /\ B_s.pk{2} = KEM_CCA_Game.pk{1}
	               /\ B_s.sk{2} = KEM_CCA_Game.sk{1}
	               /\ KEM_CCA_Game.pk{1} <> None
	               /\ (KEM_CCA_Game.pk{1} <> None => KEM_CCA_Game.sk{1} <> None)
	               /\ KEM_CCA_Game.c{1} = Some kc{1}
	               /\ B_kem_b.k{1} = DEM_CCA_Game.k{2}
	               /\ B_kem_b.c{1} = None
	               /\ B_s.c{2} = None
	               /\ DEM_CCA_Game.c{2} = None
	               /\ B_kem_b.b_lor{1} = DEM_CCA_Game.b{2}
	               /\ KEM_CCA_Game.b{1}).
	    + by wp; call (: true); auto=> /> /#.
	    by auto=> /> /#.
  + by auto=> />.
+ proc; inline *; sp.
  if{1}.
  + rcondt {2} 1; 1: by auto=> /> /#.
    seq 1 1: (#pre /\ B_kem_b.c{1} = Some (kc{1}, dc{1})
                    /\ B_s.c{2} = Some (kc{2}, dc{2})).
    + by auto=> /> /#.
    if; 1: by auto=> /> /#.
    + sp 1 2.
      if; 1: by auto=> /> /#.
      + by sim />.
      + by auto=> /> /#.
    + rcondt {1} 3; 1: by auto=> /> /#.
      by sim />.
  + rcondf {2} 1; 1: by auto=> /> /#.
    by auto=> /> /#.
by auto=> />.
qed.

local equiv B_cor_0_wrap:
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run ~
  KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A, b} /\ !B_cor_b.b_lor{1} ==> ={res}.
proof.
proc; inline {2} ^r<@.
swap {2} ^B_cor_b.b_lor<- @ 1; sp 0 2; sp 1 0.
by sim />=> /#.
qed.

local lemma pke_cor0_0 &m:
    Pr[PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
  = Pr[KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run(false) @ &m: res].
proof.
byequiv (: ={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} ==> ={res})=> //.
transitivity
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ !B_cor_b.b_lor{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ !B_cor_b.b_lor{1}
   ==> ={res})=> [/#|//||].
+ by conseq pke_cor0=> />.
+ by conseq B_cor_0_wrap=> />.
qed.

local equiv B_cor_1_wrap:
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run ~
  KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A, b} /\ B_cor_b.b_lor{1} ==> ={res}.
proof.
proc; inline {2} ^r<@.
swap {2} ^B_cor_b.b_lor<- @ 1; sp 0 2; sp 1 0.
by sim />=> /#.
qed.

local equiv B_kem_0_wrap:
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run ~
  KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A, b} /\ !B_kem_b.b_lor{1} ==> ={res}.
proof.
proc; inline {2} ^r<@.
swap {2} ^B_kem_b.b_lor<- @ 1; sp 0 2; sp 1 0.
by sim />=> /#.
qed.

local equiv B_kem_1_wrap:
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run ~
  KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A, b} /\ B_kem_b.b_lor{1} ==> ={res}.
proof.
proc; inline {2} ^r<@.
swap {2} ^B_kem_b.b_lor<- @ 1; sp 0 2; sp 1 0.
by sim />=> /#.
qed.

local lemma pke_cor0_1 &m:
    Pr[PKE_CCA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res]
  = Pr[KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run(false) @ &m: res].
proof.
byequiv (: ={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} ==> ={res})=> //.
transitivity
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} /\ B_cor_b.b_lor{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ B_cor_b.b_lor{1}
   ==> ={res})=> [/#|//||].
+ by conseq pke_cor0=> />.
by conseq B_cor_1_wrap=> />.
qed.

local equiv cor1_kem0_0_eq:
  KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run ~
  KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} ==> ={res}.
proof.
transitivity
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ !B_cor_b.b_lor{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} /\ !B_cor_b.b_lor{1}
   ==> ={res})=> [/#|//||].
+ symmetry; by conseq B_cor_0_wrap=> />.
transitivity
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A}
   /\ B_cor_b.b_lor{1} = B_kem_b.b_lor{2}
   /\ b{1} /\ !b{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ !B_kem_b.b_lor{1}
   ==> ={res})=> [/#|//||].
+ by conseq cor1_kem0=> />.
by conseq B_kem_0_wrap=> />.
qed.

local lemma cor1_kem0_0 &m:
    Pr[KEM_Correctness_b(E_kem, B_cor_0(E_s, A)).run(true) @ &m: res]
  = Pr[KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res].
proof. by byequiv cor1_kem0_0_eq. qed.

local equiv cor1_kem0_1_eq:
  KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run ~
  KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run:
    ={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} ==> ={res}.
proof.
transitivity
  KEM_Correctness_b(E_kem, B_cor_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ B_cor_b.b_lor{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} /\ B_cor_b.b_lor{1}
   ==> ={res})=> [/#|//||].
+ symmetry; by conseq B_cor_1_wrap=> />.
transitivity
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A}
   /\ B_cor_b.b_lor{1} = B_kem_b.b_lor{2}
   /\ b{1} /\ !b{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ !b{1} /\ !b{2} /\ B_kem_b.b_lor{1}
   ==> ={res})=> [/#|//||].
+ by conseq cor1_kem0=> />.
by conseq B_kem_1_wrap=> />.
qed.

local lemma cor1_kem0_1 &m:
    Pr[KEM_Correctness_b(E_kem, B_cor_1(E_s, A)).run(true) @ &m: res]
  = Pr[KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res].
proof. by byequiv cor1_kem0_1_eq. qed.

local equiv kem1_dem_0_eq:
  KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run ~
  DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run:
    ={glob E_kem, glob E_s, glob A} /\ b{1} /\ !b{2} ==> ={res}.
proof.
transitivity
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ !B_kem_b.b_lor{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ B_kem_b.b_lor{1} = b{2} /\ b{1}
   ==> ={res})=> [/#|//||].
+ symmetry; by conseq B_kem_0_wrap=> />.
by conseq kem1_dem=> />.
qed.

local lemma kem1_dem_0 &m:
    Pr[KEM_CCA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res]
  = Pr[DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run(false) @ &m: res].
proof. by byequiv kem1_dem_0_eq. qed.

local equiv kem1_dem_1_eq:
  KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run ~
  DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run:
    ={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} ==> ={res}.
proof.
transitivity
  KEM_CCA_Exp(E_kem, B_kem_b(E_s, A)).run
  (={glob E_kem, glob E_s, glob A} /\ b{1} /\ b{2} /\ B_kem_b.b_lor{2}
   ==> ={res})
  (={glob E_kem, glob E_s, glob A} /\ B_kem_b.b_lor{1} = b{2} /\ b{1}
   ==> ={res})=> [/#|//||].
+ symmetry; by conseq B_kem_1_wrap=> />.
by conseq kem1_dem=> />.
qed.

local lemma kem1_dem_1 &m:
    Pr[KEM_CCA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res]
  = Pr[DEM_CCA_Exp(E_s, B_s(E_kem, E_s, A)).run(true) @ &m: res].
proof. by byequiv kem1_dem_1_eq. qed.

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
smt(pke_cor0_0 cor1_kem0_0 kem1_dem_0 kem1_dem_1 cor1_kem0_1 pke_cor0_1).
qed.

end section.

print security_of_kem_dem.