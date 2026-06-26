(* As specified in Boneh and Shoup's "Graduate Course in Applied Cryptography"
     https://toc.cryptobook.us/
   (Exercise 11.9 of version 0.6.)
*)
prover debug verbose selected  ["Z3@4.13.4"].
require import AllCore Distr.
(* We prepare to instantiate our assumptions (those files need to be
   inspected to understand what we prove!) *)
require (*--*) KEM_CPA DEM_OTS PKE_CPA.

(* Given sets of public keys, secret keys, plaintexts, DEM keys, KEM
   ciphertexts and DEM ciphertexts ... *)
type pkey, skey, ptxt, key, kct, dct.

(* ... and the uniform distribution over the DEM key space *)
op [lossless full uniform] dkey : key distr.

(** We instantiate the KEM library with the types and distribution
    above.
**)
clone import KEM_CPA as KEM with
  type pkey           <- pkey,
  type skey           <- skey,
  type shared_secret  <- key,
  type ctxt           <- kct,
  op   dkey           <- dkey
(* This requires discharging assumptions made on the types and
   distribution in the library *)
proof *.
realize dkey_ll  by exact: dkey_ll.
realize dkey_uni by exact: dkey_uni.
realize dkey_fu  by exact: dkey_fu.

(** We instantiate the DEM library (in its LoR variant here) with the
    types and distribution above.
**)
clone import DEM_OTS as DEM with
  type key  <- key,
  type ptxt <- ptxt,
  type ctxt <- dct,
  op   dkey <- dkey,
  (* An alternative way of discharging assumptions *)
  lemma dkey_ll  <- dkey_ll,
  lemma dkey_uni <- dkey_uni,
  lemma dkey_fu  <- dkey_fu
(* This is for safety: check that we don't have leftover axioms *)
proof *.

(** We instantiate the PKE library (in its LoR variant here) with the
    types and distribution above.
**)
clone import PKE_CPA as PKE with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- kct * dct
proof *.

(** We can now define our KEM/DEM composition **)
module KEMDEM (K : KEM) (E : DEM): PKE = {
  proc keygen = K.keygen

  proc enc(pk : pkey, m : ptxt): kct * dct = {
    var k, kc, c;

    (kc, k) <@ K.encaps(pk);
    c <@ E.enc(k, m);
    return (kc, c);
  }

  proc dec(sk : skey, c : kct * dct): ptxt option = {
    var kc, dc, r, k, m;

    (kc, dc) <- c;
    r <- None;
    k <@ K.decaps(sk, kc);
    if (k <> None) {
      m <@ E.dec(oget k, dc);
      r <- Some m;
    }
    return r;
  }
}.

(*** And we prove its security: there exist reductions R1(E),
       R3(E) and R2(K) such that ...
***)
module (R1 (E : DEM) (A : PKE_CPA_Adv) : KEM_CPA_Adv) (O : KEM_CPA_Oracles) = {
  module Challenger = {
    include O [initialize, pk]

    proc enc(mL, mR : ptxt) = {
      var c_kem, k_dem, c_dem;

      (c_kem, k_dem) <@ O.enc();
      c_dem <@ E.enc(k_dem, mL);
      return (c_kem, c_dem);
    }
  }

  proc distinguish = A(Challenger).distinguish
}.

module (R2 (K : KEM) (A : PKE_CPA_Adv) : DEM_OTS_Adv) (O : DEM_OTS_Oracles) = {
  var pk : pkey
  var sk : skey

  module Challenger = {
    proc initialize() = {
      (pk, sk) <@ K.keygen();
    }

    proc pk() = {
      return pk;
    }

    proc enc(mL, mR) = {
      var c_kem, k_dem, c_dem;

      (c_kem, k_dem) <@ K.encaps(pk);
      c_dem <@ O.enc(mL, mR);
      return (c_kem, c_dem);
    }
  }

  proc distinguish() = {
    var b;

    Challenger.initialize();
    b <@ A(Challenger).distinguish();
    return b;
  }
}.

module (R3 (E : DEM) (A : PKE_CPA_Adv) : KEM_CPA_Adv) (O : KEM_CPA_Oracles) = {
  module Challenger = {
    include O [initialize, pk]

    proc enc(mL : ptxt, mR) = {
      var c_kem, k_dem, c_dem;

      (c_kem, k_dem) <@ O.enc();
      c_dem <@ E.enc(k_dem, mR);
      return (c_kem, c_dem);
    }
  }

  proc distinguish = A(Challenger).distinguish
}.

section.
(* For every KEM K *)
declare module K <: KEM { -PKE_CPA_Left, -PKE_CPA_Right, -DEM_OTS_Left, -DEM_OTS_Right, -KEM_CPA_Real, -KEM_CPA_Ideal, -R2 }.
(* For every DEM E *)
declare module E <: DEM { -PKE_CPA_Left, -PKE_CPA_Right, -DEM_OTS_Left, -DEM_OTS_Right, -KEM_CPA_Real, -KEM_CPA_Ideal, -R2, -K }.
(* and for every CPA adversary against the PKE KEMDEM(K, E) *)
declare module A <: PKE_CPA_Adv { -PKE_CPA_Left, -PKE_CPA_Right, -DEM_OTS_Left, -DEM_OTS_Right, -KEM_CPA_Real, -KEM_CPA_Ideal, -R2, -K, -E }.
(* we have
        Adv^{CPA}_{KEMDEM(K, E)}(A)
     <=   Adv^{CPA}_{K}(B_kem_0(E, A))
        + Adv^{CPA}_{K}(B_kem_1(E, A))
        + Adv^{OTS}_{E}(B_s(K, A))
*)

(** The rest of this section is analyzing the claim above, culminating
    with a proof for it-in its final lemma `security_of_kem_dem`,
    which is as stated immediately above.
**)
local module Game0 = {
  var pk : pkey
  var sk : skey

  module Challenger = {
    proc initialize() = {
      (pk, sk) <@ K.keygen();
    }

    proc pk() = {
      return pk;
    }

    proc enc(mL, mR : ptxt) = {
      var c_kem, k_dem, c_dem;

      (c_kem, k_dem) <@ K.encaps(pk);
      c_dem <@ E.enc(k_dem, mL);
      return (c_kem, c_dem);
    }
  }

  proc run() = {
    var b;

    Challenger.initialize();
    b <@ A(Challenger).distinguish();
    return b;
  }
}.

local equiv ToGame0:
  PKE_CPA_Exp(PKE_CPA_Left(KEMDEM(K, E)), A).run ~ Game0.run:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(PKE_CPA_Left, Game0))=> //.
+ by sim.
+ by sim.
+ by proc; inline {1} 1; wp; sim.
by conseq />; sim.
qed.

local lemma GameHop0 &m:
  Pr[PKE_CPA_Exp(PKE_CPA_Left(KEMDEM(K, E)), A).run() @ &m: res] = Pr[Game0.run() @ &m: res].
proof. by byequiv ToGame0. qed.

local equiv ToR1:
  Game0.run ~ KEM_CPA_Exp(KEM_CPA_Real(K), R1(E, A)).run:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(Game0, KEM_CPA_Real))=> //.
+ by sim.
+ by sim.
+ by proc; inline {2} 1; sim.
by conseq />; sim.
qed.

local module Game1 = {
  var pk : pkey
  var sk : skey

  module Challenger = {
    proc initialize() = {
      (pk, sk) <@ K.keygen();
    }

    proc pk() = {
      return pk;
    }

    proc enc(mL, mR : ptxt) = {
      var c_kem, k_dem, c_dem;

      (c_kem, k_dem) <@ K.encaps(pk);
      k_dem <$ dkey;
      c_dem <@ E.enc(k_dem, mL);
      return (c_kem, c_dem);
    }
  }

  proc run() = {
    var b;

    Challenger.initialize();
    b <@ A(Challenger).distinguish();
    return b;
  }
}.

local equiv ToGame1:
  KEM_CPA_Exp(KEM_CPA_Ideal(K), R1(E, A)).run ~ Game1.run:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(KEM_CPA_Ideal, Game1))=> //.
+ by sim.
+ by sim.
+ by proc; inline {1} 1; sim.
by conseq />; sim.
qed.

local lemma GameHop1 &m:
  `|  Pr[Game0.run() @ &m: res]
    - Pr[Game1.run() @ &m: res] |
  <= `|  Pr[KEM_CPA_Exp(KEM_CPA_Real(K), R1(E, A)).run() @ &m: res]
       - Pr[KEM_CPA_Exp(KEM_CPA_Ideal(K), R1(E, A)).run() @ &m: res] |.
proof.
have ->: Pr[Game0.run() @ &m: res] = Pr[KEM_CPA_Exp(KEM_CPA_Real(K), R1(E, A)).run() @ &m: res].
+ by byequiv ToR1.
have -> //: Pr[Game1.run() @ &m: res] = Pr[KEM_CPA_Exp(KEM_CPA_Ideal(K), R1(E, A)).run() @ &m: res].
by rewrite eq_sym; byequiv ToGame1.
qed.

local equiv ToR2:
  Game1.run ~ R2(K, A, DEM_OTS_Left(E)).distinguish:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(Game1, R2))=> //.
+ by sim.
+ by sim.
+ by proc; inline {2} 2; sim.
by conseq />; sim.
qed.

local module Game2 = {
  var pk : pkey
  var sk : skey

  module Challenger = {
    proc initialize() = {
      (pk, sk) <@ K.keygen();
    }

    proc pk() = {
      return pk;
    }

    proc enc(mL : ptxt, mR) = {
      var c_kem, k_dem, c_dem;

      (c_kem, k_dem) <@ K.encaps(pk);
      k_dem <$ dkey;
      c_dem <@ E.enc(k_dem, mR);
      return (c_kem, c_dem);
    }
  }

  proc run() = {
    var b;

    Challenger.initialize();
    b <@ A(Challenger).distinguish();
    return b;
  }
}.

local equiv ToGame2:
  R2(K, A, DEM_OTS_Right(E)).distinguish ~ Game2.run:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(R2, Game2))=> //.
+ by sim.
+ by sim.
+ by proc; inline {1} 2; sim.
by conseq />; sim.
qed.

local lemma GameHop2 &m:
  `|  Pr[Game1.run() @ &m: res]
    - Pr[Game2.run() @ &m: res] |
  <= `|  Pr[R2(K, A, DEM_OTS_Left(E)).distinguish() @ &m: res]
       - Pr[R2(K, A, DEM_OTS_Right(E)).distinguish() @ &m: res] |.
proof.
have ->: Pr[Game1.run() @ &m: res] = Pr[R2(K, A, DEM_OTS_Left(E)).distinguish() @ &m: res].
+ by byequiv ToR2.
have -> //: Pr[Game2.run() @ &m: res] = Pr[R2(K, A, DEM_OTS_Right(E)).distinguish() @ &m: res].
by rewrite eq_sym; byequiv ToGame2.
qed.

local equiv ToR3:
  Game2.run ~ KEM_CPA_Exp(KEM_CPA_Ideal(K), R3(E, A)).run:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(Game2, KEM_CPA_Ideal))=> //.
+ by sim.
+ by sim.
+ by proc; inline {2} 1; sim.
by conseq />; sim.
qed.

local module Game3 = {
  var pk : pkey
  var sk : skey

  module Challenger = {
    proc initialize() = {
      (pk, sk) <@ K.keygen();
    }

    proc pk() = {
      return pk;
    }

    proc enc(mL : ptxt, mR) = {
      var c_kem, k_dem, c_dem;

      (c_kem, k_dem) <@ K.encaps(pk);
      c_dem <@ E.enc(k_dem, mR);
      return (c_kem, c_dem);
    }
  }

  proc run() = {
    var b;

    Challenger.initialize();
    b <@ A(Challenger).distinguish();
    return b;
  }
}.

local equiv ToGame3:
  KEM_CPA_Exp(KEM_CPA_Real(K), R3(E, A)).run ~ Game3.run:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(KEM_CPA_Real, Game3))=> //.
+ by sim.
+ by sim.
+ by proc; inline {1} 1; sim.
by conseq />; sim.
qed.

local lemma GameHop3 &m:
  `|  Pr[Game2.run() @ &m: res]
    - Pr[Game3.run() @ &m: res] |
  <= `|  Pr[KEM_CPA_Exp(KEM_CPA_Real(K), R3(E, A)).run() @ &m: res]
       - Pr[KEM_CPA_Exp(KEM_CPA_Ideal(K), R3(E, A)).run() @ &m: res] |.
proof.
have ->: Pr[Game2.run() @ &m: res] = Pr[KEM_CPA_Exp(KEM_CPA_Ideal(K), R3(E, A)).run() @ &m: res].
+ by byequiv ToR3.
have -> /#: Pr[Game3.run() @ &m: res] = Pr[KEM_CPA_Exp(KEM_CPA_Real(K), R3(E, A)).run() @ &m: res].
by rewrite eq_sym; byequiv ToGame3.
qed.

local equiv ToRight:
  Game3.run ~ PKE_CPA_Exp(PKE_CPA_Right(KEMDEM(K, E)), A).run:
    ={glob A, glob K, glob E} ==> ={res}.
proof.
proc; call (: ={glob K, glob E} /\ ={pk}(Game3, PKE_CPA_Right))=> //.
+ by sim.
+ by sim.
+ by proc; inline {2} 1; wp; sim.
by conseq />; sim.
qed.

local lemma GameHop4 &m:
  Pr[Game3.run() @ &m: res] = Pr[PKE_CPA_Exp(PKE_CPA_Right(KEMDEM(K, E)), A).run() @ &m: res].
proof. by byequiv ToRight. qed.

(* We can finally conclude! *)
lemma KEMDEM_PKECPA_Security &m:
  `|  Pr[PKE_CPA_Exp(PKE_CPA_Left(KEMDEM(K, E)), A).run() @ &m: res]
    - Pr[PKE_CPA_Exp(PKE_CPA_Right(KEMDEM(K, E)), A).run() @ &m: res] |
  <= `|  Pr[KEM_CPA_Exp(KEM_CPA_Real(K), R1(E, A)).run() @ &m: res]
       - Pr[KEM_CPA_Exp(KEM_CPA_Ideal(K), R1(E, A)).run() @ &m: res] |
   + `|  Pr[R2(K, A, DEM_OTS_Left(E)).distinguish() @ &m: res]
       - Pr[R2(K, A, DEM_OTS_Right(E)).distinguish() @ &m: res] |
   + `|  Pr[KEM_CPA_Exp(KEM_CPA_Real(K), R3(E, A)).run() @ &m: res]
       - Pr[KEM_CPA_Exp(KEM_CPA_Ideal(K), R3(E, A)).run() @ &m: res] |.
proof. smt(GameHop0 GameHop1 GameHop2 GameHop3 GameHop4). qed.

end section.

print KEMDEM_PKECPA_Security.
