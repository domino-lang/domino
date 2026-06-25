# KEM-DEM: A self-contained tutorial

---

This document accompanies the proof scripts in this folder, which were used for
the EasyCrypt demonstration at [CAPS 2025](https://caps-workshop.com/). The
(pen-and-paper) proof underlying the script is heavily inspired by Exercise
11.9 from [the book "Graduate Course in Applied Cryptography" (version 0.6) by
Boneh and Shoup](https://toc.cryptobook.us/).
In essence, the proof shows that you can construct a secure public-key
encryption (PKE) scheme by combining a secure key-encapsulation mechanism (KEM)
and a secure data-encapsulation mechanism (DEM). This way of constructing a PKE
scheme is sometimes also referred to as "hybrid encryption".

In the remainder, we walk through the pen-and-paper and EasyCrypt proofs in
lockstep, comparing and contrasting them as we go. We do so by first defining
the basics, then specifying the considered (type of) schemes and their security
properties, followed by formalizing the proof artifacts, and finally presenting
the actual proof. To keep the exposition focused on the formalization of
cryptographic proofs in EasyCrypt (and the comparison to pen-and-paper proofs),
we assume some prior cryptographic knowledge throughout, particularly meaning
we won't go into detail on every cryptographic concept.

We start reading file `KEMDEM_lor.ec`, which is the main file where we define
our construction and prove its security, but we'll go explore the other files
as well.

## Basics

---

First things first: the basics. Fortunately, in this case, we don't need much more than
a couple of sets/spaces and distributions.

### Basics, Pen-and-Paper

We assume the existence of the following artifacts, forming the basis of our KEM, DEM,
and PKE scheme.

- A set $\mathcal{PK}$ of public keys called the _public key space_.
- A set $\mathcal{SK}$ of secret keys called the _secret key space_.
- A set $\mathcal{K}$ of symmetric keys called the _key space_.
- A set $\mathcal{KCT}$ of (KEM) ciphertexts called the _KEM ciphertext space_.
- A set $\mathcal{P}$ of plaintexts called the _plaintext space_.
- A set $\mathcal{DCT}$ of (DEM) ciphertexts called the _DEM ciphertext space_.
- The uniform distribution $\mathcal{U}(\mathcal{K})$ over the (entire) key space.

You may have noticed that the above doesn't define some PKE-specific components
that it does define (the analogs of) for KEMs and DEMs, e.g., a PKE ciphertext
space. This is because our construction will *instantiate* those—specializing
the notion of PKE to its specific needs. We'll get back to this.

### Basics, EasyCrypt

Starting from scratch, we formalize the above pen-and-paper definitions in EasyCrypt
as follows.[^1]

```
(* Type for (read: set of)  public keys *)
type pkey.

(* Type for (read: set of) secret keys *)
type skey.

(* Type for (read: set of) symmetric keys *)
type key.

(* Type for (read: set of) KEM ciphertexts *)
type kct.

(* Type for (read: set of) plaintexts *)
type pt.

(* Type for (read: set of) DEM ciphertexts *)
type dct.

(* Distribution over symmetric keys (at this point, not uniform yet) *)
op dkey : key distr.

(* Assume properties on dkey, making it the uniform distribution *)
(*
    Lossless (technicality):
    Total probablity sums up to 1.
*)
axiom dkey_ll : is_lossless dkey .

(*
    Full:
    All elements of type key (read: all symmetric keys) have non-zero probability.
*)
axiom dkey_fu : is_full dkey .

(*
    Uniform:
    All elements of type key (read: all symmetric keys) with non-zero probability
    have the same probability
*)
axiom dkey_uni : is_uniform dkey.
```

While this is the "official", bare-bones way of going about it, this is rather verbose
for something so basic and ubiquitous; and, in fact, it can be shortened to the following.

```
(* Types for (read: sets of) public keys, secret keys, ... *)
type pkey, skey, key, kct, ptxt, dct.

(* Uniform distribution over symmetric keys *)
op [lossless full uniform] dkey : key distr.
```

That's it, this already suffices to start specifying the relevant schemes and
their security properties, which is what we'll do next.

Worthy of note: keeping those abstract here means that whatever we prove will
hold for *every* instantiation of the above that is proved to meet the axioms.
(Essentially, every instantiation of the types where the type `key` is finite
and equipped with its uniform distribution.)

[^1]:  In EasyCrypt, `(*` and `*)` delimit a (potentially multi-line) comment.


## Schemes and Security Properties

---

The next step in any good proof is to define the assumptions (KEM and DEM
security), and the proof goal (PKE security). We could do this in a specialized
way, but that would mean redefining PKE security every time we want to
construct a PKE in a different way.

Instead, we first define them generically—parameterizing them with their own
sets, and distributions, and algorithms, and experiments; then *instantiating*
them to the sets and distributions we just declared.

### KEMs, Pen-and-Paper

Formally, a KEM with public key space $\mathcal{PK}$, secret key space
$\mathcal{SK}$, key (or message) space $\mathcal{K}$ and ciphertext space
$\mathcal{C}$ is a triple of algorithms $\left(\mathsf{KeyGen},
\mathsf{Encaps}, \mathsf{Decaps}\right)$ for which the following holds.

- $\mathsf{KeyGen}$ takes no input, and outputs a public key (from $\mathcal{PK}$)
and a secret key (from $\mathcal{SK}$).
- $\mathsf{Encaps}$ takes a public key (from $\mathcal{PK}$) as input, and outputs
a symmetric key (from $\mathcal{K}$) and a KEM ciphertext (from $\mathcal{C}$)  .
- $\mathsf{Decaps}$ takes a secret key (from $\mathcal{SK}$) and a KEM ciphertext
(from $\mathcal{C}$) as input, and outputs a symmetric key (from $\mathcal{K}$)
or an explicit indication of failure ($\bot$).

Depending on the book or lecture notes you are reading, you may encounter
several additional requirements for what constitutes a KEM (e.g., a correctness
condition or some determinism constraints). However, as these are not necessary
for our purposes here, we refrain from including them. (As far as we are
concerned, all of these algorithms may be probabilistic and stateful—as before,
without further restriction, this means that our proofs apply to any (possibly
probabilistic and stateful) KEM.

In our case, the security property of interest for KEMs is the so-called
(ciphertext) INDistinguishability under Chosen-Plaintext Attacks (IND-CPA,
shortened to simply CPA) property. Intuitively, this property captures that, if
we produce a symmetric key and encapsulation using the considered KEM (in an
honest way), then *no useful information about the symmetric key can be
extracted from the encapsulation (or other public information)*. A bit more
concretely, this property requires that no (reasonable) adversary can
meaningfully distinguish between a (uniformly) random symmetric key and one
produced (honestly) using the considered KEM, even when given the corresponding
encapsulation (and public key). To formalize this, we start by constructing
a well-defined program that matches this scenario, and subsequently capture
that "no adversary can meaningfully distinguish" by requiring some probability
statement (involving this program) to be sufficiently small. More precisely, we
use the following program (also referred to as "experiment"), parameterized on
a KEM $\mathrm{E}$, adversarial algorithm $\mathcal{A}$, and a boolean $b$.

$$
\begin{align*}
& \smash{\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}(b)}\\
& \left\lfloor
  \begin{align*}
  & (\mathrm{pk}, \mathrm{sk}) \leftarrow \mathrm{E}.\mathsf{KeyGen}()\\
  & (k_{0}, c) \leftarrow \mathrm{E}.\mathsf{Encaps}(\mathrm{pk}) \\
  & k_{1} \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{U}(\mathcal{K}) \\
  & b' \leftarrow \mathcal{A}.\mathsf{distinguish}(\mathrm{pk}, k_{b}, c)\\
  & \textsf{return}\ b'
  \end{align*}
  \right.
\end{align*}
$$

If b is 0 (i.e., false), the experiment precisely captures the case where the
adversary is given a honestly generated symmetric key and encapsulation; and if
b is 1 (i.e., true), the experiment precisely captures the case where the
adversary is given a (uniformly) random symmetric key. Then, the "extent to
which the adversary can distinguish" can be represented as the probability of
the adversary's output being different in these two cases. This is usually
referred to as the "advantage" (of an adversary in breaking CPA security of
a KEM), and is mathematically expressed as follows.

$$
\mathsf{Adv}^{\mathrm{CPA}}_{\mathrm{E}}(\mathcal{A})
= \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}(0) = 1\right]
     - \mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}(1) = 1\right]\right|
$$

Informally, if $\mathsf{Adv}^{\mathrm{CPA}}_{\mathrm{E}}(\mathcal{A})$ is
small, then $\mathcal{A}$ is not good at distinguishing (for KEM $\mathrm{E}$).
Since we are doing concrete security, we don't bother defining (at this stage)
when we deem the advantage sufficiently small for the KEM to be CPA-secure;
instead, we are happy using the above definition to show our
(relational/conditional) results.

### KEMs, EasyCrypt

This discusses the contents of file `KEM_rork.eca`. As mentioned, we define
security for KEMs generally, and not just in our context. Therefore, we start
by declaring once again types for the public and secret key spaces, as well as
the key and ciphertext spaces, and giving a name to the uniform distribution
over the (entire) key space.

```
type pkey, skey, key, ctxt.
op [lossless full uniform] dkey : key distr.
```

We can then define the *syntax* of a KEM over these using a "module type". As
the name suggests, a module type denotes the type of a module, which is nothing
more than a collection of procedures potentially sharing some state. Then,
a module type merely specifies the procedures a module must (at least)
implement to be of that module type, in addition to any potential parameters
the module must take.[^3] Using module types, the formalization of KEMs in
EasyCrypt is a rather simple, almost verbatim, translation from the
pen-and-paper definition, as shown below.

[^3]: For an analogy, a module type is comparable to a dumbed-down interface in
your typical object-oriented programming language, while a module (satisfying
a module type) would be an object implementing an interface.

```
module type KEM = {
  proc keygen(): pkey * skey
  proc encaps(pk : pkey): key * kct
  proc decaps(sk : skey, k : kct): key option
}.
```

For each algorithm of a KEM, the corresponding module type contains exactly one
`proc`edure, where the inputs (listed between parentheses) and outputs (listed
after the final colon) exactly correspond to the inputs and outputs of their
pen-and-paper counterparts. One thing to note, though, is that the output type
of `decaps` is `key option` (instead of simply the `key` type you might have
expected). In essence, the `option` extends the `key` type by one distinguished
value (`None`), which allows for a convenient way to express the "explicit
indication of failure".

In a similar fashion, we can use module types to formalize the relevant (class
of) adversaries. Indeed, an adversary is also nothing more than a (potentially
stateful) set of algorithms which adhere to some interface; or, in EasyCrypt
terms: a module implementing some module type. The module type, given below, is
exactly as you would expect, specifying a single procedures that directly
corresponds to the (implicitly defined) interface of the adversarial algorithm
considered in the (pen-and-paper) CPA experiment.

```
module type KEM_CPA_Adv = {
  proc distinguish(pk : pkey, k : key, c : ctxt): bool
}.
```

At this point, we have everything we need to formalize
$\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}$.
As implicitly mentioned above, EasyCrypt allows modules to take other modules
as parameters, which conceptually matches the way we parameterize, e.g.,
security experiments and generic constructions, on adversaries and other
constructions on pen-and-paper.
That is, stating that the CPA experiment for KEMs
$\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}$ is parameterized on
a KEM $\mathrm{E}$ and an adversary  (against CPA security for KEMs)
$\mathcal{A}$ can straightforwardly be formalized in EasyCrypt by means of
a module parameterized on a module `E` of (module) type `KEM` and a module `A`
of (module) type `KEM_CPA_Adv`. Knowing this, the formalization is rather
straightforward, see below.

```
module KEM_CPA_Exp (E : KEM) (A : KEM_CPA_Adv) = {
  proc run(b : bool) = {
    var pk, sk, k0, k1, c, b';

    (pk, sk) <@ E.keygen();
    (k0, c) <@ E.encaps(pk);
    k1 <$ dkey;
    b' <@ A.distinguish(pk, if b then k1 else k0, c);
    return b';
  }
}.
```

Note the different arrows for assignment: `<@` denotes a procedure call whose
result is assigned to the left-hand side, `<$` denotes a sampling whose result
is assigned to the left-hand side, and `<-` denotes a (regular) assignment
whose right-hand side is a pure and deterministic expression. Then
`KEM_CPA_Exp` really is almost a line-by-line translation of
$\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}$. (Where $k_{b}$ is
represented a bit more explicitly by `if b then k1 else k0`.)[^5]

Unfortunately, EasyCrypt currently does not support shorthands for expressions
involving probability statements (such as
$\mathsf{Adv}^{\mathrm{CPA}}_{\mathrm{E}}(\mathcal{A})$ for the advantage),
so we'll have to write out the full definition each time we want to refer to it.
Nevertheless, the translation of the expression that defines the advantage from
pen-and-paper to EasyCrypt is, once again, quite natural and straightforward
(barring some technicalities). Namely, using what we have formalized
hitherto, we could translate $\mathsf{Adv}^{\mathrm{CPA}}_{\mathrm{E}}(\mathcal{A})$
to EasyCrypt as follows.

```
`| Pr[KEM_CPA_Exp(E, A).run(false) @ &m: res] - Pr[KEM_CPA_Exp(E, A).run(true) @ &m: res] |
```

Indeed, ignoring (the technicality of) the memory specification `@ &m`, each element
of the pen-and-paper expression has a direct counterpart
in EasyCrypt: $\left| \right|$ becomes ``` `| |```; $\mathsf{Pr}[]$ becomes `Pr[]`;
$\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}(0)$ becomes
`KEM_CPA_Exp(E, A).run(false)`; $\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}(1)$ becomes
`KEM_CPA_Exp(E, A).run(true)`; and $= 1$ becomes `: res`.
(Here, `res` is a special variable that refers to the output of the procedure
specified before the colon; in this case, this is a boolean, meaning that
simply putting `res` is equivalent to checking for `true` or `1`.)

[^5]: Here, a technicality is that EasyCrypt mandates (imperative) code to be
contained in procedures that, in turn, have to be contained in modules. As
such, we create an auxiliary procedure (arbitrarily named `run`) in which we
actually put the experiment's code.

### DEMs, Pen-and-Paper

Formally, (for us) a DEM with key space $\mathcal{K}$, plaintext space
$\mathcal{P}$ and ciphertext space $\mathcal{C}$ is a triple of algorithms
$\left(\mathsf{KeyGen}, \mathsf{Enc}, \mathsf{Dec}\right)$ for which the
following holds.

- $\mathsf{Enc}$ takes a symmetric key (from $\mathcal{K}$) and a plaintext (from $\mathcal{P}$)
as input, and outputs DEM ciphertext (from $\mathcal{C}$)  .
- $\mathsf{Dec}$ takes a symmetric key (from $\mathcal{K}$) and a DEM ciphertext
(from $\mathcal{C}$) as input, and outputs a plaintext (from $\mathcal{P}$).

Key generation for our DEM will be done by sampling from
$\mathcal{U}(\mathcal{K})$.

(As for KEMs, you will typically see additional requirements on what precisely
constitutes a DEM, but we leave it at this.)

For the security of DEMs, we consider indistinguishability under one-time
chosen plaintext attack (IND-1CPA). Conceptually, this property is quite alike
the CPA property for KEMs. Namely, intuitively, passive security captures that,
if we produce a single ciphertext using the considered DEM (in an honest way),
then *no useful information about the plaintext can be extracted from the
ciphertext*.[^6]
Of course, since a DEM is a different primitive than a KEM, the concrete
manifestation of this intuition is going to look a bit different.
The notion requires that no (reasonable) adversary can meaningfully decide
which plaintext underlies a particular ciphertext, even when allowed to choose
the *only two* possible plaintexts.
Similarly to before, we formalize the property by means of a well-defined
program ("experiment") that matches this scenario, then defining
a corresponding advantage to capture the "extent to which an adversary can
meaningfully decide". In this case, we use the following program, parameterized
on a DEM $\mathrm{E}$, a pair adversarial algorithms $\mathcal{A}
= \left(\mathsf{choose}, \mathsf{distinguish}\right)$, and a boolean $b$.

$$
\begin{align*}
& \smash{\mathsf{Exp}^{\mathrm{1CPA}}_{\mathrm{E}, \mathcal{A}}(b)}\\
& \left\lfloor
  \begin{align*}
  & k \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{U}(\mathcal{K}) \\
  & (m_{0}, m_{1}) \leftarrow \mathcal{A}.\mathsf{choose}()\\
  & c \leftarrow \mathrm{E}.\mathsf{Enc}(k, m_{b})\\
  & b' \leftarrow \mathcal{A}.\mathsf{distinguish}(c) \\
  & \textsf{return}\ b'
  \end{align*}
  \right.
\end{align*}
$$

Using this experiment, the advantage is defined in the expected way, analogous
to the advantage we have seen for (CPA security of) KEMs. For completeness,
given a DEM $\mathrm{E}$ and an adversary $\mathcal{A}$ (against passive
security for DEMs), the advantage of $\mathcal{A}$ in breaking 1CPA-security of
$\mathrm{E}$ is defined as follows.

$$
\mathsf{Adv}^{\mathrm{1CPA}}_{\mathrm{E}}(\mathcal{A})
= \left|\mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{1CPA}}_{\mathrm{E}, \mathcal{A}}(0) = 1\right]
     - \mathsf{Pr}\left[\mathsf{Exp}^{\mathrm{1CPA}}_{\mathrm{E}, \mathcal{A}}(1) = 1\right]\right|
$$

[^6]: Comparing this to the intuition for the CPA property of KEMs, you can see they
are quite similar.


### DEMs, EasyCrypt

Having seen the translation of pen-and-paper to EasyCrypt for KEMs, it is not
much of a stretch to do the same for DEMs. (In file `DEM_lor.eca`.) In fact, no
new concepts are required: all we need are module types and modules, and use
them for the exact same purposes. As such, we'll only go through them briefly.

First off, we declare our types and distribution, and use the following module
type to formalize what it means to be a DEM.

```
type key, ptxt, ctxt.
op [lossless full uniform] dkey: key distr.

module type DEM = {
  proc enc(k : key, m : ptxt): ctxt
  proc dec(k : key, c : ctxt): ptxt
}.
```

As before, we specify one (EasyCrypt) procedure signature for each (pen-and-paper)
algorithm signature, using the appropriate input and output types for the considered
input and output elements, respectively.

Next, for the class of adversaries against one-time CPA security for DEMs, we
use yet another module type containing a single procedure for each of the
algorithms expected by such an adversary, as implicitly determined by the
experiment (for 1CPA security of DEMs).

```
module type DEM_1CPA_Adv = {
  proc choose(): ptxt * ptxt
  proc distinguish(c : ctxt): bool
}.
```

Then, we formalize the actual 1CPA experiment for DEMs with a module
parameterized on the module types we just defined, giving rise to the
following.

```
module DEM_1CPA_Exp (E : DEM) (A : DEM_1CPA_Adv) = {
  proc run(b : bool) = {
    var k, m0, m1, c, b';

    k <$ dkey;
    (m0, m1) <@ A.choose();
    c <@ E.enc(k, if b then m1 else m0);
    b' <@ A.distinguish(c);
    return b';
  }
}.
```

Comparing `DEM_1CPA_Exp` with its pen-and-paper counterpart, it is not hard to
see that, once again, EasyCrypt allows for a rather intuitive, (near)
line-by-line translation from pen-and-paper.

Finally, completing the picture, the following illustrates the formalization
of the advantage. (Again, ignore the memory specification for now.)

```
`| Pr[DEM_1CPA_Exp(E, A).run(false) @ &m: res] - Pr[DEM_1CPA_Exp(E, A).run(true) @ &m: res] |
```

### PKE Schemes, Pen-and-Paper

Formally, a PKE scheme with public key space $\mathcal{PK}$, secret key space
$\mathcal{SK}$, plaintext space $\mathcal{P}$ and ciphertext space
$\mathcal{C}$ is a triple of algorithms $\left(\mathsf{KeyGen}, \mathsf{Enc},
\mathsf{Dec}\right)$ for which the following holds.

- $\mathsf{KeyGen}$ takes no input, and outputs a public key (from $\mathcal{PK}$)
and a secret key (from $\mathcal{SK}$).
- $\mathsf{Enc}$ takes a public key (from $\mathcal{PK}$) and a plaintext (from
  $\mathcal{P}$) as input, and outputs a ciphertext (from $\mathcal{C}$).
- $\mathsf{Dec}$ takes a secret key (from $\mathcal{SK}$) and a ciphertext
  (from $\mathcal{C}$) as input, and outputs a plaintext (from $\mathcal{P}$)
  or an explicit indication of failure ($\bot$).

Again, we might have included more requirements on what actually constitutes
a PKE scheme, but we refrain from doing so as it is unnecessary for our purposes.

For the security of PKE schemes, we consider simple indistinguishability under
chosen plaintext attack.
This could be described as follows: If we produce a ciphertext using the
considered PKE scheme (in a honest way), then *no useful information about the
plaintext can be extracted from the ciphertext (or other public information)*.
By now, you might already be able to imagine what the formalization of this
property looks like. Indeed, we construct a well-defined program parameterized
on a PKE scheme and an adversary (against CPA security for PKE schemes) in
which the adversary chooses two plaintexts, after which it is given the
encryption of one of them and needs to decide which one it is. The actual
experiment is provided below, where $\mathrm{E}$ is a PKE scheme, $\mathcal{A}
= \left(\mathsf{choose}, \mathsf{distinguish}\right)$ is a pair of adversarial
algorithms, and $b$ is a boolean.

$$
\begin{align*}
& \smash{\mathsf{Exp}^{\mathrm{CPA}}_{\mathrm{E}, \mathcal{A}}(b)}\\
& \left\lfloor
  \begin{align*}
  & k \operatorname{\smash{\overset{\$}{\leftarrow}}} \mathcal{U}(\mathcal{K}) \\
  & (m_{0}, m_{1}) \leftarrow \mathcal{A}.\mathsf{choose}(\mathrm{pk})\\
  & c \leftarrow \mathrm{E}.\mathsf{Enc}(\mathrm{pk}, m_{b})\\
  & b' \leftarrow \mathcal{A}.\mathsf{distinguish}(c) \\
  & \textsf{return}\ b'
  \end{align*}
  \right.
\end{align*}
$$

Here, we assume that the different adversarial algorithms can share state, so
we don't explicitly provide the public key to the $\mathsf{distinguish}$
algorithm, or pass state from $\mathsf{choose}$ to $\mathsf{distinguish}$.

Using this experiment, the advantage is defined similarly to the previous ones.
Actually, since the name of the property is the same, it looks exactly
like the advantage of CPA security for KEMs (it's just that the parameters
have a different meaning/type). As such, we omit it here.

### PKE Schemes, EasyCrypt

As you might have noticed, there are quite a lot of aspects in the
pen-and-paper formalization of KEMs, DEMs (and their security properties) that
also appear in that of PKE schemes (and its security property). Perhaps
unexpectedly, these similarities analogously carry over to EasyCrypt! For
example, the types and module type for PKE schemes looks as follows. (This
discusses file `PKE_lor.ec`.)

```
type pkey, skey, ptxt, ctxt.

module type PKE = {
  proc keygen(): pkey * skey
  proc enc(pk : pkey, m : ptxt): ctxt
  proc dec(sk : skey, c : ctxt): ptxt option
}.
```

Nothing new here, just the same old conversion from pen-and-paper algorithm
(signatures) to EasyCrypt procedure (signatures).

Further, the class of adversaries is formalized in a similar fashion as well, i.e.,
as a module type with a procedure (signature) for each of the algorithms
expected from the adversary. Concretely, this module type is the following.


```
module type PKE_CPA_Adv = {
  proc choose(pk : pkey): ptxt * ptxt
  proc distinguish(c : ctxt): bool
}.
```

Lastly, also the formalization of the experiment contains nothing new and follows
the same type of translation from the pen-and-paper version as before. The resulting
module is given below.

```
module PKE_CPA_Exp (E : PKE) (A : PKE_CPA_Adv) = {
  proc run(b : bool) = {
    var pk, sk, c, b', m0, m1;

    (pk, sk) <@ E.keygen();
    (m0, m1) <@ A.choose(pk);
    c <@ E.enc(pk, if b then m1 else m0);
    b' <@ A.distinguish(c);
    return b';
  }
}.
```

Indeed, even the corresponding advantage would (typically) be written in
a similar way as we've seen, and we'll leave it out here.


### KEM-DEM Construction, Pen-and-Paper

We are now at a point where we can actually describe the main
construction of interest: the KEM-DEM construction. As mentioned
briefly in the beginning, this construction constructs a "secure" PKE scheme
from a "secure" KEM and a "secure" DEM. Now we have seen all the
relevant security properties, we can be more precise: the KEM-DEM
construction creates a CPA-secure PKE scheme from a CPA-secure KEM
and a 1CPA-secure DEM. How we actually prove this claim, both with
pen-and-paper and EasyCrypt, is discussed [later](#proof). For now
we only present the actual construction.

Since the KEM-DEM construction is a PKE scheme, it needs to
adhere to the corresponding interface (we outlined previously) and implement
suitable key generation, encryption and decryption algorithms. For key generation,
the construction simply executes the key generation of the given KEM and uses the
resulting key pair as its own. Then, for encryption, the construction first obtains
a symmetric key and KEM ciphertext by executing the given KEM's encapsulation, and
subsequently uses the symmetric key to encrypt the plaintext with the given DEM's encryption.
The output then consists of the KEM ciphertext and DEM ciphertext. (Intuitively, if
the KEM and DEM are both secure, the KEM and DEM ciphertexts do not reveal any "meaningful"
information about symmetric key and plaintext, respectively; in turn, together they also do
not reveal any "meaningful" information about the plaintext, meaning the construction is
secure as well as a PKE scheme.) Finally, for decryption, the construction
decapsulates the KEM ciphertext to obtain the symmetric key, given the decapsulation doesn't fail.
If decapsulation fails, meaning it returns $\bot$, then the construction simply propagates this failure.
Otherwise, the construction uses the obtained symmetric key to decrypt the DEM ciphertext (with the given
DEM's decryption, of course) and returns the resulting message.

In line with the above description, the actual algorithmic specification of the
construction, which we'll refer to as $\mathrm{KEMDEM}_{\mathrm{E}_{\mathrm{kem}}, \mathrm{E}_{s}}$,
is provided below. Here, $\mathrm{E}_{\mathrm{kem}}$ and $\mathrm{E}_{s}$ denote the KEM and DEM
(parameters) given to the construction.

$$
\begin{align*}
\begin{align*}
& \smash{\mathsf{KeyGen}()}\\
& \left\lfloor~
  \begin{align*}
  & (\mathrm{pk}, \mathrm{sk}) \leftarrow \mathrm{E}_{\mathrm{kem}}.\mathsf{KeyGen}()\\
  & \mathsf{return}\ (\mathrm{pk}, \mathrm{sk})
  \end{align*}
  \right.
\end{align*}
&&&&
\begin{align*}
& \smash{\mathsf{Enc}(\mathrm{pk}, m)}\\
& \left\lfloor~
  \begin{align*}
  & (k, \mathrm{kc}) \leftarrow \mathrm{E}_{\mathrm{kem}}.\mathsf{Encaps}(\mathrm{pk})\\
  & \mathrm{dc}\ \leftarrow \mathrm{E}_{s}.\mathsf{Enc}(k, m)\\
  & \mathsf{return}\ (\mathrm{kc}, \mathrm{dc})
  \end{align*}
  \right.\\
&
\end{align*}
&&&&
\begin{align*}
& \smash{\mathsf{Dec}(\mathrm{sk}, c)}\\
& \left\lfloor~
  \begin{align*}
  & (\mathrm{kc}, \mathrm{dc}) \leftarrow c\\
  & k \leftarrow \mathrm{E}_{\mathrm{kem}}.\mathsf{Decaps}(\mathrm{sk}, \mathrm{kc})\\
  & \mathsf{if}\ k \neq \bot\ \mathsf{then}\\
  &\ \ \ \ m \leftarrow \mathrm{E}_{s}.\mathsf{Dec}(k, \mathrm{dc})\\
  &\ \ \ \ \mathsf{return}\ m \\
  & \mathsf{return}\ \bot
  \end{align*}
  \right.\\
&
\end{align*}
\end{align*}
$$

### Interlude: Instantiating the assumptions and notion

In the above, we defined the assumptions and our security notions abstractly.
We can then *instantiate* them with the types we wish to use for our
construction. In particular, we want:
- the types of the PKE public and secret keys to be the same as those of the
  underlying KEM's public and secret keys;
- the type of the PKE's plaintext to be the same as that of the underlying
  DEM's plaintexts;
- the type of the PKE's ciphertext to be pairs of KEM ciphertexts and DEM
  ciphertexts; and
- the type and distribution of the KEM's plaintext (or keys) to be the same as
  those of the DEM's keys.

In EasyCrypt (back now to our main file `KEMDEM_lor.ec`), and given the
top-level declarations we gave earlier for the types and distribution discussed
above, we instantiate the generic definitions using *cloning*. When cloning, we
can instantiate any type or operator left abstract in the generic theory, and
we then also discharge (or prove) any axioms that may be expected to be met by
those types and operators.

We do the instantiations discussed above as follows:

```
(** We instantiate the KEM library with the types and distribution
    above.
**)
clone import KEM_rork as KEM with
  type pkey <- pkey,
  type skey <- skey,
  type key  <- key,
  type ctxt <- kct,
  op   dkey <- dkey
(* This requires discharging assumptions made on the types and
   distribution in the library *)
proof *.
realize dkey_ll  by exact: dkey_ll.
realize dkey_uni by exact: dkey_uni.
realize dkey_fu  by exact: dkey_fu.

(** We instantiate the DEM library (in its LoR variant here) with the
    types and distribution above.
**)
clone import DEM_lor as DEM with
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
clone import PKE_lor as PKE with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- kct * dct
proof *.
```

`clone import KEM_rork` would normally make
a clone—literally a verbatim copy—of theory `KEM_rork`
(which in our case is an external theory loaded from the
file of the same name), and to import the symbols it
declares and defines. The `with` directive then specifies
a list of instantiations for `type`s, `op`erators and
`lemma`s (which instantiates their proof!). Finally,
a `proof *` directive allows us to ask EasyCrypt to request
proofs for any pending axioms in the new theory.

### KEM-DEM Construction, EasyCrypt

As far as algorithmic specifications in EasyCrypt is concerned, you have
essentially seen most of the relevant concepts by now. Particularly,
the specification of concrete(ish) schemes or constructions,
including the KEM-DEM construction, does not require much more than we've
already covered. The actual formalization of the construction is given below.

```
module KEMDEM (E_kem : KEM) (E_s : DEM): PKE = {
  proc keygen = E_kem.keygen

  proc enc(pk : pkey, m : pt): kct * dct = {
    var k, kc, dc;

    (k, kc) <@ E_kem.encaps(pk);
    dc <@ E_s.enc(k, m);
    return (kc, dc);
  }

  proc dec(sk : skey, c : kct * dct): pt option = {
    var kc, dc, r, k, m;

    (kc, dc) <- c;
    r <- None;
    k <@ E_kem.decaps(sk, kc);
    if (k <> None) {
      m <@ E_s.dec(oget k, dc);
      r <- Some m;
    }
    return r;
  }
}.
```

For key generation, instead of writing out the procedure that effectively just returns
the result a call to the given KEM's key generation, we make use of the syntactic sugar EasyCrypt provides for this.
Then, for encryption, the formalization is a straightforward translation of the pen-and-paper version.
Lastly, for decryption, recall that `None` is a special value we use to explicitly indicate a failure, i.e.,
$\bot$. One thing, and essentially the only thing, that "prevents" this formalization from being
a line-by-line translation of the pen-and-paper version is the fact that EasyCrypt cannot handle multiple
return statements in a single procedure.[^8] So, instead of multiple return statements, we use a dedicated
return variable (`r`) instead.

With that, we can proceed to the proof.

[^8]: Of course, we could've circumvented this by not using multiple return statements in the pen-and-paper version,
but we tried to stick to what one (or we, at least) typically see in pen-and-paper proofs.

## Proof

---

With the basics, schemes, and security properties defined, we are ready
to actually prove our main security claim: the KEM-DEM
construction creates a CPA-secure PKE scheme from a CPA-secure KEM
and a 1CPA-secure DEM. That is, if we *are given* a CPA-secure KEM
and a 1CPA-secure DEM, then *we know* that the KEM-DEM construction creates
a CPA secure PKE scheme. As is usual in cryptography, and precisely what EasyCrypt
was built for, we demonstrate this claim by means of a *reductionist proof*.
Specifically, we demonstrate that, given an adversary that breaks CPA security
of the KEM-DEM construction, we can use this adversary to break the CPA security
of the employed KEM or the security of the employed DEM. The way to formally do this
is by explicitly constructing (reduction) adversaries that actually break the
CPA or 1CPA security of the underlying KEM or DEM when given such an (hypothetical)
adversary that breaks CPA security of the KEM-DEM construction.
In the end, this is essentially the same as showing that *if the KEM-DEM construction
(with the given KEM and DEM) is not CPA secure then the given KEM is not
CPA secure or the given DEM is not 1CPA secure*. (Then, by contraposition,
the KEM-DEM construction has to be a CPA-secure PKE if the given KEM
is CPA secure *and* the given DEM 1CPA secure.)

In this exposition, we walk through the formalization of the
proof artifacts and proof setup/structure, but only provide
an intuition for the actual formal verification of the
statements. Going through the formal verification in detail
would be too unwieldy, and is not the goal of this
demonstration. (Better tutorials for this are available from
EasyCrypt's websites and documentation.) The code itself is
commented, complementing the explanation given here. In any
case, it is advised to follow along in the code, so you can
actually see how the verification progresses for yourself.

Let's get started.

### High-Level Overview

On a high level, the proof consists of three steps: a KEM reduction, followed by
a DEM reduction, and completed with another KEM reduction. That is, we'll bound
the advantage of any adversary against CPA security of the KEM-DEM construction
by the advantages of reduction adversaries against (two instances of) CPA security
of the used KEM and 1CPA security of the used DEM. So, starting off, consider the
CPA security game for the KEM-DEM construction: it generates a key pair, asks
the adversary for two plaintexts, encrypts one of them (which one is
determined by the boolean parameter), and asks the adversary to decide
which plaintext has been encrypted. Recall that this key generation is just
the one from the KEM, and that this encryption first encapsulates
with the KEM before encrypting with the DEM. Now, notice that this
encompasses the setup of the CPA experiment for the given KEM:
honestly generating a key pair, followed by encapsulating with the generated public key.
But then, intuitively,
we can replace the symmetric key (generated by the encapsulation) by a uniformly
random one, and *if the adversary starts behaving differently, it somehow
managed to break the CPA security of the KEM*. This observation forms the basis
of both KEM reductions (the second one applying it in reverse).
With a uniformly random symmetric key (instead of a honestly computed one
through encapsulation), the experiment effectively contains an entire instance of the
1CPA experiment for the given DEM:
sampling a symmetric key uniformly at random, obtaining two plaintexts from the
adversary, encrypting one of the plaintexts with the sampled key, and asking the
adversary to decide which plaintext was encrypted. Even the check on the adversary's
success is the same. So, intuitively, if the *if the adversary succeeds at this point,
it somehow managed to break the 1CPA security of the DEM*. This observation forms the basis
of the DEM reduction.


### Step 0: Declaring Objects

Technically, before being able to talk about some (arbitrary) KEM, DEM, and adversary
against CPA security of PKE schemes, we need to "announce" or "declare" them, essentially
just stating exactly what objects we are considering.
On pen-and-paper, you will typically see this at the start of a theorem statement, with
something along the lines of "Let K be a KEM, D be a DEM, and A be a CPA adversary..."
In EasyCrypt, we can do this in a similar way: we declare the objects of interest
in the lemma statement, which implicitly performs the necessary quantification.
However, often, you prove many lemmas considering the same objects, even in the proof
of a single, larger main theorem.
For this purpose, EasyCrypt implements the concept of a "section", in which you can
declare the objects you want to (repeatedly) consider throughout the section.
Concretely, this is done as follows, where `N <: T { -M }` denotes the declaration
of a module `N` of (module) type `T` for which the memory is disjoint from that of `M`.
The latter can be interpreted as "module `N` cannot read/write the state of `M`,
or vice versa", which is essentially another EasyCrypt technicality needed to preclude
weird scenarios where the adversary can manipulate the experiment or reductions itself.

```
declare module E_kem <: KEM { -B_s }.

declare module E_s <: DEM { -B_s, -E_kem }.

declare module A <: PKE_CPA_Adv { -B_s, -E_kem, -E_s }.
```

Here, `B_s` is one of the reductions we introduce below.

### Step 1: First KEM Reduction

Following the intuition described above, our first reduction adversary is one
that essentially allows us to show it is fine to replace the original
symmetric key (obtained through the encapsulation of the KEM) by a uniformly
random one, assuming the KEM is actually CPA secure. Specifically, this reduction
adversary is given an adversary against CPA security of PKE schemes, but is itself
an adversary against CPA security of KEMs. The reduction adversary uses the given
adversary to its advantage by making sure everything is exactly (distributed) as in
the CPA experiment for KEMs, but injects the values it received from its own game to
make sure that any "breaking capabilities" of the given adversary directly translate to
"breaking capabilities" for the reduction adversary. Concretely, in this case, this means
that upon receiving the values from its experiment, the reduction adversary asks the
given adversary to choose two plaintext, encrypts one of them using
the symmetric key (provided by its experiment), asks the adversary to determine
which one was encrypted based on the ciphertext (which consists of the DEM ciphertext
resulting from the encryption *and* the KEM ciphertext provided by its
experiment), and finally directly returns the value output by the given adversary.
Crucially, if the symmetric key the *reduction* adversary gets is the one
obtained via the KEM's encapsulation, i.e., the boolean
parameter of the (KEM) CPA experiment is false, the perspective of the
*given* adversary is exactly as it would be in a run of its own (PKE) CPA
experiment with the boolean parameter set to false. Further, if the symmetric
key the reduction adversary receives is a uniformly random one, i.e., the boolean
parameter of the (KEM) CPA experiment is true, any change the *given* adversary
"notices" (by behaving differently) must be due to this difference in the symmetric key (distribution).
Since the reduction adversary directly returns whatever the given adversary outputs, any difference
in behavior between these cases (by the given adversary) directly results in a distinguishing
advantage for the reduction adversary in its experiment.

In pen-and-paper proofs, a textual description like the above is usually all you
will get (or less); if you're lucky, you'll get some additional algorithmic description.
However, formally, a reduction adversary is, like any other object
in our code-based formalism, a well-defined program. In EasyCrypt,
you have to specify them *completely*, just as you need to
for any other artifact. Fortunately, this does not require
anything we haven't seen before. The actual formalization of the reduction adversary
is shown below.


```
module B_kem_0 (E_s : DEM) (A : PKE_CPA_Adv) : KEM_CPA_Adv = {
  proc distinguish(pk : pkey, k : key, kc: kct) = {
    var m0, m1, dc, b';

    (m0, m1) <@ A.choose(pk);
    dc <@ E_s.enc(k, m0);
    b' <@ A.distinguish((kc, dc));
    return b';
  }
}.
```

As expected, the reduction adversary is a module of type `KEM_CPA_Adv`, indicating
that it is an adversary against CPA security of KEMs (and hence expected to implement the
corresponding `distinguish` procedure). Further, it is parameterized on both the
considered DEM and (PKE) CPA adversary. The reason for the latter should be obvious:
we assume/know nothing about the given adversary, and the reduction should work for any.
The reason for the former is similar: our result doesn't consider a specific DEM (or KEM),
but rather holds for arbitrary ones (meaning our reduction should also work for any such scheme).
With a bit of imagination, we can mentally replace the (adversary) parameter of the CPA
experiment for the considered KEM with this reduction adversary. Then, comparing the result with
the original (PKE) CPA experiment for the KEMDEM construction, we see they are actually identical.
Surely, then, the probability of the output having a certain value is the same as well.
Indeed, this is precisely what our first lemma, given below, captures.

```
local lemma EqPr_PKECPA0_KEMCPA0 &m:
  Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
  =
  Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res].
```

`&m` in the lemma argument list is a universally quantified memory, which is needed
to have the probabilities be well-defined.
Inside a section, we can tag artifacts such as modules, lemmas, and operators as `local`,
meaning they will not be visible outside the section, keeping the code cleaner.
`local` because it is only an intermediate result.

In typical game-playing style, we define an intermediate experiment (also often referred to as "game"),
the meaning and purpose of which is really identical to that on pen-and-paper.
In this case, the game essentially serves to simultaneously capture a slightly altered (PKE)
CPA experiment where the used symmetric key is sampled uniformly at random.
The resulting formalization is as follows.


```
local module Game1 = {
  proc run(b : bool) = {
    var pk, sk, m0, m1, k0, k1, kc, dc, b';

    (pk, sk) <@ E_kem.keygen();
    (m0, m1) <@ A.choose(pk);
    (k0, kc) <@ E_kem.encaps(pk);
    k1 <$ dkey;
    dc <@ E_s.enc(k1, if b then m1 else m0);
    b' <@ A.distinguish(kc, dc);
    return b';
  }
}.
```

Now, by design, the (CPA) KEM experiment with our reduction adversary
and the boolean parameter set to true is equal to our intermediate game
with the boolean parameter set to false.

```
local lemma EqPr_Game10_KEMCPA1 &m:
  Pr[Game1.run(false) @ &m: res] = Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res].
```

Then, combining our `EqPr_PKECPA0_KEMCPA0` and `EqPr_KEMCPA1_Game10` lemmas, it is straightforwrad
to show the following difference in probabilities. (Indeed, the subtrahend and minuend are
simply equal on both sides).

```
local lemma GameHop1 &m:
  `| Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
     - Pr[Game1.run(false) @ &m: res] |
   =
  `| Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
     - Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res] |.
```

In game-playing terminology, this is (a form of) a "game hop" (hence the name of the lemma),
since it essentially allows us to move from one experiment (or game) to the other,
(eventually) bounding any deviations through the triangle inequality.

### Step 2: DEM Reduction

The DEM reduction adversary is formalized as follows.

```
module B_s (E_kem : KEM) (A : PKE_CPA_Adv) : DEM_1CPA = {
  var pk : pkey

  proc choose() = {
    var sk, m0, m1;

    (pk, sk) <@ E_kem.keygen();
    (m0, m1) <@ A.choose(pk);
    return (m0, m1);
  }

  proc distinguish(dc : dct) = {
    var k0, kc, b';

    (k0, kc) <@ E_kem.encaps(pk);
    b' <@ A.distinguish((kc, dc));
    return b';
  }
}.
```

Inserting this reduction adversary in the 1CPA experiment and
comparing it to `Game1`, we can see that they are identical
as long as their boolean parameter is equal.
This immediately leads to the lemma for second game hop, given below.
(This time, we do not separately prove the individual equalities, but
rather encapsulate them directly in the proof for the game hop.)

```
local lemma GameHop2 &m:
  `| Pr[Game1.run(false) @ &m: res] - Pr[Game1.run(true) @ &m: res] |
  =
  `| Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res]
     - Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res] |.
```


### Step 3: Second KEM Reduction

The second KEM reduction adversary is almost identical to the first,
only differing in the plaintext it encrypts for the adversary.

```
module B_kem_1 (E_s : DEM) (A : PKE_CPA_Adv) : KEM_CPA_Adv = {
  proc distinguish(pk : pkey, k : key, kc: kct) = {
    var m0, m1, dc, b';

    (m0, m1) <@ A.choose(pk);
    dc <@ E_s.enc(k, m1);
    b' <@ A.distinguish((kc, dc));
    return b';
  }
}.
```

Certainly, this means that if we insert the reduction in the
(KEM) CPA experiment, the result will be identical to (1)
`Game1` (with boolean parameter true) when its boolean parameter is
false, and (2) the (PKE) CPA experiment (with boolean parameter true)
when its boolean parameter is true.
This gives rise to the following lemma.

```
local lemma GameHop3 &m:
  `| Pr[Game1.run(true) @ &m: res]
     - Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res] |
  =
  `| Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res]
     - Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res] |.
```


### Final Result

Finally, combining all of the intermediate lemmas above, we can show
the desired bound on the (PKE) CPA advantage for any adversary
by application of the triangle equality. In fact, EasyCrypt can figure
this out on its own (given the previous lemmas of course).

```
lemma KEMDEM_PKECPA_Security &m:
  `| Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(false) @ &m: res]
     - Pr[PKE_CPA_Exp(KEMDEM(E_kem, E_s), A).run(true) @ &m: res] |
  <=
  `| Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(false) @ &m: res]
      - Pr[KEM_CPA_Exp(E_kem, B_kem_0(E_s, A)).run(true) @ &m: res] |
  +
  `| Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(false) @ &m: res]
     - Pr[DEM_1CPA_Exp(E_s, B_s(E_kem, A)).run(true) @ &m: res] |
  +
  `| Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(false) @ &m: res]
     - Pr[KEM_CPA_Exp(E_kem, B_kem_1(E_s, A)).run(true) @ &m: res] |.
```

This concludes the formal verification of the CPA security for the KEM-DEM construction.