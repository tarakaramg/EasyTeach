(* SymEnc.ec *)

(* Symmetric Encryption *)

(* definitions, including games for judging correctness and IND-CPA
   (indistinguishability under chosen plaintext attack) security *)

prover ["Z3"].  (* no SMT solvers *)

require import AllCore Distr DBool FSet SmtMap.
require import Cyclic_group_prime.
require import Prime_field.
import Dgf_q.

(* theory parameters *)


type key.  (* encryption keys *)
  (* plaintexts *)
type  text.
const zero:text.



op ( ++ ) : text -> text -> text.
op dtext : text distr.

op ciph_def : group*text.  (* default ciphertext *)

(* encryption oracle limit before game's encryption

   this says limit_pre has type int and the axiom ge0_limit_pre says
   limit_pre is non-negative *)
op limit_pre : {int | 0 <= limit_pre} as ge0_limit_pre.

(* encryption oracle limit after game's encryption *)
op limit_post : {int | 0 <= limit_post} as ge0_limit_post.

(* end theory parameters *)

(* module type of encryption schemes

   an encryption scheme Enc should be stateless, meaning that

  forall (g1 g2 : glob Enc), g1 = g2 *)

axiom xor_commutative : forall(x : text, y : text), x ++ y = y ++  x.
axiom xor_associative : forall(x,y,z : text), (x ++ y) ++ z = x ++ (y ++ z).
axiom xor_with_0: forall(x : text), x ++ zero = x.
axiom xor_with_itself: forall(x:text), x ++ x = zero.
axiom dtext_lossless : weight dtext = 1%r.

module type RO = {
  (* initialization *)
  proc * init() : unit

  (* application to a text *)
  proc f(x : group) : text
}.


(* random function implemention using true randomness *)

module TRF : RO = {
  (* mp is a finite map associating texts with texts *)
  var mp : (group, text) fmap

  proc init() : unit = {
    mp <- empty;  (* empty map *)
  }

  proc f(x : group) : text = {
    var y : text;
    if (! x \in mp) {   (* give x a random value in *)
      y <$ dtext;  (* mp if not already in mp's domain *)
      mp.[x] <- y;
    }
    return oget mp.[x];
  }
}.


module type ENC = {
  (* Alice private key generation *)
  
  proc key_gen() : group * gf_q

  (* encryption *)
  proc enc(A:group, x : text) : group*text

  (* decryption *)
  proc dec(p: gf_q, c1 : group, c2 : text ) : text
}.

module Enc (TRF: RO): ENC = {

  proc key_gen(): group * gf_q = {
    var x: gf_q;
    x <$ dgf_q;
    return (g^x, x); (*x is Alice's  private key *)
  }

  proc enc(A: group, x : text) : group*text ={
      var k : gf_q; var c_1 : group; var c_2 : text;
      k <$ dgf_q; (* Ephemeral key *)
      c_1 <- g^k;
      c_2 <@ TRF.f(A^k); c_2 <- c_2 ++ x;
      return (c_1, c_2); (* Here A is Alice public key A = g^x , this returns c_1=g^k and c_2=mA^k *)
  }

      (* decryption *)

  proc dec(priv_key: gf_q, c_1 : group, c_2 : text) : text ={
      var y : group; var c_3 : text;
      y <- c_1^(priv_key);
      c_3 <@ TRF.f(y);
      return(c_3 ++ c_2);
  }
}.
(* module for checking correctness of encryption, parameterized
   by encryption scheme

   correctness means main returns true with probability 1, without any
   assumptions about value of x *)

module Cor (Enc : ENC) = {
  proc main(x : text) : bool = {
    var c_1  : group; var priv_key : gf_q; var pub_key : group; var y, c_2: text;
    (pub_key, priv_key) <@ Enc.key_gen();
    (c_1,c_2) <@ Enc.enc(pub_key, x);
    y <@ Enc.dec(priv_key, c_1, c_2);
    return (x = y);
  }
}.



(* encryption adversary, parameterized by encryption oracle, EO

   choose may only call EO.enc_pre; guess may only call EO.enc_post *)

module type ADV (RO : RO) = {
  (* choose a pair of plaintexts, x1/x2 *)
  proc * choose(pub_key: group ) : text * text {RO.f}

  (* given ciphertext c based on a random boolean b (the encryption
     using EO.genc of x1 if b = true, the encryption of x2 if b =
     false), try to guess b *)
  proc guess(c_1 : group, c_2 : text) : bool {RO.f}
}.

(* IND-CPA security game, parameterized by an encryption scheme Enc
   and adversary Adv

   an encryption scheme is secure iff the probability of main
   returning true (Adv winning the game) is close to 1/2, i.e., Adv
   isn't doing much better than always guessing the ciphertext comes
   from the first plaintext, or of making a random guess

   formally, we want that the absolute value of the difference between
   the probability that main returns true and 1/2 to be small; this
   says that Adv can neither win nor lose with probability much
   different than 1/2 (if it could reliably lose, the addition of
   a negation would result in an adversary that could reliably win)

   because Adv can use EO to encrypt the plaintexts it chooses,
   the encryption procedure of a secure encryption scheme is
   necessarily probabilistic

   Adv may directly use Enc (which is stateless) as much as it wants
   (and in any case could simulate it), but the security theorem must
    say it can't read/write the global variables of EncO *)

   

module IND_CPA (Enc : ENC, Adv : ADV) = {
  module A = Adv(TRF)           (* connect Adv to RO *)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c_2 : text;var priv_key : gf_q; var c_1,pub_key : group;
   (pub_key,priv_key) <@ Enc.key_gen();
    (x1, x2) <@ A.choose(pub_key);    (* let A choose plaintexts x1/x2 *)
    b <$ {0,1};                (* choose boolean b *)
    (c_1,c_2) <@ Enc.enc(pub_key, b ? x1 : x2); (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ A.guess(c_1,c_2);          (* give ciphertext to A, which returns guess *)
    return b = b';             (* see if A guessed correctly, winning game *)
  }
}.

lemma enc_stateless (g1 g2 : glob Enc): g1 = g2.
    proof.
      auto.
qed.    
    (* lemma proving correctness of encryption *)



lemma correctness : phoare[Cor(Enc(TRF)).main : true ==> res] = 1%r.
    proof.
      proc.
      inline*.
      seq 4: ((A = g^x0) /\ (x1 = x) /\ (x0 = priv_key)).
      auto.
      auto.
      progress.    
      apply lossless.
      seq 3: ((x2 = A^k) /\ (c_10 = g^k)). 
      auto.
      auto.
      progress.
      apply lossless.
      if.
      auto.
      progress.
      seq 8: (x2 = y1).
      auto.    
      auto.
      progress.
      apply dtext_lossless.
      progress.
    
      seq 2: (x3 = y0).      
      auto.
      auto.
      if.
      auto.
      progress.
      apply dtext_lossless.
      progress.
      skip.
    
    
    
    module Game_2 = {

  module EO = EncO(Enc)
  (pub_key, priv_key) <@ EO.init();
