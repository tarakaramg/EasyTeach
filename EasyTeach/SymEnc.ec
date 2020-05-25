(* SymEnc.ec *)

(* Symmetric Encryption *)

(* definitions, including games for judging correctness and IND-CPA
   (indistinguishability under chosen plaintext attack) security *)

prover ["Z3"].  (* no SMT solvers *)

require import AllCore Distr DBool.
require import Cyclic_group_prime.
require import Prime_field.



(* theory parameters *)




op dgf_q: gf_q distr.


type key.  (* encryption keys *)

type text.  (* plaintexts *)

type cipher.  (* ciphertexts *)

op hash: text -> group.
op oplus: group* group -> group.


op ciph_def : cipher.  (* default ciphertext *)

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

module type ENC = {
  (* Alice private key generation *)
  
  proc key_gen() : group * gf_q

  (* encryption *)
  proc enc(A:group, x : text) : group*group

  (* decryption *)
  proc dec(p: gf_q, k : group, c : text) : text
}.

module Enc : ENC = {

  proc key_gen(): group * gf_q = {
    var x: gf_q;
    x <$ dgf_q;
    return (g^x, x); (*x is Alice's  private key *)
  }

  proc enc(A: group, x : text) : group*group ={
      var k : gf_q; var c_1, c_2: group;
      k <$ dgf_q; (* Ephemeral key *)
      c_1 <- g^k;
      c_2 <- hash(x)**A^k;
      return (c_1, c_2); (* Here k is Alice public key A = g^x , this returns c_1=g^k and c_2=mA^k *)
  }

      (* decryption *)

  proc dec(priv_key: gf_q, c_1 : group, c_2 : text) : text ={
      var y : group; y <- c_1^(priv_key); y <- inv(y);
   
  }


}.
(* module for checking correctness of encryption, parameterized
   by encryption scheme

   correctness means main returns true with probability 1, without any
   assumptions about value of x *)

module Cor (Enc : ENC) = {
  proc main(x : text) : bool = {
    var k : key; var c : cipher; var y : text;
    k <@ Enc.key_gen();
    c <@ Enc.enc(k, x);
    y <@ Enc.dec(k, c);
    return x = y;
  }
}.

(* module type of encryption oracles *)

module type EO = {
  (* initialization *)
  proc * init() : unit

  (* encryption of text by adversary before game's encryption *)
  proc enc_pre(x : text) : cipher

  (* one-time encryption of text by game *)
  proc genc(x : text) : cipher

  (* encryption of text by adversary after game's encryption *)
  proc enc_post(x : text) : cipher
}.

(* standard encryption oracle, constructed from an encryption
   scheme *)

module EncO (Enc : ENC) : EO = {
  var key : key
  var ctr_pre : int
  var ctr_post : int

  proc init() : unit = {
    key <@ Enc.key_gen();
    ctr_pre <- 0; ctr_post <- 0;
  }

  proc enc_pre(x : text) : cipher = {
    var c : cipher;
    if (ctr_pre < limit_pre) {
      ctr_pre <- ctr_pre + 1;
      c <@ Enc.enc(key, x);
    }
    else {
      c <- ciph_def;  (* default result *)
    }  
    return c;
  }

  proc genc(x : text) : cipher = {
    var c : cipher;
    c <@ Enc.enc(key, x);
    return c;
  }

  proc enc_post(x : text) : cipher = {
    var c : cipher;
    if (ctr_post < limit_post) {
      ctr_post <- ctr_post + 1;
      c <@ Enc.enc(key, x);
    }
    else {
      c <- ciph_def;  (* default result *)
    }  
    return c;
  }
}.

(* encryption adversary, parameterized by encryption oracle, EO

   choose may only call EO.enc_pre; guess may only call EO.enc_post *)

module type ADV (EO : EO) = {
  (* choose a pair of plaintexts, x1/x2 *)
  proc * choose() : text * text {EO.enc_pre}

  (* given ciphertext c based on a random boolean b (the encryption
     using EO.genc of x1 if b = true, the encryption of x2 if b =
     false), try to guess b *)
  proc guess(c : cipher) : bool {EO.enc_post}
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

module INDCPA (Enc : ENC, Adv : ADV) = {
  module EO = EncO(Enc)        (* make EO from Enc *)
  module A = Adv(EO)           (* connect Adv to EO *)

  proc main() : bool = {
    var b, b' : bool; var x1, x2 : text; var c : cipher;
    EO.init();                 (* initialize EO *)
    (x1, x2) <@ A.choose();    (* let A choose plaintexts x1/x2 *)
    b <$ {0,1};                (* choose boolean b *)
    c <@ EO.genc(b ? x1 : x2); (* encrypt x1 if b = true, x2 if b = false *)
    b' <@ A.guess(c);          (* give ciphertext to A, which returns guess *)
    return b = b';             (* see if A guessed correctly, winning game *)
  }
}.
