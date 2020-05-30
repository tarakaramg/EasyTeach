(* SymEnc.ec *)

(* Symmetric Encryption *)

(* definitions, including games for judging correctness and IND-CPA
  (indistinguishability under chosen plaintext attack) security *)

prover ["Z3"].  (* no SMT solvers *)

require import AllCore Distr DBool FSet SmtMap.
require import Cyclic_group_prime.
require import Prime_field.
import Dgf_q.

type  text.
const zero:text.

op ( ++ ) : text -> text -> text.
op dtext : text distr.

axiom xor_commutative : forall(x : text, y : text), x ++ y = y ++  x.
axiom xor_associative (x,y,z : text) : (x ++ y) ++ z = x ++ (y ++ z).
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

module RO : RO = {
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

type pub = group.
type priv = gf_q.
type cipher = group * text.

module type ENC (RO : RO) = {
 (* Alice private key generation *)

 proc key_gen() : pub * priv {}

 (* encryption *)
 proc enc(A:group, x : text) : cipher {RO.f}

 (* decryption *)
 proc dec(p: priv, c : cipher) : text {RO.f}
}.

op ciph_def : group*text.  (* default ciphertext *)

module (Enc : ENC) (RO : RO) = {
 proc key_gen(): pub * priv = {
   var priv_k: gf_q;
   priv_k <$ dgf_q;
   return (g^priv_k, priv_k); (*x is Alice's  private key *)
 }

 proc enc(A: pub, plain_text : text) : cipher ={
     var k : gf_q; var c_1 : group; var c_2 : text;
     k <$ dgf_q; (* Ephemeral key *)
     c_1 <- g^k;
     c_2 <@ RO.f(A^k); c_2 <- c_2 ++ plain_text;
     return (c_1, c_2); (* Here A is Alice public key A = g^priv_key , this returns c_1=g^k and c_2= RO.f(A^k)++message *)
 }

     (* decryption *)

 proc dec(priv_key: priv, c : cipher) : text ={
     var y : group; var c_1 : group; var c_2, c_3 : text;
     (c_1, c_2) <- c;
     y <- c_1^(priv_key);
     c_3 <@ RO.f(y);
     return(c_3 ++ c_2); (* As y =c_1^(priv_key) and c_1 = g^k; c_3 ++ c_2 will  RO.f(c_1^(priv_key)) ++ RO.f(A^k) ++ message *)
 }
}.
(* module for checking correctness of encryption, parameterized
  by encryption scheme

  correctness means main returns true with probability 1, without any
  assumptions about value of x *)

module Cor (Enc : ENC) = {
 module E = Enc(RO)

 proc main(x : text) : bool = {
   var c  : cipher; var priv_key : priv; var pub_key : pub; var y, c_2: text;
   (pub_key, priv_key) <@ E.key_gen();
   c <@ E.enc(pub_key, x);
   y <@ E.dec(priv_key, c);
   return (x = y);
 }
}.

(* encryption adversary, parameterized by encryption oracle, EO

  choose may only call EO.enc_pre; guess may only call EO.enc_post *)

module type ADV (RO : RO) = {
 (* choose a pair of plaintexts, x1/x2 *)
 proc * choose(pub_key : pub) : text * text {RO.f}

 (* given ciphertext c based on a random boolean b (the encryption
    using EO.genc of x1 if b = true, the encryption of x2 if b =
    false), try to guess b *)
 proc guess(c : cipher) : bool {RO.f}
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
 module E = Enc(RO)  (* connect Enc to RO *)
 module A = Adv(RO)  (* connect Adv to RO *)

 proc main() : bool = {
   var b, b' : bool; var x1, x2 : text; var c : cipher;
   var priv_key : priv; var pub_key : pub;
  RO.init();
  (pub_key,priv_key) <@ E.key_gen();
   (x1, x2) <@ A.choose(pub_key);    (* let A choose plaintexts x1/x2 *)
   b <$ {0,1};                (* choose boolean b *)
   c <@ E.enc(pub_key, b ? x1 : x2); (* encrypt x1 if b = true, x2 if b = false *)
   b' <@ A.guess(c);          (* give ciphertext to A, which returns guess *)
   return b = b';             (* see if A guessed correctly, winning game *)
 }
}.


lemma exp_equal (g: group, x_1, x_2 : gf_q) : x_1 = x_2 => g^x_1 = g^x_2 .
proof. 
move => -> //.
qed.


axiom pow_pow (g: group, v,v_1 : gf_q) :  g^v^v_1 = g^(v * v_1).

lemma pow_com (g: group, v,v_1 : gf_q) : g^v^v_1 = g^v_1^v.
    proof.
    have -> :  g^v^v_1 = g^(v*v_1).
      apply pow_pow.
    have -> : v*v_1 = v_1*v.
      apply gf_q_mult_comm.
      smt(pow_pow).
  qed.

lemma pow_com_2 (g: group, v,v_1 : gf_q) : g^(v*v_1) = g^(v_1*v).
    have -> : g^(v*v_1) = g^v^v_1.
    smt(pow_pow).
    have -> : g^(v_1*v) = g^v_1^v.
    smt(pow_pow).
    apply pow_com.
  qed.
  
    


lemma correctness : phoare[Cor(Enc).main : true ==> res] = 1%r.
   proof.
     proc.
     inline*.
     seq 2: (pub_key = g ^ priv_key).
     auto.
     auto.    
     progress.
     apply lossless.
     sp.    
     seq 3: (plain_text = x /\ c_1 = g ^ k /\ x0 = g ^ (priv_key * k)).
     auto.
     auto.
     progress.
     apply lossless.
     rewrite pow_pow pow_com_2.
     trivial.   
     if.
     seq 1 : 
       (plain_text = x /\ c_1 = g ^ k /\ x0 = g ^ (priv_key * k) /\
        x0 \notin RO.mp).
     auto.
     auto; progress; apply dtext_lossless.
     sp; wp.
     rcondf 1.
         auto; progress.
       search dom _.[_<-_].
       apply mem_set.
         smt( pow_pow pow_com_2).
         auto.
         progress.
      
       search _.[_<-_].
       rewrite pow_pow pow_com_2.
       rewrite get_set_sameE.
         smt( xor_associative xor_with_itself xor_with_0).
       hoare.
         auto.
         progress.
         sp;wp.
         progress.
         rcondf 1.
         auto.
         progress.
         rewrite pow_pow pow_com_2 //. 
         auto.
         progress.
         rewrite pow_pow pow_com_2. 
       search _.[_].
       search oget.
         rewrite get_some.
trivial.
       
         rewrite  xor_associative xor_with_itself xor_with_0.
       search oget.
       
       
apply getE.
apply map_set.
       apply get_set_sameE.
       apply oget_omap_some.
apply oget_omap_some.
       

       
(*
search "_.[_<-_]" "_.[_]".
search dom. (* instead of (\in) *)
*)
admit.
auto; progress.
admit.
hoare.
auto.
trivial.




     if.
     auto; progress. apply dtext_lossless.



     seq 2: (RO.mp.[x0] = Some y1).
     auto.
     auto.
     progress.
     apply dtext_lossless.
     apply get_set_sameE.
     sp.
     if.
     seq 2: (RO.mp.[x1] = Some y2).
     auto.
     auto.
     progress.
     apply dtext_lossless.
     apply get_set_sameE.
     auto.
     progress.




   module Game_2 = {

 module EO = EncO(Enc)
 (pub_key, priv_key) <@ EO.init();(* SymEnc.ec *)

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
axiom pow_pow: forall(g: group, v,v_1 : gf_q), g^v^v_1 = g^(v_1*v).
axiom pow_com: forall(g: group, v,v_1 : gf_q), g^v^v_1 = g^v_1^v.


(*lemma pow_com: forall(g : group, v,v_1 : gf_q), g^v^v_1 = g^(v_1*v).
    proof.
*)

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
    var priv_k: gf_q;
    priv_k <$ dgf_q;
    return (g^priv_k, priv_k); (*x is Alice's  private key *)
  }

  proc enc(A: group, plain_text : text) : group*text ={
      var k : gf_q; var c_1 : group; var c_2 : text;
      k <$ dgf_q; (* Ephemeral key *)
      c_1 <- g^k;
      c_2 <@ TRF.f(A^k); c_2 <- c_2 ++ plain_text;
      return (c_1, c_2); (* Here A is Alice public key A = g^priv_key , this returns c_1=g^k and c_2= TRF.f(A^k)++message *)
  }

      (* decryption *)

  proc dec(priv_key: gf_q, c_1 : group, c_2 : text) : text ={
      var y : group; var c_3 : text;
      y <- c_1^(priv_key);
      c_3 <@ TRF.f(y);
      return(c_3 ++ c_2); (* As y =c_1^(priv_key) and c_1 = g^k; c_3 ++ c_2 will  TRF.f(c_1^(priv_key)) ++ TRF.f(A^k) ++ message *)
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

lemma exp_equal : forall(g: group, x_1, x_2 : gf_q),  x_1 = x_2 => g^x_1 = g^x_2 .
    admit.
    qed.


lemma correctness : phoare[Cor(Enc(TRF)).main : true ==> res] = 1%r.
    proof.
      proc.
      inline*.
      seq 2: (pub_key = g ^ priv_key).
      auto.
      auto.    
      progress.
      apply lossless.
      sp.
      seq 2: (c_10 = g ^ k /\  A = pub_key /\ plain_text = x /\ pub_key = g ^ priv_key).
      auto.
      auto.
      progress.
      apply lossless.
      sp.
      rcondt 1.
      auto.
      progress.
    
      seq 2: (x0 = A ^ k /\  c_10 = g ^ k /\ A = pub_key /\ plain_text = x /\ pub_key = g ^ priv_key  /\ x0 \notin TRF.mp /\ TRF.mp.[x0] = Some y1).
(*      seq 9: (c_1 = g ^ k /\ TRF.mp.[x0] = Some y1 /\ x1 = c_1 ^ priv_key /\ c_2 = y1 ).*)
      auto.
      auto.
      progress.
      apply dtext_lossless.
      trivial.
    

      apply get_set_sameE.
    
      seq 0: (x1 = c_1^priv_key).   
      auto.
      auto.
      if.
      auto.
      progress.
      apply dtext_lossless.
         
    
      seq 4: ((TRF.mp.[x0] = Some y1)/\ (c_20 = oget TRF.mp.[x0] ++ plain_text) /\ x0 = A ^ k).
      auto.
      wp.
      auto.
      progress.
      apply dtext_lossless.
      apply get_set_sameE.
      sp.
      progress.
      if.
      seq 1: ((TRF.mp.[x1] = Some y2)/\(c_20 = oget TRF.mp.[x0] ++ plain_text ) /\ (c_21 = c_2) /\ (x1 = c_1^ priv_key)).
      auto.
      auto.
      progress.
      apply dtext_lossless.
      apply get_some.
      apply get_set_sameE.
      apply oget_some.
    
      auto.
      progress.
      apply get_some.
      seq 2: (TRF.mp.[x0] = Some y1).
      auto.
      auto.    
      progress.
    apply oget_same.
      wp.
      auto.    
      progress.
      auto.
      progress.
      auto.    
      if.
      seq 2: (TRF.mp.[x1] = Some y2).

    
    
    module Game_2 = {

  module EO = EncO(Enc)
  (pub_key, priv_key) <@ EO.init();
