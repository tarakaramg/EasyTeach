(* SymEnc.ec *)

(* Symmetric Encryption *)

(* definitions, including games for judging correctness and IND-CPA
 (indistinguishability under chosen plaintext attack) security *)

prover ["Z3"].  (* no SMT solvers *)

require import AllCore Distr DBool FSet List SmtMap.
require import Cyclic_group_prime.
require import Prime_field.
import Dgf_q.

type  text.
const zero:text.

op ( ++ ) : text -> text -> text.
op dtext : text distr.

axiom xor_commutative : forall(x : text, y : text), x ++ y = y ++  x.
axiom xor_associative (x,y,z : text) : (x ++ y) ++ z = x ++ (y ++ z).
axiom xor_with_0 (x : text) :  x ++ zero  = x.
axiom xor_with_itself: forall(x:text), x ++ x = zero.
axiom dtext_lossless : weight dtext = 1%r.

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

proc enc(pub_key: pub, plain_text : text) : cipher ={
    var eph_key : gf_q; var c_1 : group; var c_2 : text;
    eph_key <$ dgf_q; (* Ephemeral key *)
    c_1 <- g^eph_key;
    c_2 <@ RO.f(pub_key^eph_key); c_2 <- c_2 ++ plain_text;
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

module type ADV_LCDH = {

 proc main (x1 : pub, x2 : group) : group fset
}.


module type GAME_LCDH = {

 proc main () : bool
}.

print fset.
search fdom.

module Adv_LCDH (Adv : ADV)  : ADV_LCDH = {
  (* LCDH adversary, takes g^x and g^y, return list of g^xy guesses using ADV choose and guess procedures*)
 module Or : RO = {

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

 }

 module A = Adv(Or)

     proc main (pub_key : pub, gy : group) : group fset = {
     var x1, x2, x3 : text; var b : bool; var c : cipher;
     Or.init();
     (x1, x2) <@ A.choose(pub_key);
       x3 <$ dtext;
     c <- (gy ,x3);
       b <@ A.guess(c);
       return fdom Or.mp;
     }
 }.



module  Game_LCDH (Adv_LCDH : ADV_LCDH) : GAME_LCDH = {

 (* LCDH Game, we randomly pick x,y, and pass g^x, g^y to LCDH Adversary, which returns a list *)
   proc main() : bool = {
   var priv_key: priv; var eph_key : gf_q; var l : group fset;
   priv_key <$ dgf_q;
   eph_key <$ dgf_q;
   l <@ Adv_LCDH.main( g ^ priv_key, g ^ eph_key);
   return (g^ (priv_key * eph_key) \in l);
   }
 }.

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
     seq 3: (plain_text = x /\ c_1 = g ^ eph_key /\ x0 = g ^ (priv_key * eph_key)).
     auto.
     auto.
     progress.
     apply lossless.
     rewrite pow_pow pow_com_2.
     trivial.   
     if.
     seq 1 : 
   (plain_text = x /\ c_1 = g ^ eph_key /\ x0 = g ^ (priv_key * eph_key) /\
     x0 \notin RO.mp).
     auto.
     auto; progress; apply dtext_lossless.
     sp; wp.
     rcondf 1.
     auto; progress.
   search dom _.[_<-_].
     rewrite pow_pow. rewrite pow_com_2.
     rewrite pow_com_2.
     apply mem_set.
     smt( pow_pow pow_com_2).
     auto.
     progress.
     rewrite pow_pow pow_com_2.
     rewrite get_set_sameE.
     have -> : oget (Some y1{hr}) ++ (oget (Some y1{hr}) ++ x{hr}) =
   (oget (Some y1{hr}) ++ oget (Some y1{hr})) ++ x{hr}.
     rewrite xor_associative //.
     rewrite xor_with_itself.
     have -> : zero ++ x{hr} = x{hr}.
     rewrite xor_commutative.
     by rewrite xor_with_0 //.       
     trivial.       
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
     rewrite - xor_associative.
     rewrite xor_with_itself.
     rewrite xor_commutative.       
     rewrite xor_with_0.
     trivial.
 hoare.
     auto.
     progress.
     rewrite pow_pow.
     trivial.
     auto.
     wp.
     auto.
     trivial.
 qed.


section.

declare module Adv : ADV{RO}.

axiom Adv_choose_ll (Or <: RO{Adv}) :
  islossless Or.f => islossless Adv(Or).choose.

axiom Adv_guess_ll (Or <: RO{Adv}) :
  islossless Or.f => islossless Adv(Or).guess.


local module ROL : RO = {

   var mp : (group, text) fmap
   var bad_flag : bool
   var bad_key : group

   proc init() : unit = {

     }
         proc f(x : group) : text = {
         var y : text;
         bad_flag <- bad_flag \/ (x = bad_key);
         (*
         if ( x = bad_key) bad_flag <- true;
         *)
         if (! x \in mp) {   (* give x a random value in *)
         y <$ dtext;  (* mp if not already in mp's domain *)
         mp.[x] <- y;
       }
           return oget mp.[x];
     }

   }.

local module GAME_1 = {

       module A = Adv(ROL)

         proc main() : bool = {
         var b, b' : bool; var x1, x2, x3 : text; var c : cipher; var eph_key : gf_q;
         var priv_key : priv; var pub_key : pub;
         ROL.mp <- empty;  (* empty map *)
         ROL.bad_flag <- false;
         priv_key  <$ dgf_q;
         eph_key <$ dgf_q;
         pub_key <- g ^ priv_key;
         ROL.bad_key <- pub_key ^ eph_key;
         (x1, x2) <@ A.choose(pub_key);
           b <$ {0,1};
           if (! pub_key ^ eph_key \in ROL.mp) {   (* give x a random value in *)
           x3 <$ dtext;  (* mp if not already in mp's domain *)
           ROL.mp.[pub_key ^ eph_key] <- x3;
         }
             x3 <- oget ROL.mp.[pub_key^eph_key];
             c <- (g^eph_key, x3 ++ (b ? x1 : x2));
             b' <@ A.guess(c);
         return (b=b');
       }
     }.


local module GAME_2 = {

         module A = Adv(ROL)

           proc main() : bool = {
           var b, b' : bool; var x1, x2, x3 : text; var c : cipher; var eph_key : gf_q;
           var priv_key : priv; var pub_key : pub; 
           ROL.mp <- empty;  (* empty map *)
           ROL.bad_flag <- false;
           priv_key  <$ dgf_q;
           eph_key  <$ dgf_q;
           pub_key <- g ^ priv_key;
           ROL.bad_key <- pub_key ^ eph_key;
           (x1, x2) <@ A.choose(pub_key);
             b <$ {0,1};
             x3 <$ dtext;
             c <- (g^eph_key, x3 ++ (b ? x1 : x2));
             b' <- A.guess(c);
           return (b=b');
         }
       }.


local module GAME_3  = {

    module A = Adv(ROL)

      proc main() : bool = {
      var b, b' : bool; var x1, x2, x3 : text; var c : cipher; var eph_key : gf_q;
      var priv_key : priv; var pub_key : pub;
      ROL.mp <- empty;  (* empty map *)
      ROL.bad_flag <- false;
      priv_key  <$ dgf_q;
      eph_key <$ dgf_q;
      pub_key <- g ^ priv_key;             
      ROL.bad_key <- pub_key ^ eph_key;
      (x1, x2) <@ A.choose(pub_key);
        x3 <$ dtext;
        c <- (g ^ eph_key, x3);
        b' <- A.guess(c);
        b <$ {0,1};
      return (b=b');
    }
}.


 local lemma IND_CPA_G1 &m :
     Pr[IND_CPA(Enc, Adv).main() @ &m : res] = Pr[GAME_1.main() @ &m : res].
     proof. 
       byequiv.
     
       proc.
       inline*.
       sp.
       swap{1} 7 -5.
       swap{1} 5 -2.
       swap{2} 6 -3.
       seq 4 5:(ROL.bad_key{2} = pub_key{2}^eph_key{2} /\
       pub_key{2} = g^priv_key{2} /\ pub_key{1} = g^priv_key{1}/\
       RO.mp{1} = ROL.mp{2} /\ ={pub_key, eph_key,priv_key} /\ ={b}).
       auto. progress.
       seq 1 1: (={pub_key,b,x1,x2, eph_key,priv_key} /\
       RO.mp{1} = ROL.mp{2} /\ ={glob Adv}).
       call (_ : (RO.mp{1} = ROL.mp{2})).
       proc.
       sim.
       auto. 
       sim.
       wp ;sp.
       if.
       progress.
       auto.
       progress.
       trivial.
       trivial.
   qed.


local lemma G1_G2_equiv :
 equiv[GAME_1.main ~ GAME_2.main :
         true ==> ={ROL.bad_flag}/\(!ROL.bad_flag{1}  => ={res})].
       
    proof.
      proc.

      sp.
      swap 6 -1.
      seq 5 5: (={priv_key,eph_key, ROL.bad_key, ROL.bad_flag, pub_key, b, ROL.mp} /\
      ROL.bad_key{2} = pub_key{2}^eph_key{2} /\
      !ROL.bad_flag{1} /\
      pub_key{1} = g^priv_key{1} /\ ROL.mp{1} = empty ).
      auto.
      seq 1 1: (={priv_key,eph_key, ROL.bad_key, ROL.bad_flag,
      pub_key, b, ROL.mp, x1,x2, glob Adv}/\ ROL.bad_key{2} = pub_key{2}^eph_key{2}  /\
        pub_key{1} = g^priv_key{1}  /\
      (!ROL.bad_flag{1} => ROL.bad_key{2}  \notin ROL.mp{2})).
    
        call (_ : (={ROL.bad_flag, ROL.bad_key, ROL.mp})/\
      (!ROL.bad_flag{1} => ROL.bad_key{2}  \notin ROL.mp{2})).
        proc.
        sp. 
    if => //.
        auto.
        progress.
        rewrite mem_set.
        smt().
        auto.
        progress. 
        smt().
        auto.
        progress.
        apply mem_empty.
    
        seq 3 2 : (={pub_key, priv_key, eph_key, b, ROL.bad_key, ROL.bad_flag, glob Adv, x1,x2} /\
      (!ROL.bad_flag{1} => ={c} /\
        ROL.mp{1} = ROL.mp{2}.[ROL.bad_key{2} <- x3{2}] /\
        !ROL.bad_key{2} \in ROL.mp{2}) ) .
        if{1}.
        wp.
        auto.
        progress.
        rewrite get_set_sameE.  
        smt(). (*rewrite get_set_sameE*)
        auto.
        progress.
        (*auto.
        progress.*)
        apply dtext_lossless.
        smt().
        smt().
        apply H. trivial.
        exists* x3{2}.
        elim* => x3_R.

        call (_ : ={ROL.bad_flag, ROL.bad_key, glob Adv}/\
      (!ROL.bad_flag{1} => ={c} /\ ROL.bad_key{2}  \notin ROL.mp{2}/\
        ROL.mp{1} = ROL.mp{2}.[ROL.bad_key{2} <- x3_R]) ==> (* P ==> *)
      ={ROL.bad_flag, ROL.bad_key}/\(!ROL.bad_flag{1}  => ={res})). (* Q *)

        proc (ROL.bad_flag) (*Bad *)
    ( ={ROL.bad_flag, ROL.bad_key} /\
      ROL.bad_key{2} \notin ROL.mp{2}  /\
      ROL.mp{1} = ROL.mp{2}.[ROL.bad_key{2} <- x3_R]) (* I *)
    (ROL.bad_flag{1}/\ ={ROL.bad_flag, ROL.bad_key}).  (* J *)
    by move => />.
    move => &1 &2.
      by case (ROL.bad_flag{2}).
      apply Adv_guess_ll.
      proc.
      sp.
      if{1}.
      if{2}.
      auto.
      progress.
      rewrite get_set_sameE.
      by rewrite get_set_sameE //.    
      rewrite mem_set.
      smt().
    search _.[_<-_].[_<-_].
      rewrite set_set_neqE.
      smt().
      trivial.
      auto.
      progress.
      apply dtext_lossless.
    search oget.
      rewrite get_set_eqE. trivial.
      smt(mem_set).
      rewrite set_set_neqE.
      smt(). 
      smt(mem_set).
      if{2}.
      auto.
      progress.
      apply dtext_lossless.
      smt(mem_set).
      smt(mem_set).
      smt(mem_set).    
      auto.
      progress.
    search  _.[_<-_].[_].
      rewrite get_set_neqE.
      smt(). trivial.
      progress.
      proc.   
      sp.
      if.
      auto.
      progress.
      apply dtext_lossless.
      smt().
      smt().
      progress.
      auto.
      progress.
      smt().
      smt().
      progress.
      proc.
      sp.
      if.
      auto.
      progress.
      apply dtext_lossless.
      smt().
      smt().
      auto.
      progress.

      smt().
      smt().
      auto.
      progress. progress.
      smt().
      smt().
      smt().
      smt().
  qed.
    
local lemma G1_G2 &m :`| Pr[GAME_1.main() @ &m: res] - Pr[GAME_2.main() @ &m : res]| <= Pr[GAME_2.main() @ &m : ROL.bad_flag].
        
    proof.
byequiv
    (_ :
      true ==> ={ROL.bad_flag} /\ ( ={ROL.bad_flag} /\ !ROL.bad_flag{1}  => ={res})):
  (ROL.bad_flag).
    by conseq G1_G2_equiv.  
    progress.
    progress.
    smt().
    smt().
qed.

axiom dtext_fu : is_full dtext.
axiom dtext_uni : is_uniform dtext.
axiom dtext_ll : is_lossless dtext.

  
 local lemma G2_G3_equiv &m :
     Pr[GAME_2.main() @ &m : res] = Pr[GAME_3.main() @ &m : res].
     proof.
       byequiv.
       proc.
       sp.
       seq 4 4: (={ROL.mp, ROL.bad_flag, ROL.bad_key, priv_key, eph_key, pub_key} /\
       ROL.mp{1} = empty /\ pub_key{1} = g ^ priv_key{1} /\
       ROL.bad_key{1} = pub_key{1} ^ eph_key{1}).
       auto.
       seq 1 1: (={ROL.mp, ROL.bad_flag, ROL.bad_key, priv_key, eph_key,pub_key,x1,x2, glob Adv}).
       call (_ : ={ROL.mp, ROL.bad_key, ROL.bad_flag}). 
       proc.
       sim.
       progress.
       swap{2} 4 -3.
       seq 3 3: ( ={ROL.mp, ROL.bad_flag, ROL.bad_key, priv_key, eph_key, glob Adv,pub_key,b,x1,x2,c}).    
       wp.
     rnd( fun x => (b{1} ? x1{1} : x2{1}) ++ x).     
       auto.
       progress.
       smt(xor_associative xor_commutative xor_with_0 xor_with_itself).
       apply dtext_uni.
       apply dtext_fu.
       apply dtext_fu.
       apply dtext_fu.
       smt(xor_associative xor_commutative xor_with_0 xor_with_itself).
       smt(xor_associative xor_commutative xor_with_0 xor_with_itself).
       call(_ : ={ROL.mp, ROL.bad_flag, ROL.bad_key}).
       proc.
       sim.
       auto.
       progress.
       progress.
   qed.

 local lemma G3_Pr &m : Pr[GAME_3.main() @ &m: res] = 1%r/2%r .
     proof.
       byphoare.
       proc.
       sp.
       rnd (pred1 b').
       call (_ : true).
       apply Adv_guess_ll.
       proc.
       sp.
       if.
       auto.
       progress.
       apply dtext_lossless.
       auto.
       progress.
       auto.
       call(_ : true).
       apply Adv_choose_ll.
       proc.
       sp.
       if.
       auto.
       progress.
       apply dtext_lossless.
       progress.
       auto.
       progress.
       apply lossless.
       apply dtext_lossless.
       smt.
       smt().
       trivial.
       trivial.
   qed.

 local lemma G2_Pr &m : Pr[GAME_2.main() @ &m: res] = 1%r/2%r .
     proof.
       rewrite -(G3_Pr &m).
       apply (G2_G3_equiv &m).
   qed.

 local lemma G2_G3_bad &m : Pr[GAME_2.main() @ &m : ROL.bad_flag] = Pr[GAME_3.main() @ &m : ROL.bad_flag].
     proof.
       byequiv.
       proc.
       sp.
       seq 4 4: (={ROL.mp, ROL.bad_flag, ROL.bad_key, priv_key, eph_key, pub_key} /\
       ROL.mp{1} = empty /\ pub_key{1} = g ^ priv_key{1} /\
       ROL.bad_key{1} = pub_key{1} ^ eph_key{1}).
       auto.
       seq 1 1: (={ROL.mp, ROL.bad_flag, ROL.bad_key, priv_key, eph_key,pub_key,x1,x2, glob Adv}).
       call (_ : ={ROL.mp, ROL.bad_key, ROL.bad_flag}). 
       proc.
       sim.
       progress.
       swap{2} 4 -3.
       seq 3 3: ( ={ROL.mp, ROL.bad_flag, ROL.bad_key, priv_key, eph_key, glob Adv,pub_key,b,x1,x2,c}).    
       wp.
     rnd( fun x => (b{1} ? x1{1} : x2{1}) ++ x).     
       auto.
       progress.
       smt(xor_associative xor_commutative xor_with_0 xor_with_itself).
       apply dtext_uni.
       apply dtext_fu.
       apply dtext_fu.
       apply dtext_fu.
       smt(xor_associative xor_commutative xor_with_0 xor_with_itself).
       smt(xor_associative xor_commutative xor_with_0 xor_with_itself).
       call(_ : ={ROL.mp, ROL.bad_flag, ROL.bad_key}).
       proc.
       sim.
       auto.
       progress.
       progress.
   qed.

local lemma G3_LCDH_equiv &m : Pr[GAME_3.main() @ &m : ROL.bad_flag]
    = Pr[Game_LCDH(Adv_LCDH(Adv)).main() @ &m : res].
    proof.
      byequiv.
      proc.
      sp.
      inline*.
seq 5 6: (={priv_key, eph_key, pub_key}).    
      call(_ : true).
      proc.
      sp.
      sim.
      progress.
      admit.
      admit.
      admit.
      trivial.
      trivial.
qed.    

local lemma INDCPA_LCDH_equiv &m : `| Pr[IND_CPA(Enc, Adv).main() @ &m : res] - 1%r/2%r | <=
    Pr[Game_LCDH(Adv_LCDH(Adv)).main() @ &m : res].
    proof.
    
    

     


     
     
     
     


     
