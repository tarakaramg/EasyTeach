(* UCCore.eca *)

prover ["Z3" "Alt-Ergo"].

(* Core UC Definitions and Lemmas *)

require import AllCore List FSet ListPO Encoding.

(* real protocols and ideal functionalities (collectively,
   "functionalities") have hierarchical addresses

   if a functionality has address alpha, it is also responsible for all
   sub-functionalities with addresses beta >= alpha (in the prefix
   partial ordering of ListPO)

   adversaries are also modeled as functionalities - but with no
   subaddresses/sub-functionalties; simulators are functionalities
   parameterized by adversaries

   [] is the root address of the environment *)

type addr = int list.

(* ports - pairs of functionality addresses and port indices

   a functionality's ports are used/interpreted however the
   functionality chooses, but typically they are divided into
   different parties

   adversaries can handle multiple port indices, and each simulator
   has a single, distinct port index

   ([], 0) is the root port of the environment *)

type port = addr * int.

(* messages have modes:

     * direct - supplying functionality inputs, consuming their
         outputs

     * adversarial - communication between functionalties and
         adversaries/simulators, communication between different
         adversaries/simulators, and communication between
         environments and adversaries/simulators *)

type mode = [
    Dir  (* direct *)
  | Adv  (* adversarial *)
].

lemma not_dir (mod : mode) :
  mod <> Dir <=> mod = Adv.
proof. by case mod. qed.

lemma not_adv (mod : mode) :
  mod <> Adv <=> mod = Dir.
proof. by case mod. qed.

(* universe *)

type univ = bool list.  (* universe values are lists of bits *)

(* we axiomatize the existence of encoding/partial decoding operators
   on the following types

   we could provide concrete definitions, but we won't rely on
   the details, and so we prefer to keep things abstract; of course
   all types being encoded must be countable *)

clone EPDP as EPDP_Univ_Unit with  (* unit *)
  type orig <- unit, type enc <- univ.

clone EPDP as EPDP_Univ_Bool with  (* bool *)
  type orig <- bool, type enc <- univ.

clone EPDP as EPDP_Univ_Int with  (* int *)
  type orig <- int, type enc <- univ.

clone EPDP as EPDP_Univ_UnivPair with  (* univ * univ *)
  type orig <- univ * univ, type enc <- univ.

clone EPDP as EPDP_Univ_UnivList with  (* univ list *)
  type orig <- univ list, type enc <- univ.

(* now we can build on these axiomatized encoding/partial decoding
   operators *)

(* triple encoding: *)

op nosmt enc_univ_triple (t : univ * univ * univ) : univ =
  EPDP_Univ_UnivPair.enc (t.`1, (EPDP_Univ_UnivPair.enc (t.`2, t.`3))).

op nosmt dec_univ_triple (u : univ) : (univ * univ * univ) option =
  match EPDP_Univ_UnivPair.dec u with
    None   => None
  | Some p =>
      match EPDP_Univ_UnivPair.dec p.`2 with
        None   => None
      | Some q => Some (p.`1, q.`1, q.`2)
      end
  end.

clone EPDP as EPDP_Univ_UnivTriple with (* univ * univ * univ *)
  type orig <- univ * univ * univ, type enc <- univ,
  op enc = enc_univ_triple, op dec = dec_univ_triple
proof *.
realize epdp.
apply epdp_intro => [x | u x].
rewrite /enc /dec /enc_univ_triple /dec_univ_triple /=.
by case x.
rewrite /enc /dec /enc_univ_triple /dec_univ_triple => match_dec_u_eq_some.
have val_u :
  EPDP_Univ_UnivPair.dec u =
  Some (x.`1, EPDP_Univ_UnivPair.enc (x.`2, x.`3)).
  move : match_dec_u_eq_some.
  case (EPDP_Univ_UnivPair.dec u) => // [[]] x1 q /=.
  move => match_dec_q_eq_some.
  have val_y2 :
    EPDP_Univ_UnivPair.dec q = Some (x.`2, x.`3).
    move : match_dec_q_eq_some.
    case (EPDP_Univ_UnivPair.dec q) => // [[]] x2 x3 /= <- //.
  move : match_dec_q_eq_some.
  rewrite val_y2 /= => <- /=.
  by rewrite (EPDP_Univ_UnivPair.dec_enc _ q).
by rewrite (EPDP_Univ_UnivPair.dec_enc _ u).
qed.

(* address encoding: *)

op nosmt enc_addr (x : addr) : univ =
  EPDP_Univ_UnivList.enc (map EPDP_Univ_Int.enc x).

op nosmt dec_addr (u : univ) : addr option =
  match EPDP_Univ_UnivList.dec u with
    None    => None
  | Some vs =>
      let ys = map EPDP_Univ_Int.dec vs
      in if all is_some ys
         then Some (map oget ys)
         else None
  end.

clone EPDP as EPDP_Univ_Addr with (* addr *)
  type orig <- addr, type enc <- univ,
  op enc = enc_addr, op dec = dec_addr
proof *.
realize epdp.
apply epdp_intro => [x | u x].
rewrite /enc /dec /enc_addr /dec_addr /=.
have -> :
  map EPDP_Univ_Int.dec (map EPDP_Univ_Int.enc x) = map Some x by elim x.
have -> /= : all is_some (map Some x) = true by elim x.
by elim x.
rewrite /enc /dec /enc_addr /dec_addr => match_dec_u_eq_some.
have val_u : 
  EPDP_Univ_UnivList.dec u = Some (map EPDP_Univ_Int.enc x).
  move : match_dec_u_eq_some.
  case (EPDP_Univ_UnivList.dec u) => // z /=.
  case (all is_some (map EPDP_Univ_Int.dec z)) =>
    // all_is_some_map_dec_z /= <-.
  move : all_is_some_map_dec_z.
  elim z => [// | v zs IH /= [#] val_v all_is_some_map_dec_zs].
  split; first smt(EPDP_Univ_Int.dec_enc).
  by apply IH.
by rewrite (EPDP_Univ_UnivList.dec_enc _ u).
qed.

(* port encoding: *)

op nosmt enc_port (pt : port) : univ =
  EPDP_Univ_UnivPair.enc (EPDP_Univ_Addr.enc pt.`1, EPDP_Univ_Int.enc pt.`2).

op nosmt dec_port (u : univ) : port option =
  match EPDP_Univ_UnivPair.dec u with
    None   => None
  | Some p =>
      match EPDP_Univ_Addr.dec p.`1 with
        None   => None
      | Some x =>
          match EPDP_Univ_Int.dec p.`2 with
            None   => None
          | Some n => Some (x, n)
          end
      end
  end.

cloneenv EPDP as EPDP_Univ_Port with (* port *)
  type orig <- port, type enc <- univ,
  op enc = enc_port, op dec = dec_port
proof *.
realize epdp.
apply epdp_intro => [x | u x].
rewrite /enc /dec /enc_port /dec_port /=.
by case x.
rewrite /enc /dec /enc_port /dec_port => match_eq_some.
have val_u :
  EPDP_Univ_UnivPair.dec u =
  Some (EPDP_Univ_Addr.enc x.`1, EPDP_Univ_Int.enc x.`2).
  move : match_eq_some.
  case (EPDP_Univ_UnivPair.dec u) => // p /= match_eq_some.
  have val_p_fst : EPDP_Univ_Addr.dec p.`1 = Some x.`1.
    move : match_eq_some.
    case (EPDP_Univ_Addr.dec p.`1) => // ys /=.
    by case (EPDP_Univ_Int.dec p.`2).
  move : match_eq_some.
  rewrite val_p_fst /= => match_eq_some.
  have val_p_snd : EPDP_Univ_Int.dec p.`2 = Some x.`2.
    move : match_eq_some.
    case (EPDP_Univ_Int.dec p.`2) => // x0 /= <- //.
  move : match_eq_some.
  rewrite val_p_snd /= => <- /=.
  move : val_p_fst val_p_snd.
  case p => p1 p2 /= val_p_fst val_p_snd.
  split.
  by rewrite (EPDP_Univ_Addr.dec_enc x.`1 p1).
  by rewrite (EPDP_Univ_Int.dec_enc x.`2 p2).
by rewrite (EPDP_Univ_UnivPair.dec_enc _ u).
qed.

(* port * univ encoding: *)

op nosmt enc_port_univ (x : port * univ) : univ =
  EPDP_Univ_UnivPair.enc (EPDP_Univ_Port.enc x.`1, x.`2).

op nosmt dec_port_univ (u : univ) : (port * univ) option =
  match EPDP_Univ_UnivPair.dec u with
    None   => None
  | Some p =>
      match EPDP_Univ_Port.dec p.`1 with
        None    => None
      | Some pt => Some (pt, p.`2)
      end
  end.

clone EPDP as EPDP_Univ_PortUniv with (* port * univ *)
  type orig <- port * univ, type enc <- univ,
  op enc = enc_port_univ, op dec = dec_port_univ
proof *.
realize epdp.
apply epdp_intro => [x | u x].
rewrite /enc /dec /enc_port_univ /dec_port_univ /=.
by case x.
rewrite /enc /dec /enc_port_univ /dec_port_univ => match_dec_u_eq_some.
rewrite (EPDP_Univ_UnivPair.dec_enc _ u) //.
move : match_dec_u_eq_some.
case (EPDP_Univ_UnivPair.dec u) => // [[]] x1 x2 /=.
move => match_dec_x1_eq_some.
have val_dec_x1 : EPDP_Univ_Port.dec x1 = Some x.`1 by smt().
move : match_dec_x1_eq_some.
rewrite val_dec_x1 /= => <- /=.
by rewrite (EPDP_Univ_Port.dec_enc _ x1).
qed.

(* port * port * univ encoding: *)

op nosmt enc_port_port_univ (x : port * port * univ) : univ =
  EPDP_Univ_UnivTriple.enc
  (EPDP_Univ_Port.enc x.`1, EPDP_Univ_Port.enc x.`2, x.`3).

op nosmt dec_port_port_univ (u : univ) : (port * port * univ) option =
  match EPDP_Univ_UnivTriple.dec u with
    None   => None
  | Some t =>
      match EPDP_Univ_Port.dec t.`1 with
        None     => None
      | Some pt1 =>
          match EPDP_Univ_Port.dec t.`2 with
            None     => None
          | Some pt2 => Some (pt1, pt2, t.`3)
          end
      end
  end.

clone EPDP as EPDP_Univ_PortPortUniv with (* port * port * univ *)
  type orig <- port * port * univ, type enc <- univ,
  op enc = enc_port_port_univ, op dec = dec_port_port_univ
proof *.
realize epdp.
apply epdp_intro => [x | u x].
rewrite /enc /dec /enc_port_port_univ /dec_port_port_univ /=.
by case x.
rewrite /enc /dec /enc_port_port_univ /dec_port_port_univ =>
  match_dec_u_eq_some.
rewrite (EPDP_Univ_UnivTriple.dec_enc _ u) //.
move : match_dec_u_eq_some.
case (EPDP_Univ_UnivTriple.dec u) => // [[]] x1 x2 x3 /=.
move => match_dec_x1_eq_some.
have val_dec_x1 : EPDP_Univ_Port.dec x1 = Some x.`1 by smt().
move : match_dec_x1_eq_some.
rewrite val_dec_x1 /=.
move => match_dec_x2_eq_some.
have val_dec_x2 : EPDP_Univ_Port.dec x2 = Some x.`2 by smt().
split; first by rewrite (EPDP_Univ_Port.dec_enc _ x1).
split; first by rewrite (EPDP_Univ_Port.dec_enc _ x2).
smt().
qed.

(* port * int * univ encoding: *)

op nosmt enc_port_int_univ (x : port * int * univ) : univ =
  EPDP_Univ_UnivTriple.enc
  (EPDP_Univ_Port.enc x.`1, EPDP_Univ_Int.enc x.`2, x.`3).

op nosmt dec_port_int_univ (u : univ) : (port * int * univ) option =
  match EPDP_Univ_UnivTriple.dec u with
    None   => None
  | Some t =>
      match EPDP_Univ_Port.dec t.`1 with
        None    => None
      | Some pt =>
          match EPDP_Univ_Int.dec t.`2 with
            None   => None
          | Some n => Some (pt, n, t.`3)
          end
      end
  end.

clone EPDP as EPDP_Univ_PortIntUniv with (* port * int * univ *)
  type orig <- port * int * univ, type enc <- univ,
  op enc = enc_port_int_univ, op dec = dec_port_int_univ
proof *.
realize epdp.
apply epdp_intro => [x | u x].
rewrite /enc /dec /enc_port_int_univ /dec_port_int_univ /=.
by case x.
rewrite /enc /dec /enc_port_int_univ /dec_port_int_univ =>
  match_dec_u_eq_some.
rewrite (EPDP_Univ_UnivTriple.dec_enc _ u) //.
move : match_dec_u_eq_some.
case (EPDP_Univ_UnivTriple.dec u) => // [[]] x1 x2 x3 /=.
move => match_dec_x1_eq_some.
have val_dec_x1 : EPDP_Univ_Port.dec x1 = Some x.`1 by smt().
move : match_dec_x1_eq_some.
rewrite val_dec_x1 /=.
move => match_dec_x2_eq_some.
have val_dec_x2 : EPDP_Univ_Int.dec x2 = Some x.`2 by smt().
split; first by rewrite (EPDP_Univ_Port.dec_enc _ x1).
split; first by rewrite (EPDP_Univ_Int.dec_enc _ x2).
smt().
qed.

(* a message has the form (mod, pt1, pt2, u), for a mode mod, a
   destination port pt1, a source port pt2, and a universe
   value u *)

type msg = mode * port * port * univ.

(* guard an optional message using predicate *)

op opt_msg_guard :
     (mode -> addr -> int -> addr -> int -> univ -> bool) ->
     msg option -> msg option =
     fun f : mode -> addr -> int -> addr -> int -> univ -> bool =>
     fun m_opt : msg option =>
       match m_opt with
         None   => None
       | Some m =>
           if f m.`1 m.`2.`1 m.`2.`2 m.`3.`1 m.`3.`2 m.`4
           then m_opt
           else None
       end.

(* module type used for real protocols and ideal functionalities
   (collectively, "functionalities"), as well as adversaries and
   simulators *)

(* precondition: *)

pred func_init_pre (self adv : addr) = inc self adv.

(* envport0 self adv pt says that pt is part of the environment, not
   the functionality or adversary; it's allowed to be the root port,
   ([], 0) *)

op envport0 (self adv : addr, pt : port) : bool =
  ! self <= pt.`1 /\ ! adv <= pt.`1.

(* envport self adv pt says that pt is part of the
   environment and is not the root port *)

op envport (self adv : addr, pt : port) : bool =
  envport0 self adv pt /\ pt <> ([], 0).

module type FUNC = {
  (* initialize functionality (or adversary), telling it its address
     (self) and the address of its adversary (adv)

     in the case of the adversary, the second argument will be [], the
     root address of the environment (so the adversary's "adversary" is
     the environment)

     precondition for ordinary (non-adversary) functionalties:
     func_init_pre self adv *)

  proc init(self adv : addr) : unit

  (* respond to an incoming message, producing an optional
     outgoing message (None means error)

     messages to a functionality should have addresses that are >=
     self (in the case of an adversary, = self)

     if Some m' is returned, then the destination address of m' should
     not be >= self, and the source address of m' should be >= self
     (in the case of an adversary, the source address should be =
     self) *)

  proc invoke(m : msg) : msg option
}.

(* module type of interfaces (to environment): consists of
   a functionality part and an adversary part *)

pred inter_init_pre (func adv : addr) = inc func adv.

module type INTER = {
  (* initialize interface, telling it:

       * the address (func) of its functionality part;

       * the address (adv) of its adversary part;

       * an incoming message guard (in_guard)

     the interface will initialize its functionality and adversary
     parts; when calling the adversary part's init function, the
     second argument will be [], the root address of the environment

     precondition:

       inter_init_pre func adv *)

  proc init(func adv : addr, in_guard : int fset) : unit

  (* respond to an incoming message, producing an optional
     outgoing message (None means error)

     messages whose destination addresses aren't either >= the
     interface's functionality part's address, func, or *equal* to the
     interface's adversary part's addresss, adv, should result in None
     being returned

     all incoming messages with mode Dir must be addressed to the
     interface's functionality part (else None is returned); all
     incoming messages with mode Adv must be addressed to the
     interface's adversary part (else None is returned)

     if the interface's functionality part returns a message with
     destination address >= func, or if the interface's adversary part
     returns a message with destination address >= adv, then
     None should be returned

     if the interface's functionality part returns a message with
     source address not >= func, or if the interface's adversary part
     returns a message with source address <> adv, then None should be
     returned

     all outgoing messages with mode Dir come from the interface's
     functionality part; all outgoing messages with mode Adv come from
     the interface's adversary part

     the standard (Adv mode) channel between the environment and the
     interface's adversary part consists of messages between port
     ([], 0) (in the environment) and port (adv, 0) (in the
     interface's adversary part)

     the environment may communicate with other port indices of the
     interface's adversary part, except that such a communication will
     result in an error if its destination port isn't of the form
     (adv, n) for some n in in_guard; communication with such other
     ports must not originate from ([], 0)

     when the interface's adversary part sends a message to a port of
     the environment other than ([], 0), the message may not originate
     from (adv, 0)

     if the interface's functionality part sends a message to the
     interface's adversary port (destination address must be = adv),
     this message must have mode Adv, and it may not have destination
     port (adv, 0)

     if the interface's adversary port sends a message to the
     interface's functionality part, this message must have mode
     Adv, and must not come from port (adv, 0) *)

  proc invoke(m : msg) : msg option
}.

(* module type of environments, parameterized by interfaces *)

pred env_init_pre (func adv : addr) = inter_init_pre func adv.

module type ENV (Inter : INTER) = {
  (* start environment, and let it interact with Inter (only via
     Inter.invoke, not via Inter.init), eventually returning a boolean
     judgment

     we have:

       * func is the address of interface's functionality part

       * adv is the address of interface's adversary part

     the standard (Adv mode) channel between the environment and the
     interface's adversary part consists of messages between port
     ([], 0) (in the environment) and port (adv, 0) (in the
     interface's adversary part)

     the environment may communicate with other ports of the
     interface's adversary part, except that such a communication will
     result in an error if its destination port isn't of the form
     (adv, n) for some n in in_guard

     precondition : env_pre func adv *)

  proc main(func adv : addr, in_guard : int fset) : bool {Inter.invoke}
}.

(* carry out experiment in which the environment is allowed to
   interact with, and issue a final boolean judgment about, an
   interface, which is first initialized *)

pred exper_pre (func adv : addr) = inter_init_pre func adv.

lemma exper_pre_ext1 (func adv ext : addr) :
  exper_pre func adv => exper_pre (func ++ ext) adv.
proof.
rewrite /exper_pre /inter_init_pre.
move => |> inc_fun_adv.
by apply inc_ext1.
qed.

module Exper (Inter : INTER, Env : ENV) = {
  module E = Env(Inter)

  (* arguments to main:

       * func is address of interface's functionality part

       * adv is the address of the interface's adversary part

       * in_guard is the incoming message guard used by the interface
         and supplied to the environment

     precondition:

       exper_pre func adv *)

  proc main(func adv : addr, in_guard : int fset) : bool = {
    var b : bool;
    Inter.init(func, adv, in_guard);
    b <@ E.main(func, adv, in_guard);
    return b;
  }    
}.

(* make interface out of functionality and adversary parts *)

abstract theory MakeInterface.

(* loop invariant for interface's while loop *)

pred mi_loop_invar
     (func adv : addr, in_guard : int fset,
      m : msg, r : msg option, not_done : bool) =
  inter_init_pre func adv /\
  (not_done =>
   (m.`1 = Dir /\ func <= m.`2.`1 /\ envport func adv m.`3 /\
    m.`3 <> ([], 0)) \/
   (m.`1 = Adv /\ func <= m.`2.`1 /\ m.`3.`1 = adv /\ m.`3.`2 <> 0) \/
   (m.`1 = Adv /\ m.`2.`1 = adv /\
    ((func <= m.`3.`1 /\ m.`2.`2 <> 0) \/
     (m.`3 = ([], 0) /\ m.`2.`2 = 0) \/
     (envport func adv m.`3 /\ m.`2.`2 <> 0 /\
     m.`2.`2 \in in_guard)))) /\
  (! not_done =>
   r = None \/
   (envport0 func adv (oget r).`2 /\
    (((oget r).`1 = Dir /\ (oget r).`2 <> ([], 0) /\
      func <= (oget r).`3.`1) \/
     ((oget r).`1 = Adv /\ adv = (oget r).`3.`1 /\
      ((oget r).`2 = ([], 0) <=> (oget r).`3.`2 = 0))))).

lemma mi_loop_invar_not_done_imp_dest
      (func adv : addr, in_guard : int fset,
       m : msg, r : msg option) :
  mi_loop_invar func adv in_guard m r true =>
  func <= m.`2.`1 \/ adv = m.`2.`1.
proof.
smt().
qed.

(* guard for invoke procedure of interface *)

op main_guard (func adv : addr, in_guard : int fset, m : msg) : bool =
  m.`1 = Dir /\ func <= m.`2.`1 /\ envport func adv m.`3 \/
  m.`1 = Adv /\ m.`2.`1 = adv /\
  (m.`2.`2 = 0 /\ m.`3 = ([], 0) \/
   m.`2.`2 <> 0 /\ m.`2.`2 \in in_guard /\ envport func adv m.`3).

module MI (Func : FUNC, Adv : FUNC) : INTER = {
  var func, adv : addr
  var in_guard : int fset

  proc init(func_ adv_ : addr, in_guard_ : int fset) : unit = {
    func <- func_; adv <- adv_; in_guard <- in_guard_;
    Func.init(func, adv);
    Adv.init(adv, []);
  }

  proc after_func(r : msg option) : msg option * msg * bool = {
    var m : msg <- witness;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (func <= m.`2.`1 \/ ! func <= m.`3.`1) {
        r <- None; not_done <- false;
      }
      (* else: ! func <= m.`2.`1 /\ func <= m.`3.`1 *)
      elif (m.`1 = Dir) {
        not_done <- false;
        if (adv <= m.`2.`1 \/ m.`2 = ([], 0)) {
          r <- None;
        }
        (* else: envport func adv m.`2 *)
      }
      (* else: m.`1 = Adv *)
      elif (m.`2.`1 <> adv \/ m.`2.`2 = 0) {
        r <- None; not_done <- false;
      }
      (* else: m.`2.`1 = adv /\ m.`2.`2 <> 0 *)
    }          
    return (r, m, not_done);
  }

  proc after_adv(r : msg option) : msg option * msg * bool = {
    var m : msg <- witness;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (m.`1 = Dir \/ adv <= m.`2.`1 \/ adv <> m.`3.`1) {
        r <- None; not_done <- false;
      }
      (* else: m.`1 = Adv /\ ! adv <= m.`2.`1 /\ adv = m.`3.`1 *)
      elif (func <= m.`2.`1) {
        if (m.`3.`2 = 0) {
          r <- None; not_done <- false;
        }
        (* else: m.`3.`2 <> 0 *)
      }
      else {  (* envport0 func adv m.`2 *)
        not_done <- false;
        if (! (m.`3.`2 = 0 <=> m.`2 = ([], 0))) {
          r <- None;
        }
      }
    }
    return (r, m, not_done);
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;

    while (not_done) {
      if (func <= m.`2.`1) {
        r <@ Func.invoke(m);
        (r, m, not_done) <@ after_func(r);
      }
      else {  (* adv = m.`2.`1 *)
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ after_adv(r);
      }      
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option;
    if (main_guard func adv in_guard m) {
      r <@ loop(m);
    }
    else {
      r <- None;
    }
    return r;
  }
}.

(* check that invariant is actually preserved: *)

lemma MI_after_func_hoare (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI}) :
  hoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv ==>
   mi_loop_invar MI.func MI.adv MI.in_guard res.`2 res.`1 res.`3].
proof.
proc; auto; smt().
qed.

lemma MI_after_adv_hoare (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI}) :
  hoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv ==>
   mi_loop_invar MI.func MI.adv MI.in_guard res.`2 res.`1 res.`3].
proof.
proc; auto; smt().
qed.

lemma MI_invoke_hoare (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI}) :
  hoare
  [MI(Func, Adv).invoke :
   inter_init_pre MI.func MI.adv ==>
   res = None \/
   (envport0 MI.func MI.adv (oget res).`2 /\
    (((oget res).`1 = Dir /\ (oget res).`2 <> ([], 0) /\
      MI.func <= (oget res).`3.`1) \/
     ((oget res).`1 = Adv /\ MI.adv = (oget res).`3.`1 /\
      ((oget res).`2 = ([], 0) <=> (oget res).`3.`2 = 0))))].
proof.
proc.
if.
inline MI(Func, Adv).loop.
wp; sp.
while (mi_loop_invar MI.func MI.adv MI.in_guard m0 r0 not_done).
if.
seq 1 : (inter_init_pre MI.func MI.adv /\ not_done).
call (_ : true); first auto; smt().
call (MI_after_func_hoare Func Adv).
auto.
seq 1 : (inter_init_pre MI.func MI.adv /\ not_done).
call (_ : true); first auto; smt().
call (MI_after_adv_hoare Func Adv).
auto.
auto; smt().
auto.
qed.

(* phoare lemmas for after_func and after_adv: *)

pred after_func_to_env (func adv : addr, r : msg option) =
  r <> None /\
  (oget r).`1 = Dir /\ envport func adv (oget r).`2 /\
  func <= (oget r).`3.`1.

pred after_func_to_adv (func adv : addr, r : msg option) =
  r <> None /\
  (oget r).`1 = Adv /\ (oget r).`2.`1 = adv /\ (oget r).`2.`2 <> 0 /\
  func <= (oget r).`3.`1.

pred after_func_error (func adv : addr, r : msg option) =
   (r = None \/
    func <= (oget r).`2.`1 \/
    ! func <= (oget r).`3.`1 \/
    ((oget r).`1 = Dir /\
     (adv <= (oget r).`2.`1 \/ (oget r).`2 = ([], 0))) \/
    ((oget r).`1 = Adv /\ ((oget r).`2.`1 <> adv \/ (oget r).`2.`2 = 0))).

lemma after_func_disj (func adv : addr, r : msg option) :
  after_func_to_env func adv r \/
  after_func_to_adv func adv r \/
  after_func_error func adv r.
proof.
smt().
qed.

lemma MI_after_func_to_env (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_func_to_env MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

lemma MI_after_func_to_adv (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_func_to_adv MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

lemma MI_after_func_error (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI}) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv /\ after_func_error MI.func MI.adv r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

pred after_adv_to_env (func adv : addr, r : msg option) =
   r <> None /\
   (oget r).`1 = Adv /\ envport0 func adv (oget r).`2 /\
   adv = (oget r).`3.`1 /\
   ((oget r).`2 = ([], 0) <=> (oget r).`3.`2 = 0).

pred after_adv_to_func (func adv : addr, r : msg option) =
  r <> None /\
  (oget r).`1 = Adv /\ func <= (oget r).`2.`1 /\
  (oget r).`3.`1 = adv /\ (oget r).`3.`2 <> 0.

pred after_adv_error (func adv : addr, r : msg option) =
   (r = None \/
    (oget r).`1 = Dir \/
    adv <= (oget r).`2.`1 \/
    adv <> (oget r).`3.`1 \/
    (func <= (oget r).`2.`1 /\ (oget r).`3.`2 = 0) \/
    (! func <= (oget r).`2.`1 /\
     ! ((oget r).`3.`2 = 0 <=> (oget r).`2 = ([], 0)))).

lemma after_adv_disj (func adv : addr, r : msg option) :
  after_adv_to_env func adv r  \/
  after_adv_to_func func adv r \/
  after_adv_error func adv r.
proof.
smt().
qed.

lemma MI_after_adv_to_func (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_adv_to_func MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt(inc_le1_not_rl).
qed.

lemma MI_after_adv_to_env (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_adv_to_env MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

lemma MI_after_adv_error (Func <: FUNC{MI}) (Adv <: FUNC{Func, MI}) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv /\ after_adv_error MI.func MI.adv r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

end MakeInterface.

(* dummy adversary (DA) - completely controlled by environment *)

abstract theory DummyAdversary.

(* message from port ([], 0) of environment to port (dfe_da, 0) of
   dummy adversary, instructing dummy adversary to send message (Adv,
   dfe_pt, (dfe_da, dfe_n), dfe_u); MI will reject the message if
   dfe_n is 0 (unless dfe_pt is ([], 0)), or if the address of dfe_pt
   is >= dfe_da, or if dfe_pt is ([], 0) (unless dfe_n is 0) *)

type da_from_env =
  {dfe_da : addr;   (* address of dummy adversary *)
   (* data: *)
   dfe_pt : port;   (* destination port of message to be sent by DA *)
   dfe_n  : int;    (* source port index of message to be sent by DA *)
   dfe_u  : univ}.  (* value of message to be sent by DA *)

op da_from_env (x : da_from_env) : msg =
     (Adv, (x.`dfe_da, 0), ([], 0),
      EPDP_Univ_PortIntUniv.enc (x.`dfe_pt, x.`dfe_n, x.`dfe_u)).

op nosmt dec_da_from_env (m : msg) : da_from_env option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> ([], 0) \/
         ! EPDP_Univ_PortIntUniv.valid v) ?
        None :
        let (pt, n, u) = oget (EPDP_Univ_PortIntUniv.dec v)
        in Some {|dfe_da = pt1.`1; dfe_pt = pt; dfe_n = n; dfe_u = u|}.

lemma epdp_da_from_env : epdp da_from_env dec_da_from_env.
proof.
apply epdp_intro.
move => x.
rewrite /da_from_env /dec_da_from_env /= EPDP_Univ_PortIntUniv.valid_enc /=.
by case x.
move => [mod pt1 pt2 u] v.
rewrite /da_from_env /dec_da_from_env /=.
case (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> ([], 0) \/
      ! (EPDP_Univ_PortIntUniv.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 -> val_u.
have [] t : exists (t : port * int * univ), EPDP_Univ_PortIntUniv.dec u = Some t.
  exists (oget (EPDP_Univ_PortIntUniv.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortIntUniv.dec_enc <- /= /#.
qed.

lemma da_from_env_enc_dec (x : da_from_env) :
  dec_da_from_env (da_from_env x) = Some x.
proof.
apply (epdp_enc_dec _ _ _ epdp_da_from_env).
qed.

hint simplify da_from_env_enc_dec.

op nosmt dec_da_from_env_check (m : msg, da : addr) : da_from_env option =
  match dec_da_from_env m with
    None   => None
  | Some x => (x.`dfe_da = da) ? Some x : None
  end.

lemma mode_valid_da_from_env (m : msg) :
  dec2valid dec_da_from_env m => m.`1 = Adv.
proof.
move => val_m.
have [] x : exists (x : da_from_env), dec_da_from_env m = Some x.
  exists (oget (dec_da_from_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_from_env) <- //.
qed.

lemma dest_valid_da_from_env (m : msg) :
  dec2valid dec_da_from_env m =>
  m.`2.`1 = (oget (dec_da_from_env m)).`dfe_da /\ m.`2.`2 = 0.
proof.
move => val_m.
have [] x : exists (x : da_from_env), dec_da_from_env m = Some x.
  exists (oget (dec_da_from_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_from_env) <- //.
qed.

lemma source_valid_da_from_env (m : msg) :
  dec2valid dec_da_from_env m => m.`3 = ([], 0).
proof.
move => val_m.
have [] x : exists (x : da_from_env), dec_da_from_env m = Some x.
  exists (oget (dec_da_from_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_from_env) => <- //.
qed.

(* message from port (dte_da, 0) of dummy adversary to port ([], 0) of
   environment, telling environment that dummy adversary received
   message (Adv, (dte_da, dte_n), dte_pt, dte_u) *)

type da_to_env =
  {dte_da : addr;   (* address of dummy adversary *)
   (* data: *)
   dte_pt : port;   (* source port of message sent to DA *)
   dte_n : int;     (* destination port index of message; the port's
                       address will be dte_da (enforced by MI) *)
   dte_u  : univ}.  (* value of message sent to DA *)

op da_to_env (x : da_to_env) : msg =
     (Adv, ([], 0), (x.`dte_da, 0), 
      EPDP_Univ_PortIntUniv.enc(x.`dte_pt, x.`dte_n, x.`dte_u)).

op nosmt dec_da_to_env (m : msg) : da_to_env option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1 <> ([], 0) \/ pt2.`2 <> 0 \/
         ! EPDP_Univ_PortIntUniv.valid v) ?
        None :
        let (pt, n, u) = oget (EPDP_Univ_PortIntUniv.dec v)
        in Some {|dte_da = pt2.`1; dte_pt = pt; dte_n = n; dte_u = u|}.

lemma epdp_da_to_env : epdp da_to_env dec_da_to_env.
proof.
apply epdp_intro.
move => x.
rewrite /da_to_env /dec_da_to_env /= EPDP_Univ_PortIntUniv.valid_enc /=.
by case x.
move => [mod pt1 pt2 u] v.
rewrite /da_to_env /dec_da_to_env /=.
case (mod = Dir \/ pt1 <> ([], 0) \/ pt2.`2 <> 0 \/
      ! (EPDP_Univ_PortIntUniv.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> -> pt2_2 val_u.
have [] t : exists (t : port * int * univ), EPDP_Univ_PortIntUniv.dec u = Some t.
  exists (oget (EPDP_Univ_PortIntUniv.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortIntUniv.dec_enc <-.
rewrite EPDP_Univ_PortIntUniv.enc_dec oget_some /#.
qed.

lemma mode_valid_da_to_env (m : msg) :
  dec2valid dec_da_to_env m => m.`1 = Adv.
proof.
move => val_m.
have [] x : exists (x : da_to_env), dec_da_to_env m = Some x.
  exists (oget (dec_da_to_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_to_env) <- //.
qed.

lemma dest_valid_da_to_env (m : msg) :
  dec2valid dec_da_to_env m => m.`2 = ([], 0).
proof.
move => val_m.
have [] x : exists (x : da_to_env), dec_da_to_env m = Some x.
  exists (oget (dec_da_to_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_to_env) => <- //.
qed.

lemma source_valid_da_to_env (m : msg) :
  dec2valid dec_da_to_env m =>
  m.`3.`1 = (oget (dec_da_to_env m)).`dte_da /\ m.`3.`2 = 0.
proof.
move => val_m.
have [] x : exists (x : da_to_env), dec_da_to_env m = Some x.
  exists (oget (dec_da_to_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_to_env) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_da_to_env).
qed.

module DummyAdv : FUNC = {
  var self, env : addr

  proc init(self_ env_ : addr) = {
    self <- self_; env <- env_;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;

    match (dec_da_from_env_check m self) with
      Some x => {  (* message from ([], 0) to (self, 0) *)
        if (x.`dfe_n <> 0 /\ x.`dfe_pt.`1 <> [] /\
            !self <= x.`dfe_pt.`1 ) {
          r <- Some (Adv, x.`dfe_pt, (self, x.`dfe_n), x.`dfe_u);
        }
      }
    | None   => {
        (* message from functionality or environment; MI will enforce
           that m.`1 = Adv /\ m.`2.`1 = self /\ ! self <= m.`3.`1

           if m has come from functionality, then MI will have enforced
           that m.`2.`2 <> 0

           if m has come from environment, then m.`2.`2 <> 0 iff
           m.`3 <> ([], 0) *)
        r <-
          Some
          (da_to_env
           {|dte_da = self; dte_pt = m.`3; dte_n = m.`2.`2; dte_u = m.`4|});
      }
    end;
    return r;
  }
}.

end DummyAdversary.


  (* Added by Ram for broadcast*)

type port_list = port list.

op is_in( x : port_list, y : port_list) : bool = 
