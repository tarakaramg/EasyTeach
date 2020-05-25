(* cyclic groups of prime order *)
require import Prime_field.
require import Real.
require import Distr.

type group.
const g:group. (* the generator *)
const id:group.



op ( ** ): group -> group -> group.   (* multiplication of group elements *)
op ( ^ ): group -> gf_q -> group.    (* exponentiation *)
op log:group -> gf_q.                (* discrete logarithm *)

op (//) (a b:group): group = g^(log a - log b).

op inv: group -> group.

axiom group_pow_add: forall (x y:gf_q),
  g ^ x ** g ^ y = g ^ (x + y).

axiom group_pow_mult: forall (x y:gf_q),
  (g ^ x) ^ y = g ^ (x * y).

axiom group_log_pow: forall (a:group),
  g ^ (log a) = a.

axiom group_pow_log: forall (x:gf_q),
  log (g ^ x) = x.

(*axiom inverse_group: forall (x:group),
  (exists (x_inv : group), true),
  x**x_inv = x_inv**x = id.*)

axiom mul_id : forall(x: group),
  x**id = id**x /\ x**id = x.

axiom group_order: exists (q:gf_q),
(g^q) = id. (* fix me -- this doesn't give the order of g *)

(*axiom exp_ele: forall(x:group),
 x = g^r.

*)

theory Dgroup.
op dgroup: group distr.

op dgf_q: gf_q distr.

  axiom supp_def: forall (s:group),
    support dgroup s.

  axiom mu_x_def_in: forall (s:group),
    mu dgroup ((=)s) = 1%r/q%r.

  axiom lossless: weight dgroup = 1%r.

end Dgroup.
