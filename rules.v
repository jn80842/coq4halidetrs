(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv.
Require Import NZAdd NZOrder ZAdd NZBase.
Require Import GenericMinMax ZMaxMin.


(** * Euclidean Division for integers, Euclid convention
    We use here the "usual" formulation of the Euclid Theorem
    [forall a b, b<>0 -> exists r q, a = b*q+r /\ 0 <= r < |b| ]
    The outcome of the modulo function is hence always positive.
    This corresponds to convention "E" in the following paper:
    R. Boute, "The Euclidean definition of the functions div and mod",
    ACM Transactions on Programming Languages and Systems,
    Vol. 14, No.2, pp. 127-144, April 1992.
    See files [ZDivTrunc] and [ZDivFloor] for others conventions.
    We simply extend NZDiv with a bound for modulo that holds
    regardless of the sign of a and b. This new specification
    subsume mod_bound_pos, which nonetheless stays there for
    subtyping. Note also that ZAxiomSig now already contain
    a div and a modulo (that follow the Floor convention).
    We just ignore them here.
*)

Module Type EuclidSpec (Import A : ZAxiomsSig')(Import B : DivMod A).
 Axiom mod_always_pos : forall a b, b ~= 0 -> 0 <= B.modulo a b < abs b.
End EuclidSpec.

Module Type ZEuclid (Z:ZAxiomsSig) := NZDiv.NZDiv Z <+ EuclidSpec Z.

Module ZEuclidProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B)
 (Import D : ZEuclid A).

 (** We put notations in a scope, to avoid warnings about
     redefinitions of notations *)
(* Declare Scope euclid. *)
 Infix "/" := D.div : euclid.
 Infix "mod" := D.modulo : euclid.
 Local Open Scope euclid.

 Module Import Private_NZDiv := Nop <+ NZDivProp A D B.

(** Another formulation of the main equation *)

Lemma mod_eq :
 forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof.
intros.
rewrite <- add_move_l.
symmetry. now apply div_mod.
Qed.

Ltac pos_or_neg a :=
 let LT := fresh "LT" in
 let LE := fresh "LE" in
 destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].

(** Uniqueness theorems *)

Theorem div_mod_unique : forall b q1 q2 r1 r2 : t,
  0<=r1<abs b -> 0<=r2<abs b ->
  b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof.
intros b q1 q2 r1 r2 Hr1 Hr2 EQ.
pos_or_neg b.
rewrite abs_eq in * by trivial.
apply div_mod_unique with b; trivial.
rewrite abs_neq' in * by auto using lt_le_incl.
rewrite eq_sym_iff. apply div_mod_unique with (-b); trivial.
rewrite 2 mul_opp_l.
rewrite add_move_l, sub_opp_r.
rewrite <-add_assoc.
symmetry. rewrite add_move_l, sub_opp_r.
now rewrite (add_comm r2), (add_comm r1).
Qed.

Theorem div_unique:
 forall a b q r, 0<=r<abs b -> a == b*q + r -> q == a/b.
Proof.
intros a b q r Hr EQ.
assert (Hb : b~=0).
 pos_or_neg b.
 rewrite abs_eq in Hr; intuition; order.
 rewrite <- opp_0, eq_opp_r. rewrite abs_neq' in Hr; intuition; order.
destruct (div_mod_unique b q (a/b) r (a mod b)); trivial.
now apply mod_always_pos.
now rewrite <- div_mod.
Qed.

Theorem mod_unique:
 forall a b q r, 0<=r<abs b -> a == b*q + r -> r == a mod b.
Proof.
intros a b q r Hr EQ.
assert (Hb : b~=0).
 pos_or_neg b.
 rewrite abs_eq in Hr; intuition; order.
 rewrite <- opp_0, eq_opp_r. rewrite abs_neq' in Hr; intuition; order.
destruct (div_mod_unique b q (a/b) r (a mod b)); trivial.
now apply mod_always_pos.
now rewrite <- div_mod.
Qed.

(** Sign rules *)

Lemma div_opp_r : forall a b, b~=0 -> a/(-b) == -(a/b).
Proof.
intros. symmetry.
apply div_unique with (a mod b).
rewrite abs_opp; now apply mod_always_pos.
rewrite mul_opp_opp; now apply div_mod.
Qed.

Lemma mod_opp_r : forall a b, b~=0 -> a mod (-b) == a mod b.
Proof.
intros. symmetry.
apply mod_unique with (-(a/b)).
rewrite abs_opp; now apply mod_always_pos.
rewrite mul_opp_opp; now apply div_mod.
Qed.

Lemma div_opp_l_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a)/b == -(a/b).
Proof.
intros a b Hb Hab. symmetry.
apply div_unique with (-(a mod b)).
rewrite Hab, opp_0. split; [order|].
pos_or_neg b; [rewrite abs_eq | rewrite abs_neq']; order.
now rewrite mul_opp_r, <-opp_add_distr, <-div_mod.
Qed.

Lemma div_opp_l_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a)/b == -(a/b)-sgn b.
Proof.
intros a b Hb Hab. symmetry.
apply div_unique with (abs b -(a mod b)).
rewrite lt_sub_lt_add_l.
rewrite <- le_add_le_sub_l. nzsimpl.
rewrite <- (add_0_l (abs b)) at 2.
rewrite <- add_lt_mono_r.
destruct (mod_always_pos a b); intuition order.
rewrite <- 2 add_opp_r, mul_add_distr_l, 2 mul_opp_r.
rewrite sgn_abs.
rewrite add_shuffle2, add_opp_diag_l; nzsimpl.
rewrite <-opp_add_distr, <-div_mod; order.
Qed.

Lemma mod_opp_l_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a) mod b == 0.
Proof.
intros a b Hb Hab. symmetry.
apply mod_unique with (-(a/b)).
split; [order|now rewrite abs_pos].
now rewrite <-opp_0, <-Hab, mul_opp_r, <-opp_add_distr, <-div_mod.
Qed.

Lemma mod_opp_l_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a) mod b == abs b - (a mod b).
Proof.
intros a b Hb Hab. symmetry.
apply mod_unique with (-(a/b)-sgn b).
rewrite lt_sub_lt_add_l.
rewrite <- le_add_le_sub_l. nzsimpl.
rewrite <- (add_0_l (abs b)) at 2.
rewrite <- add_lt_mono_r.
destruct (mod_always_pos a b); intuition order.
rewrite <- 2 add_opp_r, mul_add_distr_l, 2 mul_opp_r.
rewrite sgn_abs.
rewrite add_shuffle2, add_opp_diag_l; nzsimpl.
rewrite <-opp_add_distr, <-div_mod; order.
Qed.

Lemma div_opp_opp_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a)/(-b) == a/b.
Proof.
intros. now rewrite div_opp_r, div_opp_l_z, opp_involutive.
Qed.

Lemma div_opp_opp_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a)/(-b) == a/b + sgn(b).
Proof.
intros. rewrite div_opp_r, div_opp_l_nz by trivial.
now rewrite opp_sub_distr, opp_involutive.
Qed.

Lemma mod_opp_opp_z : forall a b, b~=0 -> a mod b == 0 ->
 (-a) mod (-b) == 0.
Proof.
intros. now rewrite mod_opp_r, mod_opp_l_z.
Qed.

Lemma mod_opp_opp_nz : forall a b, b~=0 -> a mod b ~= 0 ->
 (-a) mod (-b) == abs b - a mod b.
Proof.
intros. now rewrite mod_opp_r, mod_opp_l_nz.
Qed.

(** A division by itself returns 1 *)

Lemma div_same : forall a, a~=0 -> a/a == 1.
Proof.
intros. symmetry. apply div_unique with 0.
split; [order|now rewrite abs_pos].
now nzsimpl.
Qed.

Lemma mod_same : forall a, a~=0 -> a mod a == 0.
Proof.
intros.
rewrite mod_eq, div_same by trivial. nzsimpl. apply sub_diag.
Qed.

(** A division of a small number by a bigger one yields zero. *)

Theorem div_small: forall a b, 0<=a<b -> a/b == 0.
Proof. exact div_small. Qed.

(** Same situation, in term of modulo: *)

Theorem mod_small: forall a b, 0<=a<b -> a mod b == a.
Proof. exact mod_small. Qed.

(** * Basic values of divisions and modulo. *)

Lemma div_0_l: forall a, a~=0 -> 0/a == 0.
Proof.
intros. pos_or_neg a. apply div_0_l; order.
apply opp_inj. rewrite <- div_opp_r, opp_0 by trivial. now apply div_0_l.
Qed.

Lemma mod_0_l: forall a, a~=0 -> 0 mod a == 0.
Proof.
intros; rewrite mod_eq, div_0_l; now nzsimpl.
Qed.

Lemma div_1_r: forall a, a/1 == a.
Proof.
intros. symmetry. apply div_unique with 0.
assert (H:=lt_0_1); rewrite abs_pos; intuition; order.
now nzsimpl.
Qed.

Lemma mod_1_r: forall a, a mod 1 == 0.
Proof.
intros. rewrite mod_eq, div_1_r; nzsimpl; auto using sub_diag.
apply neq_sym, lt_neq; apply lt_0_1.
Qed.

Lemma div_1_l: forall a, 1<a -> 1/a == 0.
Proof. exact div_1_l. Qed.

Lemma mod_1_l: forall a, 1<a -> 1 mod a == 1.
Proof. exact mod_1_l. Qed.

Lemma div_mul : forall a b, b~=0 -> (a*b)/b == a.
Proof.
intros. symmetry. apply div_unique with 0.
split; [order|now rewrite abs_pos].
nzsimpl; apply mul_comm.
Qed.

Lemma mod_mul : forall a b, b~=0 -> (a*b) mod b == 0.
Proof.
intros. rewrite mod_eq, div_mul by trivial. rewrite mul_comm; apply sub_diag.
Qed.

Theorem div_unique_exact a b q: b~=0 -> a == b*q -> q == a/b.
Proof.
 intros Hb H. rewrite H, mul_comm. symmetry. now apply div_mul.
Qed.

(** * Order results about mod and div *)

(** A modulo cannot grow beyond its starting point. *)

Theorem mod_le: forall a b, 0<=a -> b~=0 -> a mod b <= a.
Proof.
intros. pos_or_neg b. apply mod_le; order.
rewrite <- mod_opp_r by trivial. apply mod_le; order.
Qed.

Theorem div_pos : forall a b, 0<=a -> 0<b -> 0<= a/b.
Proof. exact div_pos. Qed.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof. exact div_str_pos. Qed.

Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> 0<=a<abs b).
Proof.
intros a b Hb.
split.
intros EQ.
rewrite (div_mod a b Hb), EQ; nzsimpl.
now apply mod_always_pos.
intros. pos_or_neg b.
apply div_small.
now rewrite <- (abs_eq b).
apply opp_inj; rewrite opp_0, <- div_opp_r by trivial.
apply div_small.
rewrite <- (abs_neq' b) by order. trivial.
Qed.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> 0<=a<abs b).
Proof.
intros.
rewrite <- div_small_iff, mod_eq by trivial.
rewrite sub_move_r, <- (add_0_r a) at 1. rewrite add_cancel_l.
rewrite eq_sym_iff, eq_mul_0. tauto.
Qed.

(** As soon as the divisor is strictly greater than 1,
    the division is strictly decreasing. *)

Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. exact div_lt. Qed.

(** [le] is compatible with a positive division. *)

Lemma div_le_mono : forall a b c, 0<c -> a<=b -> a/c <= b/c.
Proof.
intros a b c Hc Hab.
rewrite lt_eq_cases in Hab. destruct Hab as [LT|EQ];
 [|rewrite EQ; order].
rewrite <- lt_succ_r.
rewrite (mul_lt_mono_pos_l c) by order.
nzsimpl.
rewrite (add_lt_mono_r _ _ (a mod c)).
rewrite <- div_mod by order.
apply lt_le_trans with b; trivial.
rewrite (div_mod b c) at 1 by order.
rewrite <- add_assoc, <- add_le_mono_l.
apply le_trans with (c+0).
nzsimpl; destruct (mod_always_pos b c); try order.
rewrite abs_eq in *; order.
rewrite <- add_le_mono_l. destruct (mod_always_pos a c); order.
Qed.

(** In this convention, [div] performs Rounding-Toward-Bottom
    when divisor is positive, and Rounding-Toward-Top otherwise.
    Since we cannot speak of rational values here, we express this
    fact by multiplying back by [b], and this leads to a nice
    unique statement.
*)

Lemma mul_div_le : forall a b, b~=0 -> b*(a/b) <= a.
Proof.
intros.
rewrite (div_mod a b) at 2; trivial.
rewrite <- (add_0_r (b*(a/b))) at 1.
rewrite <- add_le_mono_l.
now destruct (mod_always_pos a b).
Qed.

(** Giving a reversed bound is slightly more complex *)

Lemma mul_succ_div_gt: forall a b, 0<b -> a < b*(S (a/b)).
Proof.
intros.
nzsimpl.
rewrite (div_mod a b) at 1; try order.
rewrite <- add_lt_mono_l.
destruct (mod_always_pos a b). order.
rewrite abs_eq in *; order.
Qed.

Lemma mul_pred_div_gt: forall a b, b<0 -> a < b*(P (a/b)).
Proof.
intros a b Hb.
rewrite mul_pred_r, <- add_opp_r.
rewrite (div_mod a b) at 1; try order.
rewrite <- add_lt_mono_l.
destruct (mod_always_pos a b). order.
rewrite <- opp_pos_neg in Hb. rewrite abs_neq' in *; order.
Qed.

(** NB: The three previous properties could be used as
    specifications for [div]. *)

(** Inequality [mul_div_le] is exact iff the modulo is zero. *)

Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof.
intros.
rewrite (div_mod a b) at 1; try order.
rewrite <- (add_0_r (b*(a/b))) at 2.
apply add_cancel_l.
Qed.

(** Some additional inequalities about div. *)

Theorem div_lt_upper_bound:
  forall a b q, 0<b -> a < b*q -> a/b < q.
Proof.
intros.
rewrite (mul_lt_mono_pos_l b) by trivial.
apply le_lt_trans with a; trivial.
apply mul_div_le; order.
Qed.

Theorem div_le_upper_bound:
  forall a b q, 0<b -> a <= b*q -> a/b <= q.
Proof.
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; trivial. now rewrite mul_comm.
Qed.

Theorem div_le_lower_bound:
  forall a b q, 0<b -> b*q <= a -> q <= a/b.
Proof.
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; trivial. now rewrite mul_comm.
Qed.

(** A division respects opposite monotonicity for the divisor *)

Lemma div_le_compat_l: forall p q r, 0<=p -> 0<q<=r -> p/r <= p/q.
Proof. exact div_le_compat_l. Qed.

(** * Relations between usual operations and mod and div *)

Lemma mod_add : forall a b c, c~=0 ->
 (a + b * c) mod c == a mod c.
Proof.
intros.
symmetry.
apply mod_unique with (a/c+b); trivial.
now apply mod_always_pos.
rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
now rewrite mul_comm.
Qed.

Lemma div_add : forall a b c, c~=0 ->
 (a + b * c) / c == a / c + b.
Proof.
intros.
apply (mul_cancel_l _ _ c); try order.
apply (add_cancel_r _ _ ((a+b*c) mod c)).
rewrite <- div_mod, mod_add by order.
rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
now rewrite mul_comm.
Qed.

Lemma div_add_l: forall a b c, b~=0 ->
 (a * b + c) / b == a + c / b.
Proof.
 intros a b c. rewrite (add_comm _ c), (add_comm a).
 now apply div_add.
Qed.

(** Cancellations. *)

(** With the current convention, the following isn't always true
    when [c<0]: [-3*-1 / -2*-1 = 3/2 = 1] while [-3/-2 = 2] *)

Lemma div_mul_cancel_r : forall a b c, b~=0 -> 0<c ->
 (a*c)/(b*c) == a/b.
Proof.
intros.
symmetry.
apply div_unique with ((a mod b)*c).
(* ineqs *)
rewrite abs_mul, (abs_eq c) by order.
rewrite <-(mul_0_l c), <-mul_lt_mono_pos_r, <-mul_le_mono_pos_r by trivial.
now apply mod_always_pos.
(* equation *)
rewrite (div_mod a b) at 1 by order.
rewrite mul_add_distr_r.
rewrite add_cancel_r.
rewrite <- 2 mul_assoc. now rewrite (mul_comm c).
Qed.

Lemma div_mul_cancel_l : forall a b c, b~=0 -> 0<c ->
 (c*a)/(c*b) == a/b.
Proof.
intros. rewrite !(mul_comm c); now apply div_mul_cancel_r.
Qed.

Lemma mul_mod_distr_l: forall a b c, b~=0 -> 0<c ->
  (c*a) mod (c*b) == c * (a mod b).
Proof.
intros.
rewrite <- (add_cancel_l _ _ ((c*b)* ((c*a)/(c*b)))).
rewrite <- div_mod.
rewrite div_mul_cancel_l by trivial.
rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
apply div_mod; order.
rewrite <- neq_mul_0; intuition; order.
Qed.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> 0<c ->
  (a*c) mod (b*c) == (a mod b) * c.
Proof.
 intros. rewrite !(mul_comm _ c); now rewrite mul_mod_distr_l.
Qed.


(** Operations modulo. *)

Theorem mod_mod: forall a n, n~=0 ->
 (a mod n) mod n == a mod n.
Proof.
intros. rewrite mod_small_iff by trivial.
now apply mod_always_pos.
Qed.

Lemma mul_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)*b) mod n == (a*b) mod n.
Proof.
 intros a b n Hn. symmetry.
 rewrite (div_mod a n) at 1 by order.
 rewrite add_comm, (mul_comm n), (mul_comm _ b).
 rewrite mul_add_distr_l, mul_assoc.
 rewrite mod_add by trivial.
 now rewrite mul_comm.
Qed.

Lemma mul_mod_idemp_r : forall a b n, n~=0 ->
 (a*(b mod n)) mod n == (a*b) mod n.
Proof.
 intros. rewrite !(mul_comm a). now apply mul_mod_idemp_l.
Qed.

Theorem mul_mod: forall a b n, n~=0 ->
 (a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof.
 intros. now rewrite mul_mod_idemp_l, mul_mod_idemp_r.
Qed.

Lemma add_mod_idemp_l : forall a b n, n~=0 ->
 ((a mod n)+b) mod n == (a+b) mod n.
Proof.
 intros a b n Hn. symmetry.
 rewrite (div_mod a n) at 1 by order.
 rewrite <- add_assoc, add_comm, mul_comm.
 now rewrite mod_add.
Qed.

Lemma add_mod_idemp_r : forall a b n, n~=0 ->
 (a+(b mod n)) mod n == (a+b) mod n.
Proof.
 intros. rewrite !(add_comm a). now apply add_mod_idemp_l.
Qed.

Theorem add_mod: forall a b n, n~=0 ->
 (a+b) mod n == (a mod n + b mod n) mod n.
Proof.
 intros. now rewrite add_mod_idemp_l, add_mod_idemp_r.
Qed.

(** With the current convention, the following result isn't always
    true with a negative intermediate divisor. For instance
    [ 3/(-2)/(-2) = 1 <> 0 = 3 / (-2*-2) ] and
    [ 3/(-2)/2 = -1 <> 0 = 3 / (-2*2) ]. *)

Lemma div_div : forall a b c, 0<b -> c~=0 ->
 (a/b)/c == a/(b*c).
Proof.
 intros a b c Hb Hc.
 apply div_unique with (b*((a/b) mod c) + a mod b).
 (* begin 0<= ... <abs(b*c) *)
 rewrite abs_mul.
 destruct (mod_always_pos (a/b) c), (mod_always_pos a b); try order.
 split.
 apply add_nonneg_nonneg; trivial.
 apply mul_nonneg_nonneg; order.
 apply lt_le_trans with (b*((a/b) mod c) + abs b).
 now rewrite <- add_lt_mono_l.
 rewrite (abs_eq b) by order.
 now rewrite <- mul_succ_r, <- mul_le_mono_pos_l, le_succ_l.
 (* end 0<= ... < abs(b*c) *)
 rewrite (div_mod a b) at 1 by order.
 rewrite add_assoc, add_cancel_r.
 rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
 apply div_mod; order.
Qed.

(** Similarly, the following result doesn't always hold when [b<0].
    For instance [3 mod (-2*-2)) = 3] while
    [3 mod (-2) + (-2)*((3/-2) mod -2) = -1]. *)

Lemma mod_mul_r : forall a b c, 0<b -> c~=0 ->
 a mod (b*c) == a mod b + b*((a/b) mod c).
Proof.
 intros a b c Hb Hc.
 apply add_cancel_l with (b*c*(a/(b*c))).
 rewrite <- div_mod by (apply neq_mul_0; split; order).
 rewrite <- div_div by trivial.
 rewrite add_assoc, add_shuffle0, <- mul_assoc, <- mul_add_distr_l.
 rewrite <- div_mod by order.
 apply div_mod; order.
Qed.

Lemma mod_div: forall a b, b~=0 ->
 a mod b / b == 0.
Proof.
 intros a b Hb.
 rewrite div_small_iff by assumption.
 auto using mod_always_pos.
Qed.

(** A last inequality: *)

Theorem div_mul_le:
 forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof. exact div_mul_le. Qed.

(** mod is related to divisibility *)

Lemma mod_divides : forall a b, b~=0 ->
 (a mod b == 0 <-> (b|a)).
Proof.
intros a b Hb. split.
intros Hab. exists (a/b). rewrite mul_comm.
 rewrite (div_mod a b Hb) at 1. rewrite Hab; now nzsimpl.
intros (c,Hc). rewrite Hc. now apply mod_mul.
Qed.

(********* Lemmas from GenericMinMax that I can't import for some reason? ******)
Lemma max_comm : forall n m, (max n m) == (max m n).
Proof.
Admitted.

Lemma min_comm n m : min n m == min m n.
Proof.
Admitted.

Lemma max_le_iff n m p : p <= max n m <-> p <= n \/ p <= m.
Proof.
Admitted.

Lemma min_le n m p : min n m <= p -> n <= p \/ m <= p.
Proof.
Admitted.

Lemma min_le_iff n m p : min n m <= p <-> n <= p \/ m <= p.
Proof.
Admitted.

(********* Helpful lemmas ************)

Lemma lt_neq_ooo : forall n m, n < m -> m ~= n.
Proof.
  intros.
  cut (n ~= m).
  apply neq_sym.
  apply lt_neq.
  assumption.
Qed.

(********* PROOFS OF REWRITE RULES ***********)

(********* Z3 RETURNS UNKNOWN **********)

(********* SIMPLIFY_ADD ************)

(* ;; Before: (((_0 + c0) / c1) + c2) After : ((_0 + fold((c0 + (c1 * c2)))) / c1);; Pred  : 1 *)
(* rewrite((x + c0)/c1 + c2, (x + fold(c0 + c1*c2))/c1) *)
Lemma addline109 : forall x c0 c1 c2, c1 ~= 0 -> (x + c0) / c1 + c2 == (x + (c0 + c1 * c2)) / c1.
Proof.
  intros.
  rewrite <- div_add with (a := (x + c0)).
  rewrite add_assoc.
  rewrite mul_comm.
  reflexivity.
  assumption.
Qed.

(* ;; Before: ((_0 + ((_1 + c0) / c1)) + c2) After : (_0 + ((_1 + fold((c0 + (c1 * c2)))) / c1));; Pred  : 1 *)
(* rewrite((x + (y + c0)/c1) + c2, x + (y + fold(c0 + c1*c2))/c1) *)
Lemma addline110 : forall x y c0 c1 c2, c1 ~= 0 -> x + (y + c0) / c1 + c2 == x + (y + (c0 + c1 * c2)) / c1.
Proof.
  intros.
  rewrite <- add_assoc.
  rewrite addline109.
  reflexivity.
  assumption.
Qed.

(* ;; Before: ((((_1 + c0) / c1) + _0) + c2) After : (_0 + ((_1 + fold((c0 + (c1 * c2)))) / c1));; Pred  : 1 *)
(* rewrite(((y + c0)/c1 + x) + c2, x + (y + fold(c0 + c1*c2))/c1) *)
Lemma addline111 : forall x y c0 c1 c2, c1 ~= 0 -> (y + c0) / c1 + x + c2 == x + (y + c0 + c1 * c2) / c1.
Proof.
  intros.
  rewrite add_comm with (m := x).
  rewrite <- add_assoc with (n := y).
  apply addline110.
  assumption.
Qed.

(* ;; Before: (((c0 - _0) / c1) + c2) After : ((fold((c0 + (c1 * c2))) - _0) / c1);; Pred  : ((c0 != 0) && (c1 != 0)) *)
(* rewrite((c0 - x)/c1 + c2, (fold(c0 + c1*c2) - x)/c1, c0 != 0 && c1 != 0) *)
Lemma addline112 : forall x c0 c1 c2, c0 ~= 0 -> c1 ~= 0 -> (c0 - x) / c1 + c2 == ((c0 + c1 * c2) - x) / c1.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite addline109.
  rewrite add_comm with (n := - x).
  rewrite add_assoc.
  rewrite add_opp_r.
  reflexivity.
  assumption.
Qed.

(* ;; Before: (_0 + ((_0 + _1) / c0)) After : (((fold((c0 + 1)) * _0) + _1) / c0);; Pred  : 1 *)
(* rewrite(x + (x + y)/c0, (fold(c0 + 1)*x + y)/c0) *)
Lemma addline113 : forall x y c0, c0 ~= 0 -> x + (x + y) / c0 == ((c0 + 1) * x + y) / c0.
Proof.
  intros.
  rewrite <- div_add_l with (a := x) (b := c0).
  rewrite add_assoc.
  rewrite <- mul_1_r with (n := x) at 2.
  rewrite mul_comm.
  rewrite mul_comm with (n := x) (m := 1).
  rewrite <- mul_add_distr_r.
  reflexivity.
  assumption.
Qed.

(* ;; Before: (_0 + ((_1 + _0) / c0)) After : (((fold((c0 + 1)) * _0) + _1) / c0);; Pred  : 1 *)
(* rewrite(x + (y + x)/c0, (fold(c0 + 1)*x + y)/c0) *)
Lemma addline114 : forall x y c0, c0 ~= 0 -> x + (y + x) / c0 == ((c0 + 1) * x + y) / c0.
Proof.
  intros.
  rewrite add_comm with (n := y) (m := x).
  apply addline113.
  assumption.
Qed.

(* ;; Before: (_0 + ((_1 - _0) / c0)) After : (((fold((c0 - 1)) * _0) + _1) / c0);; Pred  : 1 *)
(* rewrite(x + (y - x)/c0, (fold(c0 - 1)*x + y)/c0) *)
Lemma addline115 : forall x y c0, c0 ~= 0 -> x + (y - x) / c0 == ((c0 - 1) * x + y) / c0.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- div_add_l with (a := x) (b := c0).
  rewrite add_comm with (n := y) (m := -x).
  rewrite <- mul_1_r with (n := -x).
  rewrite mul_opp_comm.
  rewrite mul_comm.
  rewrite mul_comm with (n := x) (m := -1).
  rewrite add_assoc.
  rewrite <- mul_add_distr_r.
  rewrite add_opp_r.
  reflexivity.
  assumption.
Qed.

(* ;; Before: (_0 + ((_0 - _1) / c0)) After : (((fold((c0 + 1)) * _0) - _1) / c0);; Pred  : 1 *)
(* rewrite(x + (x - y)/c0, (fold(c0 + 1)*x - y)/c0) *)
Lemma addline116 : forall x y c0, c0 ~= 0 -> x + (x - y) / c0 == ((c0 + 1) * x - y)/c0.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite addline113.
  rewrite add_opp_r.
  reflexivity.
  assumption.
Qed.

(* ;; Before: (((_0 - _1) / c0) + _0) After : (((fold((c0 + 1)) * _0) - _1) / c0);; Pred  : 1 *)
(* rewrite((x - y)/c0 + x, (fold(c0 + 1)*x - y)/c0) *)
Lemma addline117 : forall x y c0, c0 ~= 0 -> (x - y) / c0 + x == ((c0 + 1)*x - y) / c0.
Proof.
  intros.
  rewrite add_comm.
  apply addline116.
  assumption.
Qed.

(* ;; Before: (((_1 - _0) / c0) + _0) After : ((_1 + (fold((c0 - 1)) * _0)) / c0);; Pred  : 1 *)
(* rewrite((y - x)/c0 + x, (y + fold(c0 - 1)*x)/c0) *)
Lemma addline118 : forall x y c0, c0 ~= 0 -> (y - x) / c0 + x == (y + (c0 - 1) * x) / c0.
Proof.
  intros.
  rewrite add_comm.
  rewrite addline115.
  rewrite add_comm.
  reflexivity.
  assumption.
Qed.

(* ;; Before: (((_0 + _1) / c0) + _0) After : (((fold((c0 + 1)) * _0) + _1) / c0);; Pred  : 1 *)
(* rewrite((x + y)/c0 + x, (fold(c0 + 1)*x + y)/c0) *)
Lemma addline119 : forall x y c0, c0 ~= 0 -> (x + y) / c0 + x == ((c0 + 1) * x + y) / c0.
Proof.
  intros.
  rewrite add_comm.
  apply addline113.
  assumption.
Qed.

(* ;; Before: (((_1 + _0) / c0) + _0) After : ((_1 + (fold((c0 + 1)) * _0)) / c0);; Pred  : 1 *)
(* rewrite((y + x)/c0 + x, (y + fold(c0 + 1)*x)/c0) *)
Lemma addline120 : forall x y c0, c0 ~= 0 -> (y + x) / c0 + x == (y + (c0 + 1) * x) / c0.
Proof.
  intros.
  rewrite add_comm.
  rewrite addline114.
  rewrite add_comm.
  reflexivity.
  assumption.
Qed.

(********* SIMPLIFY_DIV ************)

(* rewrite((x * c0) / c1, x / fold(c1 / c0),                          c1 % c0 == 0 && c0 > 0 && c1 / c0 != 0) *)
Lemma divline120 : forall x c0 c1, c0 > 0 -> c1/c0 ~= 0 -> c1 mod c0 == 0 -> (x*c0)/c1 == x/(c1/c0).
Proof.
  intros x c0 c1 H0 H1.
  rewrite <- div_exact with (a := c1) (b := c0).
  intros.
  rewrite H at 1.
  rewrite mul_comm.
  rewrite div_mul_cancel_l.
  reflexivity.
  assumption.
  assumption.
  cut (0 ~= c0).
  cut (0 < c0).
  intros.
  apply neq_sym.
  assumption.
  assumption.
  apply lt_neq.
  assumption.
Qed.

(* ;; Before: (((_0 * c0) + _1) / c1) After : ((_1 / c1) + (_0 * fold((c0 / c1))));; Pred  : (((c0 % c1) == 0) && (c1 > 0)) *)
(* rewrite((x * c0 + y) / c1, y / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline124 : forall x y c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (x * c0 + y)/c1 == y/c1 + x*(c0/c1).
Proof.
  intros x y c0 c1 H.
  rewrite add_comm at 1.
  rewrite <- div_exact with (b := c1).
  intro H0.
  rewrite H0 at 1.
  rewrite mul_assoc.
  rewrite mul_comm at 1.
  rewrite mul_assoc.
  rewrite div_add.
  rewrite mul_comm at 1.
  reflexivity.
  apply neq_sym.
  apply lt_neq.
  assumption.
  apply neq_sym.
  apply lt_neq.
  assumption.
Qed.

(* rewrite((x * c0 - y) / c1, (-y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline125 : forall x y c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (x * c0 - y)/c1 == (-y)/c1 + x * (c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  apply divline124.
  assumption.
  assumption.
Qed.

(* ;; Before: ((_1 + (_0 * c0)) / c1) After : ((_1 / c1) + (_0 * fold((c0 / c1))));; Pred  : (((c0 % c1) == 0) && (c1 > 0)) *)
(* rewrite((y + x * c0) / c1, y / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline126 : forall x y c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (y + x * c0)/c1 == y/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite add_comm at 1.
  apply divline124.
  assumption.
  assumption.
Qed.

(* ;; Before: ((_1 - (_0 * c0)) / c1) After : ((_1 / c1) - (_0 * fold((c0 / c1))));; Pred  : (((c0 % c1) == 0) && (c1 > 0)) *)
(* rewrite((y - x * c0) / c1, y / c1 - x * fold(c0 / c1),             c0 % c1 == 0 && c1 > 0) *)
Lemma divline127 : forall x y c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (y - x*c0)/c1 == y/c1 - x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- mul_opp_l.
  rewrite divline126.
  rewrite mul_opp_l.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite(((x * c0 + y) + z) / c1, (y + z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline129 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((x * c0 + y) + z)/c1 == (y + z)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite <- add_assoc.
  apply divline124.
  assumption.
  assumption.
Qed.

(* rewrite(((x * c0 - y) + z) / c1, (z - y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline130 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((x*c0 - y) + z)/c1 == (z - y)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- add_assoc.
  rewrite add_comm with (m := z).
  rewrite add_opp_r.
  apply divline124.
  assumption.
  assumption.
Qed.

(* rewrite(((x * c0 + y) - z) / c1, (y - z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline131 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((x*c0 + y) - z)/c1 == (y - z)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite divline129.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite(((x * c0 - y) - z) / c1, (-y - z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline132 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((x*c0 - y) -z)/c1 == (-y -z)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- add_opp_r.
  rewrite divline129.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite(((y + x * c0) + z) / c1, (y + z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline134 : forall x y z c0 c1, c1 >0 -> c0 mod c1 == 0 -> ((y + x * c0) + z)/c1 == (y + z)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite add_comm with (n := y).
  rewrite <- add_assoc.
  apply divline124.
  assumption.
  assumption.
Qed.

(* rewrite(((y + x * c0) - z) / c1, (y - z) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline135 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((y + x * c0) - z)/c1 == (y - z)/c1 + x * (c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite divline134.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite(((y - x * c0) - z) / c1, (y - z) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline136 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((y - x * c0) - z)/c1 == (y - z)/c1 - x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r with (n := y).
  rewrite <- mul_opp_l.
  rewrite divline135.
  rewrite mul_opp_l.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite(((y - x * c0) + z) / c1, (y + z) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline137 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((y - x*c0) + z)/c1 == (y+z)/c1 - x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r at 1.
  rewrite <- mul_opp_l.
  rewrite divline134.
  rewrite mul_opp_l.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite((z + (x * c0 + y)) / c1, (z + y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline139 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z + (x*c0 + y))/c1 == (z + y)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite add_assoc.
  apply divline134.
  assumption.
  assumption.
Qed.

(* rewrite((z + (x * c0 - y)) / c1, (z - y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline140 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z + (x*c0 - y))/c1 == (z - y)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite add_assoc.
  rewrite add_opp_r.
  apply divline135.
  assumption.
  assumption.
Qed.

(* rewrite((z - (x * c0 - y)) / c1, (z + y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline141 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z - (x*c0 - y))/c1 == (z + y)/c1 - x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite opp_sub_distr.
  rewrite <- mul_opp_l.
  rewrite add_assoc.
  rewrite mul_opp_l.
  rewrite add_opp_r.
  apply divline137.
  assumption.
  assumption.
Qed.

(* rewrite((z - (x * c0 + y)) / c1, (z - y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline142 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z - (x * c0 + y))/c1 == (z - y)/c1 - x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite opp_add_distr.
  rewrite <- mul_opp_l.
  rewrite divline139.
  rewrite add_opp_r.
  rewrite mul_opp_l.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite((z + (y + x * c0)) / c1, (z + y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline144 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z + (y + x*c0))/c1 == (z + y)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite add_comm with (n := y).
  apply divline139.
  assumption.
  assumption.
Qed.

(* rewrite((z - (y + x * c0)) / c1, (z - y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline145 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z - (y + x * c0))/c1 == (z - y)/c1 - x*(c0/c1).
Proof.
  intros.
  rewrite add_comm with (n := y).
  apply divline142.
  assumption.
  assumption.
Qed.

(* rewrite((z + (y - x * c0)) / c1, (z + y) / c1 - x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline146 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z + (y - x*c0))/c1 == (z + y)/c1 - x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- mul_opp_l.
  rewrite add_comm with (n := y).
  rewrite divline139.
  rewrite mul_opp_l.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite((z - (y - x * c0)) / c1, (z - y) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline147 : forall x y z c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z - (y - x*c0))/c1 == (z - y)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- add_opp_r.
  rewrite <- mul_opp_l.
  rewrite opp_add_distr.
  rewrite add_comm with (n := -y).
  rewrite <- mul_opp_l.
  rewrite opp_involutive.
  rewrite divline139.
  rewrite add_opp_r.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite((((x * c0 + y) + z) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline150 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (x * c0 + y + z + w)/c1 == (y + z + w)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite <- add_assoc.
  rewrite <- add_assoc.
  rewrite add_assoc with (n := y).
  apply divline124.
  assumption.
  assumption.
Qed.

(* rewrite((((y + x * c0) + z) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline151 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (((y + x * c0) + z) + w)/c1 == (y + z + w)/c1 + x*(c0/c1).
Proof.
  intros.
  rewrite add_comm with (n := y).
  apply divline150.
  assumption.
  assumption.
Qed.

(* rewrite(((z + (x * c0 + y)) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline152 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (z + (x * c0 + y) + w)/c1 == (y + z + w)/c1 + x *(c0/c1).
Proof.
  intros.
  rewrite add_comm with (n := z).
  apply divline150.
  assumption.
  assumption.
Qed.

(* rewrite(((z + (y + x * c0)) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline153 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((z + (y + x * c0)) + w) / c1 == (y + z + w) / c1 + x * (c0 / c1).
Proof.
  intros.
  rewrite add_comm with (n := y).
  apply divline152.
  assumption.
  assumption.
Qed.

(* rewrite(((z + (y + x * c0)) + w) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline154 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> ((z + (y + x * c0)) + w) / c1 == (y + z + w) / c1 + x * (c0 / c1).
Proof.
  intros.
  rewrite add_comm with (n := y).
  rewrite add_comm with (n := z).
  apply divline150.
  assumption.
  assumption.
Qed.

(* rewrite((w + ((y + x * c0) + z)) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline155 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (w + ((y + x * c0) + z)) / c1 == (y + z + w) / c1 + x * (c0 / c1).
Proof.
  intros.
  rewrite add_comm.
  rewrite add_comm with (n := y).
  apply divline150.
  assumption.
  assumption.
Qed.

(* rewrite((w + (z + (x * c0 + y))) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline156 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (w + (z + (x * c0 + y))) / c1 == (y + z + w) / c1 + x * (c0 / c1).
Proof.
  intros.
  rewrite add_comm with (n := z).
  rewrite add_comm.
  apply divline150.
  assumption.
  assumption.
Qed.

(* rewrite((w + (z + (y + x * c0))) / c1, (y + z + w) / c1 + x * fold(c0 / c1), c0 % c1 == 0 && c1 > 0) *)
Lemma divline157 : forall x y z w c0 c1, c1 > 0 -> c0 mod c1 == 0 -> (w + (z + (y + x * c0))) / c1 == (y + z + w) / c1 + x * (c0 / c1).
Proof.
  intros.
  rewrite add_comm with (n := y).
  rewrite add_comm with (n := z).
  rewrite add_comm with (n := w).
  apply divline150.
  assumption.
  assumption.
Qed.

(* rewrite((x + c0) / c1, x / c1 + fold(c0 / c1), c0 % c1 == 0) *)
Lemma divline159 : forall x c0 c1, c1 ~= 0 -> c0 mod c1 == 0 -> (x + c0)/c1 == x/c1 + c0/c1.
Proof.
  intros x c0 c1 H.
  rewrite <- div_exact with (b := c1).
  intro H0.
  rewrite H0 at 1.
  rewrite mul_comm at 1.
  rewrite div_add.
  reflexivity.
  assumption.
  assumption.
Qed.

(* rewrite((x + y)/x, y/x + 1) *)
Lemma divline160 : forall x y, x ~= 0 -> (x + y)/x == (y/x + 1).
Proof.
  intros.
  rewrite <- mul_1_l with (n := x) at 1.
  rewrite div_add_l.
  rewrite add_comm at 1.
  reflexivity.
  assumption.
Qed.

(* rewrite((y + x)/x, y/x + 1) *)
Lemma divline1161 : forall x y, x ~=  0 -> (y + x)/x == (y/x + 1).
Proof.
  intros.
  rewrite add_comm at 1.
  apply divline160.
  assumption.
Qed.

(* rewrite((x - y)/x, (-y)/x + 1) *)
Lemma divline162 : forall x y, x ~= 0 -> (x - y)/x == ((-y)/x + 1).
Proof.
  intros.
  rewrite <- add_opp_r.
  apply divline160.
  assumption.
Qed.

(* rewrite((y - x)/x, y/x - 1) *)
Lemma divline163 : forall x y, x ~= 0 -> (y - x)/x == y/x - 1.
Proof.
  intros.
  rewrite <- mul_1_l with (n := x) at 1.
  rewrite <- add_opp_r.
  rewrite <- mul_opp_l.
  rewrite div_add.
  rewrite add_opp_r.
  reflexivity.
  assumption.
Qed.

(* rewrite(((x + y) + z)/x, (y + z)/x + 1) *)
Lemma divline164 : forall x y z, x ~= 0 -> (x + y + z)/x == (y + z)/x + 1.
Proof.
  intros.
  rewrite <- mul_1_l with (n := x) at 1.
  rewrite <- add_assoc.
  rewrite div_add_l.
  rewrite add_comm at 1.
  reflexivity.
  assumption.
Qed.

(* rewrite(((y + x) + z)/x, (y + z)/x + 1) *)
Lemma divline165 : forall x y z, x ~= 0 -> ((y + x) + z)/x == (y + z)/x + 1.
Proof.
  intros.
  rewrite <- add_assoc.
  rewrite add_comm with (n := x).
  rewrite add_assoc.
  rewrite <- mul_1_l with (n := x) at 1.
  rewrite div_add.
  reflexivity.
  assumption.
Qed.

(* rewrite((z + (y + x))/x, (z + y)/x + 1) *)
Lemma divline167 : forall x y z, x ~= 0 -> (z + (y + x))/ x == (z + y)/x + 1.
Proof.
  intros.
  rewrite add_comm.
  rewrite add_comm with (n := z).
  apply divline165.
  assumption.
Qed.

(* rewrite((x*y + z)/x, y + z/x) *)
Lemma divline170 : forall x y z, x ~= 0 -> (x * y + z)/x == (y + z/x).
Proof.
  intros.
  rewrite mul_comm at 1.
  rewrite div_add_l.
  reflexivity.
  assumption.
Qed.

(* rewrite((y*x + z)/x, y + z/x) *)
Lemma divline171 : forall x y z, x ~= 0 -> (y * x + z)/x == (y + z/x).
Proof.
  intros.
  rewrite mul_comm at 1.
  apply divline170.
  assumption.
Qed.

(* ;; Before: ((_2 + (_0 * _1)) / _0) After : ((_2 / _0) + _1);; Pred  : 1 *)
(* rewrite((z + x*y)/x, z/x + y) *)
Lemma divline172 : forall x y z, x ~= 0 -> (z + x * y)/x == z/x + y.
Proof.
  intros.
  rewrite add_comm at 1.
  rewrite divline170.
  rewrite add_comm at 1.
  reflexivity.
  assumption.
Qed.

(* ;; Before: ((_2 + (_1 * _0)) / _0) After : ((_2 / _0) + _1);; Pred  : 1 *)
(* rewrite((z + y*x)/x, z/x + y) *)
Lemma divline173 : forall x y z, x ~= 0 -> (z + y*x)/x == z/x + y.
Proof.
  intros.
  rewrite mul_comm.
  apply divline172.
  assumption.
Qed.

(* ;; Before: (((_0 * _1) - _2) / _0) After : (_1 + (-_2 / _0));; Pred  : 1 *)
(* rewrite((x*y - z)/x, y + (-z)/x) *)
Lemma divline174 : forall x y z, x ~= 0 -> (x*y - z)/x == (y + (-z)/x).
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite mul_comm.
  rewrite div_add_l.
  reflexivity.
  assumption.
Qed.

(* rewrite((y*x - z)/x, y + (-z)/x) *)
Lemma divline175 : forall x y z, x ~= 0 -> (y*x - z)/x == y + (-z)/x.
Proof.
  intros.
  rewrite mul_comm.
  apply divline174.
  assumption.
Qed.

(* ;; Before: ((_2 - (_0 * _1)) / _0) After : ((_2 / _0) - _1);; Pred  : 1 *)
(* rewrite((z - x*y)/x, z/x - y) *)
Lemma divline176 : forall x y z, x ~= 0 -> (z - x*y)/x == z/x - y.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- mul_opp_r.
  rewrite mul_comm.
  rewrite div_add.
  rewrite add_opp_r.
  reflexivity.
  assumption.
Qed.

(* rewrite((z - y*x)/x, z/x - y) *)
Lemma divline177 : forall x y z, x ~= 0 -> (z - y*x)/x == (z/x - y).
Proof.
  intros.
  rewrite mul_comm.
  apply divline176.
  assumption.
Qed.


(* ;; Before: (ramp(_0, c0) / broadcast(c1)) After : ramp((_0 / c1), fold((c0 / c1)), 1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite(ramp(x, c0) / broadcast(c1), ramp(x / c1, fold(c0 / c1), lanes), c0 % c1 == 0) *)
Lemma divline180 : forall x c0 c1 lanes, c1 ~= 0 -> c0 mod c1 == 0 -> (x + c0*lanes)/c1 == x/c1 + (c1/c0)*lanes.
Proof.
Admitted.

(* ;; Before: (((_0 * c0) + c1) / c2) After : ((_0 + fold((c1 / c0))) / fold((c2 / c0)));; Pred  : (((c2 > 0) && (c0 > 0)) && ((c2 % c0) == 0)) *)
(* rewrite((x * c0 + c1) / c2, (x + fold(c1 / c0)) / fold(c2 / c0), c2 > 0 && c0 > 0 && c2 % c0 == 0) *)
Lemma divline187 : forall x c0 c1 c2, c2 > 0 -> c0 > 0 -> c2 mod c0 == 0 -> (x * c0 + c1)/c2 == (x + (c1/c0))/(c2/c0).
Proof.
Admitted.

Lemma divline187alt : forall x c0 c1 c2, c2/c0 ~= 0 -> c2 > 0 -> c0 > 0 -> c2 mod c0 == 0 -> c1 mod c0 == 0 -> 
(x * c0 + c1)/c2 == (x + (c1/c0))/(c2/c0).
Proof.
  intros x c0 c1 c2 H0 H2 H3 H4.
  rewrite <- div_exact with (a := c1).
  intros H5.
  cut (c2 mod c0 == 0).
  rewrite <- div_exact with (a := c2).
  intros H6.
  rewrite H5 at 1.
  rewrite H6 at 1.
  rewrite mul_comm.
  rewrite <- mul_add_distr_l.
  rewrite div_mul_cancel_l.
  reflexivity.
  assumption.
  assumption.
  apply lt_neq_ooo.
  assumption.
  assumption.
  apply lt_neq_ooo.
  assumption.
Qed.

Lemma divline187alt2 : forall x c0 c1 c2, c2/c0 ~= 0 -> c2 ~= 0 -> c0 > 0 -> c2 mod c0 == 0 -> c1 mod c0 == 0 ->
(x * c0 + c1)/c2 == (x + (c1/c0))/(c2/c0).
Proof.
  intros x c0 c1 c2 H0 H1 H2 H3.
  rewrite <- div_exact with (a := c1).
  intros H4.
  cut (c2 mod c0 == 0).
  rewrite <- div_exact with (a := c2).
  intros H5.
  rewrite H4 at 1.
  rewrite H5 at 1.
  rewrite mul_comm.
  rewrite <- mul_add_distr_l.
  rewrite div_mul_cancel_l.
  reflexivity.
  assumption.
  assumption.
  apply lt_neq_ooo.
  assumption.
  assumption.
  apply lt_neq_ooo.
  assumption.
Qed.

(* rewrite((x * c0 + c1) / c2, x * fold(c0 / c2) + fold(c1 / c2), c2 > 0 && c0 % c2 == 0) *)
Lemma divline190 : forall x c0 c1 c2, c2 > 0 -> c0 mod c2 == 0 -> (x * c0 + c1)/c2 == x*(c0/c2) + c1/c2.
Proof.
  intros x c0 c1 c2 H.
  rewrite <- div_exact with (b := c2).
  intro H0.
  rewrite H0 at 1.
  rewrite mul_comm with (n := c2).
  rewrite mul_assoc.
  rewrite div_add_l.
  reflexivity.
  apply neq_sym.
  apply lt_neq.
  assumption.
  apply neq_sym.
  apply lt_neq.
  assumption.
Qed.



(********* SIMPLIFY_LT ************)

(* ;; Before: ((_0 * c0) < c1) After : (_0 < fold((((c1 + c0) - 1) / c0)));; Pred  : (c0 > 0) *)
(* rewrite(x * c0 < c1, x < fold((c1 + c0 - 1) / c0), c0 > 0) *)
Lemma ltline140 : forall x c0 c1, c0 > 0 -> (x * c0) < c1 -> x < (c1 + c0 - 1)/c0.
Proof.
Admitted.
(* proved true in z3 *)

(* ;; Before: (c1 < (_0 * c0)) After : (fold((c1 / c0)) < _0);; Pred  : (c0 > 0) *)
(* rewrite(c1 < x * c0, fold(c1 / c0) < x, c0 > 0) *)
Lemma ltline142 : forall x c0 c1, c0 > 0 -> c1 < (x * c0) -> (c1 / c0) < x.
Proof.
 intros x c0 c1 H.
  rewrite mul_lt_mono_pos_l with (n := c1/c0) (m := x) (p := c0).
  cut (c0 * (c1/c0) <= c1).
  rewrite mul_comm with (n := x) (m := c0).
  apply le_lt_trans.
  apply mul_div_le.
  apply lt_neq_ooo.
  assumption.
  assumption.
Qed.

(* ;; Before: ((_0 / c0) < c1) After : (_0 < (c1 * c0));; Pred  : (c0 > 0) *)
(* rewrite(x / c0 < c1, x < c1 * c0, c0 > 0) *)
Lemma ltline145 : forall x c0 c1, c0 > 0 -> (x/c0) < c1 -> x < c1*c0.
Proof.
(*  intros.
  constructor.
  Focus 2.
  rewrite mul_comm.
  apply div_lt_upper_bound.
  assumption. *)
Admitted.

(* ;; Before: ((_0 * c0) < ((_1 * c0) + c1)) After : (_0 < (_1 + fold((((c1 + c0) - 1) / c0))));; Pred  : (c0 > 0) *)
(* rewrite(x * c0 < y * c0 + c1, x < y + fold((c1 + c0 - 1)/c0), c0 > 0) *)
Lemma ltline226 : forall x y c0 c1, c0 > 0 -> x * c0 < y * c0 + c1 -> x < y + ((c1 + c0) - 1)/c0.
Proof.
Admitted.
(* this is true but x < y + c1/c0 is a tighter bound. see c0 = 2, c1 = 1 *)


(* ;; Before: (((_0 * c0) + c1) < (_1 * c0)) After : ((_0 + fold((c1 / c0))) < _1);; Pred  : (c0 > 0) *)
(* rewrite(x * c0 + c1 < y * c0, x + fold(c1/c0) < y, c0 > 0) *)
Lemma ltline227 : forall x y c0 c1, c0 > 0 -> x * c0 + c1 < y * c0 -> x + c1 / c0 < y.
Proof.
  intros x y c0 c1 H0.
  cut (c0 * (c1/c0) <= c1).
  rewrite add_le_mono_l with (p := x*c0).
  intros H1 H2.
  cut (x * c0 + c0 * (c1 / c0) < y * c0).
  Focus 2.
  apply le_lt_trans with (n := x*c0 + c0*(c1/c0)) (m := x*c0 + c1) (p := y * c0).
  assumption.
  assumption.
  rewrite mul_comm with (n := x) (m := c0).
  rewrite <- mul_add_distr_l.
  rewrite mul_comm with (n := y) (m := c0).
  rewrite <- mul_lt_mono_pos_l.
  auto.
  assumption.
  apply mul_div_le.
  apply lt_neq_ooo.
  assumption.
Qed.


(* ;; Before: (((_0 + c1) / c0) < ((_0 + c2) / c0)) After : 0;; Pred  : ((c0 > 0) && (c1 >= c2)) *)
(* rewrite((x + c1)/c0 < (x + c2)/c0, false, c0 > 0 && c1 >= c2) *)
Lemma ltline289 : forall x c0 c1 c2, c0 > 0 -> c1 >= c2 -> ~((x + c1) / c0 < (x + c2) / c0).
Proof.
  intros.
  rewrite nlt_ge.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
Qed.

(* ;; Before: ((_0 / c0) < ((_0 + c2) / c0)) After : 0;; Pred  : ((c0 > 0) && (0 >= c2)) *)
(* rewrite(x/c0 < (x + c2)/c0, false, c0 > 0 && 0 >= c2) *)
Lemma ltline292 : forall x c0 c2, c0 > 0 -> 0 >= c2 -> ~ (x/c0 < (x + c2)/c0).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite <- add_0_r with (n := x) at 2.
  cut (x + c2 <= x + 0).
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < (_0 / c0)) After : 0;; Pred  : ((c0 > 0) && (c1 >= 0)) *)
(* rewrite((x + c1)/c0 < x/c0, false, c0 > 0 && c1 >= 0) *)
Lemma ltline295 : forall x c0 c1, c0 > 0 -> c1 >= 0 -> ~((x + c1) / c0 < x / c0).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite <- add_0_r with (n := x) at 1.
  cut (x + 0 <= x + c1).
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < ((_0 / c0) + c2)) After : 0;; Pred  : ((c0 > 0) && (c1 >= (c2 * c0))) *)
(* rewrite((x + c1)/c0 < x/c0 + c2, false, c0 > 0 && c1 >= c2 * c0) *)
Lemma ltline299 : forall x c0 c1 c2, c0 > 0 -> c1 >= c2 * c0 -> ~((x + c1) / c0 < x / c0 + c2).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite <- div_add.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
  apply lt_neq_ooo.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < (min((_0 / c0), _1) + c2)) After : 0;; Pred  : ((c0 > 0) && (c1 >= (c2 * c0))) *)
(* rewrite((x + c1)/c0 < (min(x/c0, y) + c2), false, c0 > 0 && c1 >= c2 * c0) *)
Lemma ltline303 : forall x y c0 c1 c2, c0 > 0 -> c1 >= (c2 * c0) -> ~((x + c1) / c0 < (min (x / c0) y) + c2).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite le_add_le_sub_r.
  rewrite min_le_iff.
  cut (x / c0 <= (x + c1) / c0 - c2).
  auto.
  rewrite <- le_add_le_sub_r.
  rewrite <- div_add.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
  apply lt_neq_ooo.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < min(((_0 + c2) / c0), _1)) After : 0;; Pred  : ((c0 > 0) && (c1 >= c2)) *)
(* rewrite((x + c1)/c0 < min((x + c2)/c0, y), false, c0 > 0 && c1 >= c2) *)
Lemma ltline305 : forall x y c0 c1 c2, c0 > 0 -> c1 >= c2 -> ~((x + c1) / c0 < (min ((x + c2) / c0) y)).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite min_le_iff.
  cut ((x + c2) / c0 <= (x + c1) / c0).
  auto.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < min((_0 / c0), _1)) After : 0;; Pred  : ((c0 > 0) && (c1 >= 0)) *)
(* rewrite((x + c1)/c0 < min(x/c0, y), false, c0 > 0 && c1 >= 0) *)
Lemma ltline307 : forall x y c0 c1, c0 > 0 -> c1 >= 0 -> ~((x + c1) / c0 < (min (x / c0) y)).
Proof.
  intros.
  rewrite <- le_ngt.
  cut (x/c0 <= (x + c1)/c0).
  intros.
  rewrite min_le_iff.
  auto.
  rewrite <- add_0_r with (n := x) at 1.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < (min(_1, (_0 / c0)) + c2)) After : 0;; Pred  : ((c0 > 0) && (c1 >= (c2 * c0))) *)
(* rewrite((x + c1)/c0 < (min(y, x/c0) + c2), false, c0 > 0 && c1 >= c2 * c0) *)
Lemma ltline310 : forall x y c0 c1 c2, c0 > 0 -> c1 >= c2 * c0 -> ~((x + c1) / c0 < (min y (x / c0)) + c2).
Proof.
  intros.
  rewrite min_comm.
  apply ltline303.
  assumption.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < min(_1, ((_0 + c2) / c0))) After : 0;; Pred  : ((c0 > 0) && (c1 >= c2)) *)
(* rewrite((x + c1)/c0 < min(y, (x + c2)/c0), false, c0 > 0 && c1 >= c2) *)
Lemma ltline312 : forall x y c0 c1 c2, c0 > 0 -> c1 >= c2 -> ~((x + c1) / c0 < (min y ((x + c2)/c0))).
Proof.
  intros.
  rewrite min_comm.
  apply ltline305.
  assumption.
  assumption.
Qed.

(* ;; Before: (((_0 + c1) / c0) < min(_1, (_0 / c0))) After : 0;; Pred  : ((c0 > 0) && (c1 >= 0)) *)
(* rewrite((x + c1)/c0 < min(y, x/c0), false, c0 > 0 && c1 >= 0) *)
Lemma ltline314 : forall x y c0 c1, c0 > 0 -> c1 >= 0 -> ~((x + c1) / c0 < (min y (x / c0))).
Proof.
  intros.
  rewrite min_comm.
  apply ltline307.
  assumption.
  assumption.
Qed.

(* ;; Before: (max(((_0 + c2) / c0), _1) < ((_0 + c1) / c0)) After : 0;; Pred  : ((c0 > 0) && (c2 >= c1)) *)
(* rewrite(max((x + c2)/c0, y) < (x + c1)/c0, false, c0 > 0 && c2 >= c1) *)
Lemma ltline317 : forall x y c0 c1 c2, c0 > 0 -> c2 >= c1 -> ~((max ((x + c2)/c0) y) < (x + c1) / c0).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite max_le_iff.
  cut ((x + c1) / c0 <= (x + c2) / c0).
  auto.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
Qed.

(* ;; Before: (max((_0 / c0), _1) < ((_0 + c1) / c0)) After : 0;; Pred  : ((c0 > 0) && (0 >= c1)) *)
(* rewrite(max(x/c0, y) < (x + c1)/c0, false, c0 > 0 && 0 >= c1) *)
Lemma ltline319 : forall x y c0 c1, c0 > 0 -> 0 >= c1 -> ~((max (x / c0) y) < (x + c1) / c0).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite max_le_iff.
  cut ((x + c1)/c0 <= x/c0).
  auto.
  rewrite <- add_0_r with (n := x) at 2.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
Qed.

(* ;; Before: (max(_1, ((_0 + c2) / c0)) < ((_0 + c1) / c0)) After : 0;; Pred  : ((c0 > 0) && (c2 >= c1)) *)
(* rewrite(max(y, (x + c2)/c0) < (x + c1)/c0, false, c0 > 0 && c2 >= c1) *)
Lemma ltline321 : forall x y c0 c1 c2, c0 > 0 -> c2 >= c1 -> ~((max y ((x + c2)/c0)) < (x + c1) / c0).
Proof.
  intros.
  rewrite max_comm.
  apply ltline317.
  assumption.
  assumption.
Qed.

(* ;; Before: (max(_1, (_0 / c0)) < ((_0 + c1) / c0)) After : 0;; Pred  : ((c0 > 0) && (0 >= c1)) *)
(* rewrite(max(y, x/c0) < (x + c1)/c0, false, c0 > 0 && 0 >= c1) *)
Lemma ltline323 : forall x y c0 c1, c0 > 0 -> 0 >= c1 -> ~((max y (x/c0)) < (x + c1)/c0).
Proof.
  intros.
  rewrite max_comm.
  apply ltline319.
  assumption.
  assumption.
Qed.

(* ;; Before: (max(((_0 + c2) / c0), _1) < ((_0 / c0) + c1)) After : 0;; Pred  : ((c0 > 0) && (c2 >= (c1 * c0))) *)
(* rewrite(max((x + c2)/c0, y) < x/c0 + c1, false, c0 > 0 && c2 >= c1 * c0) *)
Lemma ltline327 : forall x y c0 c1 c2, c0 > 0 -> c2 >= (c1 * c0) -> ~((max ((x + c2) / c0) y) < ((x / c0) + c1)).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite max_le_iff.
  cut (x / c0 + c1 <= (x + c2) / c0).
  auto.
  rewrite <- div_add.
  apply div_le_mono.
  assumption.
  apply add_le_mono_l.
  assumption.
  apply lt_neq_ooo.
  assumption.
Qed.

(* ;; Before: (max(_1, ((_0 + c2) / c0)) < ((_0 / c0) + c1)) After : 0;; Pred  : ((c0 > 0) && (c2 >= (c1 * c0))) *)
(* rewrite(max(y, (x + c2)/c0) < x/c0 + c1, false, c0 > 0 && c2 >= c1 * c0) *)
Lemma ltline329 : forall x y c0 c1 c2, c0 > 0 -> c2 >= c1 * c0 -> ~((max y ((x + c2)/c0)) < x/c0 + c1).
Proof.
  intros.
  rewrite max_comm.
  apply ltline327.
  assumption.
  assumption.
Qed.

(* ;; Before: ((_0 / c0) < min(((_0 + c2) / c0), _1)) After : 0;; Pred  : ((c0 > 0) && (c2 < 0)) *)
(* rewrite(x/c0 < min((x + c2)/c0, y), false, c0 > 0 && c2 < 0) *)
Lemma ltline333 : forall x y c0 c2, c0 > 0 -> c2 < 0 -> ~(x/c0 < (min ((x + c2)/c0) y)).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite <- add_0_r with (n := x) at 2.
  cut ((x + c2) / c0 <= (x + 0)/c0).
  intros.
  rewrite min_le_iff with (n := (x+c2)/c0) (m := y) (p := (x + 0)/c0).
  auto.
  rewrite add_0_r.
  rewrite le_ngt.
  apply ltline292.
  assumption.
  apply lt_le_incl.
  assumption.
Qed.

(* ;; Before: ((_0 / c0) < min(_1, ((_0 + c2) / c0))) After : 0;; Pred  : ((c0 > 0) && (c2 < 0)) *)
(* rewrite(x/c0 < min(y, (x + c2)/c0), false, c0 > 0 && c2 < 0) *)
Lemma ltline335 : forall x y c0 c2, c0 > 0 -> c2 < 0 -> ~(x/c0 < (min y ((x + c2)/c0))).
Proof.
  intros.
  rewrite min_comm.
  apply ltline333.
  assumption.
  assumption.
Qed.

(* ;; Before: (max(((_0 + c2) / c0), _1) < (_0 / c0)) After : 0;; Pred  : ((c0 > 0) && (c2 >= 0)) *)
(* rewrite(max((x + c2)/c0, y) < x/c0, false, c0 > 0 && c2 >= 0) *)
Lemma ltline337 : forall x y c0 c2, c0 > 0 -> c2 >= 0 -> ~((max ((x + c2) / c0) y) < (x / c0)).
Proof.
  intros.
  rewrite <- le_ngt.
  rewrite max_le_iff.
  cut (x/c0 <= (x + c2)/c0).
  intros.
  auto.
  rewrite le_ngt.
  apply ltline295.
  assumption.
  assumption.
Qed.

(* ;; Before: (max(_1, ((_0 + c2) / c0)) < (_0 / c0)) After : 0;; Pred  : ((c0 > 0) && (c2 >= 0)) *)
(* rewrite(max(y, (x + c2)/c0) < x/c0, false, c0 > 0 && c2 >= 0) *)
Lemma ltline339 : forall x y c0 c2, c0 > 0 -> c2 >= 0 -> ~((max y ((x + c2)/c0)) < x/c0).
Proof.
  intros.
  rewrite max_comm.
  apply ltline337.
  assumption.
  assumption.
Qed.

(********* SIMPLIFY_MAX ************)

(* ;; Before: max((_0 / c0), (_1 / c0)) After : (max(_0, _1) / c0);; Pred  : (c0 > 0) *)
(* rewrite(max(x / c0, y / c0), max(x, y) / c0, c0 > 0) *)
Lemma maxline233 : forall x y c0, c0 > 0 -> (max (x/c0) (y/c0)) == (max x y)/c0.
Proof.
  intros.
  cut (y <= x \/ x <= y).
  intros.
  destruct H0.
  rewrite max_l with (x := x) (y := y).
  cut (y/c0 <= x/c0).
  intros.
  rewrite max_l.
  reflexivity.
  assumption.
  apply div_le_mono.
  assumption.
  assumption.
  assumption.
  rewrite max_comm with (n := x) (m := y).
  rewrite max_l with (x := y) (y := x).
  cut (x/c0 <= y/c0).
  intros.
  rewrite max_comm.
  rewrite max_l.
  reflexivity.
  assumption.
  apply div_le_mono.
  assumption.
  assumption.
  assumption.
  apply le_ge_cases.
Qed.

Lemma neg_div_antimonotone : forall a b c, c < 0 -> a <= b -> a/c >= b/c.
Proof.
  intros.
  rewrite <- opp_involutive with (n := c) at 1.
  rewrite div_opp_r.
  rewrite le_ngt.
  rewrite <- opp_involutive with (n := c) at 1.
  rewrite div_opp_r.
  rewrite nlt_ge.
  rewrite <- opp_le_mono.
  apply div_le_mono.
  apply opp_pos_neg.
  assumption.
  assumption.
  apply lt_neq_ooo.
  apply opp_pos_neg.
  assumption.
  apply lt_neq_ooo.
  apply opp_pos_neg.
  assumption.
Qed.


(* ;; Before: max((_0 / c0), (_1 / c0)) After : (min(_0, _1) / c0);; Pred  : (c0 < 0) *)
(* rewrite(max(x / c0, y / c0), min(x, y) / c0, c0 < 0) *)
Lemma maxline234 : forall x y c0, c0 < 0 -> (max (x/c0) (y/c0)) == (min x y)/c0.
Proof.
  intros.
  cut (x <= y \/ y <= x).
  intros.
  destruct H0.
  cut (x/c0 >= y/c0).
  intros.
  rewrite max_l.
  rewrite min_l.
  reflexivity.
  assumption.
  apply neg_div_antimonotone.
  assumption.
  assumption.
  apply neg_div_antimonotone.
  assumption.
  assumption.
  cut (y/c0 >= x/c0).
  intros.
  rewrite max_r.
  rewrite min_r.
  reflexivity.
  assumption.
  assumption.
  apply neg_div_antimonotone.
  assumption.
  assumption.
  apply le_ge_cases.
Qed.

Lemma max_proper : forall x y z, x == y -> (max x z) == (max y z).
Proof.
  intros.
  cut (x <= z \/ x > z).
  intros.
  destruct H0.
  rewrite max_r.
  cut (y <= z).
  intros.
  rewrite max_r.
  reflexivity.
  assumption.
  rewrite <- H.
  assumption.
  assumption.
  (cut (z <= x)).
  intros.
  rewrite max_l.
  (cut (z <= y)).
  intros.
  rewrite max_l.
  assumption.
  assumption.
  rewrite <- H.
  assumption.
  assumption.
  apply lt_le_incl.
  assumption.
  apply le_gt_cases.
Qed.

(* ;; Before: max((_0 / c0), ((_1 / c0) + c1)) After : (max(_0, (_1 + fold((c1 * c0)))) / c0);; Pred  : ((c0 > 0) && !(overflows((c1 * c0)))) *)
(* rewrite(max(x / c0, y / c0 + c1), max(x, y + fold(c1 * c0)) / c0, c0 > 0 && !overflows(c1 * c0)) *)
Lemma maxline241 : forall x y c0 c1, c0 > 0 -> (max (x/c0) ((y/c0) + c1)) == ((max x (y + c1 * c0)) / c0).
Proof.
  intros.
  cut (y/c0 + c1 == (y + c1 * c0)/c0).
  intros.
  cut ((max (x / c0) (y / c0 + c1)) == (max (x/c0) ((y + c1 * c0) / c0) )).
  intros.
  rewrite H1.
  apply maxline233 with (x := x) (y := (y + c1 * c0)) (c0 := c0).
  assumption.
  rewrite max_comm.
  cut ((max (y / c0 + c1) (x / c0)) == (max ((y + c1 * c0)/c0) (x / c0))).
  intros.
  rewrite H1.
  rewrite max_comm.
  reflexivity.
  apply max_proper.
  assumption.
  apply eq_sym.
  apply div_add.
  apply lt_neq_ooo.
  assumption.
Qed.
(* ;; Before: max((_0 / c0), ((_1 / c0) + c1)) After : (min(_0, (_1 + fold((c1 * c0)))) / c0);; Pred  : ((c0 < 0) && !(overflows((c1 * c0)))) *)
(* rewrite(max(x / c0, y / c0 + c1), min(x, y + fold(c1 * c0)) / c0, c0 < 0 && !overflows(c1 * c0)) *)
Lemma maxline242 : forall x y c0 c1, c0 < 0 -> (max (x / c0) (y / c0 + c1)) == (min x (y + c1 * c0)) / c0.
Proof.
  intros.
  cut (y/c0 + c1 == (y + c1 * c0)/c0).
  intros.
  rewrite max_comm.
  cut ((max (y/c0 + c1) (x/c0)) == (max ((y + c1 * c0)/c0) (x/c0))).
  intros.
  rewrite H1.
  rewrite max_comm.
  apply maxline234.
  assumption.
  apply max_proper.
  assumption.
  apply eq_sym.
  apply div_add.
  apply neq_sym.
  apply lt_neq_ooo.
  assumption.
Qed.

(********* SIMPLIFY_MIN ************)

Lemma min_comm : forall n m, (min n m) == (min m n).
Proof.
Admitted.

(* ;; Before: min((_0 / c0), (_1 / c0)) After : (min(_0, _1) / c0);; Pred  : (c0 > 0) *)
(* rewrite(min(x / c0, y / c0), min(x, y) / c0, c0 > 0) *)
Lemma minline236 : forall x y c0, c0 > 0 -> (min (x / c0) (y / c0)) == (min x y) / c0.
Proof.
  intros.
  cut (y <= x \/ x <= y).
  intros.
  destruct H0.
  cut (y/c0 <= x/c0).
  intros.
  rewrite min_r.
  rewrite min_r.
  reflexivity.
  assumption.
  assumption.
  apply div_le_mono.
  assumption.
  assumption.
  cut (x/c0 <= y/c0).
  intros.
  rewrite min_l.
  rewrite min_l.
  reflexivity.
  assumption.
  assumption.
  apply div_le_mono.
  assumption.
  assumption.
  apply le_ge_cases.
Qed.

Lemma min_proper : forall x y z, x == y -> (min x z) == (min y z).
Proof.
  intros.
  cut (x <= z \/ x > z).
  intros.
  destruct H0.
  rewrite min_l.
  cut (y <= z).
  intros.
  rewrite min_l.
  rewrite H.
  reflexivity.
  assumption.
  rewrite <- H.
  assumption.
  assumption.
  cut (z <= x).
  intros.
  rewrite min_r.
  cut (z <= y).
  intros.
  rewrite min_r.
  reflexivity.
  assumption.
  rewrite <- H.
  assumption.
  assumption.
  apply lt_le_incl.
  assumption.
  apply le_gt_cases.
Qed.

(* ;; Before: min((_0 / c0), (_1 / c0)) After : (max(_0, _1) / c0);; Pred  : (c0 < 0) *)
(* rewrite(min(x / c0, y / c0), max(x, y) / c0, c0 < 0) *)
Lemma minline237 : forall x y c0, c0 < 0 -> (min (x / c0) (y / c0)) == (max x y) / c0.
Proof.
  intros.
  cut (x <= y \/ y <= x).
  intros.
  destruct H0.
  cut (x/c0 >= y/c0).
  intros.
  rewrite max_r.
  rewrite min_r.
  reflexivity.
  assumption.
  assumption.
  apply neg_div_antimonotone.
  assumption.
  assumption.
  cut (y/c0 >= x/c0).
  intros.
  rewrite max_l.
  rewrite min_l.
  reflexivity.
  assumption.
  assumption.
  apply neg_div_antimonotone.
  assumption.
  assumption.
  apply le_ge_cases.
Qed.

(* ;; Before: min((_0 / c0), ((_1 / c0) + c1)) After : (min(_0, (_1 + fold((c1 * c0)))) / c0);; Pred  : ((c0 > 0) && !(overflows((c1 * c0)))) *)
(* rewrite(min(x / c0, y / c0 + c1), min(x, y + fold(c1 * c0)) / c0, c0 > 0 && !overflows(c1 * c0)) *)
Lemma minline244 : forall x y c0 c1, c0 > 0 -> (min (x / c0) (y / c0 + c1)) == (min x (y + c1 * c0)) / c0.
Proof.
  intros.
  cut (y/c0 + c1 == (y + c1 * c0)/c0).
  intros.
  cut ((min (x/c0) (y/c0 + c1)) == (min (x/c0) ((y + c1 * c0)/c0))).
  intros.
  rewrite H1.
  apply minline236.
  assumption.
  rewrite min_comm.
  cut ((min (y/c0 + c1) (x/c0)) == (min ((y + c1 * c0) / c0) (x/c0))).
  intros.
  rewrite H1.
  rewrite min_comm.
  reflexivity.
  apply min_proper.
  assumption.
  apply eq_sym.
  apply div_add.
  apply lt_neq_ooo.
  assumption.
Qed.

(* ;; Before: min((_0 / c0), ((_1 / c0) + c1)) After : (max(_0, (_1 + fold((c1 * c0)))) / c0);; Pred  : ((c0 < 0) && !(overflows((c1 * c0)))) *)
(* rewrite(min(x / c0, y / c0 + c1), max(x, y + fold(c1 * c0)) / c0, c0 < 0 && !overflows(c1 * c0)) *)
Lemma minline245 : forall x y c0 c1, c0 < 0 -> (min (x / c0) (y / c0 + c1)) == (max x (y + c1 * c0)) / c0.
Proof.
  intros.
  cut (y/c0 + c1 == (y + c1 * c0)/c0).
  intros.
  rewrite max_comm.
  cut ((min (x/c0) (y/c0 + c1)) == (min ((y + c1 * c0)/c0) (x/c0))).
  intros.
  rewrite H1.
  rewrite max_comm.
  rewrite min_comm.
  apply minline237.
  assumption.
  rewrite min_comm.
  apply min_proper.
  assumption.
  apply eq_sym.
  apply div_add.
  apply neq_sym.
  apply lt_neq_ooo.
  assumption.
Qed.


(********* SIMPLIFY_MOD ************)

(* ;; Before: ((_0 * c0) % c1) After : ((_0 * fold((c0 % c1))) % c1);; Pred  : ((c1 > 0) && ((c0 >= c1) || (c0 < 0))) *)
(* rewrite((x * c0) % c1, (x * fold(c0 % c1)) % c1, c1 > 0 && (c0 >= c1 || c0 < 0)) *)
Lemma modline67 : forall x c0 c1, c1 > 0 -> (c0 >= c1 \/ c0 < 0) -> (x * c0) mod c1 == (x * (c0 mod c1)) mod c1.
Proof.
  intros.
  rewrite <- mul_mod_idemp_r.
  reflexivity.
  apply lt_neq_ooo.
  assumption.
Qed.
(* only required predicate is c1 ~= 0 *)

(* ;; Before: ((_0 + c0) % c1) After : ((_0 + fold((c0 % c1))) % c1);; Pred  : ((c1 > 0) && ((c0 >= c1) || (c0 < 0))) *)
(* rewrite((x + c0) % c1, (x + fold(c0 % c1)) % c1, c1 > 0 && (c0 >= c1 || c0 < 0)) *)
Lemma modline68 : forall x c0 c1, c1 > 0 -> (c0 >= c1 \/ c0 < 0) -> (x + c0) mod c1 == (x + (c0 mod c1)) mod c1.
Proof.
  intros.
  rewrite <- add_mod_idemp_r.
  reflexivity.
  apply lt_neq_ooo.
  assumption.
Qed.

(* ;; Before: ((_0 * c0) % c1) After : ((_0 % fold((c1 / c0))) * c0);; Pred  : ((c0 > 0) && ((c1 % c0) == 0)) *)
(* rewrite((x * c0) % c1, (x % fold(c1/c0)) * c0, c0 > 0 && c1 % c0 == 0) *)
Lemma modline69 : forall x c0 c1, c0 > 0 -> c0 == 0 -> (x * c0) mod c1 == (x mod (c1/c0))*c0.
Proof.
Admitted.

(* ;; Before: (((_0 * c0) + _1) % c1) After : (_1 % c1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite((x * c0 + y) % c1, y % c1, c0 % c1 == 0) *)
Lemma modline70 : forall x y c0 c1, c1 ~= 0 -> c0 mod c1 == 0 -> (x * c0 + y) mod c1 == y mod c1.
Proof.
  intros.
  rewrite <- add_mod_idemp_l.
  rewrite mul_mod.
  rewrite H0.
  rewrite mul_0_r.
  rewrite mod_0_l.
  rewrite add_0_l.
  reflexivity.
  assumption.
  assumption.
  assumption.
Qed.

(* ;; Before: ((_1 + (_0 * c0)) % c1) After : (_1 % c1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite((y + x * c0) % c1, y % c1, c0 % c1 == 0) *)
Lemma modline71 : forall x y c0 c1, c1 ~= 0 -> c0 mod c1 == 0 -> (y + x*c0) mod c1 == y mod c1.
Proof.
  intros.
  rewrite add_comm.
  apply modline70.
  assumption.
  assumption.
Qed.

(* ;; Before: (((_0 * c0) - _1) % c1) After : (-_1 % c1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite((x * c0 - y) % c1, (-y) % c1, c0 % c1 == 0) *)
Lemma modline72 : forall x y c0 c1, c1 ~= 0 -> c0 mod c1 == 0 -> (x*c0 - y) mod c1 == (- y) mod c1.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite modline70.
  reflexivity.
  assumption.
  assumption.
Qed.

(* ;; Before: ((_1 - (_0 * c0)) % c1) After : (_1 % c1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite((y - x * c0) % c1, y % c1, c0 % c1 == 0) *)
Lemma modline73 : forall x y c0 c1, c1 ~= 0 -> c0 mod c1 == 0 -> (y - x*c0) mod c1 == y mod c1.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- mul_opp_l.
  rewrite modline71 with (x := - x).
  reflexivity.
  assumption.
  assumption.
Qed.

(* ;; Before: (ramp(_0, c0) % broadcast(c1)) After : (broadcast(_0, 1) % c1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite(ramp(x, c0) % broadcast(c1), broadcast(x, lanes) % c1, c0 % c1 == 0) *)
Lemma modline76 : forall x c0 c1 lanes, c1 ~= 0 -> c0 mod c1 == 0 -> (x + c0 * lanes) mod c1 == x mod c1.
Proof.
  intros.
  rewrite mul_comm.
  apply modline71.
  assumption.
  assumption.
Qed.

(* ;; Before: (ramp((_0 + c0), c2) % broadcast(c1)) After : (ramp((_0 + fold((c0 % c1))), fold((c2 % c1)), 1) % c1);; Pred  : ((c1 > 0) && ((c0 >= c1) || (c0 < 0))) *)
(* rewrite(ramp(x + c0, c2) % broadcast(c1), (ramp(x + fold(c0 % c1), fold(c2 % c1), lanes) % c1), c1 > 0 && (c0 >= c1 || c0 < 0)) *)
Lemma modline81 : forall x c0 c1 c2 lanes, c1 > 0 -> (c0 >= c1 \/ c0 < 0) -> 
(x + c0 + c2 * lanes) mod c1 == (x + (c0 mod c1) + (c2 mod c1)*lanes) mod c1.
Proof.
  intros.
  rewrite <- add_mod_idemp_l.
  rewrite <- add_mod_idemp_r.
  rewrite <- mul_mod_idemp_l.
  rewrite <- add_mod_idemp_r with (b := c0).
  rewrite add_mod_idemp_r.
  rewrite add_mod_idemp_l.
  reflexivity.
  apply lt_neq_ooo.
  assumption.
  apply lt_neq_ooo.
  assumption.
  apply lt_neq_ooo.
  assumption.
  apply lt_neq_ooo.
  assumption.
  apply lt_neq_ooo.
  assumption.
  apply lt_neq_ooo.
  assumption.
Qed.
(* only predicate needed is c1 ~= 0 *)

(* ;; Before: (ramp(((_0 * c0) + _1), c2) % broadcast(c1)) After : (ramp(_1, fold((c2 % c1)), 1) % c1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite(ramp(x * c0 + y, c2) % broadcast(c1), ramp(y, fold(c2 % c1), lanes) % c1, c0 % c1 == 0) *)
Lemma modline82 : forall x y c0 c1 c2 lanes, c1 ~= 0 -> c0 mod c1 == 0 -> (x*c0 + y + c2 * lanes) mod c1 == (y + (c2 mod c1)*lanes) mod c1.
Proof.
  intros.
  rewrite <- add_mod_idemp_l.
  rewrite modline70.
  rewrite <- add_mod_idemp_r.
  rewrite <- mul_mod_idemp_l.
  rewrite add_mod_idemp_l.
  rewrite add_mod_idemp_r.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.


(* ;; Before: (ramp((_1 + (_0 * c0)), c2) % broadcast(c1)) After : (ramp(_1, fold((c2 % c1)), 1) % c1);; Pred  : ((c0 % c1) == 0) *)
(* rewrite(ramp(y + x * c0, c2) % broadcast(c1), ramp(y, fold(c2 % c1), lanes) % c1, c0 % c1 == 0) *)
Lemma modline83 : forall x y c0 c1 c2 lanes, c1 ~= 0 -> c0 mod c1 == 0 -> (y + x*c0 + c2*lanes) mod c1 == (y + (c2 mod c1)*lanes) mod c1.
Proof.
  intros.
  rewrite add_comm with (n := y).
  apply modline82.
  assumption.
  assumption.
Qed.



(********* SIMPLIFY_SUB ************)

(* ;; Before: (c0 - ((c1 - _0) / c2)) After : ((fold(((((c0 * c2) - c1) + c2) - 1)) + _0) / c2);; Pred  : (c2 > 0) *)
(* rewrite(c0 - (c1 - x)/c2, (fold(c0*c2 - c1 + c2 - 1) + x)/c2, c2 > 0) *)
Lemma subline250 : forall x c0 c1 c2, c2 > 0 -> c0 - (c1 - x)/c2 == (c0*c2 - c1 + c2 - 1 + x)/c2.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- div_opp_r.
  rewrite <- add_opp_r with (n := c1).
  rewrite add_comm with (n := c1) (m := - x).
  rewrite <- opp_sub_distr.
Admitted.


(* ;; Before: (c0 - ((_0 + c1) / c2)) After : ((fold(((((c0 * c2) - c1) + c2) - 1)) - _0) / c2);; Pred  : (c2 > 0) *)
(* rewrite(c0 - (x + c1)/c2, (fold(c0*c2 - c1 + c2 - 1) - x)/c2, c2 > 0) *)
Lemma subline251 : forall x c0 c1 c2, c0 - (x + c1)/c2 == (c0*c2 - c1 + c2 - 1 - x)/c2.
Proof.
Admitted.

(* ;; Before: (_0 - ((_0 + _1) / c0)) After : ((((_0 * fold((c0 - 1))) - _1) + fold((c0 - 1))) / c0);; Pred  : (c0 > 0) *)
(* rewrite(x - (x + y)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0) *)
Lemma subline252 : forall x y c0, c0 > 0 -> x - (x + y)/c0 == (x*(c0 - 1) - y + (c0 - 1))/c0.
Proof.
Admitted.

(* ;; Before: (_0 - ((_0 - _1) / c0)) After : ((((_0 * fold((c0 - 1))) + _1) + fold((c0 - 1))) / c0);; Pred  : (c0 > 0) *)
(* rewrite(x - (x - y)/c0, (x*fold(c0 - 1) + y + fold(c0 - 1))/c0, c0 > 0) *)
Lemma subline253 : forall x y c0, c0 > 0 -> x - (x - y)/c0 == (x*(c0 - 1) + y + (c0 - 1))/c0.
Proof.
Admitted.

(* ;; Before: (_0 - ((_1 + _0) / c0)) After : ((((_0 * fold((c0 - 1))) - _1) + fold((c0 - 1))) / c0);; Pred  : (c0 > 0) *)
(* rewrite(x - (y + x)/c0, (x*fold(c0 - 1) - y + fold(c0 - 1))/c0, c0 > 0) *)
Lemma subline254 : forall x y c0, c0 > 0 -> x - (y + x)/c0 == (x*(c0 - 1) - y + (c0 - 1))/c0.
Proof.
Admitted.

(* ;; Before: (_0 - ((_1 - _0) / c0)) After : ((((_0 * fold((c0 + 1))) - _1) + fold((c0 - 1))) / c0);; Pred  : (c0 > 0) *)
(* rewrite(x - (y - x)/c0, (x*fold(c0 + 1) - y + fold(c0 - 1))/c0, c0 > 0) *)
Lemma subline255 : forall x y c0, c0 > 0 -> x - (y - x)/c0 == ((x * (c0 - 1) + y) + (c0 - 1))/c0.
Proof.
Admitted.

(* ;; Before: (((_0 + _1) / c0) - _0) After : (((_0 * fold((1 - c0))) + _1) / c0);; Pred  : 1 *)
(* rewrite((x + y)/c0 - x, (x*fold(1 - c0) + y)/c0) *)
Lemma subline256 : forall x y c0, c0 ~= 0 -> (x + y)/c0 - x == (x*(1 - c0) + y)/c0.
Proof.
  intros.
  rewrite <- add_opp_r.
  rewrite <- div_add with (b := (- x)).
  rewrite <- add_assoc.
  rewrite add_comm with (n := y).
  rewrite add_assoc.
  rewrite <- mul_1_r with (n := x) at 1.
  rewrite mul_opp_comm.
  rewrite <- mul_add_distr_l.
  rewrite add_opp_r.
  reflexivity.
  assumption.
Qed.

(* ;; Before: (((_1 + _0) / c0) - _0) After : ((_1 + (_0 * fold((1 - c0)))) / c0);; Pred  : 1 *)
(* rewrite((y + x)/c0 - x, (y + x*fold(1 - c0))/c0) *)
Lemma subline257 : forall x y c0, c0 ~= 0 -> (y + x)/c0 - x == (y + x*(1 - c0))/c0.
Proof.
  intros.
  rewrite add_comm.
  rewrite add_comm with (m := (x * (1 - c0))).
  apply subline256.
  assumption.
Qed.

(* ;; Before: (((_0 - _1) / c0) - _0) After : (((_0 * fold((1 - c0))) - _1) / c0);; Pred  : 1 *)
(* rewrite((x - y)/c0 - x, (x*fold(1 - c0) - y)/c0) *)
Lemma subline258 : forall x y c0, c0 ~= 0 ->(x - y)/c0 - x == (x*(1 - c0) - y)/c0.
Proof.
  intros.
  rewrite <- add_opp_r with (n := x) (m := y).
  rewrite <- add_opp_r with (n := (x * (1 - c0))).
  apply subline256.
  assumption.
Qed.

(* ;; Before: (((_1 - _0) / c0) - _0) After : ((_1 - (_0 * fold((1 + c0)))) / c0);; Pred  : 1 *)
(* rewrite((y - x)/c0 - x, (y - x*fold(1 + c0))/c0) *)
Lemma subline259 : forall x y c0, c0 ~= 0 -> (y - x)/c0 - x == (y - x*(1 + c0))/c0.
Proof.
  intros.
  rewrite <- add_opp_r with (n := y) (m := x).
  rewrite <- add_opp_r with (n := (y + - x) / c0).
  rewrite addline120.
  rewrite add_comm with (n := c0).
  rewrite mul_comm.
  rewrite mul_opp_l.
  rewrite add_opp_r.
  reflexivity.
  assumption.
Qed.

(* ;; Before: ((((_0 + c0) / c1) * c1) - _0) After : (-_0 % c1);; Pred  : ((c1 > 0) && ((c0 + 1) == c1)) *)
(* rewrite(((x + c0)/c1)*c1 - x, (-x) % c1, c1 > 0 && c0 + 1 == c1) *)
Lemma subline263 : forall x c0 c1, c1 > 0 -> c0 + 1 == c1 -> ((x + c0)/c1) * c1 - x == (- x) mod c1.
Proof.
Admitted.

(* ;; Before: (((_0 + _1) / c0) - ((_0 + c1) / c0)) After : ((((_0 + fold((c1 % c0))) % c0) + (_1 - c1)) / c0);; Pred  : (c0 > 0) *)
(* rewrite((x + y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) + (y - c1))/c0, c0 > 0) *)
Lemma subline273 : forall x y c0 c1, c0 > 0 -> (x + y)/c0 - (x + c1)/c0 == (((x + (c1 mod c0)) mod c0) + y - c1)/c0.
Proof.
Admitted.

(* ;; Before: (((_0 + c1) / c0) - ((_0 + _1) / c0)) After : (((fold(((c0 + c1) - 1)) - _1) - ((_0 + fold((c1 % c0))) % c0)) / c0);; Pred  : (c0 > 0) *)
(* rewrite((x + c1)/c0 - (x + y)/c0, ((fold(c0 + c1 - 1) - y) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0) *)
Lemma subline274 : forall x y c0 c1, c0 > 0 -> (x + c1)/c0 - (x + y)/c0 == ((c0 + c1 - 1) - y - (x + (c1 mod c0)) mod c0) / c0.
Proof.
Admitted.

(* ;; Before: (((_0 - _1) / c0) - ((_0 + c1) / c0)) After : (((((_0 + fold((c1 % c0))) % c0) - _1) - c1) / c0);; Pred  : (c0 > 0) *)
(* rewrite((x - y)/c0 - (x + c1)/c0, (((x + fold(c1 % c0)) % c0) - y - c1)/c0, c0 > 0) *)
Lemma subline275 : forall x y c0 c1, c0 > 0 -> (x - y)/c0 - (x + c1)/c0 == (((x + (c1 mod c0)) mod c0) - y - c1)/c0.
Proof.
Admitted.

(* ;; Before: (((_0 + c1) / c0) - ((_0 - _1) / c0)) After : (((_1 + fold(((c0 + c1) - 1))) - ((_0 + fold((c1 % c0))) % c0)) / c0);; Pred  : (c0 > 0) *)
(* rewrite((x + c1)/c0 - (x - y)/c0, ((y + fold(c0 + c1 - 1)) - ((x + fold(c1 % c0)) % c0))/c0, c0 > 0) *)
Lemma subline276 : forall x y c0 c1, c0 > 0 -> (x + c1)/c0 - (x - y)/c0 == (y + c0 + c1 - 1 - (x + (c1 mod c0) mod c0))/c0.
Proof.
Admitted.

(* ;; Before: ((_0 / c0) - ((_0 + _1) / c0)) After : (((fold((c0 - 1)) - _1) - (_0 % c0)) / c0);; Pred  : (c0 > 0) *)
(* rewrite(x/c0 - (x + y)/c0, ((fold(c0 - 1) - y) - (x % c0))/c0, c0 > 0) *)
Lemma subline277 : forall x y c0, c0 > 0 -> x/c0 - (x + y)/c0 == (((c0 - 1) - y) - (x mod c0))/c0.
Proof.
Admitted.

(* ;; Before: (((_0 + _1) / c0) - (_0 / c0)) After : (((_0 % c0) + _1) / c0);; Pred  : (c0 > 0) *)
(* rewrite((x + y)/c0 - x/c0, ((x % c0) + y)/c0, c0 > 0) *)
Lemma subline278 : forall x y c0, c0 > 0 -> (x + y)/c0 - x/c0 == ((x mod c0) + y)/c0.
Proof.
Admitted.

(* ;; Before: ((_0 / c0) - ((_0 - _1) / c0)) After : (((_1 + fold((c0 - 1))) - (_0 % c0)) / c0);; Pred  : (c0 > 0) *)
(* rewrite(x/c0 - (x - y)/c0, ((y + fold(c0 - 1)) - (x % c0))/c0, c0 > 0) *)
Lemma subline279 : forall x y c0, c0 > 0 -> x/c0 - (x - y)/c0 == (y + (c0 - 1) - (x mod c0))/c0.
Proof.
Admitted.

(* ;; Before: (((_0 - _1) / c0) - (_0 / c0)) After : (((_0 % c0) - _1) / c0);; Pred  : (c0 > 0) *)
(* rewrite((x - y)/c0 - x/c0, ((x % c0) - y)/c0, c0 > 0)) *)
Lemma subline280 : forall x y c0, c0 > 0 -> (x - y)/c0 - x/c0 == ((x mod c0) - y)/c0.
Proof.
Admitted.








































End ZEuclidProp.