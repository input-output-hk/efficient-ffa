require import AllCore Int IntDiv StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract.
import IntOrder.

(* A row contains k*P - V for 0 <= k < b. *)
op table_entry (p v : R) (k : int) : R = k *** p +++ -v.
op add_safe (a b : R) = a <> idR /\ b <> idR /\ xdiff a b.
op row_safe (p v : R) (n : int) =
  p <> idR /\
  (forall k, 0 <= k < n => table_entry p v k <> idR) /\
  (forall k, 0 <= k < n - 1 => xdiff (table_entry p v k) p).

lemma table_entry0 p v : table_entry p v 0 = -v.
proof. by rewrite /table_entry zero_mul op_id'. qed.

lemma table_entryS p v k :
 table_entry p v (k+1) = table_entry p v k +++ p.
proof. rewrite /table_entry nplus_dist one_mul. smt(op_assoc op_comm). qed.

lemma add_safe_result a b : add_safe a b =>
 a %%% b = a +++ b /\ a +++ b <> idR.
proof. rewrite /add_safe /xdiff. smt(same_res opt_never_id). qed.

lemma row_safe1 p v : row_safe p v 1 = (p <> idR /\ -v <> idR).
proof. rewrite /row_safe. smt(table_entry0). qed.

lemma row_safeS p v n : 1 <= n =>
 row_safe p v (n+1) =
 (row_safe p v n /\ add_safe (table_entry p v (n-1)) p).
proof.
move=> Hn.
have Hnext := add_safe_result (table_entry p v (n-1)) p.
have Heq : table_entry p v n = table_entry p v (n-1) +++ p
 by rewrite -table_entryS; congr; smt().
move: Hnext. rewrite /row_safe /add_safe.
smt().
qed.

module TableBuilder = {
 proc row(p v : R, b : int) = {
  var entries : int -> R;
  var q : R;
  var i : int;
  var ok : bool;
  q <- -v;
  entries <- fun k => if k = 0 then q else idR;
  ok <- 0 < b /\ p <> idR /\ q <> idR;
  i <- 1;
  while (i < b) {
   if (ok) {
    ok <- add_safe q p;
    if (ok) {
     q <- q %%% p;
     entries <- fun k => if k = i then q else entries k;
    }
   }
   i <- i + 1;
  }
  return (ok, entries);
 }

 proc build(P : int -> R, U : R) = {
  var table : int -> int -> R;
  var entries : int -> R;
  var v : R;
  var j : int;
  var ok, row_ok : bool;
  table <- fun j k => idR;
  v <- (2 ^ w - 1) *** U;
  ok <- true;
  j <- 0;
  while (j < l) {
   (row_ok, entries) <@ row(P j, v, 2 ^ w);
   table <- fun h => if h = j then entries else table h;
   ok <- ok /\ row_ok;
   j <- j + 1;
  }
  return (ok, table);
 }
}.

lemma table_row_spec P V width : 0 < width =>
 phoare [TableBuilder.row : arg = (P,V,width) ==>
  (res.`1 = row_safe P V width) /\
  (res.`1 => forall k, 0 <= k < width => res.`2 k = table_entry P V k)] = 1%r.
proof.
move=> Hb.
proc.
while (p = P /\ v = V /\ b = width /\ 1 <= i <= b /\
       ok = row_safe P V i /\
       (ok => q = table_entry P V (i-1) /\
        forall k, 0 <= k < i => entries k = table_entry P V k)) (b-i).
move=> z.
wp. skip. progress; smt(row_safeS add_safe_result table_entryS).
wp. skip. progress; smt(row_safe1 table_entry0).
qed.

(* A sufficient group-level exclusion set for a complete row. *)
op row_admissible (p v : R) (b : int) =
 p <> idR /\ forall j, -1 <= j <= b-1 => v <> j *** p.

lemma table_entry_eq_mul p v k j :
 (table_entry p v k = j *** p) = (v = (k-j) *** p).
proof.
rewrite /table_entry (_: k-j = k + -j) 1:/# nplus_dist neg_mul.
smt(op_assoc op_comm op_id op_id' op_inv neg_neg_id const_add_inj).
qed.

lemma row_admissible_safe p v b : 0 < b =>
 row_admissible p v b => row_safe p v b.
proof.
rewrite /row_admissible /row_safe.
move=> Hb [Hp Hv]. split; first exact Hp.
split.
+ move=> k Hk.
  have H := table_entry_eq_mul p v k 0.
  smt(zero_mul).
+ move=> k Hk.
  have H := notxdiff (table_entry p v k) p.
  have Hplus := table_entry_eq_mul p v k 1.
  have Hminus := table_entry_eq_mul p v k (-1).
  smt(one_mul neg_mul).
qed.


op table_safe (P : int -> R) (U : R) =
 forall j, 0 <= j < l => row_safe (P j) ((2 ^ w - 1) *** U) (2 ^ w).

lemma table_build_spec argP argU :
 phoare [TableBuilder.build : arg = (argP,argU) ==>
  (res.`1 = table_safe argP argU) /\
  (res.`1 => forall j k, 0 <= j < l => 0 <= k < 2 ^ w =>
   res.`2 j k = perfect_table_pure argP argU j k)] = 1%r.
proof.
proc.
while (P = argP /\ U = argU /\ v = (2 ^ w - 1) *** argU /\
  0 <= j <= l /\
  ok = (forall h, 0 <= h < j => row_safe (argP h) v (2 ^ w)) /\
  (ok => forall h k, 0 <= h < j => 0 <= k < 2 ^ w =>
    table h k = table_entry (argP h) v k)) (l-j).
move=> z.
wp.
ecall (table_row_spec (P j) v (2 ^ w) _).
+ skip. progress; smt().
+ smt(expr_gt0).
wp. skip. rewrite /table_safe /table_entry /perfect_table_pure.
progress; smt(param_pos).
qed.


op valid_windows (s : int -> int -> int) =
 forall j i, 0 <= j < l => 0 <= i < T => 0 <= s j i < 2 ^ w.

lemma table_safe_u_check P U s : table_safe P U =>
 l *** U <> idR => valid_windows s => u_check U P s.
proof.
rewrite /table_safe /row_safe /valid_windows /u_check
 /perfect_table_pure /table_entry.
smt().
qed.

lemma admissible_table_safe P U :
 (forall j, 0 <= j < l =>
   row_admissible (P j) ((2 ^ w - 1) *** U) (2 ^ w)) =>
 table_safe P U.
proof. rewrite /table_safe. smt(row_admissible_safe expr_gt0). qed.


lemma table_build_spec_h argP argU :
 hoare [TableBuilder.build : arg = (argP,argU) ==>
  (res.`1 = table_safe argP argU) /\
  (res.`1 => forall j k, 0 <= j < l => 0 <= k < 2 ^ w =>
   res.`2 j k = perfect_table_pure argP argU j k)].
proof. conseq (table_build_spec argP argU); smt(). qed.
