require import AllCore Int StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract MSM_WindowOrder.

op two_windows (j i : int) = if i=0 then 1 else if i=1 then 2 else 0.

lemma iteri_one ['a] (f : int -> 'a -> 'a) acc : iteri 1 f acc = f 0 acc.
proof. rewrite (iteriS 0) 1:/# iteri0 1:/#. trivial. qed.

lemma iteri_two ['a] (f : int -> 'a -> 'a) acc :
  iteri 2 f acc = f 1 (f 0 acc).
proof. rewrite (iteriS 1) 1:/# iteri_one. trivial. qed.

(* The published forward traversal interprets [1,2] in base four as 6. *)
lemma unreversed_two_windows P : w=2 =>
  multiScalarMul_Simpl two_windows (fun _ => P) 2 1 = 6 *** P.
proof.
move=> Hw. rewrite /multiScalarMul_Simpl iteri_two /= !iteri_one /= /two_windows Hw /=.
rewrite expr2 expr0 /= !op_id' -nplus_dist. trivial.
qed.

(* The intended little-endian scalar is 1+4*2=9. *)
lemma little_endian_two_windows P : w=2 =>
  msm_little_endian two_windows (fun _ => P) 2 1 = 9 *** P.
proof.
move=> Hw. rewrite /msm_little_endian iteri_two /= !iteri_one /= /two_windows Hw /=.
rewrite expr2 expr0 /= !op_id' -nplus_dist. trivial.
qed.

lemma reversed_two_windows P : w=2 =>
  multiScalarMul_Simpl (reverse_windows 2 two_windows) (fun _ => P) 2 1 = 9 *** P.
proof. move=> Hw. rewrite reversed_core_spec 1:/#. exact (little_endian_two_windows P Hw). qed.

(* This concerns window order, not byte order within an individual window. *)
lemma reversal_reads_highest_first n s j :
  reverse_windows n s j 0 = s j (n-1) /\
  reverse_windows n s j (n-1) = s j 0.
proof. rewrite /reverse_windows. smt(). qed.

(* Rule out accidental equality caused by a small-order base point. *)
lemma unreversed_not_little_endian P :
  w=2 => P <> idR => 3 < order =>
  multiScalarMul_Simpl two_windows (fun _ => P) 2 1 <>
  msm_little_endian two_windows (fun _ => P) 2 1.
proof.
move=> Hw Hp Horder.
rewrite (unreversed_two_windows P Hw) (little_endian_two_windows P Hw).
have Hsum : 9 *** P = 6 *** P +++ 3 *** P by smt(nplus_dist).
case (6 *** P = 9 *** P); last smt().
move=> Heq.
have Hzero : 3 *** P = idR by smt(const_add_inj op_comm op_id).
have Hinv := invertmeP 3 P _; first smt().
rewrite Hzero mul_idr in Hinv. smt().
qed.
