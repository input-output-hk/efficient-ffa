require import AllCore Int IntDiv StdOrder Distr.
require import AffineAddition AffineComplete MSM_CompleteCoordinates MSM_CoordinateTrace MSM_CoordinateTables.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract MultiScalarMul_Abstract_Completeness
  MSM_TableConstruction MSM_TableConstraints MSM_CoordinateWitnesses MSM_RejectionBound MSM_WindowOrder.
import Ring.IntID IntOrder.

(* All intermediates below are raw coordinate tuples. Offset scalar
   multiplication uses a complete-addition chain for l*U and w doublings
   followed by subtraction for (2^w-1)*U. This specifies witnesses, not a
   particular low-level circuit or an optimal scalar-multiplication cost. *)
op offset_trace m ca u v = exists pow,
  doubling_trace m ca w u pow /\ complete_step m ca pow (negate_point m u) v.

op full_msm_constraints m ca (P : int -> coordinate_point) s u r =
  valid_windows s /\ exists initial v table terminal,
    multiple_trace m ca l u initial /\ !initial.`1 /\
    offset_trace m ca u v /\ coordinate_tables m P v table /\
    msm_loop_trace m ca T table s initial terminal /\
    complete_step m ca terminal (negate_point m initial) r.

lemma offset_trace_group x y m ca cb u v :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  (offset_trace m ca (group_point x y u) v <=> v=group_point x y ((2^w-1) *** u)).
proof.
move=> Hc Hm. have Hw : 0 <= w by smt(param_pos).
have E : 2^w *** u +++ -u = (2^w-1) *** u
  by rewrite (_ : 2^w-1=2^w+(-1)) 1:/# nplus_dist neg_mul one_mul.
rewrite /offset_trace (negate_point_group x y m ca cb u Hc Hm). split.
+ move=> [pow [Hd Ha]].
  have Ed : pow=group_point x y (2^w *** u) by smt(doubling_trace_group).
  move: Ha. rewrite Ed (complete_step_group x y m ca cb (2^w *** u) (-u) v Hc Hm) E. trivial.
+ move=> Hv. exists (group_point x y (2^w *** u)). split.
  + smt(doubling_trace_group).
  + rewrite (complete_step_group x y m ca cb (2^w *** u) (-u) v Hc Hm) E. exact Hv.
qed.

lemma selected_table_nonzero P u s : table_safe P u => valid_windows s =>
  forall i j, 0 <= i < T => 0 <= j < l => perfect_table_pure P u j (s j i)<>idR.
proof.
rewrite /table_safe /row_safe /valid_windows /perfect_table_pure /table_entry. smt().
qed.

lemma functional_final_correct P s u :
  (multiScalarMulLoop T l (perfect_table_pure P u) s (l *** u) w).`2 +++ -(l *** u)
    = multiScalarMul_Simpl s P T l.
proof.
have HT : 0 <= T by smt(param_pos).
have H := spec_equiv_fun_impl T s u P HT.
move: H. rewrite /gg. smt(op_assoc op_inv op_id).
qed.

lemma full_msm_constraints_sound x y m ca cb P s u r :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  full_msm_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r =>
  construction_accepts P s u /\ r=group_point x y (multiScalarMul_Simpl s P T l).
proof.
move=> Hc Hm. rewrite /full_msm_constraints.
move=> [Hwindows [initial v table terminal [Hinitial [Hnonzero [Hoffset [Htables [Hloop Hfinal]]]]]]].
have Hl : 0 <= l by smt(param_pos).
have HT : 0 <= T by smt(param_pos).
have EI : initial=group_point x y (l *** u) by smt(multiple_trace_group).
have EV : v=group_point x y ((2^w-1) *** u) by smt(offset_trace_group).
have Hnz : l *** u<>idR by move: Hnonzero; rewrite EI group_point_flag; smt().
move: Htables. rewrite EV. move=> Htables.
have [Hsafe Hentries] := coordinate_tables_sound x y m ca cb P u table Hc Hm Htables.
have Hselected := selected_table_nonzero P u s Hsafe Hwindows.
have HE := msm_loop_trace_ext m ca T table (fun j k => group_point x y (perfect_table_pure P u j k))
  s initial terminal _.
+ move=> i j Hi Hj. apply Hentries; first exact Hj. move: Hwindows; rewrite /valid_windows; smt().
move: Hloop. rewrite HE EI. move=> Hloop.
have [Hloopnz Hloopiff] := msm_loop_trace_group x y m ca cb (perfect_table_pure P u) s (l *** u)
  Hc Hm Hnz T HT Hselected.
have HL := Hloopiff terminal.
have Hflag : loop_ok P s u by rewrite /loop_ok; smt().
have EL : terminal=group_point x y (multiScalarMulLoop T l (perfect_table_pure P u) s (l *** u) w).`2 by smt().
split; first by rewrite /construction_accepts; smt().
move: Hfinal. rewrite EI EL (negate_point_group x y m ca cb (l *** u) Hc Hm).
rewrite (complete_step_group x y m ca cb
  (multiScalarMulLoop T l (perfect_table_pure P u) s (l *** u) w).`2 (-(l *** u)) r Hc Hm)
  functional_final_correct. trivial.
qed.

lemma full_msm_constraints_exists x y m ca cb P s u :
  coordinate_laws x y m => complete_affine_model x y m ca cb => construction_accepts P s u =>
  full_msm_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u)
    (group_point x y (multiScalarMul_Simpl s P T l)).
proof.
move=> Hc Hm. rewrite /construction_accepts. move=> [Hsafe [Hwindows [Hnz Hflag]]].
have Hl : 0 <= l by smt(param_pos).
have HT : 0 <= T by smt(param_pos).
rewrite /full_msm_constraints. split; first exact Hwindows.
exists (group_point x y (l *** u)) (group_point x y ((2^w-1) *** u))
  (fun j k => group_point x y (perfect_table_pure P u j k))
  (group_point x y (multiScalarMulLoop T l (perfect_table_pure P u) s (l *** u) w).`2).
split; first smt(multiple_trace_group).
split; first by rewrite group_point_flag.
split; first smt(offset_trace_group).
split; first exact (coordinate_tables_exists x y m ca cb P u Hc Hm Hsafe).
split.
+ have Hselected := selected_table_nonzero P u s Hsafe Hwindows.
  have [Hloopnz Hloopiff] := msm_loop_trace_group x y m ca cb (perfect_table_pure P u) s (l *** u)
    Hc Hm Hnz T HT Hselected.
  have H := Hloopiff (group_point x y (multiScalarMulLoop T l (perfect_table_pure P u) s (l *** u) w).`2).
  move: Hflag. rewrite /loop_ok. smt().
+ rewrite (negate_point_group x y m ca cb (l *** u) Hc Hm).
  rewrite (complete_step_group x y m ca cb
    (multiScalarMulLoop T l (perfect_table_pure P u) s (l *** u) w).`2 (-(l *** u))
    (group_point x y (multiScalarMul_Simpl s P T l)) Hc Hm) functional_final_correct. trivial.
qed.

lemma full_msm_constraints_iff x y m ca cb P s u r :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  (full_msm_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r <=>
    construction_accepts P s u /\ r=group_point x y (multiScalarMul_Simpl s P T l)).
proof.
move=> Hc Hm. split.
+ exact (full_msm_constraints_sound x y m ca cb P s u r Hc Hm).
+ move=> [Ha ->]. exact (full_msm_constraints_exists x y m ca cb P s u Hc Hm Ha).
qed.

lemma full_witness_iff x y m ca cb P s u :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  ((exists r, full_msm_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r)
    <=> construction_accepts P s u).
proof.
move=> Hc Hm. split.
+ move=> [r H]. have HS := full_msm_constraints_sound x y m ca cb P s u r Hc Hm H. smt().
+ move=> H. exists (group_point x y (multiScalarMul_Simpl s P T l)).
  exact (full_msm_constraints_exists x y m ca cb P s u Hc Hm H).
qed.

lemma full_witness_failure_bound x y m ca cb P s :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  nonzero_bases P => valid_windows s => scalar_invertible (2^w-1) => scalar_invertible l =>
  mu r_distr (fun u => !exists r,
    full_msm_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r)
  <= (1+l*(2^w+1)+2*T*l)%r / group_cardinality%r.
proof.
move=> Hc Hm HP Hs Htable Hinitial.
have HE : (fun u => !exists r,
    full_msm_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r) =
  (fun u => !construction_accepts P s u)
  by apply fun_ext=> u; have H := full_witness_iff x y m ca cb P s u Hc Hm; smt().
rewrite HE.
have H := construction_failure_mass P s HP Hs Htable Hinitial.
move: H. rewrite /rejection_bound point_mass_cardinality. smt().
qed.

(* External scalar windows remain little endian. *)
op little_endian_full_constraints m ca P s u r =
  full_msm_constraints m ca P (reverse_windows T s) u r.

lemma little_endian_full_sound x y m ca cb P s u r :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  little_endian_full_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r =>
  r=group_point x y (msm_little_endian s P T l).
proof.
move=> Hc Hm. rewrite /little_endian_full_constraints. move=> H.
have [_ Hr] := full_msm_constraints_sound x y m ca cb P (reverse_windows T s) u r Hc Hm H.
move: Hr. rewrite reversed_core_spec 1:/#. trivial.
qed.

lemma little_endian_full_failure_bound x y m ca cb P s :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  nonzero_bases P => valid_windows s => scalar_invertible (2^w-1) => scalar_invertible l =>
  mu r_distr (fun u => !exists r,
    little_endian_full_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r)
  <= (1+l*(2^w+1)+2*T*l)%r / group_cardinality%r.
proof.
move=> Hc Hm HP Hs Htable Hinitial. rewrite /little_endian_full_constraints.
apply (full_witness_failure_bound x y m ca cb P (reverse_windows T s) Hc Hm HP _ Htable Hinitial).
smt(reverse_windows_valid).
qed.

lemma little_endian_full_rejection_mass x y m ca cb P s &mem :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  Pr[SampledLittleEndianMSM.run(P,s) @ &mem : !res.`1] =
  mu r_distr (fun u => !exists r,
    little_endian_full_constraints m ca (fun j => group_point x y (P j)) s (group_point x y u) r).
proof.
move=> Hc Hm.
have -> : Pr[SampledLittleEndianMSM.run(P,s) @ &mem : !res.`1] =
  Pr[MSM_WithTable.SampledConstructedMSM.run(P,reverse_windows T s) @ &mem : !res.`1].
+ byequiv sampled_little_endian_equiv; smt().
rewrite sampled_rejection_mass /little_endian_full_constraints.
have HE : (fun u => !construction_accepts P (reverse_windows T s) u) =
  (fun u => !exists r,
    full_msm_constraints m ca (fun j => group_point x y (P j)) (reverse_windows T s) (group_point x y u) r).
+ apply fun_ext=> u. have H := full_witness_iff x y m ca cb P (reverse_windows T s) u Hc Hm. smt().
by rewrite HE.
qed.
