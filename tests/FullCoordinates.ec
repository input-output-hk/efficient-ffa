require import AllCore Int IntDiv StdOrder.
require import AffineAddition AffineComplete MSM_CoordinateTrace MSM_CoordinateTables MSM_FullCoordinates.
require import MultiScalarMul_Abstract MSM_TableConstruction.
import Ring.IntID IntOrder.

lemma chain_one step a r : coordinate_chain 1 step a r <=> step 0 a r.
proof.
have E : 1=0+1 by smt(). rewrite E coordinate_chainS 1:/#.
smt(coordinate_chain0).
qed.

(* A complete concrete one-window run on y^2=x^3+2x+2 over F_17.
   P=(5,1), U=2P=(6,3), window=1. The loop finishes at 3P=(10,6);
   final cancellation of 2P returns P. Every intermediate is a raw tuple. *)
lemma f17_double_u : complete_step 17 2 (false,6,3) (false,6,3) (false,3,1).
proof.
rewrite /complete_step. exists 7.
rewrite /complete_constraints /point_bounded /AffineDoubling.doubling_equations /=. smt().
qed.

lemma f17_offset : complete_step 17 2 (false,3,1) (false,6,14) (false,6,3).
proof.
rewrite /complete_step. exists 10.
rewrite /complete_constraints /point_bounded /affine_equations /=. smt().
qed.

lemma f17_table : incomplete_step 17 (false,6,14) (false,5,1) (false,5,16).
proof.
rewrite /incomplete_step /point_bounded /=. exists 13.
rewrite /affine_equations. smt().
qed.

lemma f17_loop : guarded_step 17 (false,3,1) (false,5,16) (false,10,6).
proof.
rewrite /guarded_step /coordinate_safe /incomplete_step /point_bounded /=.
exists 16. rewrite /affine_equations. smt().
qed.

lemma f17_correction : complete_step 17 2 (false,10,6) (false,6,14) (false,5,1).
proof.
rewrite /complete_step. exists 15.
rewrite /complete_constraints /point_bounded /affine_equations /=. smt().
qed.

lemma f17_full_trace : w=1 => T=1 => l=1 =>
  full_msm_constraints 17 2 (fun (_ : int) => (false,5,1)) (fun (_ _ : int) => 1)
    (false,6,3) (false,5,1).
proof.
move=> Hw HT Hl. have Hpow : 2^w=2 by rewrite Hw expr1.
rewrite /full_msm_constraints. split.
+ rewrite /valid_windows Hpow HT Hl /=. smt().
exists (false,6,3) (false,6,3)
  (fun (_ : int) k => if k=0 then (false,6,14) else (false,5,16)) (false,10,6).
split.
+ rewrite /multiple_trace Hl chain_one /= /complete_step. exists 0.
  rewrite /complete_constraints /point_bounded /normalize_point /infinity /=. smt().
split; first trivial. split.
+ rewrite /offset_trace. exists (false,3,1). split.
  + rewrite /doubling_trace Hw chain_one /=. exact f17_double_u.
  + have E : negate_point 17 (false,6,3)=(false,6,14) by rewrite /negate_point /=; smt().
    rewrite E. exact f17_offset.
split.
+ rewrite /coordinate_tables /coordinate_row Hpow Hl /=.
  move=> j Hj. split.
  + rewrite /coordinate_safe /=. smt().
  split; first by rewrite /negate_point /=; smt().
  move=> k Hk. have E : k=0 by smt(). rewrite E /=. exact f17_table.
split.
+ rewrite /msm_loop_trace HT chain_one /= /window_trace. exists (false,3,1). split.
  + rewrite /doubling_trace Hw chain_one /=. exact f17_double_u.
  + rewrite /addition_trace Hl chain_one /=. exact f17_loop.
+ have E : negate_point 17 (false,6,3)=(false,6,14) by rewrite /negate_point /=; smt().
  rewrite E. exact f17_correction.
qed.

(* The terminal accumulator is not the MSM output until correction. *)
lemma uncorrected_output_rejected :
  !complete_step 17 2 (false,10,6) (false,6,14) (false,10,6).
proof. rewrite /complete_step /complete_constraints /affine_equations /=. smt(). qed.

(* V=2P at width three reaches an inverse pair in its second step.
   The initial check holds, but the row equations cannot be completed. *)
lemma exceptional_table_row_rejected : forall entries,
  !coordinate_row 17 3 (false,5,1) (false,6,3) entries.
proof.
move=> entries. rewrite /coordinate_row /coordinate_safe /negate_point /=.
(* The first step forces (5,16); the second then has an impossible slope. *)
case (coordinate_row 17 3 (false,5,1) (false,6,3) entries); last smt().
move=> Hrow.
have H0 : entries 0=(false,6,14) by move: Hrow; rewrite /coordinate_row /negate_point /=; smt().
have H1 : incomplete_step 17 (false,6,14) (false,5,1) (entries 1)
  by move: Hrow; rewrite /coordinate_row; smt().
have H2 : incomplete_step 17 (entries 1) (false,5,1) (entries 2)
  by move: Hrow; rewrite /coordinate_row; smt().
have Hsafe : coordinate_safe 17 (false,6,14) (false,5,1) by rewrite /coordinate_safe /=; smt().
have Hprime : prime 17 by rewrite /prime; smt().
have HC : complete_step 17 2 (false,6,14) (false,5,1) (entries 1) by smt(incomplete_as_complete).
have HCknown : complete_step 17 2 (false,6,14) (false,5,1) (false,5,16)
  by have H := f17_table; smt(incomplete_as_complete).
have E : entries 1=(false,5,16) by move: HC HCknown; rewrite /complete_step; smt(complete_constraints_sound).
move: H2. rewrite E /incomplete_step /affine_equations /=. smt().
qed.

lemma f17_zero_scalar_full_trace : w=1 => T=1 => l=1 =>
  full_msm_constraints 17 2 (fun (_ : int) => (false,5,1)) (fun (_ _ : int) => 0)
    (false,6,3) infinity.
proof.
move=> Hw HT Hl. have Hpow : 2^w=2 by rewrite Hw expr1.
have Eneg : negate_point 17 (false,6,3)=(false,6,14) by rewrite /negate_point /=; smt().
rewrite /full_msm_constraints. split.
+ rewrite /valid_windows Hpow HT Hl /=. smt().
exists (false,6,3) (false,6,3)
  (fun (_ : int) k => if k=0 then (false,6,14) else (false,5,16)) (false,6,3).
split.
+ rewrite /multiple_trace Hl chain_one /= /complete_step. exists 0.
  rewrite /complete_constraints /point_bounded /normalize_point /infinity /=. smt().
split; first trivial. split.
+ rewrite /offset_trace. exists (false,3,1). split.
  + rewrite /doubling_trace Hw chain_one /=. exact f17_double_u.
  + rewrite Eneg. exact f17_offset.
split.
+ rewrite /coordinate_tables /coordinate_row Hpow Hl /=.
  move=> j Hj. split; first by rewrite /coordinate_safe /=; smt().
  split; first by rewrite Eneg.
  move=> k Hk. have E : k=0 by smt(). rewrite E /=. exact f17_table.
split.
+ rewrite /msm_loop_trace HT chain_one /= /window_trace. exists (false,3,1). split.
  + rewrite /doubling_trace Hw chain_one /=. exact f17_double_u.
  + rewrite /addition_trace Hl chain_one /= /guarded_step. split.
    + rewrite /coordinate_safe /=. smt().
    + have Hsafe : coordinate_safe 17 (false,3,1) (false,6,14) by rewrite /coordinate_safe /=; smt().
      have H := incomplete_as_complete 17 2 (false,3,1) (false,6,14) (false,6,3) Hsafe.
      smt(f17_offset).
+ rewrite Eneg /complete_step. exists 0.
  rewrite /complete_constraints /point_bounded /infinity /=. smt().
qed.
