require import AllCore IntDiv StdOrder ZModP Distr.
import Ring.IntID IntOrder.

(* E/F_5: y^2 = x^3 + 2x + 1. G=(0,1) has order seven.
   Represent points by their discrete logarithm in this tiny group.
   The coordinate table is verified against the affine formulas below. *)
clone ZModP.ZModField as F7 with op p <- 7
  proof prime_p.
realize prime_p. proof.
split=> // q Hq.
have Hbound : `|q| <= 7 by have H:=dvdz_le q 7 _ Hq; smt().
have Habs : `|q| %| 7 by smt(dvdzN).
have Hrange : 0 <= `|q| by smt().
have Hcases : `|q|=0 \/ `|q|=1 \/ `|q|=2 \/ `|q|=3 \/ `|q|=4 \/ `|q|=5 \/ `|q|=6 \/ `|q|=7 by smt().
move: Habs. rewrite dvdzE.
case: Hcases=> [->|[->|[->|[->|[->|[->|[->|->]]]]]]]; smt().
qed.

op cx (a : F7.zmod) =
  if F7.asint a=2 \/ F7.asint a=5 then 1
  else if F7.asint a=3 \/ F7.asint a=4 then 3 else 0.
op cy (a : F7.zmod) =
  if F7.asint a=1 then 1
  else if F7.asint a=2 \/ F7.asint a=3 then 3
  else if F7.asint a=4 \/ F7.asint a=5 then 2
  else if F7.asint a=6 then 4 else 0.
op px (a : F7.zmod) = if a=F7.zero then None else Some (cx a).
op py (a : F7.zmod) = if a=F7.zero then None else Some (cy a).
op smul n (a : F7.zmod) = F7.( * ) (F7.inzmod n) a.
op sinv n = F7.asint (F7.inv (F7.inzmod n)).

lemma cases7 (a : F7.zmod) :
  a=F7.inzmod 0 \/ a=F7.inzmod 1 \/ a=F7.inzmod 2 \/
  a=F7.inzmod 3 \/ a=F7.inzmod 4 \/ a=F7.inzmod 5 \/ a=F7.inzmod 6.
proof. have H:=F7.rg_asint a. have K:=F7.asintK a. smt(). qed.

lemma double_nonzero (a : F7.zmod) n :
  a<>F7.zero => 0<n => smul (2^n) a<>F7.zero.
proof.
move=> Ha Hn. rewrite /smul F7.ZModpField.mulf_eq0 Ha /=.
rewrite F7.inzmod_exp (_ : 0<=n) 1:/# /= F7.ZModpField.expf_eq0.
have Htwo : F7.inzmod 2 <> F7.zero
  by apply/negP=> /(congr1 F7.asint); rewrite F7.inzmodK F7.zeroE; smt().
smt().
qed.

lemma scalar_inverse n (a : F7.zmod) :
  0 < `|n| < 7 => smul (sinv n) (smul n a)=a.
proof.
move=> Hn.
have Hnz : F7.inzmod n <> F7.zero.
+ rewrite F7.inzmod_eq0P. smt(dvdz_le).
by rewrite /smul /sinv F7.asintK F7.ZModpField.mulrA
  F7.ZModpField.mulVr // F7.ZModpField.mul1r.
qed.

lemma equal_x (a b : F7.zmod) : px a=px b => a=b \/ a=F7.([-]) b.
proof.
move: (cases7 a) (cases7 b).
move=> [->|[->|[->|[->|[->|[->|->]]]]]];
move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite /px /cx /F7.zero -!F7.asint_eq !F7.inzmodK ?F7.oppE ?F7.inzmodK /=; smt().
qed.

require MSM_Instance.
clone MSM_Instance.Model as Concrete with
  type MultiScalarMul_Abstract_Setup.R <- F7.zmod,
  type MultiScalarMul_Abstract_Setup.F <- int option,
  op MultiScalarMul_Abstract_Setup.order <- 7,
  op MultiScalarMul_Abstract_Setup.idR <- F7.zero,
  op MultiScalarMul_Abstract_Setup.(+++) <- F7.(+),
  op MultiScalarMul_Abstract_Setup.( *** ) <- smul,
  op MultiScalarMul_Abstract_Setup.([-]) <- F7.([-]),
  op MultiScalarMul_Abstract_Setup.(%%%) <- F7.(+),
  op MultiScalarMul_Abstract_Setup.xof <- px,
  op MultiScalarMul_Abstract_Setup.yof <- py,
  op MultiScalarMul_Abstract_Setup.invertme <- sinv,
  op MultiScalarMul_Abstract.w <- 1,
  op MultiScalarMul_Abstract.T <- 1,
  op MultiScalarMul_Abstract.l <- 1,
  op MultiScalarMul_Abstract.r_distr <- F7.DZmodP.dunifin
  proof *.

realize MultiScalarMul_Abstract_Setup.order_pos. proof. trivial. qed.
realize MultiScalarMul_Abstract_Setup.same_res. proof. trivial. qed.
realize MultiScalarMul_Abstract_Setup.opt_never_id.
proof.
move=> a b Ha Hb Hx.
apply/negP=> Hsum.
have E : a=F7.([-]) b by smt(F7.ZModpRing.addrK F7.ZModpRing.addr0 F7.ZModpRing.addrA F7.ZModpRing.addrN).
move: Hx. rewrite E /px /cx.
move: (cases7 b). move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite -!F7.asint_eq ?F7.zeroE ?F7.oppE !F7.inzmodK /=; smt().
qed.
realize MultiScalarMul_Abstract_Setup.no_order_two_elems.
proof. exact double_nonzero. qed.
realize MultiScalarMul_Abstract_Setup.op_assoc.
proof. smt(F7.ZModpRing.addrA). qed.
realize MultiScalarMul_Abstract_Setup.op_comm.
proof. exact F7.ZModpRing.addrC. qed.
realize MultiScalarMul_Abstract_Setup.op_id.
proof. exact F7.ZModpRing.addr0. qed.
realize MultiScalarMul_Abstract_Setup.op_id'.
proof. exact F7.ZModpRing.add0r. qed.
realize MultiScalarMul_Abstract_Setup.op_inv.
proof. exact F7.ZModpRing.addrN. qed.
realize MultiScalarMul_Abstract_Setup.one_mul.
proof. move=> a. by rewrite /smul F7.ZModpRing.mul1r. qed.
realize MultiScalarMul_Abstract_Setup.zero_mul.
proof. move=> a. by rewrite /smul F7.ZModpRing.mul0r. qed.
realize MultiScalarMul_Abstract_Setup.nplus_dist.
proof. move=> i b a. by rewrite /smul F7.inzmodD F7.ZModpRing.mulrDl. qed.
realize MultiScalarMul_Abstract_Setup.nmul_mul.
proof. move=> i b a. by rewrite /smul F7.inzmodM F7.ZModpRing.mulrA. qed.
realize MultiScalarMul_Abstract_Setup.neg_mul.
proof. move=> i a. by rewrite /smul F7.inzmodN F7.ZModpRing.mulNr. qed.
realize MultiScalarMul_Abstract_Setup.mul_idr.
proof. move=> n. by rewrite /smul F7.ZModpRing.mulr0. qed.
realize MultiScalarMul_Abstract_Setup.mul_plus_distr.
proof. move=> n a b. by rewrite /smul F7.ZModpRing.mulrDr. qed.
realize MultiScalarMul_Abstract_Setup.notxdiff.
proof. move=> a b. rewrite /Concrete.MultiScalarMul_Abstract_Setup.xdiff. exact (equal_x a b). qed.
realize MultiScalarMul_Abstract_Setup.invertmeP.
proof. exact scalar_inverse. qed.
realize MultiScalarMul_Abstract.param_pos. proof. trivial. qed.
realize MultiScalarMul_Abstract.r_distr_full. proof. exact F7.DZmodP.dunifin_fu. qed.
realize MultiScalarMul_Abstract.r_distr_uni. proof. exact F7.DZmodP.dunifin_uni. qed.
realize MultiScalarMul_Abstract.r_distr_ll. proof. exact F7.DZmodP.dunifin_ll. qed.
realize MultiScalarMul_Abstract_Completeness.completeness_constraints.
proof. move=> i Hi. have -> : i=0 by smt(). rewrite expr1. trivial. qed.

require import AffineAddition AffineDoubling AffineComplete.
import Concrete.MultiScalarMul_Abstract_Setup Concrete.MultiScalarMul_Abstract
  Concrete.MSM_TableConstruction Concrete.MSM_TableConstraints
  Concrete.MSM_CoordinateWitnesses Concrete.MSM_CompleteCoordinates.

lemma prime5 : prime 5.
proof.
split=> // q Hq.
have Hbound : `|q| <= 5 by have H:=dvdz_le q 5 _ Hq; smt().
have Habs : `|q| %| 5 by rewrite dvdz_norml.
have Hcases : `|q|=0 \/ `|q|=1 \/ `|q|=2 \/ `|q|=3 \/ `|q|=4 \/ `|q|=5 by smt().
move: Habs. rewrite dvdzE.
case: Hcases=> [->|[->|[->|[->|[->|->]]]]]; smt().
qed.

lemma coordinates : coordinate_laws cx cy 5.
proof.
rewrite /coordinate_laws. split; first trivial. split.
+ move=> p. move: (cases7 p).
  move=> [->|[->|[->|[->|[->|[->|->]]]]]];
  rewrite /cy -!F7.asint_eq F7.zeroE !F7.inzmodK /=; smt().
split.
+ move=> p. move: (cases7 p).
  move=> [->|[->|[->|[->|[->|[->|->]]]]]];
  rewrite /cx /cy -!F7.asint_eq F7.zeroE !F7.oppE !F7.inzmodK /=; smt().
+ move=> a b. move: (cases7 a) (cases7 b).
  move=> [->|[->|[->|[->|[->|[->|->]]]]]];
  move=> [->|[->|[->|[->|[->|[->|->]]]]]];
  rewrite /xdiff /px /cx -!F7.asint_eq F7.zeroE !F7.inzmodK /=; smt().
qed.

lemma coordinates_injective (a b : F7.zmod) :
  a<>F7.zero => b<>F7.zero => eqm 5 (cx a) (cx b) => eqm 5 (cy a) (cy b) => a=b.
proof.
move: (cases7 a) (cases7 b).
move=> [->|[->|[->|[->|[->|[->|->]]]]]];
move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite /cx /cy -!F7.asint_eq F7.zeroE !F7.inzmodK /=; smt().
qed.

(* A computable slope witness; correctness is checked in every finite case. *)
op inv5 n = if n %% 5=1 then 1 else if n %% 5=2 then 3
  else if n %% 5=3 then 2 else if n %% 5=4 then 4 else 0.
op add_slope (a b : F7.zmod) = (cy b-cy a)*inv5 (cx b-cx a).
op double_slope (a : F7.zmod) = (3*cx a*cx a+2)*inv5 (2*cy a).

lemma addition_equations a b : add_safe a b =>
  affine_equations 5 (cx a) (cy a) (cx b) (cy b)
    (cx (F7.(+) a b)) (cy (F7.(+) a b)) (add_slope a b).
proof.
move: (cases7 a) (cases7 b).
move=> [->|[->|[->|[->|[->|[->|->]]]]]];
move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite /add_safe /xdiff /px /affine_equations /add_slope /inv5 /cx /cy
  -!F7.asint_eq F7.zeroE !F7.addE !F7.inzmodK /=; smt().
qed.

lemma doubling_equations_checked a : a<>F7.zero =>
  doubling_equations 5 2 (cx a) (cy a) (cx (F7.(+) a a)) (cy (F7.(+) a a)) (double_slope a).
proof.
move: (cases7 a). move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite /doubling_equations /double_slope /inv5 /cx /cy
  -!F7.asint_eq F7.zeroE !F7.addE !F7.inzmodK /=; smt().
qed.

lemma point_coordinates a : a<>F7.zero =>
  0<=cx a<5 /\ 0<=cy a<5 /\ on_affine_curve 5 2 1 (cx a) (cy a).
proof.
move: (cases7 a). move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite /on_affine_curve /curve_residual /cx /cy
  -!F7.asint_eq F7.zeroE !F7.inzmodK /=; smt().
qed.

lemma affine_model : affine_group_model cx cy 5.
proof.
rewrite /affine_group_model. split; first exact prime5.
split; first exact coordinates_injective.
move=> a b Hsafe.
have Hden := safe_coordinate_denominator cx cy 5 a b coordinates Hsafe.
have H := affine_equations_unique 5 (cx a) (cy a) (cx b) (cy b)
  (cx (F7.(+) a b)) (cy (F7.(+) a b)) (add_slope a b) prime5 Hden
  (addition_equations a b Hsafe).
smt().
qed.

lemma complete_model : complete_affine_model cx cy 5 2 1.
proof.
rewrite /complete_affine_model. split; first exact affine_model.
split; first exact point_coordinates.
move=> a Ha.
have Hden : (2*cy a) %% 5<>0 by move: coordinates; rewrite /coordinate_laws; smt().
have H := doubling_equations_unique 5 2 (cx a) (cy a)
  (cx (F7.(+) a a)) (cy (F7.(+) a a)) (double_slope a) prime5 Hden
  (doubling_equations_checked a Ha).
smt().
qed.

(* The chosen short-Weierstrass curve is nonsingular over F_5. *)
lemma nonsingular : (4*2*2*2+27*1*1) %% 5 <> 0.
proof. smt(). qed.
