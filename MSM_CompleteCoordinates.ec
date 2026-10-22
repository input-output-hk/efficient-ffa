require import AllCore Int IntDiv StdOrder.
require import AffineAddition AffineDoubling AffineComplete.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
  MSM_TableConstruction MSM_TableConstraints MSM_CoordinateWitnesses.
import Ring.IntID IntOrder.

op group_point (x y : R -> int) (a : R) : coordinate_point =
  if a=idR then infinity else (false,x a,y a).

(* Explicit, uninstantiated representation obligations. The safe-addition
   model is reused, and the tangent formula for group doubling is added.
   Coordinates are canonical; curve membership is required only for inputs
   to the representation, never assumed for raw witnessed output tuples. *)
op complete_affine_model (x y : R -> int) m ca cb =
  affine_group_model x y m /\
  (forall a, a<>idR => 0 <= x a < m /\ 0 <= y a < m /\
    on_affine_curve m ca cb (x a) (y a)) /\
  (forall a, a<>idR =>
    let sl = doubling_slope m ca (x a) (y a) in
    let sx = affine_x (x a) (x a) sl in
    eqm m (x (a +++ a)) sx /\
    eqm m (y (a +++ a)) (affine_y (x a) (y a) sx sl)).

lemma group_point_on_curve x y m ca cb a : complete_affine_model x y m ca cb =>
  point_on_curve m ca cb (group_point x y a).
proof. rewrite /complete_affine_model /point_on_curve /group_point /infinity. smt(). qed.

lemma group_point_normal x y m ca cb a : complete_affine_model x y m ca cb =>
  normalize_point m (group_point x y a) = group_point x y a.
proof.
rewrite /complete_affine_model /affine_group_model.
move=> [[Hp Hmodel] [Hcoords Hdbl]].
case (a=idR).
+ move=> Ha. by rewrite /normalize_point /group_point Ha /infinity /=.
move=> Ha. have H := Hcoords a Ha.
rewrite /normalize_point /group_point Ha /=. smt(modz_small gt0_prime).
qed.

lemma group_point_injective x y m ca cb a b : complete_affine_model x y m ca cb =>
  group_point x y a = group_point x y b => a=b.
proof. rewrite /complete_affine_model /affine_group_model /group_point /infinity. smt(). qed.

lemma double_nonzero a : a<>idR => a +++ a <> idR.
proof.
move=> Ha.
have H := no_order_two_elems a 1 Ha _; first smt().
have Epow : 2^1=1+1 by rewrite expr1.
have E : 2^1 *** a = a +++ a by rewrite Epow nplus_dist !one_mul.
smt().
qed.

lemma complete_add_group x y m ca cb a b :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  complete_add m ca (group_point x y a) (group_point x y b) = group_point x y (a +++ b).
proof.
move=> Hcoord Hmodel.
have Hnorma := group_point_normal x y m ca cb a Hmodel.
have Hnormb := group_point_normal x y m ca cb b Hmodel.
case (a=idR).
+ move=> ->. rewrite op_id' /complete_add /group_point /infinity /=.
  move: Hnormb. rewrite /group_point. smt().
move=> Ha. case (b=idR).
+ move=> ->. rewrite op_id /complete_add /group_point /infinity Ha /=.
  move: Hnorma. rewrite /group_point Ha. smt().
move=> Hb.
move: (Hmodel). rewrite /complete_affine_model /affine_group_model.
move=> [[Hp [Hinj Hadd]] [Hcoords Hdbl]].
rewrite /complete_add /group_point Ha Hb /=.
case ((x b-x a) %% m <> 0).
+ move=> Hdx.
  have Hsafe : add_safe a b by move: Hcoord; rewrite /coordinate_laws /add_safe; smt().
  have Hnonzero := safe_sum_nonzero x y m a b Hcoord Hsafe.
  have Hlaw := Hadd a b Hsafe.
  have Hrange := Hcoords (a +++ b) Hnonzero.
  rewrite Hnonzero /normalize_point /=.
  move: Hlaw. simplify. move=> [Hx Hy].
  have Hxm : x (a +++ b) %% m = x (a +++ b) by smt(modz_small gt0_prime).
  have Hym : y (a +++ b) %% m = y (a +++ b) by smt(modz_small gt0_prime).
  smt().
move=> Hdx.
have Hnot : !xdiff a b by move: Hcoord; rewrite /coordinate_laws; smt().
have Hcases := notxdiff a b Hnot.
case ((y b+y a) %% m = 0).
+ move=> Hsum.
  have Htwo : (2*y a) %% m <> 0 by move: Hcoord; rewrite /coordinate_laws; smt().
  have Hab : a = -b by smt().
  have Hzero : a +++ b = idR by smt(op_eq_neg).
  rewrite Hzero. trivial.
move=> Hsum.
have Hneg : (y (-b)+y b) %% m = 0 by move: Hcoord; rewrite /coordinate_laws; smt().
have Hab : a=b by smt().
subst b.
have Hnonzero := double_nonzero a Ha.
have Hlaw := Hdbl a Ha.
have Hrange := Hcoords (a +++ a) Hnonzero.
rewrite Hnonzero /normalize_point /=.
  move: Hlaw. simplify. move=> [Hx Hy].
  have Hxm : x (a +++ a) %% m = x (a +++ a) by smt(modz_small gt0_prime).
  have Hym : y (a +++ a) %% m = y (a +++ a) by smt(modz_small gt0_prime).
  smt().
qed.

lemma complete_group_witness x y m ca cb a b :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  exists lam, complete_constraints m ca (group_point x y a) (group_point x y b)
    (group_point x y (a +++ b)) lam.
proof.
move=> Hcoord Hmodel.
have Hp : prime m by move: Hmodel; rewrite /complete_affine_model /affine_group_model; smt().
have Ha := group_point_on_curve x y m ca cb a Hmodel.
have Hb := group_point_on_curve x y m ca cb b Hmodel.
have H := complete_add_has_witness m ca cb (group_point x y a) (group_point x y b) Hp Ha Hb.
have E := complete_add_group x y m ca cb a b Hcoord Hmodel.
move: H. by rewrite E.
qed.

(* The output is a raw tuple. Its correctness and curve membership do not
   rely on assuming it encodes some abstract group element. *)
lemma complete_group_sound x y m ca cb a b r lam :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  complete_constraints m ca (group_point x y a) (group_point x y b) r lam =>
  r = group_point x y (a +++ b).
proof.
move=> Hcoord Hmodel H.
have Hp : prime m by move: Hmodel; rewrite /complete_affine_model /affine_group_model; smt().
have E := complete_constraints_sound m ca (group_point x y a) (group_point x y b) r lam Hp H.
have Egroup := complete_add_group x y m ca cb a b Hcoord Hmodel.
smt().
qed.
