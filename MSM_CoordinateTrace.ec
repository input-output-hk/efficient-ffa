require import AllCore Int IntDiv StdOrder.
require import AffineAddition AffineComplete MSM_CompleteCoordinates.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract IterationProps
  MSM_TableConstruction MSM_TableConstraints MSM_CoordinateWitnesses.
import Ring.IntID IntOrder.

op complete_step m ca a b r = exists lam, complete_constraints m ca a b r lam.
op coordinate_safe m (a b : coordinate_point) =
  !a.`1 /\ !b.`1 /\ (b.`2-a.`2) %% m <> 0.
op incomplete_step m (a b r : coordinate_point) =
  !a.`1 /\ !b.`1 /\ !r.`1 /\ point_bounded m r /\
  exists lam, 0 <= lam < m /\ affine_equations m a.`2 a.`3 b.`2 b.`3 r.`2 r.`3 lam.
op guarded_step m a b r = coordinate_safe m a b /\ incomplete_step m a b r.
op negate_point m (a : coordinate_point) : coordinate_point =
  if a.`1 then infinity else (false,a.`2 %% m,(-a.`3) %% m).

lemma group_point_flag x y a : (group_point x y a).`1 = (a=idR).
proof. by rewrite /group_point /infinity; case (a=idR). qed.

lemma group_point_bounded x y m ca cb a : complete_affine_model x y m ca cb =>
  point_bounded m (group_point x y a).
proof.
move=> H. rewrite /point_bounded /group_point /infinity.
case (a=idR); first smt(). move=> Ha.
move: H. rewrite /complete_affine_model. smt().
qed.

lemma complete_step_group x y m ca cb a b r :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  (complete_step m ca (group_point x y a) (group_point x y b) r <=>
    r=group_point x y (a +++ b)).
proof.
move=> Hc Hm. rewrite /complete_step. split.
+ move=> [lam H]. exact (complete_group_sound x y m ca cb a b r lam Hc Hm H).
+ move=> ->. exact (complete_group_witness x y m ca cb a b Hc Hm).
qed.

lemma coordinate_safe_group x y m a b : coordinate_laws x y m =>
  (coordinate_safe m (group_point x y a) (group_point x y b) <=> add_safe a b).
proof. rewrite /coordinate_laws /coordinate_safe /group_point /infinity /add_safe. smt(). qed.

lemma incomplete_as_complete m ca a b r : coordinate_safe m a b =>
  (incomplete_step m a b r <=> complete_step m ca a b r).
proof. rewrite /coordinate_safe /incomplete_step /complete_step /complete_constraints. smt(). qed.

lemma guarded_step_group x y m ca cb a b r :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  (guarded_step m (group_point x y a) (group_point x y b) r <=>
    add_safe a b /\ r=group_point x y (a +++ b)).
proof.
move=> Hc Hm. rewrite /guarded_step.
have Hsafe := coordinate_safe_group x y m a b Hc.
have Hcomplete := complete_step_group x y m ca cb a b r Hc Hm.
have Hinc := incomplete_as_complete m ca (group_point x y a) (group_point x y b) r.
smt().
qed.

lemma negate_point_group x y m ca cb a :
  coordinate_laws x y m => complete_affine_model x y m ca cb =>
  negate_point m (group_point x y a) = group_point x y (-a).
proof.
move=> Hc Hm.
case (a=idR).
+ move=> ->. have E : -idR=idR by smt(op_inv op_id').
  by rewrite /negate_point /group_point /infinity E /=.
move=> Ha. have Hneg : -a <> idR by smt(op_inv op_id).
have Hlaws : (x (-a)-x a) %% m=0 /\ (y (-a)+y a) %% m=0
  by move: Hc; rewrite /coordinate_laws; smt().
have Hbounds := group_point_bounded x y m ca cb (-a) Hm.
move: Hbounds. rewrite /point_bounded /group_point Hneg /=. move=> Hbounds.
have Hx : eqm m (x (-a)) (x a) by smt(congr_zero).
have Hy : eqm m (y (-a)) (-y a).
+ rewrite -congr_zero. have E : y (-a)-(-y a)=y (-a)+y a by ring.
  rewrite E. smt().
rewrite Ha /negate_point /=.
smt(modz_small).
qed.

(* Finite traces contain raw coordinate tuples, with an existential slope
   per edge. Intermediate group membership is never assumed. *)
op coordinate_chain n (step : int -> coordinate_point -> coordinate_point -> bool)
    start finish = 0 <= n /\ exists (nodes : int -> coordinate_point),
  nodes 0=start /\ nodes n=finish /\
  forall i, 0 <= i < n => step i (nodes i) (nodes (i+1)).

lemma coordinate_chain_exists (encode : R -> coordinate_point) step f n a :
  0 <= n =>
  (forall i v, 0 <= i < n => step i (encode v) (encode (f i v))) =>
  coordinate_chain n step (encode a) (encode (iteri n f a)).
proof.
move=> Hn Hstep. rewrite /coordinate_chain. split; first exact Hn.
exists (fun i => encode (iteri i f a)). simplify. split; first by rewrite iteri0.
move=> i Hi. rewrite iteriS 1:/# /=. apply Hstep. exact Hi.
qed.

lemma coordinate_chain_sound (encode : R -> coordinate_point) step f n a r :
  (forall i v z, 0 <= i < n => step i (encode v) z => z=encode (f i v)) =>
  coordinate_chain n step (encode a) r => r=encode (iteri n f a).
proof.
move=> Hstep. rewrite /coordinate_chain. move=> [Hn [nodes [Hfirst [Hlast Hedges]]]].
have Hind : forall k, 0 <= k => k <= n => nodes k=encode (iteri k f a).
+ apply intind.
  + move=> Hk. by rewrite iteri0.
  + move=> k Hk IH Hkn.
    have Hprev := IH _; first smt().
    have H := Hedges k _; first smt().
    move: H. rewrite Hprev. move=> H.
    rewrite iteriS 1:/# /=. apply (Hstep k (iteri k f a) (nodes (k+1))); smt().
smt().
qed.

op doubling_trace m ca n a r =
  coordinate_chain n (fun _ p q => complete_step m ca p p q) a r.
op multiple_trace m ca n a r =
  coordinate_chain n (fun _ p q => complete_step m ca p a q) infinity r.

lemma doubling_iter a : forall n, 0 <= n =>
  iteri n (fun _ p => p +++ p) a = 2^n *** a.
proof.
apply intind; simplify.
+ by rewrite iteri0 1:/# expr0 one_mul.
+ move=> n Hn IH. rewrite iteriS 1:/# /= IH -nplus_dist exprS 1:/#.
  congr. ring.
qed.

lemma doubling_trace_group x y m ca cb n a r :
  coordinate_laws x y m => complete_affine_model x y m ca cb => 0 <= n =>
  (doubling_trace m ca n (group_point x y a) r <=> r=group_point x y (2^n *** a)).
proof.
move=> Hc Hm Hn. rewrite /doubling_trace. split.
+ move=> H. have Hsound := coordinate_chain_sound (group_point x y) _
    (fun _ p => p +++ p) n a r _ H.
  + move=> i v z Hi Hstep. smt(complete_step_group).
  + move: Hsound. by rewrite doubling_iter.
+ move=> ->. rewrite -(doubling_iter a n Hn).
  apply (coordinate_chain_exists (group_point x y) _ (fun _ p => p +++ p) n a Hn).
  move=> i v Hi. smt(complete_step_group).
qed.

lemma multiple_trace_group x y m ca cb n a r :
  coordinate_laws x y m => complete_affine_model x y m ca cb => 0 <= n =>
  (multiple_trace m ca n (group_point x y a) r <=> r=group_point x y (n *** a)).
proof.
move=> Hc Hm Hn. rewrite /multiple_trace.
have Hid : infinity=group_point x y idR by rewrite /group_point.
have Heq : iteri n (fun (_ : int) p => p +++ a) idR=n *** a by apply iteriZZZ.
rewrite Hid. split.
+ move=> H. have Hsound := coordinate_chain_sound (group_point x y) _
    (fun _ p => p +++ a) n idR r _ H.
  + move=> i v z Hi Hstep. smt(complete_step_group).
  + smt().
+ move=> ->. rewrite -Heq. apply (coordinate_chain_exists (group_point x y) _ (fun _ p => p +++ a) n idR Hn).
  move=> i v Hi. smt(complete_step_group).
qed.

lemma coordinate_chain0 step a r : coordinate_chain 0 step a r <=> r=a.
proof.
rewrite /coordinate_chain. split; first smt().
move=> ->. split; first smt(). exists (fun (_ : int) => a). smt().
qed.

lemma coordinate_chainS n step a r : 0 <= n =>
  (coordinate_chain (n+1) step a r <=>
    exists mid, coordinate_chain n step a mid /\ step n mid r).
proof.
move=> Hn. rewrite /coordinate_chain. split.
+ move=> [_ [nodes [H0 [Hlast Hsteps]]]]. exists (nodes n). split.
  + split; first exact Hn. exists nodes. smt().
  + smt().
+ move=> [mid [[_ [nodes [H0 [Hlast Hsteps]]]] Hstep]].
  split; first smt(). exists (fun i => if i=n+1 then r else nodes i).
  split; first smt(). split; first smt(). move=> i Hi. simplify.
  case (i=n); smt().
qed.

op addition_trace m n (table : int -> coordinate_point) a r =
  coordinate_chain n (fun j p q => guarded_step m p (table j) q) a r.
op group_additions n (table : int -> R) a =
  iteri n (fun j (acc : bool * R) =>
    (acc.`1 /\ xdiff acc.`2 (table j),acc.`2 +++ table j)) (true,a).

lemma group_additionsS n table a : 0 <= n =>
  group_additions (n+1) table a =
  ((group_additions n table a).`1 /\ xdiff (group_additions n table a).`2 (table n),
    (group_additions n table a).`2 +++ table n).
proof. move=> Hn. by rewrite /group_additions iteriS 1://. qed.

lemma addition_trace_group x y m ca cb table a :
  coordinate_laws x y m => complete_affine_model x y m ca cb => a<>idR =>
  forall n, 0 <= n => (forall j, 0 <= j < n => table j<>idR) =>
  let result=group_additions n table a in
  (result.`1 => result.`2<>idR) /\
  forall r, addition_trace m n (fun j => group_point x y (table j)) (group_point x y a) r
    <=> result.`1 /\ r=group_point x y result.`2.
proof.
move=> Hc Hm Ha. apply intind; simplify.
+ move=> Htable. rewrite /group_additions iteri0 1:/# /=.
  split; first exact Ha. move=> r. by rewrite /addition_trace coordinate_chain0.
+ move=> n Hn IH Htable.
  have [Hprev_nonzero Hprev] := IH _; first smt().
  rewrite group_additionsS 1:// /=.
  split.
  + move=> [Hflag Hdiff]. have Hsafe : add_safe (group_additions n table a).`2 (table n)
      by rewrite /add_safe; smt().
    smt(safe_sum_nonzero).
  + move=> r. rewrite /addition_trace coordinate_chainS 1://. split.
    + move=> [mid [Hchain Hedge]].
      have HC : addition_trace m n (fun j => group_point x y (table j)) (group_point x y a) mid by exact Hchain.
      have HI := Hprev mid.
      have Hprefix : (group_additions n table a).`1 /\ mid=group_point x y (group_additions n table a).`2 by smt().
      have [Hflag Hmid] := Hprefix.
      move: Hedge. simplify. rewrite Hmid (guarded_step_group x y m ca cb (group_additions n table a).`2 (table n) r Hc Hm) /add_safe. smt().
    + move=> [[Hflag Hdiff] Hr]. exists (group_point x y (group_additions n table a).`2). split.
      + have HC : addition_trace m n (fun j => group_point x y (table j)) (group_point x y a)
          (group_point x y (group_additions n table a).`2) by smt().
        exact HC.
      + simplify. rewrite (guarded_step_group x y m ca cb (group_additions n table a).`2 (table n) r Hc Hm) /add_safe. smt().
qed.

op window_trace m ca (table : int -> int -> coordinate_point) (s : int -> int -> int) (i : int) a r =
  exists d, doubling_trace m ca w a d /\
    addition_trace m l (fun j => table j (s j i)) d r.
op msm_loop_trace m ca n table s a r =
  coordinate_chain n (fun i p q => window_trace m ca table s i p q) a r.

lemma window_trace_group x y m ca cb table s i a :
  coordinate_laws x y m => complete_affine_model x y m ca cb => a<>idR =>
  (forall j, 0 <= j < l => table j (s j i)<>idR) =>
  let result=completeAddLoop l table s i (2^w *** a) in
  (result.`1 => result.`2<>idR) /\
  forall r, window_trace m ca (fun j k => group_point x y (table j k)) s i (group_point x y a) r
    <=> result.`1 /\ r=group_point x y result.`2.
proof.
move=> Hc Hm Ha Htable. simplify.
have Hw : 0 <= w by smt(param_pos).
have Hl : 0 <= l by smt(param_pos).
have Hd : 2^w *** a <> idR by apply no_order_two_elems; smt(param_pos).
have [Hnz Htrace] := addition_trace_group x y m ca cb (fun j => table j (s j i))
  (2^w *** a) Hc Hm Hd l Hl Htable.
have E : group_additions l (fun j => table j (s j i)) (2^w *** a) =
  completeAddLoop l table s i (2^w *** a) by rewrite /group_additions /completeAddLoop.
move: Hnz Htrace. rewrite E. move=> Hnz Htrace.
split; first exact Hnz. move=> r. rewrite /window_trace. split.
+ move=> [d [Hdoub Hadd]].
  have Ed : d=group_point x y (2^w *** a) by smt(doubling_trace_group).
  have H := Htrace r. move: Hadd. rewrite Ed. smt().
+ move=> H. exists (group_point x y (2^w *** a)). split.
  + smt(doubling_trace_group).
  + have H' := Htrace r. smt().
qed.

lemma msm_loopS n table s a : 0 <= n =>
  multiScalarMulLoop (n+1) l table s a w =
  let prev=multiScalarMulLoop n l table s a w in
  let next=completeAddLoop l table s n (2^w *** prev.`2) in
  (prev.`1 /\ next.`1,next.`2).
proof. move=> Hn. by rewrite /multiScalarMulLoop iteriS 1://. qed.

lemma msm_loop_trace_group x y m ca cb table s a :
  coordinate_laws x y m => complete_affine_model x y m ca cb => a<>idR =>
  forall n, 0 <= n =>
  (forall i j, 0 <= i < n => 0 <= j < l => table j (s j i)<>idR) =>
  let result=multiScalarMulLoop n l table s a w in
  (result.`1 => result.`2<>idR) /\
  forall r, msm_loop_trace m ca n (fun j k => group_point x y (table j k)) s (group_point x y a) r
    <=> result.`1 /\ r=group_point x y result.`2.
proof.
move=> Hc Hm Ha. apply intind; simplify.
+ move=> Htable. rewrite /multiScalarMulLoop iteri0 1:/# /=.
  split; first exact Ha. move=> r. by rewrite /msm_loop_trace coordinate_chain0.
+ move=> n Hn IH Htable.
  have [Hprev_nonzero Hprev] := IH _; first smt().
  rewrite msm_loopS 1:// /=. split.
  + move=> [Hflag Hnext].
    have Hnonzero := Hprev_nonzero Hflag.
    have [Hnz Hwindow] := window_trace_group x y m ca cb table s n
      (multiScalarMulLoop n l table s a w).`2 Hc Hm Hnonzero _; first smt().
    smt().
  + move=> r. rewrite /msm_loop_trace coordinate_chainS 1://. split.
    + move=> [mid [Hchain Hedge]].
      have HC : msm_loop_trace m ca n (fun j k => group_point x y (table j k)) s (group_point x y a) mid by exact Hchain.
      have HI := Hprev mid.
      have Hflag : (multiScalarMulLoop n l table s a w).`1 by smt().
      have Hmid : mid=group_point x y (multiScalarMulLoop n l table s a w).`2 by smt().
      have [Hnz Hwindow] := window_trace_group x y m ca cb table s n
        (multiScalarMulLoop n l table s a w).`2 Hc Hm (Hprev_nonzero Hflag) _; first smt().
      have HW := Hwindow r. move: Hedge. simplify. rewrite Hmid. smt().
    + move=> [[Hflag Hnext] Hr].
      exists (group_point x y (multiScalarMulLoop n l table s a w).`2). split.
      + have HC : msm_loop_trace m ca n (fun j k => group_point x y (table j k)) s
          (group_point x y a) (group_point x y (multiScalarMulLoop n l table s a w).`2) by smt().
        exact HC.
      + have [Hnz Hwindow] := window_trace_group x y m ca cb table s n
          (multiScalarMulLoop n l table s a w).`2 Hc Hm (Hprev_nonzero Hflag) _; first smt().
        simplify. have HW := Hwindow r. smt().
qed.

lemma coordinate_chain_ext n step1 step2 a r :
  (forall i p q, 0 <= i < n => step1 i p q = step2 i p q) =>
  coordinate_chain n step1 a r = coordinate_chain n step2 a r.
proof. rewrite /coordinate_chain. smt(). qed.

lemma addition_trace_ext m n table1 table2 a r :
  (forall j, 0 <= j < n => table1 j=table2 j) =>
  addition_trace m n table1 a r = addition_trace m n table2 a r.
proof.
move=> H. rewrite /addition_trace. apply coordinate_chain_ext. smt().
qed.

lemma window_trace_ext m ca table1 table2 s i a r :
  (forall j, 0 <= j < l => table1 j (s j i)=table2 j (s j i)) =>
  window_trace m ca table1 s i a r = window_trace m ca table2 s i a r.
proof.
move=> H. rewrite /window_trace.
have HE : forall d, addition_trace m l (fun j => table1 j (s j i)) d r =
  addition_trace m l (fun j => table2 j (s j i)) d r.
+ move=> d. apply addition_trace_ext. exact H.
smt().
qed.

lemma msm_loop_trace_ext m ca n table1 table2 s a r :
  (forall i j, 0 <= i < n => 0 <= j < l => table1 j (s j i)=table2 j (s j i)) =>
  msm_loop_trace m ca n table1 s a r = msm_loop_trace m ca n table2 s a r.
proof.
move=> H. rewrite /msm_loop_trace. apply coordinate_chain_ext.
move=> i p q Hi. simplify. apply window_trace_ext. smt().
qed.
