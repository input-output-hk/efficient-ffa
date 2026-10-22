require import AllCore IntDiv StdOrder Distr List SmallCurve SmallMSM AffineComplete.
import Ring.IntID IntOrder.
import Concrete.MultiScalarMul_Abstract_Setup Concrete.MultiScalarMul_Abstract
  Concrete.MSM_TableConstruction Concrete.MSM_RejectionBound Concrete.MSM_WindowOrder
  Concrete.MSM_CompleteCoordinates Concrete.MSM_FullCoordinates.

op bases = fun (_ : int) => F7.inzmod 1.
op windows (d : int) = fun (_ _ : int) => d.

lemma iteri_one ['a] (f : int -> 'a -> 'a) a : iteri 1 f a=f 0 a.
proof. by rewrite (@iteriS 0) 1:/# iteri0 1:/#. qed.

lemma tiny_table u : table_safe bases u =
  (F7.inzmod 1<>F7.zero /\ F7.([-]) u<>F7.zero /\ xdiff (F7.([-]) u) (F7.inzmod 1)).
proof.
rewrite /table_safe /bases expr1 /= one_mul.
have -> : (forall j, 0<=j<1 => row_safe (F7.inzmod 1) u 2)=row_safe (F7.inzmod 1) u 2 by smt().
have E := row_safeS (F7.inzmod 1) u 1 _; first trivial.
rewrite E row_safe1 /= table_entry0 /add_safe. smt().
qed.

lemma tiny_acceptance d u : construction_accepts bases (windows d) u =
  (0<=d<2 /\ F7.inzmod 1<>F7.zero /\ F7.([-]) u<>F7.zero /\ u<>F7.zero /\
    xdiff (F7.([-]) u) (F7.inzmod 1) /\
    xdiff (smul 2 u) (F7.(+) (smul d (F7.inzmod 1)) (F7.([-]) u))).
proof.
rewrite /construction_accepts tiny_table /valid_windows /windows expr1 /= one_mul.
rewrite /loop_ok /multiScalarMulLoop iteri_one /= /completeAddLoop iteri_one /=.
rewrite /perfect_table_pure /bases expr1 /= one_mul.
have Ewin : (forall (j i : int), 0<=j<1 => 0<=i<1 => 0<=d<2) <=> (0<=d<2).
+ split; last smt(). move=> H. exact (H 0 0 _ _).
  + trivial.
  + trivial.
rewrite Ewin. smt().
qed.

lemma accept_zero u : construction_accepts bases (windows 0) u =
  (F7.asint u=2 \/ F7.asint u=3 \/ F7.asint u=4 \/ F7.asint u=5).
proof.
rewrite tiny_acceptance /xdiff /px /smul /cx.
move: (cases7 u). move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite -!F7.asint_eq ?F7.zeroE !F7.addE !F7.mulE !F7.oppE !F7.inzmodK /=; smt().
qed.

lemma accept_one u : construction_accepts bases (windows 1) u =
  (F7.asint u=2 \/ F7.asint u=3 \/ F7.asint u=4).
proof.
rewrite tiny_acceptance /xdiff /px /smul /cx.
move: (cases7 u). move=> [->|[->|[->|[->|[->|[->|->]]]]]];
rewrite -!F7.asint_eq ?F7.zeroE !F7.addE !F7.mulE !F7.oppE !F7.inzmodK /=; smt().
qed.

lemma seven_indices : range 0 7 = [0;1;2;3;4;5;6].
proof.
rewrite (range_ltn 0 7) 1:/# /= (range_ltn 1 7) 1:/# /=
  (range_ltn 2 7) 1:/# /= (range_ltn 3 7) 1:/# /=
  (range_ltn 4 7) 1:/# /= (range_ltn 5 7) 1:/# /=
  (range_ltn 6 7) 1:/# /= range_geq 1:/#. trivial.
qed.

lemma scalar_zero_rejection :
  mu F7.DZmodP.dunifin (fun u => !construction_accepts bases (windows 0) u)=3%r/7%r.
proof.
rewrite F7.DZmodP.dunifinE F7.DZmodP.cardE /F7.DZmodP.Support.enum seven_indices /=.
rewrite !accept_zero !F7.inzmodK /=. trivial.
qed.

lemma scalar_one_rejection :
  mu F7.DZmodP.dunifin (fun u => !construction_accepts bases (windows 1) u)=4%r/7%r.
proof.
rewrite F7.DZmodP.dunifinE F7.DZmodP.cardE /F7.DZmodP.Support.enum seven_indices /=.
rewrite !accept_one !F7.inzmodK /=. trivial.
qed.

lemma encoding_generator : group_point cx cy (F7.inzmod 1)=(false,0,1).
proof. rewrite /group_point /cx /cy -F7.asint_eq F7.zeroE !F7.inzmodK /=. trivial. qed.
lemma encoding_offset : group_point cx cy (F7.inzmod 2)=(false,1,3).
proof. rewrite /group_point /cx /cy -F7.asint_eq F7.zeroE !F7.inzmodK /=. trivial. qed.

lemma digit_result d : multiScalarMul_Simpl (windows d) bases 1 1=smul d (F7.inzmod 1).
proof.
rewrite /multiScalarMul_Simpl /windows /bases iteri_one /= iteri_one /= expr0 /= !op_id'. trivial.
qed.

lemma scalar_one_full_witness :
  little_endian_full_constraints 5 2 (fun (_ : int) => (false,0,1)) (windows 1)
    (false,1,3) (false,0,1).
proof.
have Ha : construction_accepts bases (windows 1) (F7.inzmod 2)
  by rewrite accept_one F7.inzmodK /=.
have H := full_msm_constraints_exists cx cy 5 2 1 bases (windows 1) (F7.inzmod 2)
  coordinates complete_model Ha.
move: H. rewrite digit_result one_mul /bases encoding_generator encoding_offset.
by rewrite /little_endian_full_constraints /reverse_windows /windows /=.
qed.

lemma scalar_zero_full_witness :
  little_endian_full_constraints 5 2 (fun (_ : int) => (false,0,1)) (windows 0)
    (false,1,3) infinity.
proof.
have Ha : construction_accepts bases (windows 0) (F7.inzmod 2)
  by rewrite accept_zero F7.inzmodK /=.
have H := full_msm_constraints_exists cx cy 5 2 1 bases (windows 0) (F7.inzmod 2)
  coordinates complete_model Ha.
move: H. rewrite digit_result zero_mul /bases encoding_generator encoding_offset /group_point /=.
by rewrite /little_endian_full_constraints /reverse_windows /windows /=.
qed.

lemma scalar_one_wrong_output_rejected :
  !little_endian_full_constraints 5 2 (fun (_ : int) => (false,0,1)) (windows 1)
    (false,1,3) infinity.
proof.
have H := full_msm_constraints_sound cx cy 5 2 1 bases (windows 1) (F7.inzmod 2)
  infinity coordinates complete_model.
move: H. rewrite digit_result one_mul /bases encoding_generator encoding_offset.
rewrite /little_endian_full_constraints /reverse_windows /windows /infinity /=. smt().
qed.

lemma scalar_one_program_rejection &mem :
  Pr[SampledLittleEndianMSM.run(bases,windows 1) @ &mem : !res.`1]=4%r/7%r.
proof.
rewrite concrete_program_rejection /little_endian_full_constraints /reverse_windows /windows /=.
have E : (fun u => !exists r,
    full_msm_constraints 5 2 (fun j => group_point cx cy (bases j))
      (fun (_ _ : int) => 1) (group_point cx cy u) r) =
  (fun u => !construction_accepts bases (windows 1) u).
+ apply fun_ext=> u. rewrite (full_witness_iff cx cy 5 2 1 bases (windows 1) u coordinates complete_model).
  trivial.
rewrite E. exact scalar_one_rejection.
qed.
