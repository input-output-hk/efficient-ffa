require import AllCore Int IntDiv StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract
  MSM_TableConstruction MSM_WithTable MSM_RejectionBound MSM_TableConstraints.

(* The core consumes the most significant window first. The paper and
   Lean artifact describe least-significant-window-first input arrays. *)
op reverse_windows n (s : int -> int -> int) = fun j i => s j (n-1-i).

lemma reverse_windows_involutive n s :
  reverse_windows n (reverse_windows n s) = s.
proof. rewrite /reverse_windows. apply fun_ext=> j. apply fun_ext=> i. smt(). qed.

lemma reverse_windows_valid s :
  valid_windows (reverse_windows T s) <=> valid_windows s.
proof.
rewrite /valid_windows /reverse_windows. split.
+ move=> H j i Hj Hi. have Hidx : 0 <= T-1-i < T by smt().
  have Hval := H j (T-1-i) Hj Hidx. smt().
+ move=> H j i Hj Hi. apply (H j (T-1-i)); smt().
qed.

(* Independent little-endian specification: weight of input window i is
   2^(w*i), rather than the core's 2^(w*(n-1-i)). *)
op msm_little_endian s P n count =
  iteri n (fun i acc => acc +++
    iteri count (fun j part => part +++
      (2^(w*i) * s j i) *** (P j)) idR) idR.

lemma group_sum_shift : forall n, 0 <= n => forall (f : int -> R),
  iteri (n+1) (fun i acc => acc +++ f i) idR =
  f 0 +++ iteri n (fun i acc => acc +++ f (i+1)) idR.
proof.
apply intind.
+ move=> f. rewrite iteriS 1:/# /= !iteri0 1,2:/# /=. smt(op_id op_id').
+ move=> n Hn IH f.
  rewrite iteriS 1:/# /= (IH f).
  rewrite iteriS 1:/# /=. smt(op_assoc).
qed.

lemma group_sum_reverse : forall n, 0 <= n => forall (f : int -> R),
  iteri n (fun i acc => acc +++ f (n-1-i)) idR =
  iteri n (fun i acc => acc +++ f i) idR.
proof.
apply intind.
+ move=> f. by rewrite !iteri0 1,2:/#.
+ move=> n Hn IH f.
  rewrite iteriS 1:/# /=.
  have E : (fun i acc => acc +++ f (n+1-1-i)) =
    (fun i acc => acc +++ (fun k => f (k+1)) (n-1-i)).
  + apply fun_ext=> i. apply fun_ext=> acc. smt().
  rewrite E (IH (fun k => f (k+1))) /=.
  rewrite group_sum_shift 1:/#.
  smt(op_comm).
qed.

lemma reversed_core_spec s P n count : 0 <= n =>
  multiScalarMul_Simpl (reverse_windows n s) P n count =
  msm_little_endian s P n count.
proof.
move=> Hn. rewrite /multiScalarMul_Simpl /reverse_windows /msm_little_endian.
apply (group_sum_reverse n Hn (fun i =>
  iteri count (fun j part => part +++ (2^(w*i)*s j i) *** (P j)) idR)).
qed.

(* Reindexing is a function view: no extra group operations or constraints.
   The first core iteration reads input T-1; the last reads input 0. *)
module LittleEndianMSM = {
  proc with_table(P : int -> R, s : int -> int -> int, U : R,
                  table : int -> int -> R) = {
    var result : bool * R;
    result <@ ConstructedMSM.with_table(P,reverse_windows T s,U,table);
    return result;
  }

  proc run(P : int -> R, s : int -> int -> int, U : R) = {
    var result : bool * R;
    result <@ ConstructedMSM.run(P,reverse_windows T s,U);
    return result;
  }
}.

module SampledLittleEndianMSM = {
  proc run(P : int -> R, s : int -> int -> int) = {
    var result : bool * R;
    result <@ SampledConstructedMSM.run(P,reverse_windows T s);
    return result;
  }
}.

lemma little_endian_msm_soundness P s U :
  phoare [LittleEndianMSM.run : arg = (P,s,U) ==>
    res.`1 => res.`2 = msm_little_endian s P T l] = 1%r.
proof.
proc. ecall (constructed_msm_soundness P (reverse_windows T s) U).
skip. smt(reversed_core_spec param_pos).
qed.

lemma sampled_little_endian_soundness P s :
  phoare [SampledLittleEndianMSM.run : arg = (P,s) ==>
    res.`1 => res.`2 = msm_little_endian s P T l] = 1%r.
proof.
proc. ecall (sampled_constructed_msm_soundness P (reverse_windows T s)).
skip. smt(reversed_core_spec param_pos).
qed.

lemma sampled_little_endian_equiv :
  equiv [SampledLittleEndianMSM.run ~ SampledConstructedMSM.run :
    P{1}=P{2} /\ s{2}=reverse_windows T s{1} ==> ={res}].
proof.
proc*. inline SampledLittleEndianMSM.run. wp.
call (_: true).
+ sim.
+ auto.
qed.

lemma little_endian_rejection_bound P s &m :
  nonzero_bases P => valid_windows s =>
  scalar_invertible (2^w-1) => scalar_invertible l =>
  Pr[SampledLittleEndianMSM.run(P,s) @ &m : !res.`1]
  <= (1 + l*(2^w+1) + 2*T*l)%r / group_cardinality%r.
proof.
move=> HP Hs Htable Hinitial.
have -> : Pr[SampledLittleEndianMSM.run(P,s) @ &m : !res.`1] =
  Pr[SampledConstructedMSM.run(P,reverse_windows T s) @ &m : !res.`1].
+ byequiv sampled_little_endian_equiv; smt().
apply sampled_rejection_bound_cardinality; smt(reverse_windows_valid).
qed.

lemma little_endian_success_bound P s &m :
  nonzero_bases P => valid_windows s =>
  scalar_invertible (2^w-1) => scalar_invertible l =>
  1%r - (1 + l*(2^w+1) + 2*T*l)%r / group_cardinality%r
  <= Pr[SampledLittleEndianMSM.run(P,s) @ &m : res.`1].
proof.
move=> HP Hs Htable Hinitial.
have -> : Pr[SampledLittleEndianMSM.run(P,s) @ &m : res.`1] =
  Pr[SampledConstructedMSM.run(P,reverse_windows T s) @ &m : res.`1].
+ byequiv sampled_little_endian_equiv; smt().
apply sampled_success_bound_cardinality; smt(reverse_windows_valid).
qed.

lemma little_endian_constraint_table_soundness x y m P s U table slopes :
  coordinate_laws x y m => safe_constraint_correct x y m =>
  accepted_tables x y m P U table slopes => valid_windows s =>
  phoare [LittleEndianMSM.with_table : arg = (P,s,U,table) ==>
    res.`1 => res.`2 = msm_little_endian s P T l] = 1%r.
proof.
move=> Hcoord Hcorrect Hrows Hwindows.
have Hrev : valid_windows (reverse_windows T s) by smt(reverse_windows_valid).
proc. ecall (constraint_table_msm_soundness x y m P (reverse_windows T s) U table slopes
  Hcoord Hcorrect Hrows Hrev).
skip. smt(reversed_core_spec param_pos).
qed.
