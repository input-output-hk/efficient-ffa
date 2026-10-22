require import AllCore IntDiv StdOrder SmallFFA.
import Ring.IntID IntOrder.
import Concrete.FFA Concrete.FFA.BN.

lemma native_encoded a b c u :
  NativeLHS (-1) u (bn_ofint a) (bn_ofint b) (bn_ofint c) =
  (a %% 4)*(b %% 4) + 4*(a %% 4)*(b %/ 4 %% 4)
  +4*(a %/ 4 %% 4)*(b %% 4)+3*(a %/ 4 %% 4)*(b %/ 4 %% 4)
  -(c %% 4)-4*(c %/ 4 %% 4)-(u-1)*13.
proof.
rewrite /NativeLHS base_four !sigma_two /= !sigma_two /=
  !encoding_digit //=; ring.
qed.

lemma auxiliary_encoded a b c u v :
  AuxLHS 2 v (-1) (-10) u (bn_ofint a) (bn_ofint b) (bn_ofint c) =
  (a %% 4)*(b %% 4)+(a %/ 4 %% 4)*(b %/ 4 %% 4)-(c %% 4)-u-1-(v-10)*2.
proof.
rewrite /AuxLHS base_four !sigma_two /= !sigma_two /=
  !encoding_digit //=; ring.
qed.

lemma seven_times_eight : accepts (bn_ofint 7) (bn_ofint 8) (bn_ofint 4) 3 9.
proof. by rewrite /accepts native_encoded auxiliary_encoded /=. qed.

lemma zero_product : accepts (bn_ofint 0) (bn_ofint 15) (bn_ofint 0) 1 9.
proof. by rewrite /accepts native_encoded auxiliary_encoded /=. qed.

lemma maximal_limbs : accepts (bn_ofint 15) (bn_ofint 15) (bn_ofint 4) 9 14.
proof. by rewrite /accepts native_encoded auxiliary_encoded /=. qed.

(* Inputs and outputs need not be canonical representatives modulo 13. *)
lemma noncanonical_input : accepts (bn_ofint 13) (bn_ofint 7) (bn_ofint 0) 5 10.
proof. by rewrite /accepts native_encoded auxiliary_encoded /=. qed.

lemma noncanonical_output : accepts (bn_ofint 7) (bn_ofint 2) (bn_ofint 14) 1 11.
proof. by rewrite /accepts native_encoded auxiliary_encoded /=. qed.

lemma completeness_for_all_residues a b : 0<=a<13 => 0<=b<13 =>
  exists u v, accepts (bn_ofint a) (bn_ofint b) (bn_ofint (a*b %% 13)) u v.
proof.
move=> Ha Hb. rewrite encoded_iff 1:/# 1:/#.
+ smt(modz_ge0 ltz_pmod).
by rewrite modz_mod.
qed.

(* The wrong equation 1*3=0 passes the native constraint with a bounded U. *)
lemma native_only_false_acceptance :
  0<=11<16 /\ NativeLHS (-1) 11 (bn_ofint 1) (bn_ofint 3) (bn_ofint 0) = -127 /\
  NativeLHS (-1) 11 (bn_ofint 1) (bn_ofint 3) (bn_ofint 0) %% 127=0 /\
  1*3 %% 13 <> 0.
proof. by rewrite !native_encoded /=. qed.

(* Dropping V's range permits both equations to wrap by the native modulus. *)
lemma unbounded_auxiliary_false_acceptance :
  AuxLHS 2 69 (-1) (-10) 11 (bn_ofint 1) (bn_ofint 3) (bn_ofint 0) = -127 /\
  AuxLHS 2 69 (-1) (-10) 11 (bn_ofint 1) (bn_ofint 3) (bn_ofint 0) %% 127=0 /\
  !(0<=69<32).
proof. by rewrite !auxiliary_encoded /=. qed.

lemma bounded_constraints_reject_false_product u v :
  !accepts (bn_ofint 1) (bn_ofint 3) (bn_ofint 0) u v.
proof.
apply/negP=> H. have E := concrete_sound _ _ _ _ _ H.
move: E. by rewrite !encoding_value /=.
qed.

lemma reversed_limbs_change_value :
  bn (pair_init (fun i => if i=0 then Word.of_int 1 else Word.of_int 3))=13 /\
  bn (pair_init (fun i => if i=0 then Word.of_int 3 else Word.of_int 1))=7.
proof.
rewrite (@bnkS 1) 1:/# (@bnkS 1) 1:/# !bnk1 /dig /pair_get /pair_init /=. trivial.
qed.
