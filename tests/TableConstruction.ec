require import AllCore Int StdOrder.
require import MultiScalarMul_Abstract_Setup MultiScalarMul_Abstract MSM_TableConstruction.

(* V = 2P forces the third table entry to be the identity. *)
lemma two_p_row_unsafe P : ! row_safe P (2 *** P) 4.
proof.
have H := table_entry_eq_mul P (2 *** P) 2 0.
rewrite /row_safe. smt(zero_mul).
qed.

lemma two_p_builder_rejects P :
 phoare [TableBuilder.row : arg = (P, 2 *** P, 4) ==> !res.`1] = 1%r.
proof.
conseq (table_row_spec P (2 *** P) 4 _); smt(two_p_row_unsafe).
qed.

lemma zero_point_builder_rejects V b : 0 < b =>
 phoare [TableBuilder.row : arg = (idR, V, b) ==> !res.`1] = 1%r.
proof.
move=> Hb. conseq (table_row_spec idR V b Hb); rewrite /row_safe; smt().
qed.

lemma admissible_row_builder_succeeds P V b :
 0 < b => row_admissible P V b =>
 phoare [TableBuilder.row : arg = (P,V,b) ==>
  res.`1 /\ forall k, 0 <= k < b =>
    res.`2 k = table_entry P V k] = 1%r.
proof.
move=> Hb Hadmissible. conseq (table_row_spec P V b Hb); smt(row_admissible_safe).
qed.
