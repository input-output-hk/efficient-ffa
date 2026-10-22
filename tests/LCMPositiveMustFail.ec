require import AllCore AuxResults LCMRegression.

(* LCM_pos promises nonnegativity; an included zero modulus gives zero. *)
lemma zero_modulus_is_not_positive : 0<LCM (two_moduli 6 0) 2.
proof. rewrite zero_modulus. smt(). qed.
