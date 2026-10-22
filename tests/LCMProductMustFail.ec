require import AllCore AuxResults LCMRegression.

(* Shared factors cannot be counted twice in the combined modulus. *)
lemma product_is_not_lcm : LCM (two_moduli 4 6) 2=4*6.
proof. rewrite noncoprime_moduli. smt(). qed.
