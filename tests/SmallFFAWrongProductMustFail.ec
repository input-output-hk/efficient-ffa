require import AllCore SmallFFA.
import Concrete.FFA.BN.

(* A fully instantiated constraint system must not accept 1*3=0. *)
lemma wrong_product_accepted :
  exists u v, accepts (bn_ofint 1) (bn_ofint 3) (bn_ofint 0) u v.
proof.
have H := encoded_iff 1 3 0 _ _ _; try trivial.
smt().
qed.
