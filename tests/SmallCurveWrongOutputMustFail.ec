require import SmallCurveInstance SmallCurve SmallMSM AffineComplete.
import Concrete.MSM_FullCoordinates.

(* The concrete instance must not make a false full witness provable. *)
lemma wrong_result_cannot_be_proved :
  little_endian_full_constraints 5 2 (fun (_ : int) => (false,0,1)) (windows 1)
    (false,1,3) infinity.
proof. smt(scalar_one_wrong_output_rejected). qed.
