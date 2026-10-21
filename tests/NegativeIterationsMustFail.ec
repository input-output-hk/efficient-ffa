require import AllCore Distr IterationProps.

(* EXPECTED FAILURE. Without 0 <= N, the admitted union bound at N = -1
   has a vacuous per-iteration hypothesis but a negative upper bound. *)
lemma negative_iterations_would_prove_false : false.
proof.
have bad := iteri_ub3 (fun (_ : unit) => ())
  (fun (_ : unit) (_ : int) => (true, ())) (dunit ()) (-1) 1%r.
smt(ge0_mu).
qed.
