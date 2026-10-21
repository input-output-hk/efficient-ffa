require import AllCore Distr DistributionSemantics.

(* Full support and uniformity must not discharge a losslessness obligation. *)
lemma half_mass_sampler_lossless : islossless HalfMassSampler.sample.
proof.
proc. rnd. skip.
smt(partial_is_full partial_is_uniform).
qed.
