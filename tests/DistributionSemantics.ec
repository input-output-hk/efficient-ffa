require import AllCore Distr.

op partial : unit distr = dscalar (1%r / 2%r) (dunit ()).

lemma partial_is_full : is_full partial.
proof.
rewrite /partial. apply dscalar_fu.
+ smt().
+ rewrite dunit_ll. smt().
+ move=> x. rewrite supp_dunit. smt().
qed.

lemma partial_is_uniform : is_uniform partial.
proof.
rewrite /partial. apply dscalar_uni.
+ rewrite dunit_ll. smt().
+ apply dunit_uni.
qed.

lemma partial_has_half_mass : weight partial = 1%r / 2%r.
proof.
rewrite /partial weight_dscalar.
+ smt().
+ rewrite dunit_ll. smt().
+ rewrite dunit_ll. smt().
qed.

lemma partial_not_lossless : ! is_lossless partial.
proof. rewrite /is_lossless partial_has_half_mass. smt(). qed.

module HalfMassSampler = {
  proc sample() : unit = {
    var x;
    x <$ partial;
    return x;
  }
}.
