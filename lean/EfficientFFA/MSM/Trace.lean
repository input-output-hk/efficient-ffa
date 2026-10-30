import EfficientFFA.MSM.Chains

namespace EfficientFFA.MSM
open EllipticCurve

/-- Supplied coordinate witnesses. Functions are inspected only within their stated bounds. -/
structure CoordinateTrace (K : Type*) where
  seed : Coordinates K
  offset : Coordinates K
  offsetChain : ℕ → Encoded K
  initialChain : ℕ → Encoded K
  table : ℕ → ℕ → Coordinates K
  boundary : ℕ → Coordinates K
  doubles : ℕ → ℕ → Coordinates K
  rows : ℕ → ℕ → Coordinates K
  output : Encoded K

end EfficientFFA.MSM

namespace EfficientFFA.EllipticCurve.Curve
open MSM
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

/-- Coordinate-only acceptance for the whole trace, in window processing order.
Group meanings of the supplied values are conclusions, not acceptance premises. -/
structure TraceAccepts (w l n : ℕ) (bases : ℕ → Coordinates K)
    (windows : ℕ → ℕ → ℕ) (tr : CoordinateTrace K) : Prop where
  seed_on : C.OnCurve tr.seed
  offset_scale : C.ScaleChecks tr.seed tr.offsetChain (2^w-1)
  offset_end : tr.offsetChain (2^w-1) = finiteEncoding tr.offset
  initial_scale : C.ScaleChecks tr.seed tr.initialChain l
  initial_end : tr.initialChain l = finiteEncoding (tr.boundary 0)
  table_zero : ∀ j, j < l → tr.table j 0 = opposite tr.offset
  table_guard : ∀ j, j < l → (bases j).x ≠ tr.offset.x
  table_checks : ∀ j, j < l → TableChecks (bases j) (tr.table j) (2^w-1)
  window_range : ∀ i, i < n → ∀ j, j < l → windows i j < 2^w
  double_start : ∀ i, i < n → tr.doubles i 0 = tr.boundary i
  double_checks : ∀ i, i < n → ∀ k, k < w →
    ∃ slope, DoubleChecks C (tr.doubles i k) (tr.doubles i (k+1)) slope
  row_start : ∀ i, i < n → tr.rows i 0 = tr.doubles i w
  row_checks : ∀ i, i < n → ∀ j, j < l →
    (tr.rows i j).x ≠ (tr.table j (windows i j)).x ∧
    ∃ slope, AddChecks (tr.rows i j) (tr.table j (windows i j)) (tr.rows i (j+1)) slope
  window_end : ∀ i, i < n → tr.boundary (i+1) = tr.rows i l
  final_check : C.CompleteAccepts (finiteEncoding (tr.boundary n))
    (finiteEncoding (opposite (tr.boundary 0))) tr.output

theorem trace_setup {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (ha : C.TraceAccepts w l n bases windows tr) :
    (∃ hv : C.OnCurve tr.offset,
      C.point tr.offset hv = (2^w-1) • C.point tr.seed ha.seed_on) ∧
    (∃ h0 : C.OnCurve (tr.boundary 0),
      C.point (tr.boundary 0) h0 = l • C.point tr.seed ha.seed_on) :=
  ⟨C.scale_finite_sound ha.seed_on ha.offset_scale ha.offset_end,
   C.scale_finite_sound ha.seed_on ha.initial_scale ha.initial_end⟩

theorem trace_lookup {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (hbases : ∀ j, C.OnCurve (bases j)) (ha : C.TraceAccepts w l n bases windows tr)
    {i j : ℕ} (hi : i < n) (hj : j < l) :
    ∃ ht : C.OnCurve (tr.table j (windows i j)),
      C.point (tr.table j (windows i j)) ht =
        entry (C.point (bases j) (hbases j)) ((2^w-1) • C.point tr.seed ha.seed_on) (windows i j) := by
  obtain ⟨⟨hv, he⟩, _⟩ := C.trace_setup ha
  have ht0 : C.OnCurve (tr.table j 0) := by
    rw [ha.table_zero j hj]
    exact C.opposite_on_curve hv
  have hzero : C.point (tr.table j 0) ht0 = -((2^w-1) • C.point tr.seed ha.seed_on) := by
    simp only [ha.table_zero j hj, C.point_opposite hv, he]
  have hx : (tr.table j 0).x ≠ (bases j).x := by
    simpa only [ha.table_zero j hj, opposite] using (ha.table_guard j hj).symm
  have hwidth : 2^w-1+1 = 2^w := Nat.sub_add_cancel (Nat.one_le_pow w 2 (by decide))
  exact C.table_lookup_sound (hbases j) ht0 hzero hx (ha.table_checks j hj)
    ⟨windows i j, by rw [hwidth]; exact ha.window_range i hi j hj⟩

theorem trace_doubles {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (ha : C.TraceAccepts w l n bases windows tr) {i : ℕ} (hi : i < n)
    (hstart : C.OnCurve (tr.boundary i)) :
    ∀ k, k ≤ w → ∃ hk : C.OnCurve (tr.doubles i k),
      C.point (tr.doubles i k) hk = 2^k • C.point (tr.boundary i) hstart := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : C.OnCurve (tr.doubles i 0) := by rw [ha.double_start i hi]; exact hstart
    exact ⟨h0, by simp [ha.double_start i hi]⟩
  | succ k ih =>
    intro hk
    obtain ⟨hv, he⟩ := ih (by omega)
    obtain ⟨slope, hc⟩ := ha.double_checks i hi k (by omega)
    obtain ⟨hv', he'⟩ := C.doubling_sound hv hc
    exact ⟨hv', by rw [he', he, pow_succ, mul_comm, mul_smul, two_smul]⟩

theorem trace_rows {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (hbases : ∀ j, C.OnCurve (bases j)) (ha : C.TraceAccepts w l n bases windows tr)
    {i : ℕ} (hi : i < n) (hstart : C.OnCurve (tr.rows i 0)) :
    ∀ j, j ≤ l → ∃ hj : C.OnCurve (tr.rows i j),
      C.point (tr.rows i j) hj = addRows (fun j => C.point (bases j) (hbases j))
        (windows i) ((2^w-1) • C.point tr.seed ha.seed_on) (C.point (tr.rows i 0) hstart) j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hstart, rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hv, he⟩ := ih (by omega)
    obtain ⟨ht, htable⟩ := C.trace_lookup hbases ha hi (by omega : j < l)
    obtain ⟨hx, slope, hc⟩ := ha.row_checks i hi j (by omega)
    obtain ⟨hv', he'⟩ := C.addition_sound hv ht hx hc
    exact ⟨hv', by rw [he', he, htable, addRows]⟩

theorem trace_boundaries {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (hbases : ∀ j, C.OnCurve (bases j)) (ha : C.TraceAccepts w l n bases windows tr) :
    ∀ i, i ≤ n → ∃ hi : C.OnCurve (tr.boundary i),
      C.point (tr.boundary i) hi = loop (2^w) l
        (fun j => C.point (bases j) (hbases j)) windows (C.point tr.seed ha.seed_on) i := by
  intro i
  induction i with
  | zero => intro _; exact (C.trace_setup ha).2
  | succ i ih =>
    intro hi
    obtain ⟨hv, he⟩ := ih (by omega)
    obtain ⟨hd, hed⟩ := C.trace_doubles ha (by omega : i < n) hv w (by omega)
    have hs : C.OnCurve (tr.rows i 0) := by rw [ha.row_start i (by omega)]; exact hd
    obtain ⟨hr, her⟩ := C.trace_rows hbases ha (by omega : i < n) hs l (by omega)
    have hout : C.OnCurve (tr.boundary (i+1)) := by rw [ha.window_end i (by omega)]; exact hr
    refine ⟨hout, ?_⟩
    simpa only [ha.window_end i (by omega), ha.row_start i (by omega), hed, he, loop] using her

/-- Every accepted supplied trace agrees with the mathematical group loop. -/
theorem trace_sound {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (hbases : ∀ j, C.OnCurve (bases j)) (ha : C.TraceAccepts w l n bases windows tr) :
    ∃ hout : C.Valid tr.output, C.decode tr.output hout =
      loop (2^w) l (fun j => C.point (bases j) (hbases j)) windows
        (C.point tr.seed ha.seed_on) n - l • C.point tr.seed ha.seed_on := by
  obtain ⟨hn, hen⟩ := C.trace_boundaries hbases ha n (by omega)
  obtain ⟨h0, he0⟩ := (C.trace_setup ha).2
  obtain ⟨hout, he⟩ := C.complete_sound (show C.Valid (finiteEncoding (tr.boundary n)) from fun _ => hn)
    (show C.Valid (finiteEncoding (opposite (tr.boundary 0))) from fun _ => C.opposite_on_curve h0)
    ha.final_check
  refine ⟨hout, ?_⟩
  rw [C.decode_finite (P := finiteEncoding (tr.boundary n)) _ rfl,
    C.decode_finite (P := finiteEncoding (opposite (tr.boundary 0))) _ rfl] at he
  simpa only [finiteEncoding, C.point_opposite h0, hen, he0, sub_eq_add_neg] using he

/-- End-to-end soundness for the corrected traversal of little-endian windows. -/
theorem trace_sound_littleEndian {w l n : ℕ} {bases : ℕ → Coordinates K}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace K}
    (hbases : ∀ j, C.OnCurve (bases j))
    (ha : C.TraceAccepts w l n bases (descending windows n) tr) :
    ∃ hout : C.Valid tr.output, C.decode tr.output hout =
      ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range n, (2^w)^i * windows i j) •
        C.point (bases j) (hbases j) := by
  obtain ⟨hout, he⟩ := C.trace_sound hbases ha
  exact ⟨hout, he.trans (loop_correct (2^w) l n (by positivity) _ _ _)⟩

end EfficientFFA.EllipticCurve.Curve
