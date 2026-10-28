import EfficientFFA.MSM.Safety

namespace EfficientFFA.MSM
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)

theorem map_entry (base offset : G) (k : ℕ) :
    f (entry base offset k) = entry (f base) (f offset) k := by simp [entry]

theorem map_addRows (bases : ℕ → G) (digits : ℕ → ℕ) (offset acc : G) (j : ℕ) :
    f (addRows bases digits offset acc j) = addRows (fun j => f (bases j)) digits (f offset) (f acc) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [addRows, map_add, ih, map_entry]

theorem map_loop (b l : ℕ) (bases : ℕ → G) (windows : ℕ → ℕ → ℕ) (u : G) (i : ℕ) :
    f (loop b l bases windows u i) = loop b l (fun j => f (bases j)) windows (f u) i := by
  induction i with
  | zero => simp [loop]
  | succ i ih => simp only [loop, map_addRows, map_nsmul, ih]

theorem tableSafe_map_iff (hf : Function.Injective f) (base offset : G) (steps : ℕ) :
    TableSafe (f base) (f offset) steps ↔ TableSafe base offset steps := by
  simp only [TableSafe, ne_eq, ← map_entry, ← map_zero f, ← map_neg f, hf.eq_iff]

theorem collision_map_iff (hf : Function.Injective f) (b l : ℕ) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G) (i j : ℕ) :
    Collision b l (fun j => f (bases j)) windows (f u) i j ↔ Collision b l bases windows u i j := by
  simp only [Collision, ← map_loop, ← map_nsmul, ← map_addRows, ← map_entry, ← map_neg f, hf.eq_iff]

/-- An injective group embedding preserves all exceptional-case conditions. -/
theorem groupAccepts_map_iff (hf : Function.Injective f) (b l n : ℕ) (bases : ℕ → G)
    (windows : ℕ → ℕ → ℕ) (u : G) :
    GroupAccepts b l n (fun j => f (bases j)) windows (f u) ↔ GroupAccepts b l n bases windows u := by
  simp only [GroupAccepts, ne_eq, ← map_nsmul, tableSafe_map_iff f hf, collision_map_iff f hf,
    ← map_zero f, hf.eq_iff]

end EfficientFFA.MSM
