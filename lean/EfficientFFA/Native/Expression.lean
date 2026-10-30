import EfficientFFA.Native.Gate
import EfficientFFA.Representation
import Mathlib.Data.ZMod.Basic

namespace EfficientFFA.Native

/-- Arithmetic syntax compiled to explicit sparse limb polynomials. -/
inductive Expression (α : Type*) where
  | const : ℤ → Expression α
  | var : α → Expression α
  | add : Expression α → Expression α → Expression α
  | mul : Expression α → Expression α → Expression α
  | neg : Expression α → Expression α

namespace Expression
variable {α : Type*}
instance : Add (Expression α) := ⟨.add⟩
instance : Mul (Expression α) := ⟨.mul⟩
instance : Neg (Expression α) := ⟨.neg⟩
instance : Sub (Expression α) := ⟨fun e f => .add e (.neg f)⟩
instance (k : ℕ) : OfNat (Expression α) k := ⟨.const k⟩

def value {K : Type*} [Ring K] (x : α → K) : Expression α → K
  | .const c => c
  | .var a => x a
  | .add e f => value x e + value x f
  | .mul e f => value x e * value x f
  | .neg e => -value x e

@[simp] theorem value_add {K : Type*} [Ring K] (x : α → K) (e f : Expression α) :
    value x (e+f) = value x e + value x f := rfl
@[simp] theorem value_mul {K : Type*} [Ring K] (x : α → K) (e f : Expression α) :
    value x (e*f) = value x e * value x f := rfl
@[simp] theorem value_neg {K : Type*} [Ring K] (x : α → K) (e : Expression α) :
    value x (-e) = -value x e := rfl
@[simp] theorem value_sub {K : Type*} [Ring K] (x : α → K) (e f : Expression α) :
    value x (e-f) = value x e - value x f := by
  change value x e + -value x f = _
  exact (sub_eq_add_neg _ _).symm
@[simp] theorem value_nat {K : Type*} [Ring K] (x : α → K) (k : ℕ) :
    value x (OfNat.ofNat k : Expression α) = (k : K) := by simp [value]

def limb (B : ℤ) (n : ℕ) (a : α) : Polynomial (α × Fin n) :=
  List.ofFn (fun i : Fin n => (B^i.val, [(a,i)]))

def compile (B : ℤ) (n : ℕ) : Expression α → Polynomial (α × Fin n)
  | .const c => Polynomial.constant c
  | .var a => limb B n a
  | .add e f => Polynomial.add (compile B n e) (compile B n f)
  | .mul e f => Polynomial.mul (compile B n e) (compile B n f)
  | .neg e => Polynomial.scale (-1) (compile B n e)

theorem limb_eval (B : ℤ) (n : ℕ) (a : α) (x : α × Fin n → ℤ) :
    Polynomial.eval (limb B n a) x = EfficientFFA.eval B (fun i => x (a,i)) := by
  simp [limb, Polynomial.eval, Polynomial.monomial, EfficientFFA.eval, List.sum_ofFn]

theorem compile_eval (B : ℤ) (n : ℕ) (e : Expression α) (x : α × Fin n → ℤ) :
    Polynomial.eval (compile B n e) x = value (fun a => EfficientFFA.eval B (fun i => x (a,i))) e := by
  induction e with
  | const c => simp [compile, value, Polynomial.eval_constant]
  | var a => exact limb_eval B n a x
  | add e f he hf => simp [compile, value, Polynomial.eval_add, he, hf]
  | mul e f he hf => simp [compile, value, Polynomial.eval_mul, he, hf]
  | neg e he => simp [compile, value, Polynomial.eval_scale, he]

theorem cast_value {K : Type*} [Ring K] (e : Expression α) (x : α → ℤ) :
    ((value x e : ℤ) : K) = value (fun a => (x a : K)) e := by
  induction e <;> simp_all [value]

theorem value_congr {K : Type*} [Ring K] (e : Expression α) {x y : α → K}
    (h : ∀ a, x a = y a) : value x e = value y e := by
  rw [funext h]

/-- A gate carries actual native equations and bounded integer representations of
its semantic inputs. Copy/lookup wiring between separate gates is outside this layer. -/
def Checks {r : ℕ} (P : Parameters r) (n q : ℕ) (e : Expression α) (values : α → ZMod q) : Prop :=
  ∃ x : α × Fin n → ℤ, Polynomial.Bounded P.B x ∧
    (∀ a, (EfficientFFA.eval P.B (fun i => x (a,i)) : ZMod q) = values a) ∧
    ∃ u v, P.Accepts (compile P.B n e) x u v

theorem checks_sound {r n q : ℕ} (P : Parameters r) (hq : P.q = q)
    {e : Expression α} (hvalid : P.Valid (compile P.B n e)) {values : α → ZMod q}
    (hc : Checks P n q e values) : value values e = 0 := by
  obtain ⟨x, hx, hr, u, v, ha⟩ := hc
  have h := P.sound hvalid.positive hvalid.nowrap hx ha
  rw [hq, ← ZMod.intCast_eq_intCast_iff] at h
  simpa only [Int.cast_zero, compile_eval, cast_value, value_congr e hr] using h

theorem checks_complete {r n q : ℕ} [NeZero q] (P : Parameters r) (hq : P.q = q)
    {e : Expression α} (hvalid : P.Valid (compile P.B n e)) (hcap : P.q ≤ P.B^n)
    {values : α → ZMod q} (he : value values e = 0) : Checks P n q e values := by
  have hex : ∀ a, ∃ z : Limbs n, WellFormed P.B z ∧ (EfficientFFA.eval P.B z : ZMod q) = values a := by
    intro a
    obtain ⟨z, hz, hr⟩ := exists_canonical_limbs hvalid.positive.radix hvalid.positive.foreign n hcap
      (values a).val
    refine ⟨z, hz, ?_⟩
    rw [hr, hq, ZMod.intCast_mod]
    simp
  choose z hz hr using hex
  let x : α × Fin n → ℤ := fun a => z a.1 a.2
  have hx : Polynomial.Bounded P.B x := fun a => hz a.1 a.2
  have hd : Polynomial.eval (compile P.B n e) x ≡ 0 [ZMOD P.q] := by
    rw [hq, ← ZMod.intCast_eq_intCast_iff, Int.cast_zero, compile_eval, cast_value]
    exact (value_congr e hr).trans he
  exact ⟨x, hx, hr, _, _, P.witnesses_accept hvalid.positive hvalid.widths hx hd⟩

theorem checks_iff {r n q : ℕ} [NeZero q] (P : Parameters r) (hq : P.q = q)
    {e : Expression α} (hvalid : P.Valid (compile P.B n e)) (hcap : P.q ≤ P.B^n)
    (values : α → ZMod q) : Checks P n q e values ↔ value values e = 0 :=
  ⟨checks_sound P hq hvalid, checks_complete P hq hvalid hcap⟩

end Expression
end EfficientFFA.Native
