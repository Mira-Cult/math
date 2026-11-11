import Sude.GeneratedPrefix.L64Extra.All

/-! Combine the two certified L-family blocks into one indexed population. -/
namespace Sude.GeneratedPrefix.L64
noncomputable section

abbrev Block := (Fin 24 × Fin 32) × Bool

/-- Split each stage's first 64 pairs into its two consecutive 32-pair blocks. -/
def splitIndex : ((Fin 24 × Fin 64) × Bool) ≃ Sum Block Block :=
  (Equiv.prodCongr
    (Equiv.prodCongr (Equiv.refl (Fin 24)) (finSumFinEquiv (m := 32) (n := 32)).symm)
    (Equiv.refl Bool)).trans
  ((Equiv.prodCongr (Equiv.prodSumDistrib (Fin 24) (Fin 32) (Fin 32)) (Equiv.refl Bool)).trans
    (Equiv.sumProdDistrib (Fin 24 × Fin 32) (Fin 24 × Fin 32) Bool))

def endpoint : (Fin 24 × Fin 64) × Bool → ℕ :=
  (Sum.elim L32Distinct.endpoint L64Extra.endpoint) ∘ splitIndex

theorem endpoint_injective : Function.Injective endpoint :=
  L64Extra.both_injective.comp splitIndex.injective

theorem endpoint_prime (x : (Fin 24 × Fin 64) × Bool) : Nat.Prime (endpoint x) := by
  change Nat.Prime (Sum.elim L32Distinct.endpoint L64Extra.endpoint (splitIndex x))
  cases hx : splitIndex x with
  | inl a => simpa only [hx, Sum.elim_inl] using L32Primes.endpoint_prime a
  | inr b => simpa only [hx, Sum.elim_inr] using L64Extra.extra_prime b

theorem extra_bounds : ∀ x, L64Extra.endpoint x ≠ 2 ∧ L64Extra.endpoint x ≤ 55000000 := by
  decide +kernel

theorem endpoint_bounds (x : (Fin 24 × Fin 64) × Bool) : endpoint x ≠ 2 ∧ endpoint x ≤ 55000000 := by
  change Sum.elim L32Distinct.endpoint L64Extra.endpoint (splitIndex x) ≠ 2 ∧
    Sum.elim L32Distinct.endpoint L64Extra.endpoint (splitIndex x) ≤ 55000000
  cases hx : splitIndex x with
  | inl a => simpa only [hx, Sum.elim_inl] using L32Primes.endpoint_bounds a
  | inr b => simpa only [hx, Sum.elim_inr] using extra_bounds b

theorem endpoint_in_pool (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (x : (Fin 24 × Fin 64) × Bool) : endpoint x ∈ pool n := by
  have hb := endpoint_bounds x
  exact finitePrefix_L_prime_in_pool lower hn (endpoint_prime x) hb.1 (by omega)

def lows (j : Fin 24) (i : Fin 64) : ℕ :=
  Sum.elim (L32Distinct.lows j) (L64Extra.lows j) ((finSumFinEquiv (m := 32) (n := 32)).symm i)

theorem endpoint_formula (j : Fin 24) (i : Fin 64) (side : Bool) :
    endpoint ((j, i), side) = lows j i + if side then 2 ^ (j.val + 1) else 0 := by
  cases h : (finSumFinEquiv (m := 32) (n := 32)).symm i with
  | inl k => simp [endpoint, splitIndex, lows, L32Distinct.endpoint, h]
  | inr k => simp [endpoint, splitIndex, lows, L64Extra.endpoint, h]

def poolValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    (Fin 24 × Fin 64) × Bool → pool n := fun x => ⟨endpoint x, endpoint_in_pool lower hn x⟩

theorem poolValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    Function.Injective (poolValues lower hn) := by
  intro x y h
  exact endpoint_injective (congrArg Subtype.val h)

theorem poolValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (j : Fin 24) (i : Fin 64) :
    (poolValues lower hn ((j, i), true)).val =
      (poolValues lower hn ((j, i), false)).val + 2 ^ (j.val + 1) := by
  change endpoint ((j, i), true) = endpoint ((j, i), false) + 2 ^ (j.val + 1)
  rw [endpoint_formula, endpoint_formula]
  simp

end
end Sude.GeneratedPrefix.L64
