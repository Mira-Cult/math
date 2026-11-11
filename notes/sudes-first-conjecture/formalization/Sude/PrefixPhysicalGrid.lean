import Sude.BridgePhysicalGrid
import Sude.ReservoirMidpoint

/-! The finite FPF binary prefix, indexed by actual physical pair labels. -/
namespace Sude
noncomputable section

def prefixPairBlock {E K : Type*} [DecidableEq K] (P : ℕ)
    (slot : E × Fin P → K) (edge : E) : Finset K :=
  (Finset.univ : Finset (Fin P)).image (fun j => slot (edge, j))

/-- Injective physical slot assignment turns the binary-gap prefix into a
complete grid for every edge, without duplicating any pair between edges. -/
theorem prefixPairBlock_grid {E K : Type*} [DecidableEq E] [DecidableEq K]
    (P : ℕ) (slot : E × Fin P → K) (hinj : Function.Injective slot)
    (gap : K → ℕ) (hgap : ∀ edge j, gap (slot (edge, j)) = 2 ^ (j.val + 1))
    (edge : E) :
    CompleteEvenGrid (prefixPairBlock P slot edge) gap (2 ^ (P + 1) - 2) := by
  let f : {x // x ∈ Finset.range P} → K := fun x =>
    slot (edge, ⟨x.val, Finset.mem_range.mp x.property⟩)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : E × Fin P => z.2.val) (hinj h)
  have hs : (Finset.range P).attach.image f = prefixPairBlock P slot edge := by
    ext x
    simp only [Finset.mem_image, Finset.mem_attach, Finset.mem_univ, true_and,
      prefixPairBlock]
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨⟨j, Finset.mem_range.mp hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.val, Finset.mem_range.mpr j.isLt⟩, rfl⟩
  have hbase := binary_prefix_actual_grid P (fun j => 2 ^ (j + 1)) (by intros; rfl)
  have h := completeEvenGrid_finite_relabel (Finset.range P) (fun j => 2 ^ (j + 1))
    (∑ j ∈ Finset.range P, 2 ^ (j + 1)) f hf gap
    (fun x => hgap edge ⟨x.val, Finset.mem_range.mp x.property⟩) hbase.1
  simpa [hs, binary_gap_total] using h

theorem prefixPairBlock_disjoint {E K : Type*} [DecidableEq E] [DecidableEq K]
    (P : ℕ) (slot : E × Fin P → K) (hinj : Function.Injective slot)
    (edge edge' : E) (hne : edge ≠ edge') :
    Disjoint (prefixPairBlock P slot edge) (prefixPairBlock P slot edge') := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
  obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hx'
  exact hne (congrArg Prod.fst (hinj (hj.trans hj'.symm)))

theorem prefixPairBlock_endpoints {E K : Type*} [DecidableEq K] {n : ℕ}
    {a : Cell n ≃ Fin (n * n)} (P : ℕ) (slot : E × Fin P → K)
    (pairs : RowNetworkPairs K a) (source target : E → Fin n)
    (hends : ∀ edge j, pairs.low (slot (edge, j)) = source edge ∧
      pairs.high (slot (edge, j)) = target edge) :
    ∀ edge k, k ∈ prefixPairBlock P slot edge →
      pairs.low k = source edge ∧ pairs.high k = target edge := by
  intro edge k hk
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
  exact hends edge j

theorem prefixRadius_even (P : ℕ) : 2 ∣ 2 ^ (P + 1) - 2 := by
  have h := (binary_prefix_actual_grid P (fun j => 2 ^ (j + 1)) (by intros; rfl)).2
  rw [binary_gap_total] at h
  exact h

end
end Sude
