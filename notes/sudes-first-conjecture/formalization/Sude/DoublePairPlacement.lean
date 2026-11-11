import Sude.DoublePairBatch

/-! Install selected double blocks simultaneously in supplied physical cells.
The controller must still supply appropriate disjoint cell geometry. -/
namespace Sude
noncomputable section

/-- Rectangle order: top low, top high, bottom high, bottom low. -/
def DoublePair.endpoint (b : DoublePair) : Fin 4 → ℕ :=
  ![b.low₁, b.high₁, b.high₂, b.low₂]

theorem DoublePair.endpoint_mem (b : DoublePair) (i : Fin 4) :
    b.endpoint i ∈ b.footprint := by
  fin_cases i <;> simp [DoublePair.endpoint, DoublePair.footprint]

theorem DoublePair.endpoint_injective (b : DoublePair) (low high : Finset ℕ)
    (horder : ∀ a ∈ low, ∀ d ∈ high, a < d) (h : b.valid low high) :
    Function.Injective b.endpoint := by
  have h₁₁ := horder b.low₁ h.1 b.high₁ h.2.2.1
  have h₁₂ := horder b.low₁ h.1 b.high₂ h.2.2.2.1
  have h₂₁ := horder b.low₂ h.2.1 b.high₁ h.2.2.1
  have h₂₂ := horder b.low₂ h.2.1 b.high₂ h.2.2.2.1
  have hl := h.2.2.2.2.1
  have hh := h.2.2.2.2.2.1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [DoublePair.endpoint]

def doublePairSequenceEndpoint (blocks : List DoublePair)
    (x : Fin blocks.length × Fin 4) : ℕ := (blocks.get x.1).endpoint x.2

theorem doublePairSequenceEndpoint_injective (blocks : List DoublePair)
    (low high : Finset ℕ) (horder : ∀ a ∈ low, ∀ d ∈ high, a < d)
    (hvalid : ∀ b ∈ blocks, b.valid low high)
    (hpair : blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint)) :
    Function.Injective (doublePairSequenceEndpoint blocks) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ heq
  by_cases hij : i = j
  · subst j
    have hx : x = y := DoublePair.endpoint_injective (blocks.get i) low high horder
      (hvalid (blocks.get i) (List.get_mem blocks i)) heq
    cases hx
    rfl
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hd := hpair.rel_get_of_lt hlt
      have hx := DoublePair.endpoint_mem (blocks.get i) x
      have hy := DoublePair.endpoint_mem (blocks.get j) y
      change (blocks.get i).endpoint x = (blocks.get j).endpoint y at heq
      rw [← heq] at hy
      exact False.elim (Finset.disjoint_left.mp hd hx hy)
    · have hd := hpair.rel_get_of_lt hgt
      have hx := DoublePair.endpoint_mem (blocks.get i) x
      have hy := DoublePair.endpoint_mem (blocks.get j) y
      change (blocks.get i).endpoint x = (blocks.get j).endpoint y at heq
      rw [heq] at hx
      exact False.elim (Finset.disjoint_left.mp hd hy hx)

/-- Install all blocks into injectively supplied cells, preserving earlier
reserved cells and the exact pool permutation. No geometric packing is hidden. -/
theorem install_double_pair_sequence {n : ℕ} (blocks : List DoublePair)
    (low high : Finset ℕ) (horder : ∀ a ∈ low, ∀ d ∈ high, a < d)
    (hvalid : ∀ b ∈ blocks, b.valid low high)
    (hpair : blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint))
    (hpoolLow : ∀ a ∈ low, a ∈ pool n) (hpoolHigh : ∀ a ∈ high, a ∈ pool n)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin blocks.length × Fin 4 → Cell n)
    (reserved : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reserved)
    (havoid : ∀ b ∈ blocks, ∀ v ∈ b.footprint, ∀ c ∈ reserved, v ≠ entry a c) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ x, entry a' (cells x) = doublePairSequenceEndpoint blocks x) ∧
      (∀ c ∈ reserved, entry a' c = entry a c) := by
  let values : (Fin blocks.length × Fin 4) → pool n := fun x =>
    ⟨doublePairSequenceEndpoint blocks x, by
      rcases x with ⟨i, j⟩
      have hv := hvalid (blocks.get i) (List.get_mem blocks i)
      fin_cases j
      · simpa [doublePairSequenceEndpoint, DoublePair.endpoint] using hpoolLow _ hv.1
      · simpa [doublePairSequenceEndpoint, DoublePair.endpoint] using hpoolHigh _ hv.2.2.1
      · simpa [doublePairSequenceEndpoint, DoublePair.endpoint] using hpoolHigh _ hv.2.2.2.1
      · simpa [doublePairSequenceEndpoint, DoublePair.endpoint] using hpoolLow _ hv.2.1⟩
  have hinj : Function.Injective values := by
    intro x y heq
    apply doublePairSequenceEndpoint_injective blocks low high horder hvalid hpair
    exact congrArg Subtype.val heq
  have hav : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c := by
    intro ⟨i, j⟩ c hc
    exact havoid (blocks.get i) (List.get_mem blocks i) _
      (DoublePair.endpoint_mem (blocks.get i) j) c hc
  exact place_distinct_pool_entries_preserving a cells values reserved hcells hinj hnew hav

/-- Each installed block has the two positive equal-gap identities required
by a rectangle trade, in the chosen top/bottom slot order. -/
theorem installed_double_pair_gaps {n : ℕ} (blocks : List DoublePair)
    (low high : Finset ℕ) (hvalid : ∀ b ∈ blocks, b.valid low high)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin blocks.length × Fin 4 → Cell n)
    (hplace : ∀ x, entry a (cells x) = doublePairSequenceEndpoint blocks x) :
    ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧
      entry a (cells (i, 1)) = entry a (cells (i, 0)) + gap ∧
      entry a (cells (i, 2)) = entry a (cells (i, 3)) + gap := by
  intro i
  have hv := hvalid (blocks.get i) (List.get_mem blocks i)
  rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
  refine ⟨(blocks.get i).high₁ - (blocks.get i).low₁, by omega, ?_, ?_⟩
  · rw [hplace, hplace]
    change (blocks.get i).high₁ = (blocks.get i).low₁ +
      ((blocks.get i).high₁ - (blocks.get i).low₁)
    omega
  · rw [hplace, hplace]
    change (blocks.get i).high₂ = (blocks.get i).low₂ +
      ((blocks.get i).high₁ - (blocks.get i).low₁)
    omega

end
end Sude
