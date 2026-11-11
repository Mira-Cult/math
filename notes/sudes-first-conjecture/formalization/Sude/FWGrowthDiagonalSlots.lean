import Sude.PrefixPhysicalSlotGeometry

/-! Explicit disjoint diagonal and partner slot indices for one growth stage.
This is index bookkeeping; physical diagonal incidence needs the balanced
choice and the rectangle geometry. -/
namespace Sude
noncomputable section

/-- First pair in each of the first twelve rectangles. -/
def fwGrowthMainSlots (n : ℕ) : Finset (Fin (6*(n+8))) :=
  Finset.univ.image fun i : Fin 12 =>
    prefixDiagonalPairIndex (d := 6) (by omega) (⟨i.val, by omega⟩, 0)

/-- First pair in each of the last twelve rectangles. -/
def fwGrowthAntiSlots (n : ℕ) : Finset (Fin (6*(n+8))) :=
  Finset.univ.image fun i : Fin 12 =>
    prefixDiagonalPairIndex (d := 6) (by omega) (⟨i.val+12, by omega⟩, 0)

/-- Second pair in every diagonal rectangle. -/
def fwGrowthPartnerSlots (n : ℕ) : Finset (Fin (6*(n+8))) :=
  Finset.univ.image fun i : Fin 24 =>
    prefixDiagonalPairIndex (d := 6) (by omega) (i, 1)

/-- All row- and column-network slots, with no rectangle pair. -/
def fwGrowthOrdinarySlots (n : ℕ) : Finset (Fin (6*(n+8))) :=
  Finset.univ.image (prefixOrdinaryPairIndex (d := 6) (r := 3) (n := n) (by omega))

theorem fw_growth_slot_group_cardinalities (n : ℕ) :
    (fwGrowthMainSlots n).card = 12 ∧ (fwGrowthAntiSlots n).card = 12 ∧
    (fwGrowthPartnerSlots n).card = 24 ∧ (fwGrowthOrdinarySlots n).card = 6*n := by
  have hm : Function.Injective (fun i : Fin 12 =>
      prefixDiagonalPairIndex (d := 6) (Q := 6*(n+8)) (by omega) (⟨i.val, by omega⟩, 0)) := by
    intro a b h
    have h' := prefixDiagonalPairIndex_injective (d := 6) (Q := 6*(n+8)) (by omega) h
    exact Fin.ext (congrArg (fun p : Fin (4*6) × Fin 2 => p.1.val) h')
  have ha : Function.Injective (fun i : Fin 12 =>
      prefixDiagonalPairIndex (d := 6) (Q := 6*(n+8)) (by omega) (⟨i.val+12, by omega⟩, 0)) := by
    intro a b h
    have h' := prefixDiagonalPairIndex_injective (d := 6) (Q := 6*(n+8)) (by omega) h
    have hv := congrArg (fun p : Fin (4*6) × Fin 2 => p.1.val) h'
    apply Fin.ext; simp only at hv; omega
  have hp : Function.Injective (fun i : Fin 24 =>
      prefixDiagonalPairIndex (d := 6) (Q := 6*(n+8)) (by omega) (i, 1)) := by
    intro a b h
    have h' := prefixDiagonalPairIndex_injective (d := 6) (Q := 6*(n+8)) (by omega) h
    exact congrArg Prod.fst h'
  constructor
  · simp [fwGrowthMainSlots, Finset.card_image_of_injective _ hm]
  constructor
  · simp [fwGrowthAntiSlots, Finset.card_image_of_injective _ ha]
  constructor
  · simp [fwGrowthPartnerSlots, Finset.card_image_of_injective _ hp]
  · simp [fwGrowthOrdinarySlots, Finset.card_image_of_injective _
      (prefixOrdinaryPairIndex_injective (d := 6) (r := 3) (n := n) (Q := 6*(n+8)) (by omega))]
    omega

theorem fw_growth_slot_groups_disjoint (n : ℕ) :
    Disjoint (fwGrowthMainSlots n) (fwGrowthAntiSlots n) ∧
    Disjoint (fwGrowthMainSlots n) (fwGrowthPartnerSlots n) ∧
    Disjoint (fwGrowthAntiSlots n) (fwGrowthPartnerSlots n) ∧
    Disjoint (fwGrowthOrdinarySlots n) (fwGrowthMainSlots n ∪ fwGrowthAntiSlots n ∪ fwGrowthPartnerSlots n) := by
  have hd := prefixDiagonalPairIndex_injective (d := 6) (Q := 6*(n+8)) (by omega)
  have hma : Disjoint (fwGrowthMainSlots n) (fwGrowthAntiSlots n) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    have h := hd (ha.trans hb.symm)
    have hv := congrArg (fun p : Fin (4*6) × Fin 2 => p.1.val) h
    change a.val = b.val + 12 at hv
    have := a.isLt
    omega
  have hmp : Disjoint (fwGrowthMainSlots n) (fwGrowthPartnerSlots n) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    have h := hd (ha.trans hb.symm)
    have hv := congrArg (fun p : Fin (4*6) × Fin 2 => p.2.val) h
    simp at hv
  have hap : Disjoint (fwGrowthAntiSlots n) (fwGrowthPartnerSlots n) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    have h := hd (ha.trans hb.symm)
    have hv := congrArg (fun p : Fin (4*6) × Fin 2 => p.2.val) h
    simp at hv
  have ho : Disjoint (fwGrowthOrdinarySlots n) (fwGrowthMainSlots n ∪ fwGrowthAntiSlots n ∪ fwGrowthPartnerSlots n) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_union.mp hy with hy | hy
    · rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
        exact prefixOrdinary_ne_diagonal (by omega) (by omega) a (⟨b.val, by omega⟩, 0) (ha.trans hb.symm)
      · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
        exact prefixOrdinary_ne_diagonal (by omega) (by omega) a (⟨b.val+12, by omega⟩, 0) (ha.trans hb.symm)
    · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
      exact prefixOrdinary_ne_diagonal (by omega) (by omega) a (b, 1) (ha.trans hb.symm)
  exact ⟨hma, hmp, hap, ho⟩

/-- The disjoint rectangle groups occupy exactly the non-network slots. -/
theorem fw_growth_ordinary_slots_eq_complement (n : ℕ) :
    fwGrowthOrdinarySlots n = Finset.univ \
      (fwGrowthMainSlots n ∪ fwGrowthAntiSlots n ∪ fwGrowthPartnerSlots n) := by
  have hc := fw_growth_slot_group_cardinalities n
  have hd := fw_growth_slot_groups_disjoint n
  have hd' : Disjoint (fwGrowthMainSlots n ∪ fwGrowthAntiSlots n) (fwGrowthPartnerSlots n) :=
    Finset.disjoint_union_left.mpr ⟨hd.2.1, hd.2.2.1⟩
  have hcard : (fwGrowthMainSlots n ∪ fwGrowthAntiSlots n ∪ fwGrowthPartnerSlots n).card = 48 := by
    rw [Finset.card_union_of_disjoint hd', Finset.card_union_of_disjoint hd.1]
    omega
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.disjoint_left.mp hd.2.2.2) hx⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hcard, hc.2.2.2]
    omega

end
end Sude
