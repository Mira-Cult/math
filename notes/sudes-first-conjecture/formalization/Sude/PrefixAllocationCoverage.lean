import Mathlib.Data.Fintype.Sum

import Sude.PrefixPairAllocation
import Sude.NarrowSeedPoolValues

/-! The rectangle and both network allocations cover every pair endpoint when
all pair slots are used. -/
namespace Sude
noncomputable section

abbrev PrefixPhysicalInputs (P d r n : ℕ) :=
  (Fin (P * (4 * d)) × Fin 4) ⊕
    ((Fin (P * r) × (Fin n × Bool)) ⊕ (Fin (P * r) × (Fin n × Bool)))

def prefixPhysicalInput {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    PrefixPhysicalInputs P d r n → (Fin P × Fin Q) × Bool
  | Sum.inl x => prefixRectangleInput hdiag x
  | Sum.inr (Sum.inl x) => prefixNetworkInput hfit rfl 0 x
  | Sum.inr (Sum.inr x) => prefixNetworkInput hfit rfl 1 x

theorem prefixPhysicalInput_injective {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    Function.Injective (prefixPhysicalInput (P := P) hfit hdiag) := by
  intro x y h
  rcases x with x | (x | x) <;> rcases y with y | (y | y)
  · exact congrArg Sum.inl (prefixRectangleInput_injective hdiag h)
  · exact False.elim (prefixNetworkInput_ne_rectangle hfit hdiag rfl 0 y x h.symm)
  · exact False.elim (prefixNetworkInput_ne_rectangle hfit hdiag rfl 1 y x h.symm)
  · exact False.elim (prefixNetworkInput_ne_rectangle hfit hdiag rfl 0 x y h)
  · exact congrArg (Sum.inr ∘ Sum.inl) (prefixNetworkInput_injective hfit rfl 0 h)
  · exact False.elim (prefixNetworkInputs_separate hfit rfl rfl x y h)
  · exact False.elim (prefixNetworkInput_ne_rectangle hfit hdiag rfl 1 x y h)
  · exact False.elim (prefixNetworkInputs_separate hfit rfl rfl y x h.symm)
  · exact congrArg (Sum.inr ∘ Sum.inr) (prefixNetworkInput_injective hfit rfl 1 h)

/-- Exact capacity implies every retained endpoint has one physical role. -/
theorem prefixPhysicalInput_bijective {P d r n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q) :
    Function.Bijective (prefixPhysicalInput (P := P) hfit hdiag) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨prefixPhysicalInput_injective hfit hdiag, ?_⟩
  simp only [PrefixPhysicalInputs, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  rw [← hexact]
  ring

/-- The stage reindexing enumerates precisely the retained endpoint set. -/
theorem retainedSeedSlot_image (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard)) :
    Finset.univ.image (fun x : (Fin P × Fin Q) × Bool =>
      sortedSeedEndpoint candidates r Q gap hcard (retainedSeedSlot r P Q kept hsub hkept x)) =
        retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨retainedSeedSlot r P Q kept hsub hkept x, ?_, rfl⟩
    simp only [retainedSeedLabels, Finset.mem_product, Finset.mem_univ, and_true]
    exact (retainedSeedGroups r kept hsub).orderEmbOfFin_mem
      (by rw [retainedSeedGroups_card, hkept]) x.1.1
  · rw [retainedSeedEndpoints, Finset.card_image_of_injective _ hinj,
      retainedSeedLabels_card, hkept,
      Finset.card_image_of_injective _ (show Function.Injective (fun x : (Fin P × Fin Q) × Bool =>
        sortedSeedEndpoint candidates r Q gap hcard (retainedSeedSlot r P Q kept hsub hkept x)) from
        hinj.comp (retainedSeedSlot_injective r P Q kept hsub hkept))]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring_nf
    exact le_rfl

/-- Under exact capacity, the endpoints assigned to the three families of
physical locations are exactly the selected reservation, with no omissions. -/
theorem prefixPhysicalInput_retained_image (candidates : Finset ℕ) (r P Q gap d layers n : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q) :
    Finset.univ.image (fun x : PrefixPhysicalInputs P d layers n =>
      sortedSeedEndpoint candidates r Q gap hcard
        (retainedSeedSlot r P Q kept hsub hkept (prefixPhysicalInput hfit hdiag x))) =
      retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  change Finset.univ.image ((fun x : (Fin P × Fin Q) × Bool =>
    sortedSeedEndpoint candidates r Q gap hcard (retainedSeedSlot r P Q kept hsub hkept x)) ∘
      prefixPhysicalInput hfit hdiag) = _
  rw [← Finset.image_image, Finset.image_univ_of_surjective
    (prefixPhysicalInput_bijective hfit hdiag hexact).2]
  exact retainedSeedSlot_image candidates r P Q gap hcard kept hsub hkept hinj

/-- If the physical placement equations hold, every reserved endpoint appears
once in those cells. This conclusion does not assume independence of cells. -/
theorem prefixPhysical_realizes_retained {cell : Type*}
    (candidates : Finset ℕ) (r P Q gap d layers n : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (cells : PrefixPhysicalInputs P d layers n → cell) (entry : cell → ℕ)
    (hplace : ∀ x, entry (cells x) = sortedSeedEndpoint candidates r Q gap hcard
      (retainedSeedSlot r P Q kept hsub hkept (prefixPhysicalInput hfit hdiag x))) :
    Function.Injective cells ∧ Finset.univ.image (fun x => entry (cells x)) =
      retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  constructor
  · intro x y hxy
    apply (prefixPhysicalInput_injective hfit hdiag)
    apply (retainedSeedSlot_injective r P Q kept hsub hkept)
    apply hinj
    rw [← hplace x, ← hplace y, hxy]
  · have heq : (fun x => entry (cells x)) = (fun x =>
        sortedSeedEndpoint candidates r Q gap hcard
          (retainedSeedSlot r P Q kept hsub hkept (prefixPhysicalInput hfit hdiag x))) :=
      funext hplace
    rw [heq]
    exact prefixPhysicalInput_retained_image candidates r P Q gap d layers n hcard kept hsub hkept
      hinj hfit hdiag hexact

/-- Physical cells used by the diagonal rectangles, row layers, and the
transposed column layers, indexed by their common stage allocation. -/
def prefixPhysicalCells {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers) :
    PrefixPhysicalInputs P d layers n → Cell n
  | Sum.inl x => packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)
  | Sum.inr (Sum.inl x) => LayerPacking.sequenceCell rows (Fin.cast hrows.symm x.1, x.2)
  | Sum.inr (Sum.inr x) => (LayerPacking.sequenceCell cols (Fin.cast hcols.symm x.1, x.2)).swap

/-- The existing placement equations imply exact reservation coverage by the
actual rectangle and network cells. -/
theorem prefixPhysicalCells_realizes_retained {P d layers n L r Q gap : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (a : Cell n ≃ Fin (n * n))
    (hrectangle : ∀ x : Fin (P * (4 * d)) × Fin 4,
      entry a (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
        sortedSeedEndpoint candidates r Q gap hcard
          (retainedSeedSlot r P Q kept hsub hkept (prefixRectangleInput hdiag x)))
    (hrow : ∀ x, entry a (LayerPacking.sequenceCell rows x) =
      sortedSeedEndpoint candidates r Q gap hcard
        (retainedSeedSlot r P Q kept hsub hkept (prefixNetworkInput hfit hrows 0 x)))
    (hcol : ∀ x, entry a (LayerPacking.sequenceCell cols x).swap =
      sortedSeedEndpoint candidates r Q gap hcard
        (retainedSeedSlot r P Q kept hsub hkept (prefixNetworkInput hfit hcols 1 x))) :
    Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols) ∧
    Finset.univ.image (fun x => entry a (prefixPhysicalCells hrect hs choice rows cols hrows hcols x)) =
      retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  apply prefixPhysical_realizes_retained candidates r P Q gap d layers n hcard kept hsub hkept
    hinj hfit hdiag hexact _ (entry a)
  intro x
  rcases x with x | (x | x)
  · exact hrectangle x
  · simpa [prefixPhysicalCells, prefixPhysicalInput, prefixNetworkInput] using
      hrow (Fin.cast hrows.symm x.1, x.2)
  · simpa [prefixPhysicalCells, prefixPhysicalInput, prefixNetworkInput] using
      hcol (Fin.cast hcols.symm x.1, x.2)

end
end Sude
