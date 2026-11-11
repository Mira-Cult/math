import Sude.NarrowSeedPlacement
import Sude.PrefixAllocationCoverage

/-! Physical placement of stage-permuted retained prime pairs. -/
namespace Sude
noncomputable section

/-- Reindex pair slots independently within each stage, preserving both
endpoints of every pair. -/
def stagePairPermutation {P Q : ℕ} (ω : Fin P → Equiv.Perm (Fin Q)) :
    ((Fin P × Fin Q) × Bool) ≃ ((Fin P × Fin Q) × Bool) where
  toFun x := ((x.1.1, ω x.1.1 x.1.2), x.2)
  invFun x := ((x.1.1, (ω x.1.1).symm x.1.2), x.2)
  left_inv x := by rcases x with ⟨⟨j, i⟩, b⟩; simp
  right_inv x := by rcases x with ⟨⟨j, i⟩, b⟩; simp

/-- The permuted stage entries are the original retained pool values. -/
def permutedRetainedSeedValues {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (ω : Fin P → Equiv.Perm (Fin Q)) : (Fin P × Fin Q) × Bool → pool n :=
  retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ∘ stagePairPermutation ω

theorem permutedRetainedSeedValues_injective {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (ω : Fin P → Equiv.Perm (Fin Q)) :
    Function.Injective (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω) :=
  (retainedSeedPoolValues_injective candidates r P Q gap hcard kept hsub hkept initial hav hinj).comp
    (stagePairPermutation ω).injective

theorem permutedRetainedSeedValues_gap {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (ω : Fin P → Equiv.Perm (Fin Q)) :
    ∀ j i, (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω ((j, i), true)).val =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω ((j, i), false)).val + gap := by
  intro j i
  exact retainedSeedPoolValues_gap candidates r P Q gap hcard kept hsub hkept initial hav j (ω j i)

theorem permutedRetainedSeedValues_avoid {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (ω : Fin P → Equiv.Perm (Fin Q)) :
    ∀ x, (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω x).val ∉ initial := by
  intro x
  exact retainedSeedPoolValues_avoid candidates r P Q gap hcard kept hsub hkept initial hav
    (stagePairPermutation ω x)

/-- Permuting all stage slots preserves exactly the retained endpoint set. -/
theorem permutedRetainedSeedValues_image {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (ω : Fin P → Equiv.Perm (Fin Q)) :
    Finset.univ.image (fun x => (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω x).val) =
      retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  change Finset.univ.image ((fun x : (Fin P × Fin Q) × Bool =>
    sortedSeedEndpoint candidates r Q gap hcard (retainedSeedSlot r P Q kept hsub hkept x)) ∘
      stagePairPermutation ω) = _
  rw [← Finset.image_image, Finset.image_univ_of_surjective (stagePairPermutation ω).surjective]
  exact retainedSeedSlot_image candidates r P Q gap hcard kept hsub hkept hinj

/-- Install the permuted actual seed pairs in the physical rectangle and network cells. -/
theorem install_permuted_retained_seed_pairs {n r P Q gap d layers L B : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q)
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (ω : Fin P → Equiv.Perm (Fin Q))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = P * layers) (hclen : colPerms.length = P * layers)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ B)
    (hcapacity : 4 * ((B + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hfree : ∀ x : Fin (P * (4 * d)) × Fin 4,
      packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ∉ base) :
    let values := permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
    ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
      (hcols : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport hrect hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        ((base ∪ allocatedBridgeRectangleSupport hrect hs choice) ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (P * (4 * d)) × Fin 4,
        entry b (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
          (values (prefixRectangleInput hdiag x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (values (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (values (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + variablePrefixNetworkGap (fun _ => gap) hrlen (Fin.cast hrows i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + variablePrefixNetworkGap (fun _ => gap) hclen (Fin.cast hcols i) e) ∧
      (∀ c ∈ base, entry b c = entry a c) := by
  dsimp only
  exact install_variable_prefix_diagonal_and_ordinary hfit hdiag hrect hs choice (fun _ => gap)
    (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω)
    (permutedRetainedSeedValues_injective candidates r P Q gap hcard kept hsub hkept initial hav hinj ω)
    (permutedRetainedSeedValues_gap candidates r P Q gap hcard kept hsub hkept initial hav ω)
    initial (permutedRetainedSeedValues_avoid candidates r P Q gap hcard kept hsub hkept initial hav ω)
    rowPerms colPerms hrlen hclen hrderange hcderange base hrload hcload hcapacity a hbase hfree

/-- When the physical placement equations use the permuted stage values,
the physical cells are distinct and contain exactly the retained endpoints. -/
theorem permutedPrefixPhysical_realizes_retained {cell : Type*} {n r P Q gap d layers : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (ω : Fin P → Equiv.Perm (Fin Q))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (cells : PrefixPhysicalInputs P d layers n → cell) (entry : cell → ℕ)
    (hplace : ∀ x, entry (cells x) =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        (prefixPhysicalInput hfit hdiag x)).val) :
    Function.Injective cells ∧ Finset.univ.image (fun x => entry (cells x)) =
      retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  let values := permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
  have hv : Function.Injective (fun x => (values x).val) := by
    intro x y h
    apply permutedRetainedSeedValues_injective candidates r P Q gap hcard kept hsub hkept initial hav hinj ω
    exact Subtype.ext h
  constructor
  · intro x y hxy
    apply prefixPhysicalInput_injective hfit hdiag
    apply hv
    change (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
      (prefixPhysicalInput hfit hdiag x)).val =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        (prefixPhysicalInput hfit hdiag y)).val
    rw [← hplace x, ← hplace y, hxy]
  · have heq : (fun x => entry (cells x)) = (fun x => (values (prefixPhysicalInput hfit hdiag x)).val) :=
      funext hplace
    rw [heq]
    change Finset.univ.image ((fun x => (values x).val) ∘ prefixPhysicalInput hfit hdiag) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective
      (prefixPhysicalInput_bijective hfit hdiag hexact).2]
    exact permutedRetainedSeedValues_image candidates r P Q gap hcard kept hsub hkept initial hav hinj ω

/-- The rectangle, row and transposed-column cells in the square exhaust the
permuted retained reservation whenever their placement equations hold. -/
theorem permutedPrefixPhysicalCells_realizes_retained {n r P Q gap d layers L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (ω : Fin P → Equiv.Perm (Fin Q))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (a : Cell n ≃ Fin (n * n))
    (hrectangle : ∀ x : Fin (P * (4 * d)) × Fin 4,
      entry a (packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2)) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixRectangleInput hdiag x)).val)
    (hrow : ∀ x, entry a (LayerPacking.sequenceCell rows x) =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        (prefixNetworkInput hfit hrows 0 x)).val)
    (hcol : ∀ x, entry a (LayerPacking.sequenceCell cols x).swap =
      (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
        (prefixNetworkInput hfit hcols 1 x)).val) :
    Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols) ∧
    Finset.univ.image (fun x => entry a (prefixPhysicalCells hrect hs choice rows cols hrows hcols x)) =
      retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  apply permutedPrefixPhysical_realizes_retained candidates hcard kept hsub hkept initial hav hinj ω
    hfit hdiag hexact _ (entry a)
  intro x
  rcases x with x | (x | x)
  · exact hrectangle x
  · simpa [prefixPhysicalCells, prefixPhysicalInput, prefixNetworkInput] using
      hrow (Fin.cast hrows.symm x.1, x.2)
  · simpa [prefixPhysicalCells, prefixPhysicalInput, prefixNetworkInput] using
      hcol (Fin.cast hcols.symm x.1, x.2)

end
end Sude
