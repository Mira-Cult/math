import Sude.LayerPacking
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Hall decomposition of an actual regular bipartite cell factor. -/
namespace Sude
noncomputable section

/-- Every row and column has exactly `k` edges in this physical cell set. -/
def CellFactorRegular {n : ℕ} (E : Finset (Cell n)) (k : ℕ) : Prop :=
  (∀ i, (LayerPacking.rowUsed E i).card = k) ∧
    ∀ j, (LayerPacking.colUsed E j).card = k

/-- The actual cell edges of a perfect row-to-column matching. -/
def permutationCells {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Cell n) :=
  Finset.univ.image (fun i => (i, π i))

@[simp] theorem mem_permutationCells {n : ℕ} (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    (i, j) ∈ permutationCells π ↔ j = π i := by
  simp [permutationCells, Prod.ext_iff, eq_comm]

/-- A positive regular bipartite factor satisfies Hall's condition, by
counting the same physical edges from rows and from columns. -/
theorem regular_factor_perfect_matching {n k : ℕ} (E : Finset (Cell n))
    (hk : 0 < k) (hreg : CellFactorRegular E k) :
    ∃ π : Equiv.Perm (Fin n), permutationCells π ⊆ E := by
  classical
  let neighbors : Fin n → Finset (Fin n) := fun i => LayerPacking.rowUsed E i
  have hall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion neighbors).card := by
    intro S
    let T := S.biUnion neighbors
    have hrow : ∀ i ∈ S, k ≤ (T.bipartiteAbove (fun i j => (i, j) ∈ E) i).card := by
      intro i hi
      have heq : T.bipartiteAbove (fun i j => (i, j) ∈ E) i = neighbors i := by
        ext j
        simp only [Finset.mem_bipartiteAbove, neighbors, LayerPacking.rowUsed,
          Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact And.right
        · intro hij
          exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, by simp [neighbors, LayerPacking.rowUsed, hij]⟩, hij⟩
      rw [heq]
      exact (hreg.1 i).ge
    have hcol : ∀ j ∈ T, (S.bipartiteBelow (fun i j => (i, j) ∈ E) j).card ≤ k := by
      intro j hj
      have hsub : S.bipartiteBelow (fun i j => (i, j) ∈ E) j ⊆ LayerPacking.colUsed E j := by
        intro i hi
        have he : (i, j) ∈ E := (Finset.mem_filter.mp hi).2
        simp [LayerPacking.colUsed, he]
      exact (Finset.card_le_card hsub).trans_eq (hreg.2 j)
    have hcount : S.card * k ≤ T.card * k :=
      Finset.card_mul_le_card_mul (fun i j : Fin n => (i, j) ∈ E) hrow hcol
    exact Nat.le_of_mul_le_mul_right hcount hk
  obtain ⟨f, hf, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hall
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  refine ⟨π, ?_⟩
  intro z hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  have hi := hfmem i
  change (i, f i) ∈ E
  simpa [neighbors, LayerPacking.rowUsed] using hi

theorem rowUsed_remove_matching {n : ℕ} (E : Finset (Cell n)) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    LayerPacking.rowUsed (E \ permutationCells π) i = (LayerPacking.rowUsed E i).erase (π i) := by
  ext j
  simp [LayerPacking.rowUsed, mem_permutationCells, and_comm]

theorem colUsed_remove_matching {n : ℕ} (E : Finset (Cell n)) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    LayerPacking.colUsed (E \ permutationCells π) j = (LayerPacking.colUsed E j).erase (π.symm j) := by
  ext i
  have heq : j = π i ↔ i = π.symm j := by
    constructor
    · intro h
      apply π.injective
      simpa using h.symm
    · intro h
      subst i
      simp
  simp [LayerPacking.colUsed, mem_permutationCells, heq, and_comm]

/-- Removing a genuine perfect matching lowers every row and every column
degree by exactly one. -/
theorem regular_factor_remove_matching {n k : ℕ} (E : Finset (Cell n))
    (π : Equiv.Perm (Fin n)) (hπ : permutationCells π ⊆ E)
    (hreg : CellFactorRegular E (k + 1)) :
    CellFactorRegular (E \ permutationCells π) k := by
  constructor
  · intro i
    have hm : π i ∈ LayerPacking.rowUsed E i := by
      have he : (i, π i) ∈ E := hπ (by simp)
      simpa [LayerPacking.rowUsed] using he
    rw [rowUsed_remove_matching, Finset.card_erase_of_mem hm, hreg.1 i]
    omega
  · intro j
    have hm : π.symm j ∈ LayerPacking.colUsed E j := by
      have he : (π.symm j, j) ∈ E := hπ (by simp)
      simpa [LayerPacking.colUsed] using he
    rw [colUsed_remove_matching, Finset.card_erase_of_mem hm, hreg.2 j]
    omega

/-- Each constructor removes an entire physical perfect matching from the
remaining factor before the next matching is chosen. -/
inductive RegularMatchingDecomposition {n : ℕ} :
    Finset (Cell n) → List (Equiv.Perm (Fin n)) → Prop
  | nil : RegularMatchingDecomposition ∅ []
  | cons (E : Finset (Cell n)) (π : Equiv.Perm (Fin n)) (tail : List (Equiv.Perm (Fin n)))
      (hπ : permutationCells π ⊆ E)
      (hrest : RegularMatchingDecomposition (E \ permutationCells π) tail) :
      RegularMatchingDecomposition E (π :: tail)

/-- Every regular factor, including the zero-degree factor, decomposes into
exactly its degree many successively removed perfect matchings. -/
theorem regular_factor_matching_decomposition {n k : ℕ} (E : Finset (Cell n))
    (hreg : CellFactorRegular E k) :
    ∃ ps : List (Equiv.Perm (Fin n)), ps.length = k ∧ RegularMatchingDecomposition E ps := by
  induction k generalizing E with
  | zero =>
    have hE : E = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨i, j⟩ hij
      have hj : j ∈ LayerPacking.rowUsed E i := by simpa [LayerPacking.rowUsed] using hij
      have hempty : LayerPacking.rowUsed E i = ∅ := Finset.card_eq_zero.mp (hreg.1 i)
      simp [hempty] at hj
    subst E
    exact ⟨[], rfl, RegularMatchingDecomposition.nil⟩
  | succ k ih =>
    obtain ⟨π, hπ⟩ := regular_factor_perfect_matching E (by omega) hreg
    have hrest := regular_factor_remove_matching E π hπ hreg
    obtain ⟨ps, hlen, hdecomp⟩ := ih (E \ permutationCells π) hrest
    exact ⟨π :: ps, by simp [hlen], RegularMatchingDecomposition.cons E π ps hπ hdecomp⟩

def permutationCellsUnion {n : ℕ} : List (Equiv.Perm (Fin n)) → Finset (Cell n)
  | [] => ∅
  | π :: tail => permutationCells π ∪ permutationCellsUnion tail

theorem RegularMatchingDecomposition.cover {n : ℕ} {E : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (h : RegularMatchingDecomposition E ps) :
    permutationCellsUnion ps = E := by
  induction h with
  | nil => rfl
  | cons E π tail hπ hrest ih =>
    simp only [permutationCellsUnion, ih]
    exact Finset.union_sdiff_of_subset hπ

theorem RegularMatchingDecomposition.member_subset {n : ℕ} {E : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (h : RegularMatchingDecomposition E ps)
    {π : Equiv.Perm (Fin n)} (hπ : π ∈ ps) : permutationCells π ⊆ E := by
  induction h with
  | nil => simp at hπ
  | cons E σ tail hσ hrest ih =>
    rcases List.mem_cons.mp hπ with rfl | hπ
    · exact hσ
    · exact (ih hπ).trans Finset.sdiff_subset

theorem RegularMatchingDecomposition.pairwise_disjoint {n : ℕ} {E : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (h : RegularMatchingDecomposition E ps) :
    ps.Pairwise (fun π σ => Disjoint (permutationCells π) (permutationCells σ)) := by
  induction h with
  | nil => simp
  | cons E π tail hπ hrest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro σ hσ
    have hsub := hrest.member_subset hσ
    apply Finset.disjoint_left.mpr
    intro z hzπ hzσ
    exact (Finset.mem_sdiff.mp (hsub hzσ)).2 hzπ

/-- Explicitly expose exact coverage and physical disjointness, suitable
for assigning one value block to each matching. -/
theorem regular_factor_disjoint_matchings {n k : ℕ} (E : Finset (Cell n))
    (hreg : CellFactorRegular E k) :
    ∃ ps : List (Equiv.Perm (Fin n)), ps.length = k ∧
      ps.Pairwise (fun π σ => Disjoint (permutationCells π) (permutationCells σ)) ∧
      permutationCellsUnion ps = E := by
  obtain ⟨ps, hlen, hdecomp⟩ := regular_factor_matching_decomposition E hreg
  exact ⟨ps, hlen, hdecomp.pairwise_disjoint, hdecomp.cover⟩

theorem mem_permutationCellsUnion {n : ℕ} (ps : List (Equiv.Perm (Fin n))) (z : Cell n) :
    z ∈ permutationCellsUnion ps ↔ ∃ π ∈ ps, z ∈ permutationCells π := by
  induction ps with
  | nil => simp [permutationCellsUnion]
  | cons π ps ih =>
    simp only [permutationCellsUnion, Finset.mem_union, ih, List.mem_cons]
    aesop

/-- The slot at matching index `j` and row `i` is an actual factor cell. -/
def regularMatchingSlot {n : ℕ} (ps : List (Equiv.Perm (Fin n)))
    (x : Fin ps.length × Fin n) : Cell n := (x.2, (ps.get x.1) x.2)

theorem regularMatchingSlot_mem {n : ℕ} {E : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (h : RegularMatchingDecomposition E ps)
    (x : Fin ps.length × Fin n) : regularMatchingSlot ps x ∈ E := by
  apply h.member_subset (List.get_mem ps x.1)
  simp [regularMatchingSlot]

/-- Matching slots cannot alias, even across different matchings. -/
theorem regularMatchingSlot_injective {n : ℕ} {ps : List (Equiv.Perm (Fin n))}
    (hpair : ps.Pairwise (fun π σ => Disjoint (permutationCells π) (permutationCells σ))) :
    Function.Injective (regularMatchingSlot ps) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ heq
  have hil : i = l := congrArg Prod.fst heq
  by_cases hjk : j = k
  · exact Prod.ext hjk hil
  · have hjmem : regularMatchingSlot ps (j, i) ∈ permutationCells (ps.get j) := by
      simp [regularMatchingSlot]
    have hkmem : regularMatchingSlot ps (j, i) ∈ permutationCells (ps.get k) := by
      rw [heq]
      simp [regularMatchingSlot]
    rcases lt_or_gt_of_ne hjk with hjk' | hkj'
    · exact False.elim (Finset.disjoint_left.mp (hpair.rel_get_of_lt hjk') hjmem hkmem)
    · exact False.elim (Finset.disjoint_left.mp (hpair.rel_get_of_lt hkj') hkmem hjmem)

theorem regularMatchingSlot_surjective {n : ℕ} {E : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (h : RegularMatchingDecomposition E ps)
    (z : Cell n) (hz : z ∈ E) : ∃ x, regularMatchingSlot ps x = z := by
  have hz' : z ∈ permutationCellsUnion ps := h.cover ▸ hz
  obtain ⟨π, hπ, hzπ⟩ := (mem_permutationCellsUnion ps z).1 hz'
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hπ
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzπ
  refine ⟨(j, i), ?_⟩
  change (i, ps.get j i) = z
  rw [hj]
  exact hi

/-- Every factor cell corresponds bijectively to its matching and row. -/
def regularMatchingSlotEquiv {n : ℕ} {E : Finset (Cell n)}
    {ps : List (Equiv.Perm (Fin n))} (h : RegularMatchingDecomposition E ps) :
    (Fin ps.length × Fin n) ≃ {z // z ∈ E} :=
  Equiv.ofBijective (fun x => ⟨regularMatchingSlot ps x, regularMatchingSlot_mem h x⟩)
    ⟨fun x y heq => regularMatchingSlot_injective h.pairwise_disjoint (congrArg Subtype.val heq),
      fun ⟨z, hz⟩ => by
        obtain ⟨x, hx⟩ := regularMatchingSlot_surjective h z hz
        exact ⟨x, Subtype.ext hx⟩⟩

end
end Sude
