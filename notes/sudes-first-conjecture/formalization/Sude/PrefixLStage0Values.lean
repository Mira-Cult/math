import Sude.PrefixStageFamily
import Sude.PrefixTruncation
import Sude.GeneratedPrefix.LStage0.All

/-! Pool-valued, source-ordered endpoints from the accepted first L stage. -/
namespace Sude.GeneratedPrefix.LStage0
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- An irreducible name prevents elaboration from expanding the entire
certified list when comparing indexed endpoint types. -/
@[irreducible] def checkedLows : List ℕ := lows

theorem checkedLows_length : checkedLows.length = 14448 := by
  rw [checkedLows]
  exact length

theorem checkedLows_nodup : checkedLows.Nodup := by
  rw [checkedLows]
  exact valid.sorted.nodup

theorem checkedLows_matching (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    (∀ p ∈ checkedLows.toFinset, p ∈ pool n ∧ p + 2 ∈ pool n) ∧
      PairwiseDisjointPairs checkedLows.toFinset 2 := by
  rw [checkedLows]
  exact ⟨(pool_matching lower hn).1, (pool_matching lower hn).2.1⟩

/-- All 14,448 certified first-stage pairs, in source order. -/
def poolValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    Fin 14448 × Bool → pool n := fun x =>
  stagePairPoolValues checkedLows 2 (checkedLows_matching lower hn).1
    (Fin.cast checkedLows_length.symm x.1, x.2)

theorem poolValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    Function.Injective (poolValues lower hn) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have he := stagePairPoolValues_injective checkedLows 2 (checkedLows_matching lower hn).1
    checkedLows_nodup (by decide) (checkedLows_matching lower hn).2 h
  have hi := Fin.cast_injective checkedLows_length.symm (congrArg Prod.fst he)
  have hs := congrArg Prod.snd he
  exact Prod.ext hi hs

theorem poolValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (i : Fin 14448) :
    (poolValues lower hn (i, true)).val = (poolValues lower hn (i, false)).val + 2 :=
  stagePairPoolValues_gap checkedLows 2 (checkedLows_matching lower hn).1
    (Fin.cast checkedLows_length.symm i)

theorem poolValues_formula (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (i : Fin 14448) (side : Bool) :
    (poolValues lower hn (i, side)).val =
      checkedLows.get (Fin.cast checkedLows_length.symm i) + if side then 2 else 0 :=
  stagePairEndpoint_formula checkedLows 2 (Fin.cast checkedLows_length.symm i) side

/-- The source retains precisely this many pairs for an order in the L band. -/
theorem retained_size {n : ℕ} (hnmax : n ≤ 2400) : 6 * (n + 8) ≤ 14448 := by omega

def retainedPoolValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) (hnmax : n ≤ 2400) :
    Fin (6 * (n + 8)) × Bool → pool n := fun x =>
  poolValues lower hn (Fin.castLE (retained_size hnmax) x.1, x.2)

theorem retainedPoolValues_injective (lower : RSIndexLower) {n : ℕ}
    (hn : 2000 ≤ n) (hnmax : n ≤ 2400) :
    Function.Injective (retainedPoolValues lower hn hnmax) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have he := poolValues_injective lower hn h
  have hi := Fin.castLE_injective (retained_size hnmax) (congrArg Prod.fst he)
  have hs := congrArg Prod.snd he
  exact Prod.ext hi hs

theorem retainedPoolValues_gap (lower : RSIndexLower) {n : ℕ}
    (hn : 2000 ≤ n) (hnmax : n ≤ 2400) (i : Fin (6 * (n + 8))) :
    (retainedPoolValues lower hn hnmax (i, true)).val =
      (retainedPoolValues lower hn hnmax (i, false)).val + 2 :=
  poolValues_gap lower hn (Fin.castLE (retained_size hnmax) i)

/-- The retained source prefix has exactly two distinct pool entries per pair. -/
theorem retainedPoolValues_card (lower : RSIndexLower) {n : ℕ}
    (hn : 2000 ≤ n) (hnmax : n ≤ 2400) :
    ((Finset.univ : Finset (Fin (6 * (n + 8)) × Bool)).image
      (fun x => (retainedPoolValues lower hn hnmax x).val)).card = 2 * (6 * (n + 8)) := by
  have hi : Function.Injective (fun x => (retainedPoolValues lower hn hnmax x).val) := by
    intro x y h
    exact retainedPoolValues_injective lower hn hnmax (Subtype.ext h)
  rw [Finset.card_image_of_injective _ hi]
  simp [Fintype.card_prod]
  omega

/-- The first stage is a complete one-stage family. This does not assert
separation from any of the other 23 source stages. -/
def singleStageFamily (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    CertifiedPrefixFamily 1 14448 n where
  lows := fun _ => checkedLows
  length := fun _ => checkedLows_length
  nodup := fun _ => checkedLows_nodup
  pool := by
    intro j p hp
    have hj : j.val = 0 := by omega
    simpa [hj] using (checkedLows_matching lower hn).1 p hp
  matching := by
    intro j
    have hj : j.val = 0 := by omega
    simpa [hj] using (checkedLows_matching lower hn).2
  separated := by
    intro j k hne
    exact False.elim (hne (Subsingleton.elim j k))

/-- The first stage in the exact index shape consumed by the physical allocator. -/
def allocatorValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) (hnmax : n ≤ 2400) :
    (Fin 1 × Fin (6 * (n + 8))) × Bool → pool n :=
  truncatePrefixValues (retained_size hnmax) (singleStageFamily lower hn).values

theorem allocatorValues_injective (lower : RSIndexLower) {n : ℕ}
    (hn : 2000 ≤ n) (hnmax : n ≤ 2400) :
    Function.Injective (allocatorValues lower hn hnmax) :=
  truncatePrefixValues_injective (retained_size hnmax) _ (singleStageFamily lower hn).values_injective

theorem allocatorValues_gap (lower : RSIndexLower) {n : ℕ}
    (hn : 2000 ≤ n) (hnmax : n ≤ 2400) :
    ∀ j i, (allocatorValues lower hn hnmax ((j, i), true)).val =
      (allocatorValues lower hn hnmax ((j, i), false)).val + 2 ^ (j.val + 1) :=
  truncatePrefixValues_gap (retained_size hnmax) _ (singleStageFamily lower hn).values_gap

end
end Sude.GeneratedPrefix.LStage0
