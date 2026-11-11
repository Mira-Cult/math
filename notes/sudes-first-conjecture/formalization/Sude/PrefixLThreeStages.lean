import Sude.PrefixLTwoStages
import Sude.GeneratedPrefix.LStage2.All

/-! The first three completely certified L stages as one separated family. -/
namespace Sude.GeneratedPrefix
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[irreducible] def LStage2.checkedLows : List ℕ := LStage2.lows

theorem LStage2.checkedLows_valid :
    PrefixStageBlock 8 55000000 20288483 23379269 LStage2.checkedLows := by
  rw [LStage2.checkedLows]
  exact LStage2.valid

theorem LStage2.checkedLows_length : LStage2.checkedLows.length = 14448 := by
  rw [LStage2.checkedLows]
  exact LStage2.length

def firstThreeStageLows : Fin 3 → List ℕ :=
  ![LStage0.checkedLows, LStage1.checkedLows, LStage2.checkedLows]

theorem firstStage_disjoint_third :
    Disjoint (pairFootprint LStage0.checkedLows.toFinset 2)
      (pairFootprint LStage2.checkedLows.toFinset 8) :=
  PrefixStageBlock.footprints_disjoint LStage0.checkedLows_valid LStage2.checkedLows_valid (by decide)

theorem secondStage_disjoint_third :
    Disjoint (pairFootprint LStage1.checkedLows.toFinset 4)
      (pairFootprint LStage2.checkedLows.toFinset 8) :=
  PrefixStageBlock.footprints_disjoint LStage1.checkedLows_valid LStage2.checkedLows_valid (by decide)

/-- Three checked stages, with every endpoint in the prescribed pool and
all stages separated, under the published prime-index lower bound. -/
def actualFirstThreeStageFamily (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    CertifiedPrefixFamily 3 14448 n where
  lows := firstThreeStageLows
  length := by
    intro j
    fin_cases j
    · simpa [firstThreeStageLows] using LStage0.checkedLows_length
    · simpa [firstThreeStageLows] using LStage1.checkedLows_length
    · simpa [firstThreeStageLows] using LStage2.checkedLows_length
  nodup := by
    intro j
    fin_cases j
    · simpa [firstThreeStageLows] using LStage0.checkedLows_valid.sorted.nodup
    · simpa [firstThreeStageLows] using LStage1.checkedLows_valid.sorted.nodup
    · simpa [firstThreeStageLows] using LStage2.checkedLows_valid.sorted.nodup
  pool := by
    intro j
    fin_cases j
    · simpa [firstThreeStageLows] using (LStage0.checkedLows_matching lower hn).1
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) LStage1.checkedLows_valid
      simpa [firstThreeStageLows] using hm.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 2) lower hn (by decide) LStage2.checkedLows_valid
      simpa [firstThreeStageLows] using hm.1
  matching := by
    intro j
    fin_cases j
    · simpa [firstThreeStageLows] using (LStage0.checkedLows_matching lower hn).2
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) LStage1.checkedLows_valid
      simpa [firstThreeStageLows] using hm.2.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 2) lower hn (by decide) LStage2.checkedLows_valid
      simpa [firstThreeStageLows] using hm.2.1
  separated := by
    intro j k hne
    have h01 := firstStage_disjoint_secondStageCheckpoint
    have h02 := firstStage_disjoint_third
    have h12 := secondStage_disjoint_third
    fin_cases j <;> fin_cases k
    all_goals first
      | exact False.elim (hne rfl)
      | simpa [firstThreeStageLows] using h01
      | simpa [firstThreeStageLows] using h01.symm
      | simpa [firstThreeStageLows] using h02
      | simpa [firstThreeStageLows] using h02.symm
      | simpa [firstThreeStageLows] using h12
      | simpa [firstThreeStageLows] using h12.symm

/-- Retain the source-prescribed number of pairs for physical allocation. -/
def actualFirstThreeStageValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : (Fin 3 × Fin (6 * (n + 8))) × Bool → pool n :=
  truncatePrefixValues (LStage0.retained_size hnmax) (actualFirstThreeStageFamily lower hn).values

theorem actualFirstThreeStageValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : Function.Injective (actualFirstThreeStageValues lower hn hnmax) :=
  truncatePrefixValues_injective (LStage0.retained_size hnmax) _
    (actualFirstThreeStageFamily lower hn).values_injective

theorem actualFirstThreeStageValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) :
    ∀ j i, (actualFirstThreeStageValues lower hn hnmax ((j, i), true)).val =
      (actualFirstThreeStageValues lower hn hnmax ((j, i), false)).val + 2 ^ (j.val + 1) :=
  truncatePrefixValues_gap (LStage0.retained_size hnmax) _
    (actualFirstThreeStageFamily lower hn).values_gap

end
end Sude.GeneratedPrefix
