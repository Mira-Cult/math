import Sude.PrefixLThreeStages
import Sude.GeneratedPrefix.LStage3.All

/-! The first four completely certified L stages as one separated family. -/
namespace Sude.GeneratedPrefix
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[irreducible] def LStage3.checkedLows : List ℕ := LStage3.lows

theorem LStage3.checkedLows_valid :
    PrefixStageBlock 16 55000000 23744473 26908477 LStage3.checkedLows := by
  rw [LStage3.checkedLows]
  exact LStage3.valid

theorem LStage3.checkedLows_length : LStage3.checkedLows.length = 14448 := by
  rw [LStage3.checkedLows]
  exact LStage3.length

def firstFourStageLows : Fin 4 → List ℕ :=
  ![LStage0.checkedLows, LStage1.checkedLows, LStage2.checkedLows, LStage3.checkedLows]

theorem stage0_disjoint_stage3 :
    Disjoint (pairFootprint LStage0.checkedLows.toFinset 2)
      (pairFootprint LStage3.checkedLows.toFinset 16) :=
  PrefixStageBlock.footprints_disjoint LStage0.checkedLows_valid LStage3.checkedLows_valid (by decide)

theorem stage1_disjoint_stage3 :
    Disjoint (pairFootprint LStage1.checkedLows.toFinset 4)
      (pairFootprint LStage3.checkedLows.toFinset 16) :=
  PrefixStageBlock.footprints_disjoint LStage1.checkedLows_valid LStage3.checkedLows_valid (by decide)

theorem stage2_disjoint_stage3 :
    Disjoint (pairFootprint LStage2.checkedLows.toFinset 8)
      (pairFootprint LStage3.checkedLows.toFinset 16) :=
  PrefixStageBlock.footprints_disjoint LStage2.checkedLows_valid LStage3.checkedLows_valid (by decide)

/-- Four checked stages, with every endpoint in the prescribed pool and
all stages separated, under the published prime-index lower bound. -/
def actualFirstFourStageFamily (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    CertifiedPrefixFamily 4 14448 n where
  lows := firstFourStageLows
  length := by
    intro j
    fin_cases j
    · simpa [firstFourStageLows] using LStage0.checkedLows_length
    · simpa [firstFourStageLows] using LStage1.checkedLows_length
    · simpa [firstFourStageLows] using LStage2.checkedLows_length
    · simpa [firstFourStageLows] using LStage3.checkedLows_length
  nodup := by
    intro j
    fin_cases j
    · simpa [firstFourStageLows] using LStage0.checkedLows_valid.sorted.nodup
    · simpa [firstFourStageLows] using LStage1.checkedLows_valid.sorted.nodup
    · simpa [firstFourStageLows] using LStage2.checkedLows_valid.sorted.nodup
    · simpa [firstFourStageLows] using LStage3.checkedLows_valid.sorted.nodup
  pool := by
    intro j
    fin_cases j
    · simpa [firstFourStageLows] using (LStage0.checkedLows_matching lower hn).1
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) LStage1.checkedLows_valid
      simpa [firstFourStageLows] using hm.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 2) lower hn (by decide) LStage2.checkedLows_valid
      simpa [firstFourStageLows] using hm.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 3) lower hn (by decide) LStage3.checkedLows_valid
      simpa [firstFourStageLows] using hm.1
  matching := by
    intro j
    fin_cases j
    · simpa [firstFourStageLows] using (LStage0.checkedLows_matching lower hn).2
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) LStage1.checkedLows_valid
      simpa [firstFourStageLows] using hm.2.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 2) lower hn (by decide) LStage2.checkedLows_valid
      simpa [firstFourStageLows] using hm.2.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 3) lower hn (by decide) LStage3.checkedLows_valid
      simpa [firstFourStageLows] using hm.2.1
  separated := by
    intro j k hne
    have h01 := firstStage_disjoint_secondStageCheckpoint
    have h02 := firstStage_disjoint_third
    have h12 := secondStage_disjoint_third
    have h03 := stage0_disjoint_stage3
    have h13 := stage1_disjoint_stage3
    have h23 := stage2_disjoint_stage3
    fin_cases j <;> fin_cases k
    all_goals first
      | exact False.elim (hne rfl)
      | simpa [firstFourStageLows] using h01
      | simpa [firstFourStageLows] using h01.symm
      | simpa [firstFourStageLows] using h02
      | simpa [firstFourStageLows] using h02.symm
      | simpa [firstFourStageLows] using h12
      | simpa [firstFourStageLows] using h12.symm
      | simpa [firstFourStageLows] using h03
      | simpa [firstFourStageLows] using h03.symm
      | simpa [firstFourStageLows] using h13
      | simpa [firstFourStageLows] using h13.symm
      | simpa [firstFourStageLows] using h23
      | simpa [firstFourStageLows] using h23.symm

/-- Retain the source-prescribed number of pairs for physical allocation. -/
def actualFirstFourStageValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : (Fin 4 × Fin (6 * (n + 8))) × Bool → pool n :=
  truncatePrefixValues (LStage0.retained_size hnmax) (actualFirstFourStageFamily lower hn).values

theorem actualFirstFourStageValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : Function.Injective (actualFirstFourStageValues lower hn hnmax) :=
  truncatePrefixValues_injective (LStage0.retained_size hnmax) _
    (actualFirstFourStageFamily lower hn).values_injective

theorem actualFirstFourStageValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) :
    ∀ j i, (actualFirstFourStageValues lower hn hnmax ((j, i), true)).val =
      (actualFirstFourStageValues lower hn hnmax ((j, i), false)).val + 2 ^ (j.val + 1) :=
  truncatePrefixValues_gap (LStage0.retained_size hnmax) _
    (actualFirstFourStageFamily lower hn).values_gap

end
end Sude.GeneratedPrefix
