import Sude.PrefixLFourStages
import Sude.GeneratedPrefix.LStage4.All
import Sude.GeneratedPrefix.LStage5.All

/-! The first six completely certified L stages as one separated family. -/
namespace Sude.GeneratedPrefix
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[irreducible] def LStage4.checkedLows : List ℕ := LStage4.lows

theorem LStage4.checkedLows_valid :
    PrefixStageBlock 32 55000000 26974049 30197159 LStage4.checkedLows := by
  rw [LStage4.checkedLows]
  exact LStage4.valid

theorem LStage4.checkedLows_length : LStage4.checkedLows.length = 14448 := by
  rw [LStage4.checkedLows]
  exact LStage4.length

@[irreducible] def LStage5.checkedLows : List ℕ := LStage5.lows

theorem LStage5.checkedLows_valid :
    PrefixStageBlock 64 55000000 30205999 33465547 LStage5.checkedLows := by
  rw [LStage5.checkedLows]
  exact LStage5.valid

theorem LStage5.checkedLows_length : LStage5.checkedLows.length = 14448 := by
  rw [LStage5.checkedLows]
  exact LStage5.length

def firstSixStageLows : Fin 6 → List ℕ :=
  ![LStage0.checkedLows, LStage1.checkedLows, LStage2.checkedLows, LStage3.checkedLows, LStage4.checkedLows, LStage5.checkedLows]

theorem stage0_disjoint_stage4 :
    Disjoint (pairFootprint LStage0.checkedLows.toFinset 2)
      (pairFootprint LStage4.checkedLows.toFinset 32) :=
  PrefixStageBlock.footprints_disjoint LStage0.checkedLows_valid LStage4.checkedLows_valid (by decide)

theorem stage1_disjoint_stage4 :
    Disjoint (pairFootprint LStage1.checkedLows.toFinset 4)
      (pairFootprint LStage4.checkedLows.toFinset 32) :=
  PrefixStageBlock.footprints_disjoint LStage1.checkedLows_valid LStage4.checkedLows_valid (by decide)

theorem stage2_disjoint_stage4 :
    Disjoint (pairFootprint LStage2.checkedLows.toFinset 8)
      (pairFootprint LStage4.checkedLows.toFinset 32) :=
  PrefixStageBlock.footprints_disjoint LStage2.checkedLows_valid LStage4.checkedLows_valid (by decide)

theorem stage3_disjoint_stage4 :
    Disjoint (pairFootprint LStage3.checkedLows.toFinset 16)
      (pairFootprint LStage4.checkedLows.toFinset 32) :=
  PrefixStageBlock.footprints_disjoint LStage3.checkedLows_valid LStage4.checkedLows_valid (by decide)

theorem stage0_disjoint_stage5 :
    Disjoint (pairFootprint LStage0.checkedLows.toFinset 2)
      (pairFootprint LStage5.checkedLows.toFinset 64) :=
  PrefixStageBlock.footprints_disjoint LStage0.checkedLows_valid LStage5.checkedLows_valid (by decide)

theorem stage1_disjoint_stage5 :
    Disjoint (pairFootprint LStage1.checkedLows.toFinset 4)
      (pairFootprint LStage5.checkedLows.toFinset 64) :=
  PrefixStageBlock.footprints_disjoint LStage1.checkedLows_valid LStage5.checkedLows_valid (by decide)

theorem stage2_disjoint_stage5 :
    Disjoint (pairFootprint LStage2.checkedLows.toFinset 8)
      (pairFootprint LStage5.checkedLows.toFinset 64) :=
  PrefixStageBlock.footprints_disjoint LStage2.checkedLows_valid LStage5.checkedLows_valid (by decide)

theorem stage3_disjoint_stage5 :
    Disjoint (pairFootprint LStage3.checkedLows.toFinset 16)
      (pairFootprint LStage5.checkedLows.toFinset 64) :=
  PrefixStageBlock.footprints_disjoint LStage3.checkedLows_valid LStage5.checkedLows_valid (by decide)

theorem stage4_disjoint_stage5 :
    Disjoint (pairFootprint LStage4.checkedLows.toFinset 32)
      (pairFootprint LStage5.checkedLows.toFinset 64) :=
  PrefixStageBlock.footprints_disjoint LStage4.checkedLows_valid LStage5.checkedLows_valid (by decide)

/-- Six checked stages, with every endpoint in the prescribed pool and
all stages separated, under the published prime-index lower bound. -/
def actualFirstSixStageFamily (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    CertifiedPrefixFamily 6 14448 n where
  lows := firstSixStageLows
  length := by
    intro j
    fin_cases j
    · simpa [firstSixStageLows] using LStage0.checkedLows_length
    · simpa [firstSixStageLows] using LStage1.checkedLows_length
    · simpa [firstSixStageLows] using LStage2.checkedLows_length
    · simpa [firstSixStageLows] using LStage3.checkedLows_length
    · simpa [firstSixStageLows] using LStage4.checkedLows_length
    · simpa [firstSixStageLows] using LStage5.checkedLows_length
  nodup := by
    intro j
    fin_cases j
    · simpa [firstSixStageLows] using LStage0.checkedLows_valid.sorted.nodup
    · simpa [firstSixStageLows] using LStage1.checkedLows_valid.sorted.nodup
    · simpa [firstSixStageLows] using LStage2.checkedLows_valid.sorted.nodup
    · simpa [firstSixStageLows] using LStage3.checkedLows_valid.sorted.nodup
    · simpa [firstSixStageLows] using LStage4.checkedLows_valid.sorted.nodup
    · simpa [firstSixStageLows] using LStage5.checkedLows_valid.sorted.nodup
  pool := by
    intro j
    fin_cases j
    · simpa [firstSixStageLows] using (LStage0.checkedLows_matching lower hn).1
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) LStage1.checkedLows_valid
      simpa [firstSixStageLows] using hm.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 2) lower hn (by decide) LStage2.checkedLows_valid
      simpa [firstSixStageLows] using hm.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 3) lower hn (by decide) LStage3.checkedLows_valid
      simpa [firstSixStageLows] using hm.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 4) lower hn (by decide) LStage4.checkedLows_valid
      simpa [firstSixStageLows] using hm.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 5) lower hn (by decide) LStage5.checkedLows_valid
      simpa [firstSixStageLows] using hm.1
  matching := by
    intro j
    fin_cases j
    · simpa [firstSixStageLows] using (LStage0.checkedLows_matching lower hn).2
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) LStage1.checkedLows_valid
      simpa [firstSixStageLows] using hm.2.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 2) lower hn (by decide) LStage2.checkedLows_valid
      simpa [firstSixStageLows] using hm.2.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 3) lower hn (by decide) LStage3.checkedLows_valid
      simpa [firstSixStageLows] using hm.2.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 4) lower hn (by decide) LStage4.checkedLows_valid
      simpa [firstSixStageLows] using hm.2.1
    · have hm := PrefixStageBlock.L_pool_matching (j := 5) lower hn (by decide) LStage5.checkedLows_valid
      simpa [firstSixStageLows] using hm.2.1
  separated := by
    intro j k hne
    have h01 := firstStage_disjoint_secondStageCheckpoint
    have h02 := firstStage_disjoint_third
    have h12 := secondStage_disjoint_third
    have h03 := stage0_disjoint_stage3
    have h13 := stage1_disjoint_stage3
    have h23 := stage2_disjoint_stage3
    have h04 := stage0_disjoint_stage4
    have h14 := stage1_disjoint_stage4
    have h24 := stage2_disjoint_stage4
    have h34 := stage3_disjoint_stage4
    have h05 := stage0_disjoint_stage5
    have h15 := stage1_disjoint_stage5
    have h25 := stage2_disjoint_stage5
    have h35 := stage3_disjoint_stage5
    have h45 := stage4_disjoint_stage5
    fin_cases j <;> fin_cases k
    all_goals first
      | exact False.elim (hne rfl)
      | simpa [firstSixStageLows] using h01
      | simpa [firstSixStageLows] using h01.symm
      | simpa [firstSixStageLows] using h02
      | simpa [firstSixStageLows] using h02.symm
      | simpa [firstSixStageLows] using h12
      | simpa [firstSixStageLows] using h12.symm
      | simpa [firstSixStageLows] using h03
      | simpa [firstSixStageLows] using h03.symm
      | simpa [firstSixStageLows] using h13
      | simpa [firstSixStageLows] using h13.symm
      | simpa [firstSixStageLows] using h23
      | simpa [firstSixStageLows] using h23.symm
      | simpa [firstSixStageLows] using h04
      | simpa [firstSixStageLows] using h04.symm
      | simpa [firstSixStageLows] using h14
      | simpa [firstSixStageLows] using h14.symm
      | simpa [firstSixStageLows] using h24
      | simpa [firstSixStageLows] using h24.symm
      | simpa [firstSixStageLows] using h34
      | simpa [firstSixStageLows] using h34.symm
      | simpa [firstSixStageLows] using h05
      | simpa [firstSixStageLows] using h05.symm
      | simpa [firstSixStageLows] using h15
      | simpa [firstSixStageLows] using h15.symm
      | simpa [firstSixStageLows] using h25
      | simpa [firstSixStageLows] using h25.symm
      | simpa [firstSixStageLows] using h35
      | simpa [firstSixStageLows] using h35.symm
      | simpa [firstSixStageLows] using h45
      | simpa [firstSixStageLows] using h45.symm

/-- Retain the source-prescribed number of pairs for physical allocation. -/
def actualFirstSixStageValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : (Fin 6 × Fin (6 * (n + 8))) × Bool → pool n :=
  truncatePrefixValues (LStage0.retained_size hnmax) (actualFirstSixStageFamily lower hn).values

theorem actualFirstSixStageValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : Function.Injective (actualFirstSixStageValues lower hn hnmax) :=
  truncatePrefixValues_injective (LStage0.retained_size hnmax) _
    (actualFirstSixStageFamily lower hn).values_injective

theorem actualFirstSixStageValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) :
    ∀ j i, (actualFirstSixStageValues lower hn hnmax ((j, i), true)).val =
      (actualFirstSixStageValues lower hn hnmax ((j, i), false)).val + 2 ^ (j.val + 1) :=
  truncatePrefixValues_gap (LStage0.retained_size hnmax) _
    (actualFirstSixStageFamily lower hn).values_gap

end
end Sude.GeneratedPrefix
