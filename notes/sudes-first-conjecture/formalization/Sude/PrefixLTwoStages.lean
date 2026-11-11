import Sude.PrefixLFirstStages
import Sude.PrefixTruncation

/-! Assemble the first two fully accepted L stages, and retain the general
interface for any other second stage with the source's lower bound. -/
namespace Sude.GeneratedPrefix
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def firstTwoStageLows (second : List ℕ) : Fin 2 → List ℕ :=
  ![LStage0.checkedLows, second]

/-- The complete first-stage footprint and every second-stage footprint with
the source's lower bound are disjoint, independently of its upper bound. -/
theorem firstStage_disjoint_second {hi : ℕ} {second : List ℕ}
    (hsecond : PrefixStageBlock 4 55000000 16178779 hi second) :
    Disjoint (pairFootprint LStage0.checkedLows.toFinset 2)
      (pairFootprint second.toFinset 4) :=
  PrefixStageBlock.footprints_disjoint LStage0.checkedLows_valid hsecond (by decide)

/-- Supply a checked second stage to obtain two globally disjoint full
stages in the allocator's family interface. -/
def firstTwoStageFamily (lower : RSIndexLower) {n hi : ℕ} (hn : 2000 ≤ n)
    (second : List ℕ) (hlength : second.length = 14448)
    (hsecond : PrefixStageBlock 4 55000000 16178779 hi second) :
    CertifiedPrefixFamily 2 14448 n where
  lows := firstTwoStageLows second
  length := by
    intro j
    fin_cases j
    · simpa [firstTwoStageLows] using LStage0.checkedLows_length
    · simpa [firstTwoStageLows] using hlength
  nodup := by
    intro j
    fin_cases j
    · simpa [firstTwoStageLows] using LStage0.checkedLows_nodup
    · simpa [firstTwoStageLows] using hsecond.sorted.nodup
  pool := by
    intro j
    fin_cases j
    · simpa [firstTwoStageLows] using (LStage0.checkedLows_matching lower hn).1
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) hsecond
      simpa [firstTwoStageLows] using hm.1
  matching := by
    intro j
    fin_cases j
    · simpa [firstTwoStageLows] using (LStage0.checkedLows_matching lower hn).2
    · have hm := PrefixStageBlock.L_pool_matching (j := 1) lower hn (by decide) hsecond
      simpa [firstTwoStageLows] using hm.2.1
  separated := by
    intro j k hne
    have hsep := firstStage_disjoint_second hsecond
    fin_cases j <;> fin_cases k
    · exact False.elim (hne rfl)
    · simpa [firstTwoStageLows] using hsep
    · simpa [firstTwoStageLows] using hsep.symm
    · exact False.elim (hne rfl)

/-- The source-retained number of pairs per stage, suitable for physical
allocation. The acceptance of the second stage is not assumed implicitly. -/
def firstTwoStageValues (lower : RSIndexLower) {n hi : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) (second : List ℕ) (hlength : second.length = 14448)
    (hsecond : PrefixStageBlock 4 55000000 16178779 hi second) :
    (Fin 2 × Fin (6 * (n + 8))) × Bool → pool n :=
  truncatePrefixValues (LStage0.retained_size hnmax)
    (firstTwoStageFamily lower hn second hlength hsecond).values

theorem firstTwoStageValues_injective (lower : RSIndexLower) {n hi : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) (second : List ℕ) (hlength : second.length = 14448)
    (hsecond : PrefixStageBlock 4 55000000 16178779 hi second) :
    Function.Injective (firstTwoStageValues lower hn hnmax second hlength hsecond) :=
  truncatePrefixValues_injective (LStage0.retained_size hnmax) _
    (firstTwoStageFamily lower hn second hlength hsecond).values_injective

theorem firstTwoStageValues_gap (lower : RSIndexLower) {n hi : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) (second : List ℕ) (hlength : second.length = 14448)
    (hsecond : PrefixStageBlock 4 55000000 16178779 hi second) :
    ∀ j i, (firstTwoStageValues lower hn hnmax second hlength hsecond ((j, i), true)).val =
      (firstTwoStageValues lower hn hnmax second hlength hsecond ((j, i), false)).val +
        2 ^ (j.val + 1) :=
  truncatePrefixValues_gap (LStage0.retained_size hnmax) _
    (firstTwoStageFamily lower hn second hlength hsecond).values_gap

/-- The actual first two fully checked L stages. -/
def actualFirstTwoStageFamily (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    CertifiedPrefixFamily 2 14448 n :=
  firstTwoStageFamily lower hn LStage1.checkedLows LStage1.checkedLows_length LStage1.checkedLows_valid

/-- The source-ordered physical pair values for the two checked stages. -/
def actualFirstTwoStageValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : (Fin 2 × Fin (6 * (n + 8))) × Bool → pool n :=
  firstTwoStageValues lower hn hnmax LStage1.checkedLows LStage1.checkedLows_length LStage1.checkedLows_valid

theorem actualFirstTwoStageValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) : Function.Injective (actualFirstTwoStageValues lower hn hnmax) :=
  firstTwoStageValues_injective lower hn hnmax LStage1.checkedLows LStage1.checkedLows_length LStage1.checkedLows_valid

theorem actualFirstTwoStageValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)
    (hnmax : n ≤ 2400) :
    ∀ j i, (actualFirstTwoStageValues lower hn hnmax ((j, i), true)).val =
      (actualFirstTwoStageValues lower hn hnmax ((j, i), false)).val + 2 ^ (j.val + 1) :=
  firstTwoStageValues_gap lower hn hnmax LStage1.checkedLows LStage1.checkedLows_length LStage1.checkedLows_valid

end
end Sude.GeneratedPrefix
