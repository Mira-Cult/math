import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21562)) 464912429 464945197 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 464912429 464945197).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21562 464912429 464945197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21563)) 464945197 464977965 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464945197 464977965).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21563 464945197 464977965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21564)) 464977965 465010733 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464977965 465010733).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21564 464977965 465010733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21564)) 465010733 465043501 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 465010733 465043501).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21564 465010733 465043501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 464912429 464977965).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 464912429 ≤ 464945197)
    (by decide : 464945197 ≤ 464977965) block0 block1

theorem join_0_1 : (twinPrimeSegment 464977965 465043501).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 464977965 ≤ 465010733)
    (by decide : 465010733 ≤ 465043501) block2 block3

theorem join_1_0 : (twinPrimeSegment 464912429 465043501).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 464912429 ≤ 464977965)
    (by decide : 464977965 ≤ 465043501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 464912429 465043501).card = 426 := join_1_0

end S221C11
end Sude.GeneratedTwinScan
