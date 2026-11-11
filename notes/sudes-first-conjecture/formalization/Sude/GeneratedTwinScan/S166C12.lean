import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18701)) 349700141 349732909 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 349700141 349732909).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18701 349700141 349732909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18702)) 349732909 349765677 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 349732909 349765677).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18702 349732909 349765677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18702)) 349765677 349798445 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 349765677 349798445).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18702 349765677 349798445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18703)) 349798445 349831213 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 349798445 349831213).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18703 349798445 349831213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 349700141 349765677).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 349700141 ≤ 349732909)
    (by decide : 349732909 ≤ 349765677) block0 block1

theorem join_0_1 : (twinPrimeSegment 349765677 349831213).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 349765677 ≤ 349798445)
    (by decide : 349798445 ≤ 349831213) block2 block3

theorem join_1_0 : (twinPrimeSegment 349700141 349831213).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 349700141 ≤ 349765677)
    (by decide : 349765677 ≤ 349831213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 349700141 349831213).card = 430 := join_1_0

end S166C12
end Sude.GeneratedTwinScan
