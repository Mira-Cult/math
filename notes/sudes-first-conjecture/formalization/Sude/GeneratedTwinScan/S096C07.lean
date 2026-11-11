import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14222)) 202244141 202276909 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 202244141 202276909).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14222 202244141 202276909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14223)) 202276909 202309677 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202276909 202309677).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14223 202276909 202309677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14224)) 202309677 202342445 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202309677 202342445).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14224 202309677 202342445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14225)) 202342445 202375213 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202342445 202375213).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14225 202342445 202375213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 202244141 202309677).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 202244141 ≤ 202276909)
    (by decide : 202276909 ≤ 202309677) block0 block1

theorem join_0_1 : (twinPrimeSegment 202309677 202375213).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 202309677 ≤ 202342445)
    (by decide : 202342445 ≤ 202375213) block2 block3

theorem join_1_0 : (twinPrimeSegment 202244141 202375213).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 202244141 ≤ 202309677)
    (by decide : 202309677 ≤ 202375213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 202244141 202375213).card = 445 := join_1_0

end S096C07
end Sude.GeneratedTwinScan
