import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20883)) 436076589 436109357 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436076589 436109357).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20883 436076589 436109357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20884)) 436109357 436142125 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 436109357 436142125).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20884 436109357 436142125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20884)) 436142125 436174893 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436142125 436174893).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20884 436142125 436174893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20885)) 436174893 436207661 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436174893 436207661).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20885 436174893 436207661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436076589 436142125).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 436076589 ≤ 436109357)
    (by decide : 436109357 ≤ 436142125) block0 block1

theorem join_0_1 : (twinPrimeSegment 436142125 436207661).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 436142125 ≤ 436174893)
    (by decide : 436174893 ≤ 436207661) block2 block3

theorem join_1_0 : (twinPrimeSegment 436076589 436207661).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 436076589 ≤ 436142125)
    (by decide : 436142125 ≤ 436207661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436076589 436207661).card = 416 := join_1_0

end S207C15
end Sude.GeneratedTwinScan
