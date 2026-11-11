import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20174)) 406978605 407011373 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406978605 407011373).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20174 406978605 407011373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20175)) 407011373 407044141 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 407011373 407044141).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20175 407011373 407044141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20176)) 407044141 407076909 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 407044141 407076909).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20176 407044141 407076909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20176)) 407076909 407109677 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 407076909 407109677).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20176 407076909 407109677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406978605 407044141).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 406978605 ≤ 407011373)
    (by decide : 407011373 ≤ 407044141) block0 block1

theorem join_0_1 : (twinPrimeSegment 407044141 407109677).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 407044141 ≤ 407076909)
    (by decide : 407076909 ≤ 407109677) block2 block3

theorem join_1_0 : (twinPrimeSegment 406978605 407109677).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 406978605 ≤ 407044141)
    (by decide : 407044141 ≤ 407109677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406978605 407109677).card = 417 := join_1_0

end S194C01
end Sude.GeneratedTwinScan
