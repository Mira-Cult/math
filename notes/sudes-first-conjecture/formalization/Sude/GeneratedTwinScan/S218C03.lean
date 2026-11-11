import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21391)) 457572397 457605165 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457572397 457605165).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21391 457572397 457605165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21392)) 457605165 457637933 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457605165 457637933).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21392 457605165 457637933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21393)) 457637933 457670701 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 457637933 457670701).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21393 457637933 457670701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21394)) 457670701 457703469 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457670701 457703469).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21394 457670701 457703469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457572397 457637933).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 457572397 ≤ 457605165)
    (by decide : 457605165 ≤ 457637933) block0 block1

theorem join_0_1 : (twinPrimeSegment 457637933 457703469).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 457637933 ≤ 457670701)
    (by decide : 457670701 ≤ 457703469) block2 block3

theorem join_1_0 : (twinPrimeSegment 457572397 457703469).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 457572397 ≤ 457637933)
    (by decide : 457637933 ≤ 457703469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457572397 457703469).card = 457 := join_1_0

end S218C03
end Sude.GeneratedTwinScan
