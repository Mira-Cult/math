import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22479)) 505282605 505315373 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505282605 505315373).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22479 505282605 505315373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22479)) 505315373 505348141 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505315373 505348141).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22479 505315373 505348141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22480)) 505348141 505380909 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 505348141 505380909).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22480 505348141 505380909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22481)) 505380909 505413677 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 505380909 505413677).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22481 505380909 505413677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505282605 505348141).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 505282605 ≤ 505315373)
    (by decide : 505315373 ≤ 505348141) block0 block1

theorem join_0_1 : (twinPrimeSegment 505348141 505413677).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 505348141 ≤ 505380909)
    (by decide : 505380909 ≤ 505413677) block2 block3

theorem join_1_0 : (twinPrimeSegment 505282605 505413677).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 505282605 ≤ 505348141)
    (by decide : 505348141 ≤ 505413677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505282605 505413677).card = 417 := join_1_0

end S240C15
end Sude.GeneratedTwinScan
