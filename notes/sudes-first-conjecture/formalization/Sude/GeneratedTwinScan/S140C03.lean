import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17147)) 293994541 294027309 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 293994541 294027309).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17147 293994541 294027309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17148)) 294027309 294060077 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294027309 294060077).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17148 294027309 294060077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17149)) 294060077 294092845 = 90 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 294060077 294092845).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17149 294060077 294092845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17150)) 294092845 294125613 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 294092845 294125613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17150 294092845 294125613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 293994541 294060077).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 293994541 ≤ 294027309)
    (by decide : 294027309 ≤ 294060077) block0 block1

theorem join_0_1 : (twinPrimeSegment 294060077 294125613).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 294060077 ≤ 294092845)
    (by decide : 294092845 ≤ 294125613) block2 block3

theorem join_1_0 : (twinPrimeSegment 293994541 294125613).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 293994541 ≤ 294060077)
    (by decide : 294060077 ≤ 294125613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 293994541 294125613).card = 443 := join_1_0

end S140C03
end Sude.GeneratedTwinScan
