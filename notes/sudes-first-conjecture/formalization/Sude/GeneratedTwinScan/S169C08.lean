import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18854)) 355467309 355500077 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 355467309 355500077).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18854 355467309 355500077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18855)) 355500077 355532845 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 355500077 355532845).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18855 355500077 355532845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18856)) 355532845 355565613 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 355532845 355565613).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18856 355532845 355565613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18857)) 355565613 355598381 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 355565613 355598381).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18857 355565613 355598381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 355467309 355532845).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 355467309 ≤ 355500077)
    (by decide : 355500077 ≤ 355532845) block0 block1

theorem join_0_1 : (twinPrimeSegment 355532845 355598381).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 355532845 ≤ 355565613)
    (by decide : 355565613 ≤ 355598381) block2 block3

theorem join_1_0 : (twinPrimeSegment 355467309 355598381).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 355467309 ≤ 355532845)
    (by decide : 355532845 ≤ 355598381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 355467309 355598381).card = 470 := join_1_0

end S169C08
end Sude.GeneratedTwinScan
