import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18304)) 335020077 335052845 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 335020077 335052845).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18304 335020077 335052845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18305)) 335052845 335085613 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 335052845 335085613).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18305 335052845 335085613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18306)) 335085613 335118381 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 335085613 335118381).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18306 335085613 335118381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18307)) 335118381 335151149 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 335118381 335151149).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18307 335118381 335151149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 335020077 335085613).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 335020077 ≤ 335052845)
    (by decide : 335052845 ≤ 335085613) block0 block1

theorem join_0_1 : (twinPrimeSegment 335085613 335151149).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 335085613 ≤ 335118381)
    (by decide : 335118381 ≤ 335151149) block2 block3

theorem join_1_0 : (twinPrimeSegment 335020077 335151149).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 335020077 ≤ 335085613)
    (by decide : 335085613 ≤ 335151149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 335020077 335151149).card = 471 := join_1_0

end S159C12
end Sude.GeneratedTwinScan
