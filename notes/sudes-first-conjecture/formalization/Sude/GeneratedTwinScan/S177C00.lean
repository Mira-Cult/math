import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19267)) 371195949 371228717 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371195949 371228717).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19267 371195949 371228717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19268)) 371228717 371261485 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 371228717 371261485).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19268 371228717 371261485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19268)) 371261485 371294253 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 371261485 371294253).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19268 371261485 371294253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19269)) 371294253 371327021 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371294253 371327021).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19269 371294253 371327021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371195949 371261485).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 371195949 ≤ 371228717)
    (by decide : 371228717 ≤ 371261485) block0 block1

theorem join_0_1 : (twinPrimeSegment 371261485 371327021).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 371261485 ≤ 371294253)
    (by decide : 371294253 ≤ 371327021) block2 block3

theorem join_1_0 : (twinPrimeSegment 371195949 371327021).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 371195949 ≤ 371261485)
    (by decide : 371261485 ≤ 371327021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371195949 371327021).card = 424 := join_1_0

end S177C00
end Sude.GeneratedTwinScan
