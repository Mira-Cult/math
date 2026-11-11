import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16512)) 272629805 272662573 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 272629805 272662573).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16512 272629805 272662573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16513)) 272662573 272695341 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 272662573 272695341).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16513 272662573 272695341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16514)) 272695341 272728109 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 272695341 272728109).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16514 272695341 272728109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16515)) 272728109 272760877 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 272728109 272760877).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16515 272728109 272760877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 272629805 272695341).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 272629805 ≤ 272662573)
    (by decide : 272662573 ≤ 272695341) block0 block1

theorem join_0_1 : (twinPrimeSegment 272695341 272760877).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 272695341 ≤ 272728109)
    (by decide : 272728109 ≤ 272760877) block2 block3

theorem join_1_0 : (twinPrimeSegment 272629805 272760877).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 272629805 ≤ 272695341)
    (by decide : 272695341 ≤ 272760877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 272629805 272760877).card = 426 := join_1_0

end S130C00
end Sude.GeneratedTwinScan
