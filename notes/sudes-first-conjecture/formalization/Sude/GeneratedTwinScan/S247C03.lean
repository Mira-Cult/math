import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22768)) 518389805 518422573 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 518389805 518422573).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22768 518389805 518422573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22769)) 518422573 518455341 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 518422573 518455341).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22769 518422573 518455341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22770)) 518455341 518488109 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 518455341 518488109).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22770 518455341 518488109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22771)) 518488109 518520877 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 518488109 518520877).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22771 518488109 518520877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 518389805 518455341).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 518389805 ≤ 518422573)
    (by decide : 518422573 ≤ 518455341) block0 block1

theorem join_0_1 : (twinPrimeSegment 518455341 518520877).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 518455341 ≤ 518488109)
    (by decide : 518488109 ≤ 518520877) block2 block3

theorem join_1_0 : (twinPrimeSegment 518389805 518520877).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 518389805 ≤ 518455341)
    (by decide : 518455341 ≤ 518520877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 518389805 518520877).card = 462 := join_1_0

end S247C03
end Sude.GeneratedTwinScan
