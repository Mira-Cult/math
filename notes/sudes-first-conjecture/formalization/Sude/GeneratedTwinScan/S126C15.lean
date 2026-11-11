import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16316)) 266207277 266240045 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 266207277 266240045).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16316 266207277 266240045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16317)) 266240045 266272813 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 266240045 266272813).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16317 266240045 266272813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16318)) 266272813 266305581 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 266272813 266305581).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16318 266272813 266305581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16319)) 266305581 266338349 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 266305581 266338349).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16319 266305581 266338349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 266207277 266272813).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 266207277 ≤ 266240045)
    (by decide : 266240045 ≤ 266272813) block0 block1

theorem join_0_1 : (twinPrimeSegment 266272813 266338349).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 266272813 ≤ 266305581)
    (by decide : 266305581 ≤ 266338349) block2 block3

theorem join_1_0 : (twinPrimeSegment 266207277 266338349).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 266207277 ≤ 266272813)
    (by decide : 266272813 ≤ 266338349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 266207277 266338349).card = 416 := join_1_0

end S126C15
end Sude.GeneratedTwinScan
