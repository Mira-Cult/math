import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20158)) 406323245 406356013 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406323245 406356013).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20158 406323245 406356013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20159)) 406356013 406388781 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 406356013 406388781).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20159 406356013 406388781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20159)) 406388781 406421549 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 406388781 406421549).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20159 406388781 406421549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20160)) 406421549 406454317 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406421549 406454317).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20160 406421549 406454317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406323245 406388781).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 406323245 ≤ 406356013)
    (by decide : 406356013 ≤ 406388781) block0 block1

theorem join_0_1 : (twinPrimeSegment 406388781 406454317).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 406388781 ≤ 406421549)
    (by decide : 406421549 ≤ 406454317) block2 block3

theorem join_1_0 : (twinPrimeSegment 406323245 406454317).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 406323245 ≤ 406388781)
    (by decide : 406388781 ≤ 406454317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406323245 406454317).card = 444 := join_1_0

end S193C12
end Sude.GeneratedTwinScan
