import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17759)) 315359277 315392045 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 315359277 315392045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17759 315359277 315392045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17760)) 315392045 315424813 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 315392045 315424813).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17760 315392045 315424813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17761)) 315424813 315457581 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 315424813 315457581).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17761 315424813 315457581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17762)) 315457581 315490349 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 315457581 315490349).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17762 315457581 315490349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 315359277 315424813).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 315359277 ≤ 315392045)
    (by decide : 315392045 ≤ 315424813) block0 block1

theorem join_0_1 : (twinPrimeSegment 315424813 315490349).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 315424813 ≤ 315457581)
    (by decide : 315457581 ≤ 315490349) block2 block3

theorem join_1_0 : (twinPrimeSegment 315359277 315490349).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 315359277 ≤ 315424813)
    (by decide : 315424813 ≤ 315490349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 315359277 315490349).card = 422 := join_1_0

end S150C06
end Sude.GeneratedTwinScan
