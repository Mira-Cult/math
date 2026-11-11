import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20439)) 417726509 417759277 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 417726509 417759277).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20439 417726509 417759277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20439)) 417759277 417792045 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 417759277 417792045).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20439 417759277 417792045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20440)) 417792045 417824813 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417792045 417824813).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20440 417792045 417824813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20441)) 417824813 417857581 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417824813 417857581).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20441 417824813 417857581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 417726509 417792045).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 417726509 ≤ 417759277)
    (by decide : 417759277 ≤ 417792045) block0 block1

theorem join_0_1 : (twinPrimeSegment 417792045 417857581).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 417792045 ≤ 417824813)
    (by decide : 417824813 ≤ 417857581) block2 block3

theorem join_1_0 : (twinPrimeSegment 417726509 417857581).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 417726509 ≤ 417792045)
    (by decide : 417792045 ≤ 417857581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 417726509 417857581).card = 445 := join_1_0

end S199C03
end Sude.GeneratedTwinScan
