import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17051)) 290717741 290750509 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290717741 290750509).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17051 290717741 290750509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17052)) 290750509 290783277 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 290750509 290783277).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17052 290750509 290783277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17053)) 290783277 290816045 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 290783277 290816045).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17053 290783277 290816045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17054)) 290816045 290848813 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290816045 290848813).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17054 290816045 290848813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290717741 290783277).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 290717741 ≤ 290750509)
    (by decide : 290750509 ≤ 290783277) block0 block1

theorem join_0_1 : (twinPrimeSegment 290783277 290848813).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 290783277 ≤ 290816045)
    (by decide : 290816045 ≤ 290848813) block2 block3

theorem join_1_0 : (twinPrimeSegment 290717741 290848813).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 290717741 ≤ 290783277)
    (by decide : 290783277 ≤ 290848813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290717741 290848813).card = 450 := join_1_0

end S138C10
end Sude.GeneratedTwinScan
