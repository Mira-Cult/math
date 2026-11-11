import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13268)) 176029741 176062509 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 176029741 176062509).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13268 176029741 176062509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13270)) 176062509 176095277 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 176062509 176095277).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13270 176062509 176095277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13271)) 176095277 176128045 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 176095277 176128045).card = 151 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13271 176095277 176128045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13272)) 176128045 176160813 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 176128045 176160813).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13272 176128045 176160813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 176029741 176095277).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 176029741 ≤ 176062509)
    (by decide : 176062509 ≤ 176095277) block0 block1

theorem join_0_1 : (twinPrimeSegment 176095277 176160813).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 176095277 ≤ 176128045)
    (by decide : 176128045 ≤ 176160813) block2 block3

theorem join_1_0 : (twinPrimeSegment 176029741 176160813).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 176029741 ≤ 176095277)
    (by decide : 176095277 ≤ 176160813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 176029741 176160813).card = 509 := join_1_0

end S083C15
end Sude.GeneratedTwinScan
