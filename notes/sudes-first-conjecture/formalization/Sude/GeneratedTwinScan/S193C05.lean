import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20135)) 405405741 405438509 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 405405741 405438509).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20135 405405741 405438509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20136)) 405438509 405471277 = 89 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 405438509 405471277).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20136 405438509 405471277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20137)) 405471277 405504045 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 405471277 405504045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20137 405471277 405504045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20137)) 405504045 405536813 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 405504045 405536813).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20137 405504045 405536813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 405405741 405471277).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 405405741 ≤ 405438509)
    (by decide : 405438509 ≤ 405471277) block0 block1

theorem join_0_1 : (twinPrimeSegment 405471277 405536813).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 405471277 ≤ 405504045)
    (by decide : 405504045 ≤ 405536813) block2 block3

theorem join_1_0 : (twinPrimeSegment 405405741 405536813).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 405405741 ≤ 405471277)
    (by decide : 405471277 ≤ 405536813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 405405741 405536813).card = 420 := join_1_0

end S193C05
end Sude.GeneratedTwinScan
