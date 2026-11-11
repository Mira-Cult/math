import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17043)) 290455597 290488365 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290455597 290488365).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17043 290455597 290488365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17044)) 290488365 290521133 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 290488365 290521133).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17044 290488365 290521133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17045)) 290521133 290553901 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 290521133 290553901).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17045 290521133 290553901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17046)) 290553901 290586669 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290553901 290586669).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17046 290553901 290586669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290455597 290521133).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 290455597 ≤ 290488365)
    (by decide : 290488365 ≤ 290521133) block0 block1

theorem join_0_1 : (twinPrimeSegment 290521133 290586669).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 290521133 ≤ 290553901)
    (by decide : 290553901 ≤ 290586669) block2 block3

theorem join_1_0 : (twinPrimeSegment 290455597 290586669).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 290455597 ≤ 290521133)
    (by decide : 290521133 ≤ 290586669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290455597 290586669).card = 434 := join_1_0

end S138C08
end Sude.GeneratedTwinScan
