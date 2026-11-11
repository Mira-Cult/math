import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13561)) 183894061 183926829 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 183894061 183926829).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13561 183894061 183926829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13563)) 183926829 183959597 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183926829 183959597).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13563 183926829 183959597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13564)) 183959597 183992365 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183959597 183992365).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13564 183959597 183992365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13565)) 183992365 184025133 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183992365 184025133).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13565 183992365 184025133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 183894061 183959597).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 183894061 ≤ 183926829)
    (by decide : 183926829 ≤ 183959597) block0 block1

theorem join_0_1 : (twinPrimeSegment 183959597 184025133).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 183959597 ≤ 183992365)
    (by decide : 183992365 ≤ 184025133) block2 block3

theorem join_1_0 : (twinPrimeSegment 183894061 184025133).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 183894061 ≤ 183959597)
    (by decide : 183959597 ≤ 184025133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 183894061 184025133).card = 486 := join_1_0

end S087C11
end Sude.GeneratedTwinScan
