import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19780)) 391249965 391282733 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 391249965 391282733).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19780 391249965 391282733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19781)) 391282733 391315501 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 391282733 391315501).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19781 391282733 391315501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19782)) 391315501 391348269 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 391315501 391348269).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19782 391315501 391348269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19783)) 391348269 391381037 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 391348269 391381037).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19783 391348269 391381037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 391249965 391315501).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 391249965 ≤ 391282733)
    (by decide : 391282733 ≤ 391315501) block0 block1

theorem join_0_1 : (twinPrimeSegment 391315501 391381037).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 391315501 ≤ 391348269)
    (by decide : 391348269 ≤ 391381037) block2 block3

theorem join_1_0 : (twinPrimeSegment 391249965 391381037).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 391249965 ≤ 391315501)
    (by decide : 391315501 ≤ 391381037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 391249965 391381037).card = 417 := join_1_0

end S186C09
end Sude.GeneratedTwinScan
