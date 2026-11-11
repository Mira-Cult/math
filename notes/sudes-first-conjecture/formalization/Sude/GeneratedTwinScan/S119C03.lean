import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15810)) 249954349 249987117 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 249954349 249987117).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15810 249954349 249987117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15812)) 249987117 250019885 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 249987117 250019885).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15812 249987117 250019885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15813)) 250019885 250052653 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250019885 250052653).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15813 250019885 250052653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15814)) 250052653 250085421 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250052653 250085421).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15814 250052653 250085421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 249954349 250019885).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 249954349 ≤ 249987117)
    (by decide : 249987117 ≤ 250019885) block0 block1

theorem join_0_1 : (twinPrimeSegment 250019885 250085421).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 250019885 ≤ 250052653)
    (by decide : 250052653 ≤ 250085421) block2 block3

theorem join_1_0 : (twinPrimeSegment 249954349 250085421).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 249954349 ≤ 250019885)
    (by decide : 250019885 ≤ 250085421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 249954349 250085421).card = 452 := join_1_0

end S119C03
end Sude.GeneratedTwinScan
