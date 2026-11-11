import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20839)) 434241581 434274349 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 434241581 434274349).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20839 434241581 434274349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20840)) 434274349 434307117 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 434274349 434307117).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20840 434274349 434307117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20840)) 434307117 434339885 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 434307117 434339885).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20840 434307117 434339885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20841)) 434339885 434372653 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 434339885 434372653).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20841 434339885 434372653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 434241581 434307117).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 434241581 ≤ 434274349)
    (by decide : 434274349 ≤ 434307117) block0 block1

theorem join_0_1 : (twinPrimeSegment 434307117 434372653).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 434307117 ≤ 434339885)
    (by decide : 434339885 ≤ 434372653) block2 block3

theorem join_1_0 : (twinPrimeSegment 434241581 434372653).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 434241581 ≤ 434307117)
    (by decide : 434307117 ≤ 434372653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 434241581 434372653).card = 454 := join_1_0

end S207C01
end Sude.GeneratedTwinScan
