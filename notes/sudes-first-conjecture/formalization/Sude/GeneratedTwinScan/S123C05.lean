import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16082)) 258605101 258637869 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 258605101 258637869).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16082 258605101 258637869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16083)) 258637869 258670637 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 258637869 258670637).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16083 258637869 258670637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16084)) 258670637 258703405 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258670637 258703405).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16084 258670637 258703405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16085)) 258703405 258736173 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258703405 258736173).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16085 258703405 258736173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 258605101 258670637).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 258605101 ≤ 258637869)
    (by decide : 258637869 ≤ 258670637) block0 block1

theorem join_0_1 : (twinPrimeSegment 258670637 258736173).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 258670637 ≤ 258703405)
    (by decide : 258703405 ≤ 258736173) block2 block3

theorem join_1_0 : (twinPrimeSegment 258605101 258736173).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 258605101 ≤ 258670637)
    (by decide : 258670637 ≤ 258736173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 258605101 258736173).card = 434 := join_1_0

end S123C05
end Sude.GeneratedTwinScan
