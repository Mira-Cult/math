import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18207)) 331481133 331513901 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 331481133 331513901).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18207 331481133 331513901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18208)) 331513901 331546669 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 331513901 331546669).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18208 331513901 331546669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18209)) 331546669 331579437 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 331546669 331579437).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18209 331546669 331579437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18210)) 331579437 331612205 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 331579437 331612205).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18210 331579437 331612205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 331481133 331546669).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 331481133 ≤ 331513901)
    (by decide : 331513901 ≤ 331546669) block0 block1

theorem join_0_1 : (twinPrimeSegment 331546669 331612205).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 331546669 ≤ 331579437)
    (by decide : 331579437 ≤ 331612205) block2 block3

theorem join_1_0 : (twinPrimeSegment 331481133 331612205).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 331481133 ≤ 331546669)
    (by decide : 331546669 ≤ 331612205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 331481133 331612205).card = 434 := join_1_0

end S158C01
end Sude.GeneratedTwinScan
