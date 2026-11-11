import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22563)) 509083693 509116461 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 509083693 509116461).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22563 509083693 509116461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22564)) 509116461 509149229 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 509116461 509149229).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22564 509116461 509149229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22565)) 509149229 509181997 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509149229 509181997).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22565 509149229 509181997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22565)) 509181997 509214765 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509181997 509214765).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22565 509181997 509214765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 509083693 509149229).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 509083693 ≤ 509116461)
    (by decide : 509116461 ≤ 509149229) block0 block1

theorem join_0_1 : (twinPrimeSegment 509149229 509214765).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 509149229 ≤ 509181997)
    (by decide : 509181997 ≤ 509214765) block2 block3

theorem join_1_0 : (twinPrimeSegment 509083693 509214765).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 509083693 ≤ 509149229)
    (by decide : 509149229 ≤ 509214765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 509083693 509214765).card = 437 := join_1_0

end S242C12
end Sude.GeneratedTwinScan
