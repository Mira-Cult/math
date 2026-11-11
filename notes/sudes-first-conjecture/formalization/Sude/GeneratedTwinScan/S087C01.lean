import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13513)) 182583341 182616109 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 182583341 182616109).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13513 182583341 182616109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13514)) 182616109 182648877 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 182616109 182648877).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13514 182616109 182648877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13515)) 182648877 182681645 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 182648877 182681645).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13515 182648877 182681645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13517)) 182681645 182714413 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 182681645 182714413).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13517 182681645 182714413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 182583341 182648877).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 182583341 ≤ 182616109)
    (by decide : 182616109 ≤ 182648877) block0 block1

theorem join_0_1 : (twinPrimeSegment 182648877 182714413).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 182648877 ≤ 182681645)
    (by decide : 182681645 ≤ 182714413) block2 block3

theorem join_1_0 : (twinPrimeSegment 182583341 182714413).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 182583341 ≤ 182648877)
    (by decide : 182648877 ≤ 182714413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 182583341 182714413).card = 457 := join_1_0

end S087C01
end Sude.GeneratedTwinScan
