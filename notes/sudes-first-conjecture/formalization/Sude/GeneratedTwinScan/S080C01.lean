import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12959)) 167903277 167936045 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 167903277 167936045).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12959 167903277 167936045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12960)) 167936045 167968813 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167936045 167968813).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12960 167936045 167968813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12961)) 167968813 168001581 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167968813 168001581).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12961 167968813 168001581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12962)) 168001581 168034349 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168001581 168034349).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12962 168001581 168034349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 167903277 167968813).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 167903277 ≤ 167936045)
    (by decide : 167936045 ≤ 167968813) block0 block1

theorem join_0_1 : (twinPrimeSegment 167968813 168034349).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 167968813 ≤ 168001581)
    (by decide : 168001581 ≤ 168034349) block2 block3

theorem join_1_0 : (twinPrimeSegment 167903277 168034349).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 167903277 ≤ 167968813)
    (by decide : 167968813 ≤ 168034349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 167903277 168034349).card = 465 := join_1_0

end S080C01
end Sude.GeneratedTwinScan
