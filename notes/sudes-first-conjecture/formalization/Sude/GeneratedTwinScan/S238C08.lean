import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22365)) 500170797 500203565 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500170797 500203565).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22365 500170797 500203565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22365)) 500203565 500236333 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500203565 500236333).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22365 500203565 500236333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22366)) 500236333 500269101 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 500236333 500269101).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22366 500236333 500269101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22367)) 500269101 500301869 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 500269101 500301869).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22367 500269101 500301869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500170797 500236333).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 500170797 ≤ 500203565)
    (by decide : 500203565 ≤ 500236333) block0 block1

theorem join_0_1 : (twinPrimeSegment 500236333 500301869).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 500236333 ≤ 500269101)
    (by decide : 500269101 ≤ 500301869) block2 block3

theorem join_1_0 : (twinPrimeSegment 500170797 500301869).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 500170797 ≤ 500236333)
    (by decide : 500236333 ≤ 500301869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500170797 500301869).card = 412 := join_1_0

end S238C08
end Sude.GeneratedTwinScan
