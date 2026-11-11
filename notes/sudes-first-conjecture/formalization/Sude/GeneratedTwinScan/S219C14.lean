import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21474)) 461111341 461144109 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 461111341 461144109).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21474 461111341 461144109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21475)) 461144109 461176877 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 461144109 461176877).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21475 461144109 461176877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21475)) 461176877 461209645 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 461176877 461209645).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21475 461176877 461209645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21476)) 461209645 461242413 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 461209645 461242413).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21476 461209645 461242413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 461111341 461176877).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 461111341 ≤ 461144109)
    (by decide : 461144109 ≤ 461176877) block0 block1

theorem join_0_1 : (twinPrimeSegment 461176877 461242413).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 461176877 ≤ 461209645)
    (by decide : 461209645 ≤ 461242413) block2 block3

theorem join_1_0 : (twinPrimeSegment 461111341 461242413).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 461111341 ≤ 461176877)
    (by decide : 461176877 ≤ 461242413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 461111341 461242413).card = 438 := join_1_0

end S219C14
end Sude.GeneratedTwinScan
