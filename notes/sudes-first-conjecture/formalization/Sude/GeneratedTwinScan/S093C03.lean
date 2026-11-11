import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13980)) 195428397 195461165 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195428397 195461165).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13980 195428397 195461165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13981)) 195461165 195493933 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195461165 195493933).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13981 195461165 195493933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13983)) 195493933 195526701 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 195493933 195526701).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13983 195493933 195526701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13984)) 195526701 195559469 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 195526701 195559469).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13984 195526701 195559469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195428397 195493933).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 195428397 ≤ 195461165)
    (by decide : 195461165 ≤ 195493933) block0 block1

theorem join_0_1 : (twinPrimeSegment 195493933 195559469).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 195493933 ≤ 195526701)
    (by decide : 195526701 ≤ 195559469) block2 block3

theorem join_1_0 : (twinPrimeSegment 195428397 195559469).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 195428397 ≤ 195493933)
    (by decide : 195493933 ≤ 195559469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195428397 195559469).card = 493 := join_1_0

end S093C03
end Sude.GeneratedTwinScan
