import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20782)) 431882285 431915053 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 431882285 431915053).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20782 431882285 431915053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20783)) 431915053 431947821 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 431915053 431947821).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20783 431915053 431947821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20784)) 431947821 431980589 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431947821 431980589).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20784 431947821 431980589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20784)) 431980589 432013357 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431980589 432013357).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20784 431980589 432013357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 431882285 431947821).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 431882285 ≤ 431915053)
    (by decide : 431915053 ≤ 431947821) block0 block1

theorem join_0_1 : (twinPrimeSegment 431947821 432013357).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 431947821 ≤ 431980589)
    (by decide : 431980589 ≤ 432013357) block2 block3

theorem join_1_0 : (twinPrimeSegment 431882285 432013357).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 431882285 ≤ 431947821)
    (by decide : 431947821 ≤ 432013357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 431882285 432013357).card = 442 := join_1_0

end S205C15
end Sude.GeneratedTwinScan
