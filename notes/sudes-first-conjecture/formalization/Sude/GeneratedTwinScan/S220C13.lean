import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21519)) 463077421 463110189 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 463077421 463110189).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21519 463077421 463110189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21520)) 463110189 463142957 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 463110189 463142957).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21520 463110189 463142957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21521)) 463142957 463175725 = 74 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 463142957 463175725).card = 74 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21521 463142957 463175725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21522)) 463175725 463208493 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 463175725 463208493).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21522 463175725 463208493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 463077421 463142957).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 463077421 ≤ 463110189)
    (by decide : 463110189 ≤ 463142957) block0 block1

theorem join_0_1 : (twinPrimeSegment 463142957 463208493).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 463142957 ≤ 463175725)
    (by decide : 463175725 ≤ 463208493) block2 block3

theorem join_1_0 : (twinPrimeSegment 463077421 463208493).card = 397 := by
  simpa using combineTwinPrimeSegments (by decide : 463077421 ≤ 463142957)
    (by decide : 463142957 ≤ 463208493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 463077421 463208493).card = 397 := join_1_0

end S220C13
end Sude.GeneratedTwinScan
