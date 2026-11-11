import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17876)) 319553581 319586349 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 319553581 319586349).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17876 319553581 319586349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17877)) 319586349 319619117 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 319586349 319619117).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17877 319586349 319619117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17878)) 319619117 319651885 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 319619117 319651885).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17878 319619117 319651885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17879)) 319651885 319684653 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 319651885 319684653).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17879 319651885 319684653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 319553581 319619117).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 319553581 ≤ 319586349)
    (by decide : 319586349 ≤ 319619117) block0 block1

theorem join_0_1 : (twinPrimeSegment 319619117 319684653).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 319619117 ≤ 319651885)
    (by decide : 319651885 ≤ 319684653) block2 block3

theorem join_1_0 : (twinPrimeSegment 319553581 319684653).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 319553581 ≤ 319619117)
    (by decide : 319619117 ≤ 319684653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 319553581 319684653).card = 477 := join_1_0

end S152C06
end Sude.GeneratedTwinScan
