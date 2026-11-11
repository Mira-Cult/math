import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22099)) 488374317 488407085 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 488374317 488407085).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22099 488374317 488407085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22100)) 488407085 488439853 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 488407085 488439853).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22100 488407085 488439853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22101)) 488439853 488472621 = 88 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 488439853 488472621).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22101 488439853 488472621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22102)) 488472621 488505389 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 488472621 488505389).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22102 488472621 488505389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 488374317 488439853).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 488374317 ≤ 488407085)
    (by decide : 488407085 ≤ 488439853) block0 block1

theorem join_0_1 : (twinPrimeSegment 488439853 488505389).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 488439853 ≤ 488472621)
    (by decide : 488472621 ≤ 488505389) block2 block3

theorem join_1_0 : (twinPrimeSegment 488374317 488505389).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 488374317 ≤ 488439853)
    (by decide : 488439853 ≤ 488505389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 488374317 488505389).card = 413 := join_1_0

end S232C14
end Sude.GeneratedTwinScan
