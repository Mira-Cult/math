import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22052)) 486277165 486309933 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 486277165 486309933).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22052 486277165 486309933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22053)) 486309933 486342701 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 486309933 486342701).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22053 486309933 486342701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22053)) 486342701 486375469 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 486342701 486375469).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22053 486342701 486375469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22054)) 486375469 486408237 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 486375469 486408237).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22054 486375469 486408237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 486277165 486342701).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 486277165 ≤ 486309933)
    (by decide : 486309933 ≤ 486342701) block0 block1

theorem join_0_1 : (twinPrimeSegment 486342701 486408237).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 486342701 ≤ 486375469)
    (by decide : 486375469 ≤ 486408237) block2 block3

theorem join_1_0 : (twinPrimeSegment 486277165 486408237).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 486277165 ≤ 486342701)
    (by decide : 486342701 ≤ 486408237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 486277165 486408237).card = 444 := join_1_0

end S231C14
end Sude.GeneratedTwinScan
