import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22288)) 496762925 496795693 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 496762925 496795693).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22288 496762925 496795693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22289)) 496795693 496828461 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 496795693 496828461).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22289 496795693 496828461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22290)) 496828461 496861229 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 496828461 496861229).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22290 496828461 496861229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22291)) 496861229 496893997 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 496861229 496893997).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22291 496861229 496893997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 496762925 496828461).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 496762925 ≤ 496795693)
    (by decide : 496795693 ≤ 496828461) block0 block1

theorem join_0_1 : (twinPrimeSegment 496828461 496893997).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 496828461 ≤ 496861229)
    (by decide : 496861229 ≤ 496893997) block2 block3

theorem join_1_0 : (twinPrimeSegment 496762925 496893997).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 496762925 ≤ 496828461)
    (by decide : 496828461 ≤ 496893997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 496762925 496893997).card = 417 := join_1_0

end S236C14
end Sude.GeneratedTwinScan
