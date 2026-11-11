import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21550)) 464388141 464420909 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 464388141 464420909).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21550 464388141 464420909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21551)) 464420909 464453677 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464420909 464453677).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21551 464420909 464453677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21551)) 464453677 464486445 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464453677 464486445).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21551 464453677 464486445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21552)) 464486445 464519213 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 464486445 464519213).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21552 464486445 464519213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 464388141 464453677).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 464388141 ≤ 464420909)
    (by decide : 464420909 ≤ 464453677) block0 block1

theorem join_0_1 : (twinPrimeSegment 464453677 464519213).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 464453677 ≤ 464486445)
    (by decide : 464486445 ≤ 464519213) block2 block3

theorem join_1_0 : (twinPrimeSegment 464388141 464519213).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 464388141 ≤ 464453677)
    (by decide : 464453677 ≤ 464519213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 464388141 464519213).card = 421 := join_1_0

end S221C07
end Sude.GeneratedTwinScan
