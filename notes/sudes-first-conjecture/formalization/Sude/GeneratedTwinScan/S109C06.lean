import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15146)) 229376045 229408813 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 229376045 229408813).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15146 229376045 229408813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15147)) 229408813 229441581 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229408813 229441581).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15147 229408813 229441581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15148)) 229441581 229474349 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229441581 229474349).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15148 229441581 229474349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15149)) 229474349 229507117 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229474349 229507117).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15149 229474349 229507117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 229376045 229441581).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 229376045 ≤ 229408813)
    (by decide : 229408813 ≤ 229441581) block0 block1

theorem join_0_1 : (twinPrimeSegment 229441581 229507117).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 229441581 ≤ 229474349)
    (by decide : 229474349 ≤ 229507117) block2 block3

theorem join_1_0 : (twinPrimeSegment 229376045 229507117).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 229376045 ≤ 229441581)
    (by decide : 229441581 ≤ 229507117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 229376045 229507117).card = 489 := join_1_0

end S109C06
end Sude.GeneratedTwinScan
