import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19557)) 382468141 382500909 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382468141 382500909).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19557 382468141 382500909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19558)) 382500909 382533677 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 382500909 382533677).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19558 382500909 382533677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19559)) 382533677 382566445 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382533677 382566445).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19559 382533677 382566445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19560)) 382566445 382599213 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382566445 382599213).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19560 382566445 382599213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382468141 382533677).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 382468141 ≤ 382500909)
    (by decide : 382500909 ≤ 382533677) block0 block1

theorem join_0_1 : (twinPrimeSegment 382533677 382599213).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 382533677 ≤ 382566445)
    (by decide : 382566445 ≤ 382599213) block2 block3

theorem join_1_0 : (twinPrimeSegment 382468141 382599213).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 382468141 ≤ 382533677)
    (by decide : 382533677 ≤ 382599213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382468141 382599213).card = 464 := join_1_0

end S182C06
end Sude.GeneratedTwinScan
