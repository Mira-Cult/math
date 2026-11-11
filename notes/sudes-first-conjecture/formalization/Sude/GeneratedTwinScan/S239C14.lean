import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22429)) 503054381 503087149 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 503054381 503087149).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22429 503054381 503087149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22430)) 503087149 503119917 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 503087149 503119917).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22430 503087149 503119917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22431)) 503119917 503152685 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 503119917 503152685).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22431 503119917 503152685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22431)) 503152685 503185453 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 503152685 503185453).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22431 503152685 503185453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 503054381 503119917).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 503054381 ≤ 503087149)
    (by decide : 503087149 ≤ 503119917) block0 block1

theorem join_0_1 : (twinPrimeSegment 503119917 503185453).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 503119917 ≤ 503152685)
    (by decide : 503152685 ≤ 503185453) block2 block3

theorem join_1_0 : (twinPrimeSegment 503054381 503185453).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 503054381 ≤ 503119917)
    (by decide : 503119917 ≤ 503185453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 503054381 503185453).card = 471 := join_1_0

end S239C14
end Sude.GeneratedTwinScan
