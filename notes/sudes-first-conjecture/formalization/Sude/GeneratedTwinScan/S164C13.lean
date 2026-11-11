import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18592)) 345636909 345669677 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 345636909 345669677).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18592 345636909 345669677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18593)) 345669677 345702445 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345669677 345702445).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18593 345669677 345702445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18593)) 345702445 345735213 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345702445 345735213).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18593 345702445 345735213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18594)) 345735213 345767981 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345735213 345767981).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18594 345735213 345767981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 345636909 345702445).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 345636909 ≤ 345669677)
    (by decide : 345669677 ≤ 345702445) block0 block1

theorem join_0_1 : (twinPrimeSegment 345702445 345767981).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 345702445 ≤ 345735213)
    (by decide : 345735213 ≤ 345767981) block2 block3

theorem join_1_0 : (twinPrimeSegment 345636909 345767981).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 345636909 ≤ 345702445)
    (by decide : 345702445 ≤ 345767981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 345636909 345767981).card = 463 := join_1_0

end S164C13
end Sude.GeneratedTwinScan
