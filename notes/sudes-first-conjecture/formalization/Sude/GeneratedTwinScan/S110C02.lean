import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15198)) 230948909 230981677 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 230948909 230981677).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15198 230948909 230981677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15199)) 230981677 231014445 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 230981677 231014445).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15199 230981677 231014445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15200)) 231014445 231047213 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231014445 231047213).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15200 231014445 231047213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15201)) 231047213 231079981 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231047213 231079981).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15201 231047213 231079981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 230948909 231014445).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 230948909 ≤ 230981677)
    (by decide : 230981677 ≤ 231014445) block0 block1

theorem join_0_1 : (twinPrimeSegment 231014445 231079981).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 231014445 ≤ 231047213)
    (by decide : 231047213 ≤ 231079981) block2 block3

theorem join_1_0 : (twinPrimeSegment 230948909 231079981).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 230948909 ≤ 231014445)
    (by decide : 231014445 ≤ 231079981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 230948909 231079981).card = 439 := join_1_0

end S110C02
end Sude.GeneratedTwinScan
