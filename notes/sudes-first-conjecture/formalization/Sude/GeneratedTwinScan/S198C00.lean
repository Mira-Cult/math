import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20378)) 415236141 415268909 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 415236141 415268909).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20378 415236141 415268909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20378)) 415268909 415301677 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 415268909 415301677).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20378 415268909 415301677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20379)) 415301677 415334445 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 415301677 415334445).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20379 415301677 415334445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20380)) 415334445 415367213 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 415334445 415367213).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20380 415334445 415367213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 415236141 415301677).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 415236141 ≤ 415268909)
    (by decide : 415268909 ≤ 415301677) block0 block1

theorem join_0_1 : (twinPrimeSegment 415301677 415367213).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 415301677 ≤ 415334445)
    (by decide : 415334445 ≤ 415367213) block2 block3

theorem join_1_0 : (twinPrimeSegment 415236141 415367213).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 415236141 ≤ 415301677)
    (by decide : 415301677 ≤ 415367213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 415236141 415367213).card = 411 := join_1_0

end S198C00
end Sude.GeneratedTwinScan
