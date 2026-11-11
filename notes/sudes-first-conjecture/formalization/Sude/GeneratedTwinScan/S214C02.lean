import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21191)) 449052717 449085485 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449052717 449085485).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21191 449052717 449085485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21192)) 449085485 449118253 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 449085485 449118253).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21192 449085485 449118253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21193)) 449118253 449151021 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 449118253 449151021).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21193 449118253 449151021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21193)) 449151021 449183789 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449151021 449183789).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21193 449151021 449183789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449052717 449118253).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 449052717 ≤ 449085485)
    (by decide : 449085485 ≤ 449118253) block0 block1

theorem join_0_1 : (twinPrimeSegment 449118253 449183789).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 449118253 ≤ 449151021)
    (by decide : 449151021 ≤ 449183789) block2 block3

theorem join_1_0 : (twinPrimeSegment 449052717 449183789).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 449052717 ≤ 449118253)
    (by decide : 449118253 ≤ 449183789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449052717 449183789).card = 432 := join_1_0

end S214C02
end Sude.GeneratedTwinScan
