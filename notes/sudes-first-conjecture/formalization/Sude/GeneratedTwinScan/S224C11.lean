import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21707)) 471203885 471236653 = 90 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471203885 471236653).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21707 471203885 471236653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21708)) 471236653 471269421 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 471236653 471269421).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21708 471236653 471269421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21709)) 471269421 471302189 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471269421 471302189).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21709 471269421 471302189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21710)) 471302189 471334957 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471302189 471334957).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21710 471302189 471334957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471203885 471269421).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 471203885 ≤ 471236653)
    (by decide : 471236653 ≤ 471269421) block0 block1

theorem join_0_1 : (twinPrimeSegment 471269421 471334957).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 471269421 ≤ 471302189)
    (by decide : 471302189 ≤ 471334957) block2 block3

theorem join_1_0 : (twinPrimeSegment 471203885 471334957).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 471203885 ≤ 471269421)
    (by decide : 471269421 ≤ 471334957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471203885 471334957).card = 436 := join_1_0

end S224C11
end Sude.GeneratedTwinScan
