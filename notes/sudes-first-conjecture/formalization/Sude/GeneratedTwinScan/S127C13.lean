import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16372)) 268042285 268075053 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268042285 268075053).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16372 268042285 268075053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16373)) 268075053 268107821 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268075053 268107821).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16373 268075053 268107821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16374)) 268107821 268140589 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 268107821 268140589).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16374 268107821 268140589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16375)) 268140589 268173357 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 268140589 268173357).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16375 268140589 268173357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268042285 268107821).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 268042285 ≤ 268075053)
    (by decide : 268075053 ≤ 268107821) block0 block1

theorem join_0_1 : (twinPrimeSegment 268107821 268173357).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 268107821 ≤ 268140589)
    (by decide : 268140589 ≤ 268173357) block2 block3

theorem join_1_0 : (twinPrimeSegment 268042285 268173357).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 268042285 ≤ 268107821)
    (by decide : 268107821 ≤ 268173357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268042285 268173357).card = 452 := join_1_0

end S127C13
end Sude.GeneratedTwinScan
