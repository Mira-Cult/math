import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15959)) 254672941 254705709 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 254672941 254705709).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15959 254672941 254705709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15960)) 254705709 254738477 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 254705709 254738477).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15960 254705709 254738477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15961)) 254738477 254771245 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 254738477 254771245).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15961 254738477 254771245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15962)) 254771245 254804013 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 254771245 254804013).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15962 254771245 254804013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 254672941 254738477).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 254672941 ≤ 254705709)
    (by decide : 254705709 ≤ 254738477) block0 block1

theorem join_0_1 : (twinPrimeSegment 254738477 254804013).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 254738477 ≤ 254771245)
    (by decide : 254771245 ≤ 254804013) block2 block3

theorem join_1_0 : (twinPrimeSegment 254672941 254804013).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 254672941 ≤ 254738477)
    (by decide : 254738477 ≤ 254804013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 254672941 254804013).card = 461 := join_1_0

end S121C07
end Sude.GeneratedTwinScan
