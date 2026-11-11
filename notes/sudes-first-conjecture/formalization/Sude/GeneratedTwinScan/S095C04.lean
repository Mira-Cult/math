import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14134)) 199753773 199786541 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 199753773 199786541).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14134 199753773 199786541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14135)) 199786541 199819309 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 199786541 199819309).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14135 199786541 199819309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14136)) 199819309 199852077 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 199819309 199852077).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14136 199819309 199852077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14138)) 199852077 199884845 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 199852077 199884845).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14138 199852077 199884845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 199753773 199819309).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 199753773 ≤ 199786541)
    (by decide : 199786541 ≤ 199819309) block0 block1

theorem join_0_1 : (twinPrimeSegment 199819309 199884845).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 199819309 ≤ 199852077)
    (by decide : 199852077 ≤ 199884845) block2 block3

theorem join_1_0 : (twinPrimeSegment 199753773 199884845).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 199753773 ≤ 199819309)
    (by decide : 199819309 ≤ 199884845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 199753773 199884845).card = 486 := join_1_0

end S095C04
end Sude.GeneratedTwinScan
