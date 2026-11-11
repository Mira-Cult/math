import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21299)) 453640237 453673005 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 453640237 453673005).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21299 453640237 453673005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21300)) 453673005 453705773 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453673005 453705773).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21300 453673005 453705773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21301)) 453705773 453738541 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453705773 453738541).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21301 453705773 453738541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21301)) 453738541 453771309 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 453738541 453771309).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21301 453738541 453771309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 453640237 453705773).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 453640237 ≤ 453673005)
    (by decide : 453673005 ≤ 453705773) block0 block1

theorem join_0_1 : (twinPrimeSegment 453705773 453771309).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 453705773 ≤ 453738541)
    (by decide : 453738541 ≤ 453771309) block2 block3

theorem join_1_0 : (twinPrimeSegment 453640237 453771309).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 453640237 ≤ 453705773)
    (by decide : 453705773 ≤ 453771309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 453640237 453771309).card = 480 := join_1_0

end S216C05
end Sude.GeneratedTwinScan
