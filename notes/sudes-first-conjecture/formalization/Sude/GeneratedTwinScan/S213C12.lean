import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21173)) 448266285 448299053 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448266285 448299053).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21173 448266285 448299053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21173)) 448299053 448331821 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448299053 448331821).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21173 448299053 448331821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21174)) 448331821 448364589 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448331821 448364589).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21174 448331821 448364589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21175)) 448364589 448397357 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 448364589 448397357).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21175 448364589 448397357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448266285 448331821).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 448266285 ≤ 448299053)
    (by decide : 448299053 ≤ 448331821) block0 block1

theorem join_0_1 : (twinPrimeSegment 448331821 448397357).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 448331821 ≤ 448364589)
    (by decide : 448364589 ≤ 448397357) block2 block3

theorem join_1_0 : (twinPrimeSegment 448266285 448397357).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 448266285 ≤ 448331821)
    (by decide : 448331821 ≤ 448397357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448266285 448397357).card = 471 := join_1_0

end S213C12
end Sude.GeneratedTwinScan
