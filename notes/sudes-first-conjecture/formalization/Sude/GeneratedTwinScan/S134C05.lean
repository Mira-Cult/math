import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16784)) 281673773 281706541 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 281673773 281706541).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16784 281673773 281706541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16785)) 281706541 281739309 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 281706541 281739309).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16785 281706541 281739309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16786)) 281739309 281772077 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 281739309 281772077).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16786 281739309 281772077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16787)) 281772077 281804845 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 281772077 281804845).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16787 281772077 281804845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 281673773 281739309).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 281673773 ≤ 281706541)
    (by decide : 281706541 ≤ 281739309) block0 block1

theorem join_0_1 : (twinPrimeSegment 281739309 281804845).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 281739309 ≤ 281772077)
    (by decide : 281772077 ≤ 281804845) block2 block3

theorem join_1_0 : (twinPrimeSegment 281673773 281804845).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 281673773 ≤ 281739309)
    (by decide : 281739309 ≤ 281804845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 281673773 281804845).card = 462 := join_1_0

end S134C05
end Sude.GeneratedTwinScan
