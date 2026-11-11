import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15827)) 250478637 250511405 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 250478637 250511405).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15827 250478637 250511405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15828)) 250511405 250544173 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 250511405 250544173).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15828 250511405 250544173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15829)) 250544173 250576941 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250544173 250576941).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15829 250544173 250576941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15830)) 250576941 250609709 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250576941 250609709).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15830 250576941 250609709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 250478637 250544173).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 250478637 ≤ 250511405)
    (by decide : 250511405 ≤ 250544173) block0 block1

theorem join_0_1 : (twinPrimeSegment 250544173 250609709).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 250544173 ≤ 250576941)
    (by decide : 250576941 ≤ 250609709) block2 block3

theorem join_1_0 : (twinPrimeSegment 250478637 250609709).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 250478637 ≤ 250544173)
    (by decide : 250544173 ≤ 250609709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 250478637 250609709).card = 451 := join_1_0

end S119C07
end Sude.GeneratedTwinScan
