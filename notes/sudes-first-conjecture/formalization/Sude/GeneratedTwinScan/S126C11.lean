import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16300)) 265682989 265715757 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 265682989 265715757).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16300 265682989 265715757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16301)) 265715757 265748525 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 265715757 265748525).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16301 265715757 265748525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16302)) 265748525 265781293 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 265748525 265781293).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16302 265748525 265781293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16303)) 265781293 265814061 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 265781293 265814061).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16303 265781293 265814061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 265682989 265748525).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 265682989 ≤ 265715757)
    (by decide : 265715757 ≤ 265748525) block0 block1

theorem join_0_1 : (twinPrimeSegment 265748525 265814061).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 265748525 ≤ 265781293)
    (by decide : 265781293 ≤ 265814061) block2 block3

theorem join_1_0 : (twinPrimeSegment 265682989 265814061).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 265682989 ≤ 265748525)
    (by decide : 265748525 ≤ 265814061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 265682989 265814061).card = 457 := join_1_0

end S126C11
end Sude.GeneratedTwinScan
