import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22639)) 512491565 512524333 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 512491565 512524333).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22639 512491565 512524333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22639)) 512524333 512557101 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 512524333 512557101).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22639 512524333 512557101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22640)) 512557101 512589869 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 512557101 512589869).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22640 512557101 512589869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22641)) 512589869 512622637 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 512589869 512622637).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22641 512589869 512622637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 512491565 512557101).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 512491565 ≤ 512524333)
    (by decide : 512524333 ≤ 512557101) block0 block1

theorem join_0_1 : (twinPrimeSegment 512557101 512622637).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 512557101 ≤ 512589869)
    (by decide : 512589869 ≤ 512622637) block2 block3

theorem join_1_0 : (twinPrimeSegment 512491565 512622637).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 512491565 ≤ 512557101)
    (by decide : 512557101 ≤ 512622637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 512491565 512622637).card = 442 := join_1_0

end S244C06
end Sude.GeneratedTwinScan
