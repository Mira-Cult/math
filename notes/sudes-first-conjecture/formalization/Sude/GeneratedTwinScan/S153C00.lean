import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17913)) 320864301 320897069 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 320864301 320897069).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17913 320864301 320897069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17914)) 320897069 320929837 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 320897069 320929837).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17914 320897069 320929837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17915)) 320929837 320962605 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 320929837 320962605).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17915 320929837 320962605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17916)) 320962605 320995373 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 320962605 320995373).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17916 320962605 320995373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 320864301 320929837).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 320864301 ≤ 320897069)
    (by decide : 320897069 ≤ 320929837) block0 block1

theorem join_0_1 : (twinPrimeSegment 320929837 320995373).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 320929837 ≤ 320962605)
    (by decide : 320962605 ≤ 320995373) block2 block3

theorem join_1_0 : (twinPrimeSegment 320864301 320995373).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 320864301 ≤ 320929837)
    (by decide : 320929837 ≤ 320995373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 320864301 320995373).card = 446 := join_1_0

end S153C00
end Sude.GeneratedTwinScan
