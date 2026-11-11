import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20070)) 402784301 402817069 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 402784301 402817069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20070 402784301 402817069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20071)) 402817069 402849837 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402817069 402849837).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20071 402817069 402849837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20071)) 402849837 402882605 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402849837 402882605).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20071 402849837 402882605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20072)) 402882605 402915373 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 402882605 402915373).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20072 402882605 402915373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 402784301 402849837).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 402784301 ≤ 402817069)
    (by decide : 402817069 ≤ 402849837) block0 block1

theorem join_0_1 : (twinPrimeSegment 402849837 402915373).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 402849837 ≤ 402882605)
    (by decide : 402882605 ≤ 402915373) block2 block3

theorem join_1_0 : (twinPrimeSegment 402784301 402915373).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 402784301 ≤ 402849837)
    (by decide : 402849837 ≤ 402915373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 402784301 402915373).card = 445 := join_1_0

end S192C01
end Sude.GeneratedTwinScan
