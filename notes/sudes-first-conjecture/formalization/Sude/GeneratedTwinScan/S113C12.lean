import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15446)) 238551085 238583853 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238551085 238583853).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15446 238551085 238583853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15447)) 238583853 238616621 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238583853 238616621).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15447 238583853 238616621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15448)) 238616621 238649389 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 238616621 238649389).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15448 238616621 238649389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15449)) 238649389 238682157 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 238649389 238682157).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15449 238649389 238682157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238551085 238616621).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 238551085 ≤ 238583853)
    (by decide : 238583853 ≤ 238616621) block0 block1

theorem join_0_1 : (twinPrimeSegment 238616621 238682157).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 238616621 ≤ 238649389)
    (by decide : 238649389 ≤ 238682157) block2 block3

theorem join_1_0 : (twinPrimeSegment 238551085 238682157).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 238551085 ≤ 238616621)
    (by decide : 238616621 ≤ 238682157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238551085 238682157).card = 445 := join_1_0

end S113C12
end Sude.GeneratedTwinScan
