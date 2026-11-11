import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16611)) 275906605 275939373 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 275906605 275939373).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16611 275906605 275939373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16612)) 275939373 275972141 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 275939373 275972141).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16612 275939373 275972141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16613)) 275972141 276004909 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 275972141 276004909).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16613 275972141 276004909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16614)) 276004909 276037677 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 276004909 276037677).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16614 276004909 276037677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 275906605 275972141).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 275906605 ≤ 275939373)
    (by decide : 275939373 ≤ 275972141) block0 block1

theorem join_0_1 : (twinPrimeSegment 275972141 276037677).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 275972141 ≤ 276004909)
    (by decide : 276004909 ≤ 276037677) block2 block3

theorem join_1_0 : (twinPrimeSegment 275906605 276037677).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 275906605 ≤ 275972141)
    (by decide : 275972141 ≤ 276037677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 275906605 276037677).card = 497 := join_1_0

end S131C09
end Sude.GeneratedTwinScan
