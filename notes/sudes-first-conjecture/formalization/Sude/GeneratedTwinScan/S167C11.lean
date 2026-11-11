import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18753)) 351666221 351698989 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 351666221 351698989).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18753 351666221 351698989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18754)) 351698989 351731757 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 351698989 351731757).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18754 351698989 351731757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18755)) 351731757 351764525 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 351731757 351764525).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18755 351731757 351764525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18756)) 351764525 351797293 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 351764525 351797293).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18756 351764525 351797293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 351666221 351731757).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 351666221 ≤ 351698989)
    (by decide : 351698989 ≤ 351731757) block0 block1

theorem join_0_1 : (twinPrimeSegment 351731757 351797293).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 351731757 ≤ 351764525)
    (by decide : 351764525 ≤ 351797293) block2 block3

theorem join_1_0 : (twinPrimeSegment 351666221 351797293).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 351666221 ≤ 351731757)
    (by decide : 351731757 ≤ 351797293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 351666221 351797293).card = 417 := join_1_0

end S167C11
end Sude.GeneratedTwinScan
