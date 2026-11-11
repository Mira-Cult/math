import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18518)) 342884397 342917165 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 342884397 342917165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18518 342884397 342917165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18518)) 342917165 342949933 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 342917165 342949933).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18518 342917165 342949933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18519)) 342949933 342982701 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 342949933 342982701).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18519 342949933 342982701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18520)) 342982701 343015469 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 342982701 343015469).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18520 342982701 343015469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 342884397 342949933).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 342884397 ≤ 342917165)
    (by decide : 342917165 ≤ 342949933) block0 block1

theorem join_0_1 : (twinPrimeSegment 342949933 343015469).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 342949933 ≤ 342982701)
    (by decide : 342982701 ≤ 343015469) block2 block3

theorem join_1_0 : (twinPrimeSegment 342884397 343015469).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 342884397 ≤ 342949933)
    (by decide : 342949933 ≤ 343015469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 342884397 343015469).card = 414 := join_1_0

end S163C08
end Sude.GeneratedTwinScan
