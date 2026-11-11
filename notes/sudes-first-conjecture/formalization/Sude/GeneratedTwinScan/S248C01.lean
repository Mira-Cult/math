import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22809)) 520224813 520257581 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 520224813 520257581).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22809 520224813 520257581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22809)) 520257581 520290349 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 520257581 520290349).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22809 520257581 520290349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22810)) 520290349 520323117 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 520290349 520323117).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22810 520290349 520323117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22811)) 520323117 520355885 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 520323117 520355885).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22811 520323117 520355885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 520224813 520290349).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 520224813 ≤ 520257581)
    (by decide : 520257581 ≤ 520290349) block0 block1

theorem join_0_1 : (twinPrimeSegment 520290349 520355885).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 520290349 ≤ 520323117)
    (by decide : 520323117 ≤ 520355885) block2 block3

theorem join_1_0 : (twinPrimeSegment 520224813 520355885).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 520224813 ≤ 520290349)
    (by decide : 520290349 ≤ 520355885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 520224813 520355885).card = 421 := join_1_0

end S248C01
end Sude.GeneratedTwinScan
