import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20063)) 402522157 402554925 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 402522157 402554925).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20063 402522157 402554925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20064)) 402554925 402587693 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402554925 402587693).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20064 402554925 402587693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20065)) 402587693 402620461 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402587693 402620461).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20065 402587693 402620461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20066)) 402620461 402653229 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 402620461 402653229).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20066 402620461 402653229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 402522157 402587693).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 402522157 ≤ 402554925)
    (by decide : 402554925 ≤ 402587693) block0 block1

theorem join_0_1 : (twinPrimeSegment 402587693 402653229).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 402587693 ≤ 402620461)
    (by decide : 402620461 ≤ 402653229) block2 block3

theorem join_1_0 : (twinPrimeSegment 402522157 402653229).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 402522157 ≤ 402587693)
    (by decide : 402587693 ≤ 402653229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 402522157 402653229).card = 442 := join_1_0

end S191C15
end Sude.GeneratedTwinScan
