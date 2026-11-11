import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22786)) 519176237 519209005 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519176237 519209005).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22786 519176237 519209005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22786)) 519209005 519241773 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519209005 519241773).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22786 519209005 519241773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22787)) 519241773 519274541 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 519241773 519274541).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22787 519241773 519274541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22788)) 519274541 519307309 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519274541 519307309).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22788 519274541 519307309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519176237 519241773).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 519176237 ≤ 519209005)
    (by decide : 519209005 ≤ 519241773) block0 block1

theorem join_0_1 : (twinPrimeSegment 519241773 519307309).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 519241773 ≤ 519274541)
    (by decide : 519274541 ≤ 519307309) block2 block3

theorem join_1_0 : (twinPrimeSegment 519176237 519307309).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 519176237 ≤ 519241773)
    (by decide : 519241773 ≤ 519307309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519176237 519307309).card = 422 := join_1_0

end S247C09
end Sude.GeneratedTwinScan
