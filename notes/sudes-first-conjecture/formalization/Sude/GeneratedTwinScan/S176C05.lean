import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19229)) 369754157 369786925 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 369754157 369786925).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19229 369754157 369786925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19230)) 369786925 369819693 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 369786925 369819693).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19230 369786925 369819693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19231)) 369819693 369852461 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 369819693 369852461).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19231 369819693 369852461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19232)) 369852461 369885229 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 369852461 369885229).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19232 369852461 369885229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 369754157 369819693).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 369754157 ≤ 369786925)
    (by decide : 369786925 ≤ 369819693) block0 block1

theorem join_0_1 : (twinPrimeSegment 369819693 369885229).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 369819693 ≤ 369852461)
    (by decide : 369852461 ≤ 369885229) block2 block3

theorem join_1_0 : (twinPrimeSegment 369754157 369885229).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 369754157 ≤ 369819693)
    (by decide : 369819693 ≤ 369885229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 369754157 369885229).card = 421 := join_1_0

end S176C05
end Sude.GeneratedTwinScan
