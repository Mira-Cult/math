import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22814)) 520486957 520519725 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 520486957 520519725).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22814 520486957 520519725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22815)) 520519725 520552493 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 520519725 520552493).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22815 520519725 520552493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22816)) 520552493 520585261 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 520552493 520585261).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22816 520552493 520585261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22817)) 520585261 520618029 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 520585261 520618029).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22817 520585261 520618029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 520486957 520552493).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 520486957 ≤ 520519725)
    (by decide : 520519725 ≤ 520552493) block0 block1

theorem join_0_1 : (twinPrimeSegment 520552493 520618029).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 520552493 ≤ 520585261)
    (by decide : 520585261 ≤ 520618029) block2 block3

theorem join_1_0 : (twinPrimeSegment 520486957 520618029).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 520486957 ≤ 520552493)
    (by decide : 520552493 ≤ 520618029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 520486957 520618029).card = 438 := join_1_0

end S248C03
end Sude.GeneratedTwinScan
