import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19141)) 366346285 366379053 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 366346285 366379053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19141 366346285 366379053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19141)) 366379053 366411821 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 366379053 366411821).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19141 366379053 366411821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19142)) 366411821 366444589 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366411821 366444589).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19142 366411821 366444589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19143)) 366444589 366477357 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366444589 366477357).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19143 366444589 366477357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 366346285 366411821).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 366346285 ≤ 366379053)
    (by decide : 366379053 ≤ 366411821) block0 block1

theorem join_0_1 : (twinPrimeSegment 366411821 366477357).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 366411821 ≤ 366444589)
    (by decide : 366444589 ≤ 366477357) block2 block3

theorem join_1_0 : (twinPrimeSegment 366346285 366477357).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 366346285 ≤ 366411821)
    (by decide : 366411821 ≤ 366477357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 366346285 366477357).card = 449 := join_1_0

end S174C11
end Sude.GeneratedTwinScan
