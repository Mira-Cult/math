import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14804)) 219152429 219185197 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 219152429 219185197).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14804 219152429 219185197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14806)) 219185197 219217965 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 219185197 219217965).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14806 219185197 219217965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14807)) 219217965 219250733 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 219217965 219250733).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14807 219217965 219250733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14808)) 219250733 219283501 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 219250733 219283501).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14808 219250733 219283501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 219152429 219217965).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 219152429 ≤ 219185197)
    (by decide : 219185197 ≤ 219217965) block0 block1

theorem join_0_1 : (twinPrimeSegment 219217965 219283501).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 219217965 ≤ 219250733)
    (by decide : 219250733 ≤ 219283501) block2 block3

theorem join_1_0 : (twinPrimeSegment 219152429 219283501).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 219152429 ≤ 219217965)
    (by decide : 219217965 ≤ 219283501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 219152429 219283501).card = 473 := join_1_0

end S104C08
end Sude.GeneratedTwinScan
