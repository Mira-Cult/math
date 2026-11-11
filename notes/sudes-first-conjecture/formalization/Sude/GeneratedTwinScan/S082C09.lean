import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13159)) 173146157 173178925 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 173146157 173178925).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13159 173146157 173178925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13160)) 173178925 173211693 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 173178925 173211693).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13160 173178925 173211693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13162)) 173211693 173244461 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 173211693 173244461).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13162 173211693 173244461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13163)) 173244461 173277229 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 173244461 173277229).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13163 173244461 173277229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 173146157 173211693).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 173146157 ≤ 173178925)
    (by decide : 173178925 ≤ 173211693) block0 block1

theorem join_0_1 : (twinPrimeSegment 173211693 173277229).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 173211693 ≤ 173244461)
    (by decide : 173244461 ≤ 173277229) block2 block3

theorem join_1_0 : (twinPrimeSegment 173146157 173277229).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 173146157 ≤ 173211693)
    (by decide : 173211693 ≤ 173277229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 173146157 173277229).card = 469 := join_1_0

end S082C09
end Sude.GeneratedTwinScan
