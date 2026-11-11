import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18372)) 337510445 337543213 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 337510445 337543213).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18372 337510445 337543213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18373)) 337543213 337575981 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337543213 337575981).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18373 337543213 337575981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18374)) 337575981 337608749 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337575981 337608749).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18374 337575981 337608749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18375)) 337608749 337641517 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 337608749 337641517).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18375 337608749 337641517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 337510445 337575981).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 337510445 ≤ 337543213)
    (by decide : 337543213 ≤ 337575981) block0 block1

theorem join_0_1 : (twinPrimeSegment 337575981 337641517).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 337575981 ≤ 337608749)
    (by decide : 337608749 ≤ 337641517) block2 block3

theorem join_1_0 : (twinPrimeSegment 337510445 337641517).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 337510445 ≤ 337575981)
    (by decide : 337575981 ≤ 337641517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 337510445 337641517).card = 427 := join_1_0

end S160C15
end Sude.GeneratedTwinScan
