import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12542)) 157286445 157319213 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 157286445 157319213).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12542 157286445 157319213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12544)) 157319213 157351981 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 157319213 157351981).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12544 157319213 157351981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12545)) 157351981 157384749 = 150 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 157351981 157384749).card = 150 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12545 157351981 157384749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12546)) 157384749 157417517 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 157384749 157417517).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12546 157384749 157417517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 157286445 157351981).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 157286445 ≤ 157319213)
    (by decide : 157319213 ≤ 157351981) block0 block1

theorem join_0_1 : (twinPrimeSegment 157351981 157417517).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 157351981 ≤ 157384749)
    (by decide : 157384749 ≤ 157417517) block2 block3

theorem join_1_0 : (twinPrimeSegment 157286445 157417517).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 157286445 ≤ 157351981)
    (by decide : 157351981 ≤ 157417517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 157286445 157417517).card = 499 := join_1_0

end S075C00
end Sude.GeneratedTwinScan
