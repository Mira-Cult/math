import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22382)) 500957229 500989997 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500957229 500989997).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22382 500957229 500989997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22383)) 500989997 501022765 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500989997 501022765).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22383 500989997 501022765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22384)) 501022765 501055533 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501022765 501055533).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22384 501022765 501055533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22385)) 501055533 501088301 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501055533 501088301).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22385 501055533 501088301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500957229 501022765).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 500957229 ≤ 500989997)
    (by decide : 500989997 ≤ 501022765) block0 block1

theorem join_0_1 : (twinPrimeSegment 501022765 501088301).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 501022765 ≤ 501055533)
    (by decide : 501055533 ≤ 501088301) block2 block3

theorem join_1_0 : (twinPrimeSegment 500957229 501088301).card = 394 := by
  simpa using combineTwinPrimeSegments (by decide : 500957229 ≤ 501022765)
    (by decide : 501022765 ≤ 501088301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500957229 501088301).card = 394 := join_1_0

end S238C14
end Sude.GeneratedTwinScan
