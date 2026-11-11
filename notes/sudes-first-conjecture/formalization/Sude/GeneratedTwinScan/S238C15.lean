import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22385)) 501088301 501121069 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 501088301 501121069).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22385 501088301 501121069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22386)) 501121069 501153837 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 501121069 501153837).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22386 501121069 501153837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22387)) 501153837 501186605 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501153837 501186605).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22387 501153837 501186605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22387)) 501186605 501219373 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501186605 501219373).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22387 501186605 501219373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 501088301 501153837).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 501088301 ≤ 501121069)
    (by decide : 501121069 ≤ 501153837) block0 block1

theorem join_0_1 : (twinPrimeSegment 501153837 501219373).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 501153837 ≤ 501186605)
    (by decide : 501186605 ≤ 501219373) block2 block3

theorem join_1_0 : (twinPrimeSegment 501088301 501219373).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 501088301 ≤ 501153837)
    (by decide : 501153837 ≤ 501219373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 501088301 501219373).card = 444 := join_1_0

end S238C15
end Sude.GeneratedTwinScan
