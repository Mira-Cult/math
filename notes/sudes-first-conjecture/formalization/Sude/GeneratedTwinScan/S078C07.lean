import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12826)) 164495405 164528173 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 164495405 164528173).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12826 164495405 164528173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12828)) 164528173 164560941 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 164528173 164560941).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12828 164528173 164560941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12829)) 164560941 164593709 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 164560941 164593709).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12829 164560941 164593709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12830)) 164593709 164626477 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 164593709 164626477).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12830 164593709 164626477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 164495405 164560941).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 164495405 ≤ 164528173)
    (by decide : 164528173 ≤ 164560941) block0 block1

theorem join_0_1 : (twinPrimeSegment 164560941 164626477).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 164560941 ≤ 164593709)
    (by decide : 164593709 ≤ 164626477) block2 block3

theorem join_1_0 : (twinPrimeSegment 164495405 164626477).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 164495405 ≤ 164560941)
    (by decide : 164560941 ≤ 164626477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 164495405 164626477).card = 490 := join_1_0

end S078C07
end Sude.GeneratedTwinScan
