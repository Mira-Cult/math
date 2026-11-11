import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20355)) 414318637 414351405 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 414318637 414351405).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20355 414318637 414351405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20356)) 414351405 414384173 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 414351405 414384173).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20356 414351405 414384173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20357)) 414384173 414416941 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 414384173 414416941).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20357 414384173 414416941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20358)) 414416941 414449709 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 414416941 414449709).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20358 414416941 414449709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 414318637 414384173).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 414318637 ≤ 414351405)
    (by decide : 414351405 ≤ 414384173) block0 block1

theorem join_0_1 : (twinPrimeSegment 414384173 414449709).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 414384173 ≤ 414416941)
    (by decide : 414416941 ≤ 414449709) block2 block3

theorem join_1_0 : (twinPrimeSegment 414318637 414449709).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 414318637 ≤ 414384173)
    (by decide : 414384173 ≤ 414449709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 414318637 414449709).card = 483 := join_1_0

end S197C09
end Sude.GeneratedTwinScan
