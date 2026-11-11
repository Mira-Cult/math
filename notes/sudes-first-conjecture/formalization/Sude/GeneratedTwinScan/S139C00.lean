import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17074)) 291504173 291536941 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 291504173 291536941).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17074 291504173 291536941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17075)) 291536941 291569709 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291536941 291569709).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17075 291536941 291569709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17076)) 291569709 291602477 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291569709 291602477).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17076 291569709 291602477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17077)) 291602477 291635245 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291602477 291635245).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17077 291602477 291635245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 291504173 291569709).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 291504173 ≤ 291536941)
    (by decide : 291536941 ≤ 291569709) block0 block1

theorem join_0_1 : (twinPrimeSegment 291569709 291635245).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 291569709 ≤ 291602477)
    (by decide : 291602477 ≤ 291635245) block2 block3

theorem join_1_0 : (twinPrimeSegment 291504173 291635245).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 291504173 ≤ 291569709)
    (by decide : 291569709 ≤ 291635245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 291504173 291635245).card = 441 := join_1_0

end S139C00
end Sude.GeneratedTwinScan
