import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20155)) 406192173 406224941 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406192173 406224941).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20155 406192173 406224941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20155)) 406224941 406257709 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 406224941 406257709).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20155 406224941 406257709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20156)) 406257709 406290477 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 406257709 406290477).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20156 406257709 406290477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20157)) 406290477 406323245 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406290477 406323245).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20157 406290477 406323245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406192173 406257709).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 406192173 ≤ 406224941)
    (by decide : 406224941 ≤ 406257709) block0 block1

theorem join_0_1 : (twinPrimeSegment 406257709 406323245).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 406257709 ≤ 406290477)
    (by decide : 406290477 ≤ 406323245) block2 block3

theorem join_1_0 : (twinPrimeSegment 406192173 406323245).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 406192173 ≤ 406257709)
    (by decide : 406257709 ≤ 406323245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406192173 406323245).card = 434 := join_1_0

end S193C11
end Sude.GeneratedTwinScan
