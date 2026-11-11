import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14756)) 217710637 217743405 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217710637 217743405).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14756 217710637 217743405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14757)) 217743405 217776173 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 217743405 217776173).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14757 217743405 217776173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14758)) 217776173 217808941 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 217776173 217808941).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14758 217776173 217808941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14759)) 217808941 217841709 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217808941 217841709).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14759 217808941 217841709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217710637 217776173).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 217710637 ≤ 217743405)
    (by decide : 217743405 ≤ 217776173) block0 block1

theorem join_0_1 : (twinPrimeSegment 217776173 217841709).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 217776173 ≤ 217808941)
    (by decide : 217808941 ≤ 217841709) block2 block3

theorem join_1_0 : (twinPrimeSegment 217710637 217841709).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 217710637 ≤ 217776173)
    (by decide : 217776173 ≤ 217841709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217710637 217841709).card = 471 := join_1_0

end S103C13
end Sude.GeneratedTwinScan
