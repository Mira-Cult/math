import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20557)) 422576173 422608941 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422576173 422608941).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20557 422576173 422608941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20558)) 422608941 422641709 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 422608941 422641709).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20558 422608941 422641709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20559)) 422641709 422674477 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 422641709 422674477).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20559 422641709 422674477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20559)) 422674477 422707245 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422674477 422707245).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20559 422674477 422707245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422576173 422641709).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 422576173 ≤ 422608941)
    (by decide : 422608941 ≤ 422641709) block0 block1

theorem join_0_1 : (twinPrimeSegment 422641709 422707245).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 422641709 ≤ 422674477)
    (by decide : 422674477 ≤ 422707245) block2 block3

theorem join_1_0 : (twinPrimeSegment 422576173 422707245).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 422576173 ≤ 422641709)
    (by decide : 422641709 ≤ 422707245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422576173 422707245).card = 459 := join_1_0

end S201C08
end Sude.GeneratedTwinScan
