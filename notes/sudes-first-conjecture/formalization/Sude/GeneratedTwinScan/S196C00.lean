import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20274)) 411041837 411074605 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 411041837 411074605).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20274 411041837 411074605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20275)) 411074605 411107373 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 411074605 411107373).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20275 411074605 411107373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20276)) 411107373 411140141 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 411107373 411140141).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20276 411107373 411140141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20277)) 411140141 411172909 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 411140141 411172909).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20277 411140141 411172909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 411041837 411107373).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 411074605)
    (by decide : 411074605 ≤ 411107373) block0 block1

theorem join_0_1 : (twinPrimeSegment 411107373 411172909).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 411107373 ≤ 411140141)
    (by decide : 411140141 ≤ 411172909) block2 block3

theorem join_1_0 : (twinPrimeSegment 411041837 411172909).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 411107373)
    (by decide : 411107373 ≤ 411172909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 411041837 411172909).card = 445 := join_1_0

end S196C00
end Sude.GeneratedTwinScan
