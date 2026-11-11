import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22662)) 513540141 513572909 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513540141 513572909).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22662 513540141 513572909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22662)) 513572909 513605677 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513572909 513605677).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22662 513572909 513605677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22663)) 513605677 513638445 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513605677 513638445).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22663 513605677 513638445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22664)) 513638445 513671213 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 513638445 513671213).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22664 513638445 513671213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513540141 513605677).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 513540141 ≤ 513572909)
    (by decide : 513572909 ≤ 513605677) block0 block1

theorem join_0_1 : (twinPrimeSegment 513605677 513671213).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 513605677 ≤ 513638445)
    (by decide : 513638445 ≤ 513671213) block2 block3

theorem join_1_0 : (twinPrimeSegment 513540141 513671213).card = 389 := by
  simpa using combineTwinPrimeSegments (by decide : 513540141 ≤ 513605677)
    (by decide : 513605677 ≤ 513671213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513540141 513671213).card = 389 := join_1_0

end S244C14
end Sude.GeneratedTwinScan
