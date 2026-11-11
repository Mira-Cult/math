import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21361)) 456261677 456294445 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 456261677 456294445).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21361 456261677 456294445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21361)) 456294445 456327213 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 456294445 456327213).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21361 456294445 456327213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21362)) 456327213 456359981 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 456327213 456359981).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21362 456327213 456359981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21363)) 456359981 456392749 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 456359981 456392749).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21363 456359981 456392749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 456261677 456327213).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 456261677 ≤ 456294445)
    (by decide : 456294445 ≤ 456327213) block0 block1

theorem join_0_1 : (twinPrimeSegment 456327213 456392749).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 456327213 ≤ 456359981)
    (by decide : 456359981 ≤ 456392749) block2 block3

theorem join_1_0 : (twinPrimeSegment 456261677 456392749).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 456261677 ≤ 456327213)
    (by decide : 456327213 ≤ 456392749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 456261677 456392749).card = 465 := join_1_0

end S217C09
end Sude.GeneratedTwinScan
