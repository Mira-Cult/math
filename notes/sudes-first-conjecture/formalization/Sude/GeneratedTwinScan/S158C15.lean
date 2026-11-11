import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18257)) 333316141 333348909 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 333316141 333348909).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18257 333316141 333348909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18258)) 333348909 333381677 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 333348909 333381677).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18258 333348909 333381677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18259)) 333381677 333414445 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 333381677 333414445).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18259 333381677 333414445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18260)) 333414445 333447213 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 333414445 333447213).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18260 333414445 333447213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 333316141 333381677).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 333316141 ≤ 333348909)
    (by decide : 333348909 ≤ 333381677) block0 block1

theorem join_0_1 : (twinPrimeSegment 333381677 333447213).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 333381677 ≤ 333414445)
    (by decide : 333414445 ≤ 333447213) block2 block3

theorem join_1_0 : (twinPrimeSegment 333316141 333447213).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 333316141 ≤ 333381677)
    (by decide : 333381677 ≤ 333447213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 333316141 333447213).card = 437 := join_1_0

end S158C15
end Sude.GeneratedTwinScan
