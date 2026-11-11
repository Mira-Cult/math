import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22114)) 489029677 489062445 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489029677 489062445).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22114 489029677 489062445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22115)) 489062445 489095213 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489062445 489095213).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22115 489062445 489095213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22116)) 489095213 489127981 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 489095213 489127981).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22116 489095213 489127981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22116)) 489127981 489160749 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 489127981 489160749).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22116 489127981 489160749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489029677 489095213).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 489029677 ≤ 489062445)
    (by decide : 489062445 ≤ 489095213) block0 block1

theorem join_0_1 : (twinPrimeSegment 489095213 489160749).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 489095213 ≤ 489127981)
    (by decide : 489127981 ≤ 489160749) block2 block3

theorem join_1_0 : (twinPrimeSegment 489029677 489160749).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 489029677 ≤ 489095213)
    (by decide : 489095213 ≤ 489160749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489029677 489160749).card = 441 := join_1_0

end S233C03
end Sude.GeneratedTwinScan
