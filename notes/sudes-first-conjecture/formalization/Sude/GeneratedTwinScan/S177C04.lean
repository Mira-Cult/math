import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19280)) 371720237 371753005 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371720237 371753005).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19280 371720237 371753005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19281)) 371753005 371785773 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 371753005 371785773).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19281 371753005 371785773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19282)) 371785773 371818541 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 371785773 371818541).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19282 371785773 371818541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19283)) 371818541 371851309 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371818541 371851309).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19283 371818541 371851309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371720237 371785773).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 371720237 ≤ 371753005)
    (by decide : 371753005 ≤ 371785773) block0 block1

theorem join_0_1 : (twinPrimeSegment 371785773 371851309).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 371785773 ≤ 371818541)
    (by decide : 371818541 ≤ 371851309) block2 block3

theorem join_1_0 : (twinPrimeSegment 371720237 371851309).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 371720237 ≤ 371785773)
    (by decide : 371785773 ≤ 371851309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371720237 371851309).card = 456 := join_1_0

end S177C04
end Sude.GeneratedTwinScan
