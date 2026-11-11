import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15740)) 247726125 247758893 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 247726125 247758893).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15740 247726125 247758893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15741)) 247758893 247791661 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 247758893 247791661).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15741 247758893 247791661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15742)) 247791661 247824429 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 247791661 247824429).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15742 247791661 247824429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15743)) 247824429 247857197 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 247824429 247857197).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15743 247824429 247857197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 247726125 247791661).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 247726125 ≤ 247758893)
    (by decide : 247758893 ≤ 247791661) block0 block1

theorem join_0_1 : (twinPrimeSegment 247791661 247857197).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 247791661 ≤ 247824429)
    (by decide : 247824429 ≤ 247857197) block2 block3

theorem join_1_0 : (twinPrimeSegment 247726125 247857197).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 247726125 ≤ 247791661)
    (by decide : 247791661 ≤ 247857197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 247726125 247857197).card = 486 := join_1_0

end S118C02
end Sude.GeneratedTwinScan
