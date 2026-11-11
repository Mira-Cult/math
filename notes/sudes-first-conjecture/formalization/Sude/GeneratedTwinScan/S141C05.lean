import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17215)) 296353837 296386605 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 296353837 296386605).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17215 296353837 296386605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17216)) 296386605 296419373 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 296386605 296419373).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17216 296386605 296419373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17217)) 296419373 296452141 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296419373 296452141).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17217 296419373 296452141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17218)) 296452141 296484909 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296452141 296484909).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17218 296452141 296484909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 296353837 296419373).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 296353837 ≤ 296386605)
    (by decide : 296386605 ≤ 296419373) block0 block1

theorem join_0_1 : (twinPrimeSegment 296419373 296484909).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 296419373 ≤ 296452141)
    (by decide : 296452141 ≤ 296484909) block2 block3

theorem join_1_0 : (twinPrimeSegment 296353837 296484909).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 296353837 ≤ 296419373)
    (by decide : 296419373 ≤ 296484909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 296353837 296484909).card = 483 := join_1_0

end S141C05
end Sude.GeneratedTwinScan
