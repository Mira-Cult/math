import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21629)) 467796013 467828781 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 467796013 467828781).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21629 467796013 467828781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21630)) 467828781 467861549 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 467828781 467861549).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21630 467828781 467861549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21630)) 467861549 467894317 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 467861549 467894317).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21630 467861549 467894317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21631)) 467894317 467927085 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 467894317 467927085).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21631 467894317 467927085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 467796013 467861549).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 467796013 ≤ 467828781)
    (by decide : 467828781 ≤ 467861549) block0 block1

theorem join_0_1 : (twinPrimeSegment 467861549 467927085).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 467861549 ≤ 467894317)
    (by decide : 467894317 ≤ 467927085) block2 block3

theorem join_1_0 : (twinPrimeSegment 467796013 467927085).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 467796013 ≤ 467861549)
    (by decide : 467861549 ≤ 467927085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 467796013 467927085).card = 467 := join_1_0

end S223C01
end Sude.GeneratedTwinScan
