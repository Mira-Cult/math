import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18917)) 357826605 357859373 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357826605 357859373).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18917 357826605 357859373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18918)) 357859373 357892141 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357859373 357892141).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18918 357859373 357892141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18918)) 357892141 357924909 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 357892141 357924909).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18918 357892141 357924909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18919)) 357924909 357957677 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357924909 357957677).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18919 357924909 357957677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357826605 357892141).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 357826605 ≤ 357859373)
    (by decide : 357859373 ≤ 357892141) block0 block1

theorem join_0_1 : (twinPrimeSegment 357892141 357957677).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 357892141 ≤ 357924909)
    (by decide : 357924909 ≤ 357957677) block2 block3

theorem join_1_0 : (twinPrimeSegment 357826605 357957677).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 357826605 ≤ 357892141)
    (by decide : 357892141 ≤ 357957677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357826605 357957677).card = 434 := join_1_0

end S170C10
end Sude.GeneratedTwinScan
