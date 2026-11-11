import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17566)) 308543533 308576301 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 308543533 308576301).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17566 308543533 308576301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17567)) 308576301 308609069 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 308576301 308609069).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17567 308576301 308609069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17568)) 308609069 308641837 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 308609069 308641837).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17568 308609069 308641837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17569)) 308641837 308674605 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 308641837 308674605).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17569 308641837 308674605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 308543533 308609069).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 308543533 ≤ 308576301)
    (by decide : 308576301 ≤ 308609069) block0 block1

theorem join_0_1 : (twinPrimeSegment 308609069 308674605).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 308609069 ≤ 308641837)
    (by decide : 308641837 ≤ 308674605) block2 block3

theorem join_1_0 : (twinPrimeSegment 308543533 308674605).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 308543533 ≤ 308609069)
    (by decide : 308609069 ≤ 308674605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 308543533 308674605).card = 461 := join_1_0

end S147C02
end Sude.GeneratedTwinScan
