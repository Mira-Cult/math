import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18084)) 327024685 327057453 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327024685 327057453).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18084 327024685 327057453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18085)) 327057453 327090221 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327057453 327090221).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18085 327057453 327090221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18086)) 327090221 327122989 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327090221 327122989).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18086 327090221 327122989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18087)) 327122989 327155757 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 327122989 327155757).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18087 327122989 327155757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327024685 327090221).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 327024685 ≤ 327057453)
    (by decide : 327057453 ≤ 327090221) block0 block1

theorem join_0_1 : (twinPrimeSegment 327090221 327155757).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 327090221 ≤ 327122989)
    (by decide : 327122989 ≤ 327155757) block2 block3

theorem join_1_0 : (twinPrimeSegment 327024685 327155757).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 327024685 ≤ 327090221)
    (by decide : 327090221 ≤ 327155757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327024685 327155757).card = 433 := join_1_0

end S155C15
end Sude.GeneratedTwinScan
