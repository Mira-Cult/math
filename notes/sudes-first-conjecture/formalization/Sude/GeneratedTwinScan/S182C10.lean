import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19571)) 382992429 383025197 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382992429 383025197).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19571 382992429 383025197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19571)) 383025197 383057965 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383025197 383057965).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19571 383025197 383057965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19572)) 383057965 383090733 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383057965 383090733).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19572 383057965 383090733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19573)) 383090733 383123501 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 383090733 383123501).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19573 383090733 383123501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382992429 383057965).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 382992429 ≤ 383025197)
    (by decide : 383025197 ≤ 383057965) block0 block1

theorem join_0_1 : (twinPrimeSegment 383057965 383123501).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 383057965 ≤ 383090733)
    (by decide : 383090733 ≤ 383123501) block2 block3

theorem join_1_0 : (twinPrimeSegment 382992429 383123501).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 382992429 ≤ 383057965)
    (by decide : 383057965 ≤ 383123501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382992429 383123501).card = 440 := join_1_0

end S182C10
end Sude.GeneratedTwinScan
