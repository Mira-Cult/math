import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15042)) 226230317 226263085 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 226230317 226263085).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15042 226230317 226263085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15043)) 226263085 226295853 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 226263085 226295853).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15043 226263085 226295853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15044)) 226295853 226328621 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 226295853 226328621).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15044 226295853 226328621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15045)) 226328621 226361389 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 226328621 226361389).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15045 226328621 226361389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 226230317 226295853).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 226230317 ≤ 226263085)
    (by decide : 226263085 ≤ 226295853) block0 block1

theorem join_0_1 : (twinPrimeSegment 226295853 226361389).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 226295853 ≤ 226328621)
    (by decide : 226328621 ≤ 226361389) block2 block3

theorem join_1_0 : (twinPrimeSegment 226230317 226361389).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 226230317 ≤ 226295853)
    (by decide : 226295853 ≤ 226361389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 226230317 226361389).card = 434 := join_1_0

end S107C14
end Sude.GeneratedTwinScan
