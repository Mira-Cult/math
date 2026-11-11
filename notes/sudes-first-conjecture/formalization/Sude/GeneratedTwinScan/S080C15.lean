import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13029)) 169738285 169771053 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 169738285 169771053).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13029 169738285 169771053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13030)) 169771053 169803821 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 169771053 169803821).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13030 169771053 169803821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13032)) 169803821 169836589 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169803821 169836589).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13032 169803821 169836589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13033)) 169836589 169869357 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169836589 169869357).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13033 169836589 169869357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 169738285 169803821).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 169738285 ≤ 169771053)
    (by decide : 169771053 ≤ 169803821) block0 block1

theorem join_0_1 : (twinPrimeSegment 169803821 169869357).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 169803821 ≤ 169836589)
    (by decide : 169836589 ≤ 169869357) block2 block3

theorem join_1_0 : (twinPrimeSegment 169738285 169869357).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 169738285 ≤ 169803821)
    (by decide : 169803821 ≤ 169869357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 169738285 169869357).card = 481 := join_1_0

end S080C15
end Sude.GeneratedTwinScan
