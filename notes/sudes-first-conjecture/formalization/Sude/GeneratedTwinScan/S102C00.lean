import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14626)) 213909549 213942317 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 213909549 213942317).card = 144 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14626 213909549 213942317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14627)) 213942317 213975085 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 213942317 213975085).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14627 213942317 213975085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14629)) 213975085 214007853 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 213975085 214007853).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14629 213975085 214007853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14630)) 214007853 214040621 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 214007853 214040621).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14630 214007853 214040621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 213909549 213975085).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 213909549 ≤ 213942317)
    (by decide : 213942317 ≤ 213975085) block0 block1

theorem join_0_1 : (twinPrimeSegment 213975085 214040621).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 213975085 ≤ 214007853)
    (by decide : 214007853 ≤ 214040621) block2 block3

theorem join_1_0 : (twinPrimeSegment 213909549 214040621).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 213909549 ≤ 213975085)
    (by decide : 213975085 ≤ 214040621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 213909549 214040621).card = 497 := join_1_0

end S102C00
end Sude.GeneratedTwinScan
