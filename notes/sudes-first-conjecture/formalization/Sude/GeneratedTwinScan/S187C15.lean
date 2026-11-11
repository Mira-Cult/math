import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19853)) 394133549 394166317 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394133549 394166317).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19853 394133549 394166317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19854)) 394166317 394199085 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394166317 394199085).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19854 394166317 394199085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19855)) 394199085 394231853 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394199085 394231853).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19855 394199085 394231853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19856)) 394231853 394264621 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 394231853 394264621).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19856 394231853 394264621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394133549 394199085).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 394133549 ≤ 394166317)
    (by decide : 394166317 ≤ 394199085) block0 block1

theorem join_0_1 : (twinPrimeSegment 394199085 394264621).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 394199085 ≤ 394231853)
    (by decide : 394231853 ≤ 394264621) block2 block3

theorem join_1_0 : (twinPrimeSegment 394133549 394264621).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 394133549 ≤ 394199085)
    (by decide : 394199085 ≤ 394264621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394133549 394264621).card = 460 := join_1_0

end S187C15
end Sude.GeneratedTwinScan
