import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18574)) 344981549 345014317 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344981549 345014317).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18574 344981549 345014317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18575)) 345014317 345047085 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345014317 345047085).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18575 345014317 345047085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18576)) 345047085 345079853 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345047085 345079853).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18576 345047085 345079853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18577)) 345079853 345112621 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345079853 345112621).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18577 345079853 345112621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344981549 345047085).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 344981549 ≤ 345014317)
    (by decide : 345014317 ≤ 345047085) block0 block1

theorem join_0_1 : (twinPrimeSegment 345047085 345112621).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 345047085 ≤ 345079853)
    (by decide : 345079853 ≤ 345112621) block2 block3

theorem join_1_0 : (twinPrimeSegment 344981549 345112621).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 344981549 ≤ 345047085)
    (by decide : 345047085 ≤ 345112621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344981549 345112621).card = 434 := join_1_0

end S164C08
end Sude.GeneratedTwinScan
