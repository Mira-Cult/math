import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15322)) 234749997 234782765 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 234749997 234782765).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15322 234749997 234782765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15323)) 234782765 234815533 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 234782765 234815533).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15323 234782765 234815533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15324)) 234815533 234848301 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234815533 234848301).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15324 234815533 234848301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15325)) 234848301 234881069 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234848301 234881069).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15325 234848301 234881069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 234749997 234815533).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 234749997 ≤ 234782765)
    (by decide : 234782765 ≤ 234815533) block0 block1

theorem join_0_1 : (twinPrimeSegment 234815533 234881069).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 234815533 ≤ 234848301)
    (by decide : 234848301 ≤ 234881069) block2 block3

theorem join_1_0 : (twinPrimeSegment 234749997 234881069).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 234749997 ≤ 234815533)
    (by decide : 234815533 ≤ 234881069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 234749997 234881069).card = 497 := join_1_0

end S111C15
end Sude.GeneratedTwinScan
