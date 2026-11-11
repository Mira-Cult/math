import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19965)) 398589997 398622765 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 398589997 398622765).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19965 398589997 398622765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19966)) 398622765 398655533 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 398622765 398655533).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19966 398622765 398655533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19967)) 398655533 398688301 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 398655533 398688301).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19967 398655533 398688301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19968)) 398688301 398721069 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 398688301 398721069).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19968 398688301 398721069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 398589997 398655533).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 398589997 ≤ 398622765)
    (by decide : 398622765 ≤ 398655533) block0 block1

theorem join_0_1 : (twinPrimeSegment 398655533 398721069).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 398655533 ≤ 398688301)
    (by decide : 398688301 ≤ 398721069) block2 block3

theorem join_1_0 : (twinPrimeSegment 398589997 398721069).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 398589997 ≤ 398655533)
    (by decide : 398655533 ≤ 398721069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 398589997 398721069).card = 457 := join_1_0

end S190C01
end Sude.GeneratedTwinScan
