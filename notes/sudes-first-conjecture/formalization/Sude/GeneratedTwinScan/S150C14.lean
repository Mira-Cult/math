import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17788)) 316407853 316440621 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 316407853 316440621).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17788 316407853 316440621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17789)) 316440621 316473389 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 316440621 316473389).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17789 316440621 316473389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17790)) 316473389 316506157 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 316473389 316506157).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17790 316473389 316506157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17791)) 316506157 316538925 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 316506157 316538925).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17791 316506157 316538925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 316407853 316473389).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 316407853 ≤ 316440621)
    (by decide : 316440621 ≤ 316473389) block0 block1

theorem join_0_1 : (twinPrimeSegment 316473389 316538925).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 316473389 ≤ 316506157)
    (by decide : 316506157 ≤ 316538925) block2 block3

theorem join_1_0 : (twinPrimeSegment 316407853 316538925).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 316407853 ≤ 316473389)
    (by decide : 316473389 ≤ 316538925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 316407853 316538925).card = 460 := join_1_0

end S150C14
end Sude.GeneratedTwinScan
