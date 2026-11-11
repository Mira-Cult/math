import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21698)) 470810669 470843437 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 470810669 470843437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21698 470810669 470843437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21699)) 470843437 470876205 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 470843437 470876205).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21699 470843437 470876205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21700)) 470876205 470908973 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 470876205 470908973).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21700 470876205 470908973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21701)) 470908973 470941741 = 91 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 470908973 470941741).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21701 470908973 470941741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 470810669 470876205).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 470810669 ≤ 470843437)
    (by decide : 470843437 ≤ 470876205) block0 block1

theorem join_0_1 : (twinPrimeSegment 470876205 470941741).card = 185 := by
  simpa using combineTwinPrimeSegments (by decide : 470876205 ≤ 470908973)
    (by decide : 470908973 ≤ 470941741) block2 block3

theorem join_1_0 : (twinPrimeSegment 470810669 470941741).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 470810669 ≤ 470876205)
    (by decide : 470876205 ≤ 470941741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 470810669 470941741).card = 410 := join_1_0

end S224C08
end Sude.GeneratedTwinScan
