import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18365)) 337248301 337281069 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 337248301 337281069).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18365 337248301 337281069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18366)) 337281069 337313837 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337281069 337313837).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18366 337281069 337313837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18366)) 337313837 337346605 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337313837 337346605).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18366 337313837 337346605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18367)) 337346605 337379373 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 337346605 337379373).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18367 337346605 337379373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 337248301 337313837).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 337248301 ≤ 337281069)
    (by decide : 337281069 ≤ 337313837) block0 block1

theorem join_0_1 : (twinPrimeSegment 337313837 337379373).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 337313837 ≤ 337346605)
    (by decide : 337346605 ≤ 337379373) block2 block3

theorem join_1_0 : (twinPrimeSegment 337248301 337379373).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 337248301 ≤ 337313837)
    (by decide : 337313837 ≤ 337379373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 337248301 337379373).card = 448 := join_1_0

end S160C13
end Sude.GeneratedTwinScan
