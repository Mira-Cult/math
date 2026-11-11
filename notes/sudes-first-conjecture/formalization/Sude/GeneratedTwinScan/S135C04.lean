import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16842)) 283639853 283672621 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 283639853 283672621).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16842 283639853 283672621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16843)) 283672621 283705389 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283672621 283705389).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16843 283672621 283705389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16844)) 283705389 283738157 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283705389 283738157).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16844 283705389 283738157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16845)) 283738157 283770925 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 283738157 283770925).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16845 283738157 283770925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 283639853 283705389).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 283639853 ≤ 283672621)
    (by decide : 283672621 ≤ 283705389) block0 block1

theorem join_0_1 : (twinPrimeSegment 283705389 283770925).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 283705389 ≤ 283738157)
    (by decide : 283738157 ≤ 283770925) block2 block3

theorem join_1_0 : (twinPrimeSegment 283639853 283770925).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 283639853 ≤ 283705389)
    (by decide : 283705389 ≤ 283770925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 283639853 283770925).card = 467 := join_1_0

end S135C04
end Sude.GeneratedTwinScan
