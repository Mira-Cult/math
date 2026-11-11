import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17143)) 293863469 293896237 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 293863469 293896237).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17143 293863469 293896237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17144)) 293896237 293929005 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 293896237 293929005).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17144 293896237 293929005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17145)) 293929005 293961773 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 293929005 293961773).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17145 293929005 293961773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17146)) 293961773 293994541 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 293961773 293994541).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17146 293961773 293994541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 293863469 293929005).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 293863469 ≤ 293896237)
    (by decide : 293896237 ≤ 293929005) block0 block1

theorem join_0_1 : (twinPrimeSegment 293929005 293994541).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 293929005 ≤ 293961773)
    (by decide : 293961773 ≤ 293994541) block2 block3

theorem join_1_0 : (twinPrimeSegment 293863469 293994541).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 293863469 ≤ 293929005)
    (by decide : 293929005 ≤ 293994541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 293863469 293994541).card = 476 := join_1_0

end S140C02
end Sude.GeneratedTwinScan
