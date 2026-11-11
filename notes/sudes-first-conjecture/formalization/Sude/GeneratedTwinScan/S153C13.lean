import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17961)) 322568237 322601005 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 322568237 322601005).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17961 322568237 322601005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17962)) 322601005 322633773 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 322601005 322633773).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17962 322601005 322633773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17962)) 322633773 322666541 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 322633773 322666541).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17962 322633773 322666541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17963)) 322666541 322699309 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 322666541 322699309).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17963 322666541 322699309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 322568237 322633773).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 322568237 ≤ 322601005)
    (by decide : 322601005 ≤ 322633773) block0 block1

theorem join_0_1 : (twinPrimeSegment 322633773 322699309).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 322633773 ≤ 322666541)
    (by decide : 322666541 ≤ 322699309) block2 block3

theorem join_1_0 : (twinPrimeSegment 322568237 322699309).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 322568237 ≤ 322633773)
    (by decide : 322633773 ≤ 322699309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 322568237 322699309).card = 441 := join_1_0

end S153C13
end Sude.GeneratedTwinScan
