import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15382)) 236585005 236617773 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236585005 236617773).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15382 236585005 236617773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15383)) 236617773 236650541 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 236617773 236650541).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15383 236617773 236650541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15384)) 236650541 236683309 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 236650541 236683309).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15384 236650541 236683309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15385)) 236683309 236716077 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236683309 236716077).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15385 236683309 236716077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236585005 236650541).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 236585005 ≤ 236617773)
    (by decide : 236617773 ≤ 236650541) block0 block1

theorem join_0_1 : (twinPrimeSegment 236650541 236716077).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 236650541 ≤ 236683309)
    (by decide : 236683309 ≤ 236716077) block2 block3

theorem join_1_0 : (twinPrimeSegment 236585005 236716077).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 236585005 ≤ 236650541)
    (by decide : 236650541 ≤ 236716077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236585005 236716077).card = 474 := join_1_0

end S112C13
end Sude.GeneratedTwinScan
