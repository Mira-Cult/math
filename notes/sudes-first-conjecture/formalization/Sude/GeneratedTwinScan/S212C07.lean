import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21107)) 445513773 445546541 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 445513773 445546541).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21107 445513773 445546541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21108)) 445546541 445579309 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445546541 445579309).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21108 445546541 445579309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21109)) 445579309 445612077 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445579309 445612077).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21109 445579309 445612077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21110)) 445612077 445644845 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 445612077 445644845).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21110 445612077 445644845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 445513773 445579309).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 445513773 ≤ 445546541)
    (by decide : 445546541 ≤ 445579309) block0 block1

theorem join_0_1 : (twinPrimeSegment 445579309 445644845).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 445579309 ≤ 445612077)
    (by decide : 445612077 ≤ 445644845) block2 block3

theorem join_1_0 : (twinPrimeSegment 445513773 445644845).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 445513773 ≤ 445579309)
    (by decide : 445579309 ≤ 445644845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 445513773 445644845).card = 426 := join_1_0

end S212C07
end Sude.GeneratedTwinScan
