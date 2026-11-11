import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17499)) 306184237 306217005 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306184237 306217005).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17499 306184237 306217005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17499)) 306217005 306249773 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 306217005 306249773).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17499 306217005 306249773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17500)) 306249773 306282541 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 306249773 306282541).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17500 306249773 306282541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17501)) 306282541 306315309 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306282541 306315309).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17501 306282541 306315309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306184237 306249773).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 306184237 ≤ 306217005)
    (by decide : 306217005 ≤ 306249773) block0 block1

theorem join_0_1 : (twinPrimeSegment 306249773 306315309).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 306249773 ≤ 306282541)
    (by decide : 306282541 ≤ 306315309) block2 block3

theorem join_1_0 : (twinPrimeSegment 306184237 306315309).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 306184237 ≤ 306249773)
    (by decide : 306249773 ≤ 306315309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306184237 306315309).card = 453 := join_1_0

end S146C00
end Sude.GeneratedTwinScan
