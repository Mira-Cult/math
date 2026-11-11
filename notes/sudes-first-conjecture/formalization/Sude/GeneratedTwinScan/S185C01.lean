import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19701)) 388104237 388137005 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 388104237 388137005).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19701 388104237 388137005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19702)) 388137005 388169773 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 388137005 388169773).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19702 388137005 388169773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19702)) 388169773 388202541 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 388169773 388202541).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19702 388169773 388202541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19703)) 388202541 388235309 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 388202541 388235309).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19703 388202541 388235309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 388104237 388169773).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 388104237 ≤ 388137005)
    (by decide : 388137005 ≤ 388169773) block0 block1

theorem join_0_1 : (twinPrimeSegment 388169773 388235309).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 388169773 ≤ 388202541)
    (by decide : 388202541 ≤ 388235309) block2 block3

theorem join_1_0 : (twinPrimeSegment 388104237 388235309).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 388104237 ≤ 388169773)
    (by decide : 388169773 ≤ 388235309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 388104237 388235309).card = 424 := join_1_0

end S185C01
end Sude.GeneratedTwinScan
