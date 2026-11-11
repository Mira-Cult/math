import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18743)) 351273005 351305773 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 351273005 351305773).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18743 351273005 351305773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18744)) 351305773 351338541 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 351305773 351338541).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18744 351305773 351338541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18744)) 351338541 351371309 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 351338541 351371309).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18744 351338541 351371309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18745)) 351371309 351404077 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 351371309 351404077).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18745 351371309 351404077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 351273005 351338541).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 351273005 ≤ 351305773)
    (by decide : 351305773 ≤ 351338541) block0 block1

theorem join_0_1 : (twinPrimeSegment 351338541 351404077).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 351338541 ≤ 351371309)
    (by decide : 351371309 ≤ 351404077) block2 block3

theorem join_1_0 : (twinPrimeSegment 351273005 351404077).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 351273005 ≤ 351338541)
    (by decide : 351338541 ≤ 351404077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 351273005 351404077).card = 433 := join_1_0

end S167C08
end Sude.GeneratedTwinScan
