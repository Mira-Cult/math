import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19677)) 387186733 387219501 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 387186733 387219501).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19677 387186733 387219501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19678)) 387219501 387252269 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 387219501 387252269).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19678 387219501 387252269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19679)) 387252269 387285037 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 387252269 387285037).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19679 387252269 387285037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19680)) 387285037 387317805 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 387285037 387317805).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19680 387285037 387317805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 387186733 387252269).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 387186733 ≤ 387219501)
    (by decide : 387219501 ≤ 387252269) block0 block1

theorem join_0_1 : (twinPrimeSegment 387252269 387317805).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 387252269 ≤ 387285037)
    (by decide : 387285037 ≤ 387317805) block2 block3

theorem join_1_0 : (twinPrimeSegment 387186733 387317805).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 387186733 ≤ 387252269)
    (by decide : 387252269 ≤ 387317805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 387186733 387317805).card = 445 := join_1_0

end S184C10
end Sude.GeneratedTwinScan
