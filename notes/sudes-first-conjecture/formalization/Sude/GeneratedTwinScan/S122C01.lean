import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16000)) 255983661 256016429 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 255983661 256016429).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16000 255983661 256016429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16001)) 256016429 256049197 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 256016429 256049197).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16001 256016429 256049197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16002)) 256049197 256081965 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 256049197 256081965).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16002 256049197 256081965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16003)) 256081965 256114733 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 256081965 256114733).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16003 256081965 256114733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 255983661 256049197).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 255983661 ≤ 256016429)
    (by decide : 256016429 ≤ 256049197) block0 block1

theorem join_0_1 : (twinPrimeSegment 256049197 256114733).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 256049197 ≤ 256081965)
    (by decide : 256081965 ≤ 256114733) block2 block3

theorem join_1_0 : (twinPrimeSegment 255983661 256114733).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 255983661 ≤ 256049197)
    (by decide : 256049197 ≤ 256114733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 255983661 256114733).card = 448 := join_1_0

end S122C01
end Sude.GeneratedTwinScan
