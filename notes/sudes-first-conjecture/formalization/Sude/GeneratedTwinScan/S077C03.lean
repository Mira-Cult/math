import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12724)) 161873965 161906733 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 161873965 161906733).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12724 161873965 161906733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12725)) 161906733 161939501 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 161906733 161939501).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12725 161906733 161939501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12726)) 161939501 161972269 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 161939501 161972269).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12726 161939501 161972269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12728)) 161972269 162005037 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 161972269 162005037).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12728 161972269 162005037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 161873965 161939501).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 161873965 ≤ 161906733)
    (by decide : 161906733 ≤ 161939501) block0 block1

theorem join_0_1 : (twinPrimeSegment 161939501 162005037).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 161939501 ≤ 161972269)
    (by decide : 161972269 ≤ 162005037) block2 block3

theorem join_1_0 : (twinPrimeSegment 161873965 162005037).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 161873965 ≤ 161939501)
    (by decide : 161939501 ≤ 162005037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 161873965 162005037).card = 482 := join_1_0

end S077C03
end Sude.GeneratedTwinScan
