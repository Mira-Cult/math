import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22034)) 485490733 485523501 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 485490733 485523501).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22034 485490733 485523501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22035)) 485523501 485556269 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 485523501 485556269).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22035 485523501 485556269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22036)) 485556269 485589037 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485556269 485589037).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22036 485556269 485589037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22036)) 485589037 485621805 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485589037 485621805).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22036 485589037 485621805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 485490733 485556269).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 485490733 ≤ 485523501)
    (by decide : 485523501 ≤ 485556269) block0 block1

theorem join_0_1 : (twinPrimeSegment 485556269 485621805).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 485556269 ≤ 485589037)
    (by decide : 485589037 ≤ 485621805) block2 block3

theorem join_1_0 : (twinPrimeSegment 485490733 485621805).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 485490733 ≤ 485556269)
    (by decide : 485556269 ≤ 485621805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 485490733 485621805).card = 430 := join_1_0

end S231C08
end Sude.GeneratedTwinScan
