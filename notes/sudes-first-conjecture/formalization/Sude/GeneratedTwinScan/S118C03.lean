import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15744)) 247857197 247889965 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 247857197 247889965).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15744 247857197 247889965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15745)) 247889965 247922733 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 247889965 247922733).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15745 247889965 247922733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15746)) 247922733 247955501 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 247922733 247955501).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15746 247922733 247955501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15747)) 247955501 247988269 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 247955501 247988269).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15747 247955501 247988269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 247857197 247922733).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 247857197 ≤ 247889965)
    (by decide : 247889965 ≤ 247922733) block0 block1

theorem join_0_1 : (twinPrimeSegment 247922733 247988269).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 247922733 ≤ 247955501)
    (by decide : 247955501 ≤ 247988269) block2 block3

theorem join_1_0 : (twinPrimeSegment 247857197 247988269).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 247857197 ≤ 247922733)
    (by decide : 247922733 ≤ 247988269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 247857197 247988269).card = 491 := join_1_0

end S118C03
end Sude.GeneratedTwinScan
