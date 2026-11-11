import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16752)) 280625197 280657965 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 280625197 280657965).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16752 280625197 280657965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16753)) 280657965 280690733 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280657965 280690733).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16753 280657965 280690733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16754)) 280690733 280723501 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280690733 280723501).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16754 280690733 280723501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16755)) 280723501 280756269 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280723501 280756269).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16755 280723501 280756269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 280625197 280690733).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 280625197 ≤ 280657965)
    (by decide : 280657965 ≤ 280690733) block0 block1

theorem join_0_1 : (twinPrimeSegment 280690733 280756269).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 280690733 ≤ 280723501)
    (by decide : 280723501 ≤ 280756269) block2 block3

theorem join_1_0 : (twinPrimeSegment 280625197 280756269).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 280625197 ≤ 280690733)
    (by decide : 280690733 ≤ 280756269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 280625197 280756269).card = 456 := join_1_0

end S133C13
end Sude.GeneratedTwinScan
