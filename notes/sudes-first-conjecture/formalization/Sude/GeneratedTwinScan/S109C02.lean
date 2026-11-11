import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15128)) 228851757 228884525 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 228851757 228884525).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15128 228851757 228884525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15130)) 228884525 228917293 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 228884525 228917293).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15130 228884525 228917293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15131)) 228917293 228950061 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 228917293 228950061).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15131 228917293 228950061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15132)) 228950061 228982829 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 228950061 228982829).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15132 228950061 228982829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 228851757 228917293).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 228851757 ≤ 228884525)
    (by decide : 228884525 ≤ 228917293) block0 block1

theorem join_0_1 : (twinPrimeSegment 228917293 228982829).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 228917293 ≤ 228950061)
    (by decide : 228950061 ≤ 228982829) block2 block3

theorem join_1_0 : (twinPrimeSegment 228851757 228982829).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 228851757 ≤ 228917293)
    (by decide : 228917293 ≤ 228982829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 228851757 228982829).card = 443 := join_1_0

end S109C02
end Sude.GeneratedTwinScan
