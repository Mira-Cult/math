import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13872)) 192413741 192446509 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 192413741 192446509).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13872 192413741 192446509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13873)) 192446509 192479277 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 192446509 192479277).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13873 192446509 192479277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13874)) 192479277 192512045 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 192479277 192512045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13874 192479277 192512045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13876)) 192512045 192544813 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 192512045 192544813).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13876 192512045 192544813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 192413741 192479277).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 192413741 ≤ 192446509)
    (by decide : 192446509 ≤ 192479277) block0 block1

theorem join_0_1 : (twinPrimeSegment 192479277 192544813).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 192479277 ≤ 192512045)
    (by decide : 192512045 ≤ 192544813) block2 block3

theorem join_1_0 : (twinPrimeSegment 192413741 192544813).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 192413741 ≤ 192479277)
    (by decide : 192479277 ≤ 192544813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 192413741 192544813).card = 469 := join_1_0

end S091C12
end Sude.GeneratedTwinScan
