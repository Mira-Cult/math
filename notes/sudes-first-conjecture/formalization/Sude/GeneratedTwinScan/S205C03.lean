import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20744)) 430309421 430342189 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430309421 430342189).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20744 430309421 430342189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20745)) 430342189 430374957 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430342189 430374957).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20745 430342189 430374957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20746)) 430374957 430407725 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 430374957 430407725).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20746 430374957 430407725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20747)) 430407725 430440493 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430407725 430440493).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20747 430407725 430440493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430309421 430374957).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 430309421 ≤ 430342189)
    (by decide : 430342189 ≤ 430374957) block0 block1

theorem join_0_1 : (twinPrimeSegment 430374957 430440493).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 430374957 ≤ 430407725)
    (by decide : 430407725 ≤ 430440493) block2 block3

theorem join_1_0 : (twinPrimeSegment 430309421 430440493).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 430309421 ≤ 430374957)
    (by decide : 430374957 ≤ 430440493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430309421 430440493).card = 443 := join_1_0

end S205C03
end Sude.GeneratedTwinScan
