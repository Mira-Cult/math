import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17442)) 304218157 304250925 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 304218157 304250925).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17442 304218157 304250925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17443)) 304250925 304283693 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 304250925 304283693).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17443 304250925 304283693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17444)) 304283693 304316461 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 304283693 304316461).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17444 304283693 304316461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17445)) 304316461 304349229 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 304316461 304349229).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17445 304316461 304349229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 304218157 304283693).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 304218157 ≤ 304250925)
    (by decide : 304250925 ≤ 304283693) block0 block1

theorem join_0_1 : (twinPrimeSegment 304283693 304349229).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 304283693 ≤ 304316461)
    (by decide : 304316461 ≤ 304349229) block2 block3

theorem join_1_0 : (twinPrimeSegment 304218157 304349229).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 304218157 ≤ 304283693)
    (by decide : 304283693 ≤ 304349229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 304218157 304349229).card = 470 := join_1_0

end S145C01
end Sude.GeneratedTwinScan
