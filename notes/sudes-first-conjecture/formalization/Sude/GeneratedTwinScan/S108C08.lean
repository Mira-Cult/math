import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15085)) 227541037 227573805 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227541037 227573805).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15085 227541037 227573805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15086)) 227573805 227606573 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227573805 227606573).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15086 227573805 227606573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15087)) 227606573 227639341 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227606573 227639341).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15087 227606573 227639341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15088)) 227639341 227672109 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 227639341 227672109).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15088 227639341 227672109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227541037 227606573).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 227541037 ≤ 227573805)
    (by decide : 227573805 ≤ 227606573) block0 block1

theorem join_0_1 : (twinPrimeSegment 227606573 227672109).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 227606573 ≤ 227639341)
    (by decide : 227639341 ≤ 227672109) block2 block3

theorem join_1_0 : (twinPrimeSegment 227541037 227672109).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 227541037 ≤ 227606573)
    (by decide : 227606573 ≤ 227672109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227541037 227672109).card = 412 := join_1_0

end S108C08
end Sude.GeneratedTwinScan
