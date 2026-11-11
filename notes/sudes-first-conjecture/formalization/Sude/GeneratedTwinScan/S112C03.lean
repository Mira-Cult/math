import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15339)) 235274285 235307053 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 235274285 235307053).card = 144 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15339 235274285 235307053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15340)) 235307053 235339821 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 235307053 235339821).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15340 235307053 235339821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15341)) 235339821 235372589 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 235339821 235372589).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15341 235339821 235372589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15342)) 235372589 235405357 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 235372589 235405357).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15342 235372589 235405357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 235274285 235339821).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 235274285 ≤ 235307053)
    (by decide : 235307053 ≤ 235339821) block0 block1

theorem join_0_1 : (twinPrimeSegment 235339821 235405357).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 235339821 ≤ 235372589)
    (by decide : 235372589 ≤ 235405357) block2 block3

theorem join_1_0 : (twinPrimeSegment 235274285 235405357).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 235274285 ≤ 235339821)
    (by decide : 235339821 ≤ 235405357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 235274285 235405357).card = 493 := join_1_0

end S112C03
end Sude.GeneratedTwinScan
