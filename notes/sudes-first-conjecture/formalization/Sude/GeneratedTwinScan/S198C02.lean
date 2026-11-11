import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20384)) 415498285 415531053 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 415498285 415531053).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20384 415498285 415531053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20385)) 415531053 415563821 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 415531053 415563821).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20385 415531053 415563821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20386)) 415563821 415596589 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 415563821 415596589).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20386 415563821 415596589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20386)) 415596589 415629357 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 415596589 415629357).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20386 415596589 415629357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 415498285 415563821).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 415498285 ≤ 415531053)
    (by decide : 415531053 ≤ 415563821) block0 block1

theorem join_0_1 : (twinPrimeSegment 415563821 415629357).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 415563821 ≤ 415596589)
    (by decide : 415596589 ≤ 415629357) block2 block3

theorem join_1_0 : (twinPrimeSegment 415498285 415629357).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 415498285 ≤ 415563821)
    (by decide : 415563821 ≤ 415629357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 415498285 415629357).card = 402 := join_1_0

end S198C02
end Sude.GeneratedTwinScan
