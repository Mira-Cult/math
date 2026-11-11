import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14032)) 196870189 196902957 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 196870189 196902957).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14032 196870189 196902957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14033)) 196902957 196935725 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 196902957 196935725).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14033 196902957 196935725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14034)) 196935725 196968493 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196935725 196968493).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14034 196935725 196968493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14035)) 196968493 197001261 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 196968493 197001261).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14035 196968493 197001261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 196870189 196935725).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 196870189 ≤ 196902957)
    (by decide : 196902957 ≤ 196935725) block0 block1

theorem join_0_1 : (twinPrimeSegment 196935725 197001261).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 196935725 ≤ 196968493)
    (by decide : 196968493 ≤ 197001261) block2 block3

theorem join_1_0 : (twinPrimeSegment 196870189 197001261).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 196870189 ≤ 196935725)
    (by decide : 196935725 ≤ 197001261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 196870189 197001261).card = 456 := join_1_0

end S093C14
end Sude.GeneratedTwinScan
