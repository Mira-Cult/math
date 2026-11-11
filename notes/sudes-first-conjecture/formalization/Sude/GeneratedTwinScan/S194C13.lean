import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20213)) 408551469 408584237 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408551469 408584237).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20213 408551469 408584237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20214)) 408584237 408617005 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408584237 408617005).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20214 408584237 408617005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20215)) 408617005 408649773 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 408617005 408649773).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20215 408617005 408649773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20215)) 408649773 408682541 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 408649773 408682541).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20215 408649773 408682541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408551469 408617005).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 408551469 ≤ 408584237)
    (by decide : 408584237 ≤ 408617005) block0 block1

theorem join_0_1 : (twinPrimeSegment 408617005 408682541).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 408617005 ≤ 408649773)
    (by decide : 408649773 ≤ 408682541) block2 block3

theorem join_1_0 : (twinPrimeSegment 408551469 408682541).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 408551469 ≤ 408617005)
    (by decide : 408617005 ≤ 408682541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408551469 408682541).card = 444 := join_1_0

end S194C13
end Sude.GeneratedTwinScan
