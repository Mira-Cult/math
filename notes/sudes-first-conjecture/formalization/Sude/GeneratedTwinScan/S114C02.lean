import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15471)) 239337517 239370285 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239337517 239370285).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15471 239337517 239370285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15472)) 239370285 239403053 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 239370285 239403053).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15472 239370285 239403053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15473)) 239403053 239435821 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239403053 239435821).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15473 239403053 239435821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15474)) 239435821 239468589 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239435821 239468589).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15474 239435821 239468589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239337517 239403053).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 239337517 ≤ 239370285)
    (by decide : 239370285 ≤ 239403053) block0 block1

theorem join_0_1 : (twinPrimeSegment 239403053 239468589).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 239403053 ≤ 239435821)
    (by decide : 239435821 ≤ 239468589) block2 block3

theorem join_1_0 : (twinPrimeSegment 239337517 239468589).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 239337517 ≤ 239403053)
    (by decide : 239403053 ≤ 239468589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239337517 239468589).card = 508 := join_1_0

end S114C02
end Sude.GeneratedTwinScan
