import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16199)) 262406189 262438957 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262406189 262438957).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16199 262406189 262438957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16200)) 262438957 262471725 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 262438957 262471725).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16200 262438957 262471725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16201)) 262471725 262504493 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 262471725 262504493).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16201 262471725 262504493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16203)) 262504493 262537261 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 262504493 262537261).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16203 262504493 262537261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 262406189 262471725).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 262406189 ≤ 262438957)
    (by decide : 262438957 ≤ 262471725) block0 block1

theorem join_0_1 : (twinPrimeSegment 262471725 262537261).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 262471725 ≤ 262504493)
    (by decide : 262504493 ≤ 262537261) block2 block3

theorem join_1_0 : (twinPrimeSegment 262406189 262537261).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 262406189 ≤ 262471725)
    (by decide : 262471725 ≤ 262537261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262406189 262537261).card = 456 := join_1_0

end S125C02
end Sude.GeneratedTwinScan
