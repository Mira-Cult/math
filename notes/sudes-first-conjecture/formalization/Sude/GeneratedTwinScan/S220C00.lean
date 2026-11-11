import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21480)) 461373485 461406253 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 461373485 461406253).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21480 461373485 461406253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21481)) 461406253 461439021 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 461406253 461439021).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21481 461406253 461439021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21481)) 461439021 461471789 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 461439021 461471789).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21481 461439021 461471789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21482)) 461471789 461504557 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 461471789 461504557).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21482 461471789 461504557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 461373485 461439021).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 461406253)
    (by decide : 461406253 ≤ 461439021) block0 block1

theorem join_0_1 : (twinPrimeSegment 461439021 461504557).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 461439021 ≤ 461471789)
    (by decide : 461471789 ≤ 461504557) block2 block3

theorem join_1_0 : (twinPrimeSegment 461373485 461504557).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 461439021)
    (by decide : 461439021 ≤ 461504557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 461373485 461504557).card = 417 := join_1_0

end S220C00
end Sude.GeneratedTwinScan
