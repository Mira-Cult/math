import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20102)) 404095021 404127789 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 404095021 404127789).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20102 404095021 404127789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20103)) 404127789 404160557 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 404127789 404160557).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20103 404127789 404160557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20104)) 404160557 404193325 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 404160557 404193325).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20104 404160557 404193325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20105)) 404193325 404226093 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 404193325 404226093).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20105 404193325 404226093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 404095021 404160557).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 404095021 ≤ 404127789)
    (by decide : 404127789 ≤ 404160557) block0 block1

theorem join_0_1 : (twinPrimeSegment 404160557 404226093).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 404160557 ≤ 404193325)
    (by decide : 404193325 ≤ 404226093) block2 block3

theorem join_1_0 : (twinPrimeSegment 404095021 404226093).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 404095021 ≤ 404160557)
    (by decide : 404160557 ≤ 404226093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 404095021 404226093).card = 444 := join_1_0

end S192C11
end Sude.GeneratedTwinScan
