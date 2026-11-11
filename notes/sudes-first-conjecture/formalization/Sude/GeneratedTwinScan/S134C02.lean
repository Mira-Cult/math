import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16772)) 281280557 281313325 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 281280557 281313325).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16772 281280557 281313325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16773)) 281313325 281346093 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 281313325 281346093).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16773 281313325 281346093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16774)) 281346093 281378861 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 281346093 281378861).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16774 281346093 281378861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16775)) 281378861 281411629 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 281378861 281411629).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16775 281378861 281411629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 281280557 281346093).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 281280557 ≤ 281313325)
    (by decide : 281313325 ≤ 281346093) block0 block1

theorem join_0_1 : (twinPrimeSegment 281346093 281411629).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 281346093 ≤ 281378861)
    (by decide : 281378861 ≤ 281411629) block2 block3

theorem join_1_0 : (twinPrimeSegment 281280557 281411629).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 281280557 ≤ 281346093)
    (by decide : 281346093 ≤ 281411629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 281280557 281411629).card = 449 := join_1_0

end S134C02
end Sude.GeneratedTwinScan
