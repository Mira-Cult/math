import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14671)) 215220269 215253037 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 215220269 215253037).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14671 215220269 215253037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14672)) 215253037 215285805 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 215253037 215285805).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14672 215253037 215285805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14673)) 215285805 215318573 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 215285805 215318573).card = 144 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14673 215285805 215318573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14674)) 215318573 215351341 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 215318573 215351341).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14674 215318573 215351341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 215220269 215285805).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 215220269 ≤ 215253037)
    (by decide : 215253037 ≤ 215285805) block0 block1

theorem join_0_1 : (twinPrimeSegment 215285805 215351341).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 215285805 ≤ 215318573)
    (by decide : 215318573 ≤ 215351341) block2 block3

theorem join_1_0 : (twinPrimeSegment 215220269 215351341).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 215220269 ≤ 215285805)
    (by decide : 215285805 ≤ 215351341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 215220269 215351341).card = 509 := join_1_0

end S102C10
end Sude.GeneratedTwinScan
