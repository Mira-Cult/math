import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20920)) 437649453 437682221 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 437649453 437682221).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20920 437649453 437682221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20921)) 437682221 437714989 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437682221 437714989).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20921 437682221 437714989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20922)) 437714989 437747757 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437714989 437747757).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20922 437714989 437747757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20923)) 437747757 437780525 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 437747757 437780525).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20923 437747757 437780525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 437649453 437714989).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 437649453 ≤ 437682221)
    (by decide : 437682221 ≤ 437714989) block0 block1

theorem join_0_1 : (twinPrimeSegment 437714989 437780525).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 437714989 ≤ 437747757)
    (by decide : 437747757 ≤ 437780525) block2 block3

theorem join_1_0 : (twinPrimeSegment 437649453 437780525).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 437649453 ≤ 437714989)
    (by decide : 437714989 ≤ 437780525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 437649453 437780525).card = 494 := join_1_0

end S208C11
end Sude.GeneratedTwinScan
