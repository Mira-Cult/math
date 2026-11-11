import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17718)) 313917485 313950253 = 89 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 313917485 313950253).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17718 313917485 313950253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17719)) 313950253 313983021 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 313950253 313983021).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17719 313950253 313983021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17720)) 313983021 314015789 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 313983021 314015789).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17720 313983021 314015789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17721)) 314015789 314048557 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314015789 314048557).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17721 314015789 314048557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 313917485 313983021).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 313917485 ≤ 313950253)
    (by decide : 313950253 ≤ 313983021) block0 block1

theorem join_0_1 : (twinPrimeSegment 313983021 314048557).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 313983021 ≤ 314015789)
    (by decide : 314015789 ≤ 314048557) block2 block3

theorem join_1_0 : (twinPrimeSegment 313917485 314048557).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 313917485 ≤ 313983021)
    (by decide : 313983021 ≤ 314048557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 313917485 314048557).card = 420 := join_1_0

end S149C11
end Sude.GeneratedTwinScan
