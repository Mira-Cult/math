import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20304)) 412221485 412254253 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 412221485 412254253).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20304 412221485 412254253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20304)) 412254253 412287021 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 412254253 412287021).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20304 412254253 412287021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20305)) 412287021 412319789 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 412287021 412319789).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20305 412287021 412319789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20306)) 412319789 412352557 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 412319789 412352557).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20306 412319789 412352557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 412221485 412287021).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 412221485 ≤ 412254253)
    (by decide : 412254253 ≤ 412287021) block0 block1

theorem join_0_1 : (twinPrimeSegment 412287021 412352557).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 412287021 ≤ 412319789)
    (by decide : 412319789 ≤ 412352557) block2 block3

theorem join_1_0 : (twinPrimeSegment 412221485 412352557).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 412221485 ≤ 412287021)
    (by decide : 412287021 ≤ 412352557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 412221485 412352557).card = 438 := join_1_0

end S196C09
end Sude.GeneratedTwinScan
