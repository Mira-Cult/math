import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14111)) 199098413 199131181 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 199098413 199131181).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14111 199098413 199131181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14112)) 199131181 199163949 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 199131181 199163949).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14112 199131181 199163949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14113)) 199163949 199196717 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 199163949 199196717).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14113 199163949 199196717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14114)) 199196717 199229485 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 199196717 199229485).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14114 199196717 199229485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 199098413 199163949).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 199098413 ≤ 199131181)
    (by decide : 199131181 ≤ 199163949) block0 block1

theorem join_0_1 : (twinPrimeSegment 199163949 199229485).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 199163949 ≤ 199196717)
    (by decide : 199196717 ≤ 199229485) block2 block3

theorem join_1_0 : (twinPrimeSegment 199098413 199229485).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 199098413 ≤ 199163949)
    (by decide : 199163949 ≤ 199229485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 199098413 199229485).card = 475 := join_1_0

end S094C15
end Sude.GeneratedTwinScan
