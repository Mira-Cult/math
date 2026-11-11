import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20992)) 440664109 440696877 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 440664109 440696877).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20992 440664109 440696877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20993)) 440696877 440729645 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 440696877 440729645).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20993 440696877 440729645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20994)) 440729645 440762413 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 440729645 440762413).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20994 440729645 440762413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20995)) 440762413 440795181 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 440762413 440795181).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20995 440762413 440795181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 440664109 440729645).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 440664109 ≤ 440696877)
    (by decide : 440696877 ≤ 440729645) block0 block1

theorem join_0_1 : (twinPrimeSegment 440729645 440795181).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 440729645 ≤ 440762413)
    (by decide : 440762413 ≤ 440795181) block2 block3

theorem join_1_0 : (twinPrimeSegment 440664109 440795181).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 440664109 ≤ 440729645)
    (by decide : 440729645 ≤ 440795181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 440664109 440795181).card = 426 := join_1_0

end S210C02
end Sude.GeneratedTwinScan
