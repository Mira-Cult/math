import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18055)) 325976109 326008877 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 325976109 326008877).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18055 325976109 326008877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18056)) 326008877 326041645 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 326008877 326041645).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18056 326008877 326041645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18057)) 326041645 326074413 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 326041645 326074413).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18057 326041645 326074413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18058)) 326074413 326107181 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 326074413 326107181).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18058 326074413 326107181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 325976109 326041645).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 325976109 ≤ 326008877)
    (by decide : 326008877 ≤ 326041645) block0 block1

theorem join_0_1 : (twinPrimeSegment 326041645 326107181).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 326041645 ≤ 326074413)
    (by decide : 326074413 ≤ 326107181) block2 block3

theorem join_1_0 : (twinPrimeSegment 325976109 326107181).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 325976109 ≤ 326041645)
    (by decide : 326041645 ≤ 326107181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 325976109 326107181).card = 432 := join_1_0

end S155C07
end Sude.GeneratedTwinScan
