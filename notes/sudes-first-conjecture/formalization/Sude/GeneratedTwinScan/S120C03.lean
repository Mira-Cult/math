import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15877)) 252051501 252084269 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 252051501 252084269).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15877 252051501 252084269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15878)) 252084269 252117037 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 252084269 252117037).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15878 252084269 252117037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15879)) 252117037 252149805 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 252117037 252149805).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15879 252117037 252149805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15880)) 252149805 252182573 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 252149805 252182573).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15880 252149805 252182573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 252051501 252117037).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 252051501 ≤ 252084269)
    (by decide : 252084269 ≤ 252117037) block0 block1

theorem join_0_1 : (twinPrimeSegment 252117037 252182573).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 252117037 ≤ 252149805)
    (by decide : 252149805 ≤ 252182573) block2 block3

theorem join_1_0 : (twinPrimeSegment 252051501 252182573).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 252051501 ≤ 252117037)
    (by decide : 252117037 ≤ 252182573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 252051501 252182573).card = 467 := join_1_0

end S120C03
end Sude.GeneratedTwinScan
