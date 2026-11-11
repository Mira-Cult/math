import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21114)) 445775917 445808685 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 445775917 445808685).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21114 445775917 445808685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21114)) 445808685 445841453 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445808685 445841453).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21114 445808685 445841453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21115)) 445841453 445874221 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445841453 445874221).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21115 445841453 445874221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21116)) 445874221 445906989 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 445874221 445906989).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21116 445874221 445906989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 445775917 445841453).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 445775917 ≤ 445808685)
    (by decide : 445808685 ≤ 445841453) block0 block1

theorem join_0_1 : (twinPrimeSegment 445841453 445906989).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 445841453 ≤ 445874221)
    (by decide : 445874221 ≤ 445906989) block2 block3

theorem join_1_0 : (twinPrimeSegment 445775917 445906989).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 445775917 ≤ 445841453)
    (by decide : 445841453 ≤ 445906989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 445775917 445906989).card = 418 := join_1_0

end S212C09
end Sude.GeneratedTwinScan
