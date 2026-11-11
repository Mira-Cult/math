import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18606)) 346161197 346193965 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346161197 346193965).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18606 346161197 346193965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18607)) 346193965 346226733 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346193965 346226733).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18607 346193965 346226733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18608)) 346226733 346259501 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 346226733 346259501).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18608 346226733 346259501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18608)) 346259501 346292269 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 346259501 346292269).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18608 346259501 346292269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346161197 346226733).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 346161197 ≤ 346193965)
    (by decide : 346193965 ≤ 346226733) block0 block1

theorem join_0_1 : (twinPrimeSegment 346226733 346292269).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 346226733 ≤ 346259501)
    (by decide : 346259501 ≤ 346292269) block2 block3

theorem join_1_0 : (twinPrimeSegment 346161197 346292269).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 346161197 ≤ 346226733)
    (by decide : 346226733 ≤ 346292269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346161197 346292269).card = 440 := join_1_0

end S165C01
end Sude.GeneratedTwinScan
