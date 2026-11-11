import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21342)) 455475245 455508013 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 455475245 455508013).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21342 455475245 455508013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21343)) 455508013 455540781 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 455508013 455540781).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21343 455508013 455540781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21344)) 455540781 455573549 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 455540781 455573549).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21344 455540781 455573549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21344)) 455573549 455606317 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 455573549 455606317).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21344 455573549 455606317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 455475245 455540781).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 455475245 ≤ 455508013)
    (by decide : 455508013 ≤ 455540781) block0 block1

theorem join_0_1 : (twinPrimeSegment 455540781 455606317).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 455540781 ≤ 455573549)
    (by decide : 455573549 ≤ 455606317) block2 block3

theorem join_1_0 : (twinPrimeSegment 455475245 455606317).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 455475245 ≤ 455540781)
    (by decide : 455540781 ≤ 455606317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 455475245 455606317).card = 414 := join_1_0

end S217C03
end Sude.GeneratedTwinScan
