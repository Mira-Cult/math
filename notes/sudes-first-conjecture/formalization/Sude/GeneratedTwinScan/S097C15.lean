import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14332)) 205389869 205422637 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 205389869 205422637).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14332 205389869 205422637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14333)) 205422637 205455405 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205422637 205455405).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14333 205422637 205455405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14334)) 205455405 205488173 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205455405 205488173).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14334 205455405 205488173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14336)) 205488173 205520941 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 205488173 205520941).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14336 205488173 205520941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 205389869 205455405).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 205389869 ≤ 205422637)
    (by decide : 205422637 ≤ 205455405) block0 block1

theorem join_0_1 : (twinPrimeSegment 205455405 205520941).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 205455405 ≤ 205488173)
    (by decide : 205488173 ≤ 205520941) block2 block3

theorem join_1_0 : (twinPrimeSegment 205389869 205520941).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 205389869 ≤ 205455405)
    (by decide : 205455405 ≤ 205520941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 205389869 205520941).card = 450 := join_1_0

end S097C15
end Sude.GeneratedTwinScan
