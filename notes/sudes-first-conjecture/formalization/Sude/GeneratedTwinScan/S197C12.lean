import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20365)) 414711853 414744621 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 414711853 414744621).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20365 414711853 414744621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20366)) 414744621 414777389 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 414744621 414777389).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20366 414744621 414777389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20366)) 414777389 414810157 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 414777389 414810157).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20366 414777389 414810157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20367)) 414810157 414842925 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 414810157 414842925).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20367 414810157 414842925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 414711853 414777389).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 414711853 ≤ 414744621)
    (by decide : 414744621 ≤ 414777389) block0 block1

theorem join_0_1 : (twinPrimeSegment 414777389 414842925).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 414777389 ≤ 414810157)
    (by decide : 414810157 ≤ 414842925) block2 block3

theorem join_1_0 : (twinPrimeSegment 414711853 414842925).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 414711853 ≤ 414777389)
    (by decide : 414777389 ≤ 414842925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 414711853 414842925).card = 443 := join_1_0

end S197C12
end Sude.GeneratedTwinScan
