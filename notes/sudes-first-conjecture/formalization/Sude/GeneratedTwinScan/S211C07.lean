import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21058)) 443416621 443449389 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 443416621 443449389).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21058 443416621 443449389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21059)) 443449389 443482157 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 443449389 443482157).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21059 443449389 443482157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21059)) 443482157 443514925 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 443482157 443514925).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21059 443482157 443514925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21060)) 443514925 443547693 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 443514925 443547693).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21060 443514925 443547693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 443416621 443482157).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 443416621 ≤ 443449389)
    (by decide : 443449389 ≤ 443482157) block0 block1

theorem join_0_1 : (twinPrimeSegment 443482157 443547693).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 443482157 ≤ 443514925)
    (by decide : 443514925 ≤ 443547693) block2 block3

theorem join_1_0 : (twinPrimeSegment 443416621 443547693).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 443416621 ≤ 443482157)
    (by decide : 443482157 ≤ 443547693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 443416621 443547693).card = 458 := join_1_0

end S211C07
end Sude.GeneratedTwinScan
