import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20986)) 440401965 440434733 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 440401965 440434733).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20986 440401965 440434733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20987)) 440434733 440467501 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 440434733 440467501).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20987 440434733 440467501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20988)) 440467501 440500269 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 440467501 440500269).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20988 440467501 440500269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20988)) 440500269 440533037 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 440500269 440533037).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20988 440500269 440533037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 440401965 440467501).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 440401965 ≤ 440434733)
    (by decide : 440434733 ≤ 440467501) block0 block1

theorem join_0_1 : (twinPrimeSegment 440467501 440533037).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 440467501 ≤ 440500269)
    (by decide : 440500269 ≤ 440533037) block2 block3

theorem join_1_0 : (twinPrimeSegment 440401965 440533037).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 440401965 ≤ 440467501)
    (by decide : 440467501 ≤ 440533037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 440401965 440533037).card = 456 := join_1_0

end S210C00
end Sude.GeneratedTwinScan
