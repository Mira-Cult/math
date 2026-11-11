import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20190)) 407633965 407666733 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 407633965 407666733).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20190 407633965 407666733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20191)) 407666733 407699501 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 407666733 407699501).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20191 407666733 407699501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20192)) 407699501 407732269 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 407699501 407732269).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20192 407699501 407732269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20193)) 407732269 407765037 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 407732269 407765037).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20193 407732269 407765037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 407633965 407699501).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 407633965 ≤ 407666733)
    (by decide : 407666733 ≤ 407699501) block0 block1

theorem join_0_1 : (twinPrimeSegment 407699501 407765037).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 407699501 ≤ 407732269)
    (by decide : 407732269 ≤ 407765037) block2 block3

theorem join_1_0 : (twinPrimeSegment 407633965 407765037).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 407633965 ≤ 407699501)
    (by decide : 407699501 ≤ 407765037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 407633965 407765037).card = 456 := join_1_0

end S194C06
end Sude.GeneratedTwinScan
