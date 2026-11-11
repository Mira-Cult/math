import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13139)) 172621869 172654637 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 172621869 172654637).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13139 172621869 172654637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13141)) 172654637 172687405 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 172654637 172687405).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13141 172654637 172687405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13142)) 172687405 172720173 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172687405 172720173).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13142 172687405 172720173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13143)) 172720173 172752941 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172720173 172752941).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13143 172720173 172752941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 172621869 172687405).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 172621869 ≤ 172654637)
    (by decide : 172654637 ≤ 172687405) block0 block1

theorem join_0_1 : (twinPrimeSegment 172687405 172752941).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 172687405 ≤ 172720173)
    (by decide : 172720173 ≤ 172752941) block2 block3

theorem join_1_0 : (twinPrimeSegment 172621869 172752941).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 172621869 ≤ 172687405)
    (by decide : 172687405 ≤ 172752941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 172621869 172752941).card = 475 := join_1_0

end S082C05
end Sude.GeneratedTwinScan
