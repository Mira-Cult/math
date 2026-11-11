import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22633)) 512229421 512262189 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 512229421 512262189).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22633 512229421 512262189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22633)) 512262189 512294957 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 512262189 512294957).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22633 512262189 512294957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22634)) 512294957 512327725 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 512294957 512327725).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22634 512294957 512327725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22635)) 512327725 512360493 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 512327725 512360493).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22635 512327725 512360493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 512229421 512294957).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 512229421 ≤ 512262189)
    (by decide : 512262189 ≤ 512294957) block0 block1

theorem join_0_1 : (twinPrimeSegment 512294957 512360493).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 512294957 ≤ 512327725)
    (by decide : 512327725 ≤ 512360493) block2 block3

theorem join_1_0 : (twinPrimeSegment 512229421 512360493).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 512229421 ≤ 512294957)
    (by decide : 512294957 ≤ 512360493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 512229421 512360493).card = 422 := join_1_0

end S244C04
end Sude.GeneratedTwinScan
