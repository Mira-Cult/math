import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14680)) 215482413 215515181 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 215482413 215515181).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14680 215482413 215515181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14681)) 215515181 215547949 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 215515181 215547949).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14681 215515181 215547949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14682)) 215547949 215580717 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 215547949 215580717).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14682 215547949 215580717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14683)) 215580717 215613485 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 215580717 215613485).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14683 215580717 215613485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 215482413 215547949).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 215482413 ≤ 215515181)
    (by decide : 215515181 ≤ 215547949) block0 block1

theorem join_0_1 : (twinPrimeSegment 215547949 215613485).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 215547949 ≤ 215580717)
    (by decide : 215580717 ≤ 215613485) block2 block3

theorem join_1_0 : (twinPrimeSegment 215482413 215613485).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 215482413 ≤ 215547949)
    (by decide : 215547949 ≤ 215613485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 215482413 215613485).card = 461 := join_1_0

end S102C12
end Sude.GeneratedTwinScan
