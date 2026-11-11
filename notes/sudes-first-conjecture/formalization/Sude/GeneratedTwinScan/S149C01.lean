import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17681)) 312606765 312639533 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312606765 312639533).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17681 312606765 312639533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17682)) 312639533 312672301 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 312639533 312672301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17682 312639533 312672301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17683)) 312672301 312705069 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312672301 312705069).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17683 312672301 312705069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17684)) 312705069 312737837 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312705069 312737837).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17684 312705069 312737837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312606765 312672301).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 312606765 ≤ 312639533)
    (by decide : 312639533 ≤ 312672301) block0 block1

theorem join_0_1 : (twinPrimeSegment 312672301 312737837).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 312672301 ≤ 312705069)
    (by decide : 312705069 ≤ 312737837) block2 block3

theorem join_1_0 : (twinPrimeSegment 312606765 312737837).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 312606765 ≤ 312672301)
    (by decide : 312672301 ≤ 312737837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312606765 312737837).card = 455 := join_1_0

end S149C01
end Sude.GeneratedTwinScan
