import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18644)) 347602989 347635757 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 347602989 347635757).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18644 347602989 347635757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18645)) 347635757 347668525 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 347635757 347668525).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18645 347635757 347668525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18646)) 347668525 347701293 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 347668525 347701293).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18646 347668525 347701293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18647)) 347701293 347734061 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 347701293 347734061).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18647 347701293 347734061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 347602989 347668525).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 347602989 ≤ 347635757)
    (by decide : 347635757 ≤ 347668525) block0 block1

theorem join_0_1 : (twinPrimeSegment 347668525 347734061).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 347668525 ≤ 347701293)
    (by decide : 347701293 ≤ 347734061) block2 block3

theorem join_1_0 : (twinPrimeSegment 347602989 347734061).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 347602989 ≤ 347668525)
    (by decide : 347668525 ≤ 347734061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 347602989 347734061).card = 443 := join_1_0

end S165C12
end Sude.GeneratedTwinScan
