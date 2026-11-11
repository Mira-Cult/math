import Sude.FastTwinAllBands
import Sude.FastTwinScan.B96
import Sude.FastTwinScan.B97
import Sude.FastTwinScan.B98
import Sude.FastTwinScan.B99
import Sude.FastTwinScan.B100
import Sude.FastTwinScan.B101
import Sude.FastTwinScan.B102
import Sude.FastTwinScan.B103
import Sude.FastTwinScan.B104
import Sude.FastTwinScan.B105
import Sude.FastTwinScan.B106
import Sude.FastTwinScan.B107
import Sude.FastTwinScan.B108
import Sude.FastTwinScan.B109
import Sude.FastTwinScan.B110
import Sude.FastTwinScan.B111
import Sude.FastTwinScan.B112
import Sude.FastTwinScan.B113
import Sude.FastTwinScan.B114
import Sude.FastTwinScan.B115
import Sude.FastTwinScan.B116
import Sude.FastTwinScan.B117
import Sude.FastTwinScan.B118
import Sude.FastTwinScan.B119
import Sude.FastTwinScan.B120
import Sude.FastTwinScan.B121
import Sude.FastTwinScan.B122
import Sude.FastTwinScan.B123
import Sude.FastTwinScan.B124
import Sude.FastTwinScan.B125
import Sude.FastTwinScan.B126
import Sude.FastTwinScan.B127

/-! Combine FastTwinAllBands (S000..S383) with B96..B127 (S384..S511) to establish
`finiteTwinSeeds.card = 3650551` across the entire `2^30` twin-prime seed pool. -/
namespace Sude
noncomputable section

set_option autoImplicit false

theorem fastTwinEWJoin_0_0 : (twinPrimeSegment 805306413 822083629).card = 52518 := by
  simpa using combineTwinPrimeSegments (by decide : 805306413 ≤ 813695021) (by decide : 813695021 ≤ 822083629) FastTwinScan.B96.total FastTwinScan.B97.total

theorem fastTwinEWJoin_0_1 : (twinPrimeSegment 822083629 838860845).card = 52603 := by
  simpa using combineTwinPrimeSegments (by decide : 822083629 ≤ 830472237) (by decide : 830472237 ≤ 838860845) FastTwinScan.B98.total FastTwinScan.B99.total

theorem fastTwinEWJoin_0_2 : (twinPrimeSegment 838860845 855638061).card = 52408 := by
  simpa using combineTwinPrimeSegments (by decide : 838860845 ≤ 847249453) (by decide : 847249453 ≤ 855638061) FastTwinScan.B100.total FastTwinScan.B101.total

theorem fastTwinEWJoin_0_3 : (twinPrimeSegment 855638061 872415277).card = 52342 := by
  simpa using combineTwinPrimeSegments (by decide : 855638061 ≤ 864026669) (by decide : 864026669 ≤ 872415277) FastTwinScan.B102.total FastTwinScan.B103.total

theorem fastTwinEWJoin_0_4 : (twinPrimeSegment 872415277 889192493).card = 52270 := by
  simpa using combineTwinPrimeSegments (by decide : 872415277 ≤ 880803885) (by decide : 880803885 ≤ 889192493) FastTwinScan.B104.total FastTwinScan.B105.total

theorem fastTwinEWJoin_0_5 : (twinPrimeSegment 889192493 905969709).card = 52308 := by
  simpa using combineTwinPrimeSegments (by decide : 889192493 ≤ 897581101) (by decide : 897581101 ≤ 905969709) FastTwinScan.B106.total FastTwinScan.B107.total

theorem fastTwinEWJoin_0_6 : (twinPrimeSegment 905969709 922746925).card = 52136 := by
  simpa using combineTwinPrimeSegments (by decide : 905969709 ≤ 914358317) (by decide : 914358317 ≤ 922746925) FastTwinScan.B108.total FastTwinScan.B109.total

theorem fastTwinEWJoin_0_7 : (twinPrimeSegment 922746925 939524141).card = 51993 := by
  simpa using combineTwinPrimeSegments (by decide : 922746925 ≤ 931135533) (by decide : 931135533 ≤ 939524141) FastTwinScan.B110.total FastTwinScan.B111.total

theorem fastTwinEWJoin_0_8 : (twinPrimeSegment 939524141 956301357).card = 52002 := by
  simpa using combineTwinPrimeSegments (by decide : 939524141 ≤ 947912749) (by decide : 947912749 ≤ 956301357) FastTwinScan.B112.total FastTwinScan.B113.total

theorem fastTwinEWJoin_0_9 : (twinPrimeSegment 956301357 973078573).card = 51791 := by
  simpa using combineTwinPrimeSegments (by decide : 956301357 ≤ 964689965) (by decide : 964689965 ≤ 973078573) FastTwinScan.B114.total FastTwinScan.B115.total

theorem fastTwinEWJoin_0_10 : (twinPrimeSegment 973078573 989855789).card = 51539 := by
  simpa using combineTwinPrimeSegments (by decide : 973078573 ≤ 981467181) (by decide : 981467181 ≤ 989855789) FastTwinScan.B116.total FastTwinScan.B117.total

theorem fastTwinEWJoin_0_11 : (twinPrimeSegment 989855789 1006633005).card = 51576 := by
  simpa using combineTwinPrimeSegments (by decide : 989855789 ≤ 998244397) (by decide : 998244397 ≤ 1006633005) FastTwinScan.B118.total FastTwinScan.B119.total

theorem fastTwinEWJoin_0_12 : (twinPrimeSegment 1006633005 1023410221).card = 51623 := by
  simpa using combineTwinPrimeSegments (by decide : 1006633005 ≤ 1015021613) (by decide : 1015021613 ≤ 1023410221) FastTwinScan.B120.total FastTwinScan.B121.total

theorem fastTwinEWJoin_0_13 : (twinPrimeSegment 1023410221 1040187437).card = 51225 := by
  simpa using combineTwinPrimeSegments (by decide : 1023410221 ≤ 1031798829) (by decide : 1031798829 ≤ 1040187437) FastTwinScan.B122.total FastTwinScan.B123.total

theorem fastTwinEWJoin_0_14 : (twinPrimeSegment 1040187437 1056964653).card = 51220 := by
  simpa using combineTwinPrimeSegments (by decide : 1040187437 ≤ 1048576045) (by decide : 1048576045 ≤ 1056964653) FastTwinScan.B124.total FastTwinScan.B125.total

theorem fastTwinEWJoin_0_15 : (twinPrimeSegment 1056964653 1073741823).card = 51622 := by
  simpa using combineTwinPrimeSegments (by decide : 1056964653 ≤ 1065353261) (by decide : 1065353261 ≤ 1073741823) FastTwinScan.B126.total FastTwinScan.B127.total

theorem fastTwinEWJoin_1_0 : (twinPrimeSegment 805306413 838860845).card = 105121 := by
  simpa using combineTwinPrimeSegments (by decide : 805306413 ≤ 822083629) (by decide : 822083629 ≤ 838860845) fastTwinEWJoin_0_0 fastTwinEWJoin_0_1

theorem fastTwinEWJoin_1_1 : (twinPrimeSegment 838860845 872415277).card = 104750 := by
  simpa using combineTwinPrimeSegments (by decide : 838860845 ≤ 855638061) (by decide : 855638061 ≤ 872415277) fastTwinEWJoin_0_2 fastTwinEWJoin_0_3

theorem fastTwinEWJoin_1_2 : (twinPrimeSegment 872415277 905969709).card = 104578 := by
  simpa using combineTwinPrimeSegments (by decide : 872415277 ≤ 889192493) (by decide : 889192493 ≤ 905969709) fastTwinEWJoin_0_4 fastTwinEWJoin_0_5

theorem fastTwinEWJoin_1_3 : (twinPrimeSegment 905969709 939524141).card = 104129 := by
  simpa using combineTwinPrimeSegments (by decide : 905969709 ≤ 922746925) (by decide : 922746925 ≤ 939524141) fastTwinEWJoin_0_6 fastTwinEWJoin_0_7

theorem fastTwinEWJoin_1_4 : (twinPrimeSegment 939524141 973078573).card = 103793 := by
  simpa using combineTwinPrimeSegments (by decide : 939524141 ≤ 956301357) (by decide : 956301357 ≤ 973078573) fastTwinEWJoin_0_8 fastTwinEWJoin_0_9

theorem fastTwinEWJoin_1_5 : (twinPrimeSegment 973078573 1006633005).card = 103115 := by
  simpa using combineTwinPrimeSegments (by decide : 973078573 ≤ 989855789) (by decide : 989855789 ≤ 1006633005) fastTwinEWJoin_0_10 fastTwinEWJoin_0_11

theorem fastTwinEWJoin_1_6 : (twinPrimeSegment 1006633005 1040187437).card = 102848 := by
  simpa using combineTwinPrimeSegments (by decide : 1006633005 ≤ 1023410221) (by decide : 1023410221 ≤ 1040187437) fastTwinEWJoin_0_12 fastTwinEWJoin_0_13

theorem fastTwinEWJoin_1_7 : (twinPrimeSegment 1040187437 1073741823).card = 102842 := by
  simpa using combineTwinPrimeSegments (by decide : 1040187437 ≤ 1056964653) (by decide : 1056964653 ≤ 1073741823) fastTwinEWJoin_0_14 fastTwinEWJoin_0_15

theorem fastTwinEWJoin_2_0 : (twinPrimeSegment 805306413 872415277).card = 209871 := by
  simpa using combineTwinPrimeSegments (by decide : 805306413 ≤ 838860845) (by decide : 838860845 ≤ 872415277) fastTwinEWJoin_1_0 fastTwinEWJoin_1_1

theorem fastTwinEWJoin_2_1 : (twinPrimeSegment 872415277 939524141).card = 208707 := by
  simpa using combineTwinPrimeSegments (by decide : 872415277 ≤ 905969709) (by decide : 905969709 ≤ 939524141) fastTwinEWJoin_1_2 fastTwinEWJoin_1_3

theorem fastTwinEWJoin_2_2 : (twinPrimeSegment 939524141 1006633005).card = 206908 := by
  simpa using combineTwinPrimeSegments (by decide : 939524141 ≤ 973078573) (by decide : 973078573 ≤ 1006633005) fastTwinEWJoin_1_4 fastTwinEWJoin_1_5

theorem fastTwinEWJoin_2_3 : (twinPrimeSegment 1006633005 1073741823).card = 205690 := by
  simpa using combineTwinPrimeSegments (by decide : 1006633005 ≤ 1040187437) (by decide : 1040187437 ≤ 1073741823) fastTwinEWJoin_1_6 fastTwinEWJoin_1_7

theorem fastTwinEWJoin_3_0 : (twinPrimeSegment 805306413 939524141).card = 418578 := by
  simpa using combineTwinPrimeSegments (by decide : 805306413 ≤ 872415277) (by decide : 872415277 ≤ 939524141) fastTwinEWJoin_2_0 fastTwinEWJoin_2_1

theorem fastTwinEWJoin_3_1 : (twinPrimeSegment 939524141 1073741823).card = 412598 := by
  simpa using combineTwinPrimeSegments (by decide : 939524141 ≤ 1006633005) (by decide : 1006633005 ≤ 1073741823) fastTwinEWJoin_2_2 fastTwinEWJoin_2_3

theorem fastTwinEWJoin_4_0 : (twinPrimeSegment 805306413 1073741823).card = 831176 := by
  simpa using combineTwinPrimeSegments (by decide : 805306413 ≤ 939524141) (by decide : 939524141 ≤ 1073741823) fastTwinEWJoin_3_0 fastTwinEWJoin_3_1

/-- The complete 512-segment finite twin-prime seed pool `[45, 2^30 - 1)` has
exact cardinality `3,650,551`. -/
theorem finiteTwinSeeds_card_eq_3650551 : finiteTwinSeeds.card = 3650551 := by
  have h512 : (twinPrimeSegment 45 1073741823).card = 3650551 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 805306413) (by decide : 805306413 ≤ 1073741823) finiteTwinFirst384Segments fastTwinEWJoin_4_0
  simpa [finiteTwinSeeds] using h512

/-- Lower-bound corollary sufficient for the EW seed quota up to `n = 35733`. -/
theorem finiteTwinSeeds_at_least_3650551 : 3650551 ≤ finiteTwinSeeds.card := by
  rw [finiteTwinSeeds_card_eq_3650551]

end
end Sude
