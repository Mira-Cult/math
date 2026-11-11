import Sude.GeneratedFTT.N0000
import Sude.GeneratedFTT.N0002
import Sude.GeneratedFTT.N0003
import Sude.GeneratedFTT.N0004
import Sude.GeneratedFTT.N0005
import Sude.GeneratedFTT.N0006
import Sude.GeneratedFTT.N0007
import Sude.GeneratedFTT.N0008
import Sude.GeneratedFTT.N0009
import Sude.GeneratedFTT.N0010
import Sude.GeneratedFTT.N0011
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0013
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0028
import Sude.GeneratedTwinBase.B001

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B003
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_1181, by decide, by decide⟩,
    ⟨prime_1187, by decide, by decide⟩,
    ⟨prime_1193, by decide, by decide⟩,
    ⟨prime_1201, by decide, by decide⟩,
    ⟨prime_1213, by decide, by decide⟩,
    ⟨prime_1217, by decide, by decide⟩,
    ⟨prime_1223, by decide, by decide⟩,
    ⟨prime_1229, by decide, by decide⟩,
    ⟨prime_1231, by decide, by decide⟩,
    ⟨prime_1237, by decide, by decide⟩,
    ⟨prime_1249, by decide, by decide⟩,
    ⟨prime_1259, by decide, by decide⟩,
    ⟨prime_1277, by decide, by decide⟩,
    ⟨prime_1279, by decide, by decide⟩,
    ⟨prime_1283, by decide, by decide⟩,
    ⟨prime_1289, by decide, by decide⟩,
    ⟨prime_1291, by decide, by decide⟩,
    ⟨prime_1297, by decide, by decide⟩,
    ⟨prime_1301, by decide, by decide⟩,
    ⟨prime_1303, by decide, by decide⟩,
    ⟨prime_1307, by decide, by decide⟩,
    ⟨prime_1319, by decide, by decide⟩,
    ⟨prime_1321, by decide, by decide⟩,
    ⟨prime_1327, by decide, by decide⟩,
    ⟨prime_1361, by decide, by decide⟩,
    ⟨prime_1367, by decide, by decide⟩,
    ⟨prime_1373, by decide, by decide⟩,
    ⟨prime_1381, by decide, by decide⟩,
    ⟨prime_1399, by decide, by decide⟩,
    ⟨prime_1409, by decide, by decide⟩,
    ⟨prime_1423, by decide, by decide⟩,
    ⟨prime_1427, by decide, by decide⟩,
    ⟨prime_1429, by decide, by decide⟩,
    ⟨prime_1433, by decide, by decide⟩,
    ⟨prime_1439, by decide, by decide⟩,
    ⟨prime_1447, by decide, by decide⟩,
    ⟨prime_1451, by decide, by decide⟩,
    ⟨prime_1453, by decide, by decide⟩,
    ⟨prime_1459, by decide, by decide⟩,
    ⟨prime_1471, by decide, by decide⟩,
    ⟨prime_1481, by decide, by decide⟩,
    ⟨prime_1483, by decide, by decide⟩,
    ⟨prime_1487, by decide, by decide⟩,
    ⟨prime_1489, by decide, by decide⟩,
    ⟨prime_1493, by decide, by decide⟩,
    ⟨prime_1499, by decide, by decide⟩,
    ⟨prime_1511, by decide, by decide⟩,
    ⟨prime_1523, by decide, by decide⟩,
    ⟨prime_1531, by decide, by decide⟩,
    ⟨prime_1543, by decide, by decide⟩,
    ⟨prime_1549, by decide, by decide⟩,
    ⟨prime_1553, by decide, by decide⟩,
    ⟨prime_1559, by decide, by decide⟩,
    ⟨prime_1567, by decide, by decide⟩,
    ⟨prime_1571, by decide, by decide⟩,
    ⟨prime_1579, by decide, by decide⟩,
    ⟨prime_1583, by decide, by decide⟩,
    ⟨prime_1597, by decide, by decide⟩,
    ⟨prime_1601, by decide, by decide⟩,
    ⟨prime_1607, by decide, by decide⟩,
    ⟨prime_1609, by decide, by decide⟩,
    ⟨prime_1613, by decide, by decide⟩,
    ⟨prime_1619, by decide, by decide⟩,
    ⟨prime_1621, by decide, by decide⟩
  ⟩

end B003
end Sude.Lucas.Generated
