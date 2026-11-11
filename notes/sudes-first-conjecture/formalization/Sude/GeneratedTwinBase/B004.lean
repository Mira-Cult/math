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
import Sude.GeneratedFTT.N0012
import Sude.GeneratedFTT.N0014
import Sude.GeneratedFTT.N0015
import Sude.GeneratedFTT.N0016
import Sude.GeneratedFTT.N0017
import Sude.GeneratedFTT.N0018
import Sude.GeneratedFTT.N0021
import Sude.GeneratedFTT.N0024
import Sude.GeneratedFTT.N0027
import Sude.GeneratedFTT.N0028
import Sude.GeneratedFTT.N0030
import Sude.GeneratedFTT.N0032
import Sude.GeneratedFTT.N0035
import Sude.GeneratedTwinBase.B002

/-! Generated FT base block; all prime proofs are kernel checked. -/
namespace Sude.Lucas.Generated
namespace B004
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def values : List ℕ := [1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131]

theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by
  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]
  exact ⟨
    ⟨prime_1627, by decide, by decide⟩,
    ⟨prime_1637, by decide, by decide⟩,
    ⟨prime_1657, by decide, by decide⟩,
    ⟨prime_1663, by decide, by decide⟩,
    ⟨prime_1667, by decide, by decide⟩,
    ⟨prime_1669, by decide, by decide⟩,
    ⟨prime_1693, by decide, by decide⟩,
    ⟨prime_1697, by decide, by decide⟩,
    ⟨prime_1699, by decide, by decide⟩,
    ⟨prime_1709, by decide, by decide⟩,
    ⟨prime_1721, by decide, by decide⟩,
    ⟨prime_1723, by decide, by decide⟩,
    ⟨prime_1733, by decide, by decide⟩,
    ⟨prime_1741, by decide, by decide⟩,
    ⟨prime_1747, by decide, by decide⟩,
    ⟨prime_1753, by decide, by decide⟩,
    ⟨prime_1759, by decide, by decide⟩,
    ⟨prime_1777, by decide, by decide⟩,
    ⟨prime_1783, by decide, by decide⟩,
    ⟨prime_1787, by decide, by decide⟩,
    ⟨prime_1789, by decide, by decide⟩,
    ⟨prime_1801, by decide, by decide⟩,
    ⟨prime_1811, by decide, by decide⟩,
    ⟨prime_1823, by decide, by decide⟩,
    ⟨prime_1831, by decide, by decide⟩,
    ⟨prime_1847, by decide, by decide⟩,
    ⟨prime_1861, by decide, by decide⟩,
    ⟨prime_1867, by decide, by decide⟩,
    ⟨prime_1871, by decide, by decide⟩,
    ⟨prime_1873, by decide, by decide⟩,
    ⟨prime_1877, by decide, by decide⟩,
    ⟨prime_1879, by decide, by decide⟩,
    ⟨prime_1889, by decide, by decide⟩,
    ⟨prime_1901, by decide, by decide⟩,
    ⟨prime_1907, by decide, by decide⟩,
    ⟨prime_1913, by decide, by decide⟩,
    ⟨prime_1931, by decide, by decide⟩,
    ⟨prime_1933, by decide, by decide⟩,
    ⟨prime_1949, by decide, by decide⟩,
    ⟨prime_1951, by decide, by decide⟩,
    ⟨prime_1973, by decide, by decide⟩,
    ⟨prime_1979, by decide, by decide⟩,
    ⟨prime_1987, by decide, by decide⟩,
    ⟨prime_1993, by decide, by decide⟩,
    ⟨prime_1997, by decide, by decide⟩,
    ⟨prime_1999, by decide, by decide⟩,
    ⟨prime_2003, by decide, by decide⟩,
    ⟨prime_2011, by decide, by decide⟩,
    ⟨prime_2017, by decide, by decide⟩,
    ⟨prime_2027, by decide, by decide⟩,
    ⟨prime_2029, by decide, by decide⟩,
    ⟨prime_2039, by decide, by decide⟩,
    ⟨prime_2053, by decide, by decide⟩,
    ⟨prime_2063, by decide, by decide⟩,
    ⟨prime_2069, by decide, by decide⟩,
    ⟨prime_2081, by decide, by decide⟩,
    ⟨prime_2083, by decide, by decide⟩,
    ⟨prime_2087, by decide, by decide⟩,
    ⟨prime_2089, by decide, by decide⟩,
    ⟨prime_2099, by decide, by decide⟩,
    ⟨prime_2111, by decide, by decide⟩,
    ⟨prime_2113, by decide, by decide⟩,
    ⟨prime_2129, by decide, by decide⟩,
    ⟨prime_2131, by decide, by decide⟩
  ⟩

end B004
end Sude.Lucas.Generated
