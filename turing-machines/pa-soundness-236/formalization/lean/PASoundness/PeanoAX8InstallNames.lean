import PASoundness.PeanoFreeNamePermutation

/-! Three final swaps install parked names at the AX8 canonical names. -/
namespace PASoundness.PeanoAX8InstallNames
open PeanoFreeNamePermutation

def install (base : Nat) : List (Nat × Nat) :=
  [(base,4), (base+1,5), (base+2,3)]

/-- A fresh base allows the three parked names to be installed without
interference. -/
theorem install_first (base : Nat) (hb : 6 < base) :
    applyName (install base) base = 4 := by
  have h2 : base ≠ 2 := by omega
  have h3 : base ≠ 3 := by omega
  simp [install, applyName, h2, h3]

theorem install_second (base : Nat) (hb : 6 < base) :
    applyName (install base) (base+1) = 5 := by
  have h3 : base ≠ 3 := by omega
  simp [install, applyName, h3]

theorem install_third (base : Nat) (hb : 6 < base) :
    applyName (install base) (base+2) = 3 := by
  have h2 : base ≠ 2 := by omega
  have h3 : base ≠ 3 := by omega
  simp [install, applyName, h2, h3]

/-- Every name at least 6 outside the parked positions is unchanged. -/
theorem install_other (base n : Nat) (_hb : 6 < base) (hn : 6 ≤ n)
    (h0 : n ≠ base) (h1 : n ≠ base+1) (h2 : n ≠ base+2) :
    applyName (install base) n = n := by
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  have h5 : n ≠ 5 := by omega
  simp [install, applyName, h0, h1, h2, h3, h4, h5]

end PASoundness.PeanoAX8InstallNames

#print axioms PASoundness.PeanoAX8InstallNames.install_other
