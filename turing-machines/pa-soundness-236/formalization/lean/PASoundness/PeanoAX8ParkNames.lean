import PASoundness.PeanoFreeNamePermutation

/-! Three finite swaps park three distinct names beyond a finite support.
This only establishes their name action; it is not an AX8 proof. -/
namespace PASoundness.PeanoAX8ParkNames
open PeanoFreeNamePermutation

def park (a b c base : Nat) : List (Nat × Nat) :=
  [(a,base), (b,base+1), (c,base+2)]

theorem park_a (a b c base : Nat) (_hab : a ≠ b) (_hac : a ≠ c)
    (_hbc : b ≠ c) (_ha : a < base) (hb : b < base) (hc : c < base) :
    applyName (park a b c base) a = base := by
  have h1 : base ≠ b := by omega
  have h2 : base ≠ c := by omega
  simp [park, applyName, h1, h2]

theorem park_b (a b c base : Nat) (hab : a ≠ b) (_hac : a ≠ c)
    (_hbc : b ≠ c) (_ha : a < base) (hb : b < base) (hc : c < base) :
    applyName (park a b c base) b = base+1 := by
  have h1 : b ≠ a := Ne.symm hab
  have h2 : b ≠ base := by omega
  have h3 : base+1 ≠ c := by omega
  simp [park, applyName, h1, h2, h3]

theorem park_c (a b c base : Nat) (_hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (_ha : a < base) (_hb : b < base) (hc : c < base) :
    applyName (park a b c base) c = base+2 := by
  have h1 : c ≠ a := Ne.symm hac
  have h2 : c ≠ b := Ne.symm hbc
  have h3 : c ≠ base := by omega
  have h4 : c ≠ base+1 := by omega
  simp [park, applyName, h1, h2, h3, h4]

/-- Any other name below the parking base is unchanged. -/
theorem park_other (a b c base n : Nat) (hn : n < base)
    (hna : n ≠ a) (hnb : n ≠ b) (hnc : n ≠ c) :
    applyName (park a b c base) n = n := by
  have h1 : n ≠ base := by omega
  have h2 : n ≠ base+1 := by omega
  have h3 : n ≠ base+2 := by omega
  simp [park, applyName, hna, hnb, hnc, h1, h2, h3]

end PASoundness.PeanoAX8ParkNames

#print axioms PASoundness.PeanoAX8ParkNames.park_other
