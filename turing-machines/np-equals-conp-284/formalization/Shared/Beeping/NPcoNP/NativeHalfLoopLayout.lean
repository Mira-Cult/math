import Shared.Beeping.NPcoNP.NativeHalfRegularCycle

namespace Shared.Beeping.NPcoNP.NativeHalfLoopLayout
open UnarySuffixShift NativeHalfCycleTape NativeHalfSweep

lemma bitAt_cons (b : Bool) (xs : List Bool) (n : Nat) :
    bitAt (b :: xs) n = if n = 0 then b else bitAt xs (n-1) := by
  cases n <;> simp [bitAt]

lemma bitAt_append_reserve (xs : List Bool) (n : Nat) :
    bitAt (xs ++ [true, false]) n =
      if n < xs.length then bitAt xs n else if n = xs.length then true else false := by
  simp only [bitAt]
  by_cases h : n < xs.length
  · simp [h, List.getElem?_append_left]
  · have he : xs.length ≤ n := by omega
    simp only [h, if_false, List.getElem?_append_right he]
    by_cases hn : n = xs.length
    · subst n; simp
    · have h' : 0 < n - xs.length := by omega
      cases hd : n - xs.length with
      | zero => omega
      | succ k => cases k <;> simp_all

lemma encode_two (x : Nat) (xs : List Nat) :
    UnaryBank.encode ((x+2)::xs) = true :: true :: UnaryBank.encode (x::xs) := by
  simp [UnaryBank.encode, UnaryBank.block, List.replicate_succ, Nat.add_assoc]

lemma shifted_to_prior (base : Int → Bool) (g : Int) (s : List Bool) :
    after base g (true::true::s) =
      prior (put base g true) g (s ++ [true,false]) := by
  funext p
  by_cases hp : p < g
  · simp [after, prior, put, before, hp, show p ≠ g from by omega,
      show p ≠ g+1 from by omega, show p ≠ g+2 from by omega,
      show p < g+1 from by omega]
  by_cases he : p = g
  · subst p; simp [after, prior, put]
  by_cases h1 : p = g+1
  · subst p
    simp [after, prior, put, bitAt, show g+1 ≠ g+2 from by omega] <;> omega
  by_cases h2 : p = g+2
  · subst p
    simp [after, prior, put, bitAt, show g+2 ≠ g from by omega] <;> omega
  have hge : g+3 ≤ p := by omega
  have hs : ¬p < g+1 := by omega
  have hs2 : ¬p < g+3 := by omega
  have hne1 : p ≠ g+1 := by omega
  have hne2 : p ≠ g+2 := by omega
  have hidx : (p-g-1).toNat = (p-g-3).toNat + 2 := by omega
  simp only [prior, put, hne1, hne2, he, if_false, before, hs, hs2, after, hp]
  simp only [if_false, List.length_cons, bitAt_cons]
  rw [hidx]
  simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, if_false,
    Nat.add_sub_cancel]
  have hcon : ¬ (p-g-3).toNat + 2 - 1 = 0 := by omega
  have hoff : (p - (g+1) - 2).toNat = (p-g-3).toNat := by congr 1 <;> omega
  have hpos : ¬ p < g + 1 + 2 := by omega
  simp only [hcon, if_false, hoff, hpos, show (p-g-3).toNat + 2 - 1 - 1 = (p-g-3).toNat by omega]
  rw [bitAt_append_reserve]
  have hh : ((p-g-3).toNat : Int) = p-g-3 := by omega
  have hl : (0 : Int) ≤ s.length := by omega
  simp only [Nat.cast_add, Nat.cast_one] at *
  split_ifs <;> first | rfl | (exfalso; omega)


theorem next_cycle_layout (base : Int → Bool) (b : Int) (x : Nat) (xs : List Nat) :
    after base (b+1) (UnaryBank.encode ((x+2)::xs)) =
      prior (put base (b+1) true) (b+1) (UnaryBank.encode (x::(xs++[0]))) := by
  rw [encode_two, show UnaryBank.encode (x::(xs++[0])) =
      UnaryBank.encode (x::xs) ++ [true,false] by
    simpa using UnaryBank.append_zero_block (x::xs)]
  exact shifted_to_prior base (b+1) (UnaryBank.encode (x::xs))

end Shared.Beeping.NPcoNP.NativeHalfLoopLayout
