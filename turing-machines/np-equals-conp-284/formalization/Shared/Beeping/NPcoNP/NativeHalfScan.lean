import Shared.Beeping.NPcoNP.NativeHalfScanStep
import Shared.Beeping.WordBridge
import Shared.Beeping.ScalarWordRefinement

/-! The literal native-HALF forward scan reaches the first double zero in
finite positive time, leaving the complete two-sided tape unchanged and
emitting no event. The prefix language forbids an earlier adjacent zero pair.
This proves the scanner segment only, not the backward shift or HALF. -/
namespace Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.Table284

def cfg {n : Nat} (q : Fin n) (h : Int) (t : Int → Bool) : Config n := ⟨q,h,t⟩

inductive Prefix : List Bool → Prop where
  | nil : Prefix []
  | one {xs} : Prefix xs → Prefix (true :: xs)
  | zeroOne {xs} : Prefix xs → Prefix (false :: true :: xs)

def Holds (t : Int → Bool) (h : Int) : List Bool → Prop
  | [] => True
  | b :: xs => t h = b ∧ Holds t (h+1) xs

variable {n : Nat} (M : Machine n) (a b d : Fin n)
variable (hA1 : ∀ h t, t h = true → M.step (cfg a h t) = (cfg a (h+1) t,false))
variable (hA0 : ∀ h t, t h = false → M.step (cfg a h t) = (cfg b (h+1) t,false))
variable (hB1 : ∀ h t, t h = true → M.step (cfg b h t) = (cfg a (h+1) t,false))
variable (hB0 : ∀ h t, t h = false → M.step (cfg b h t) = (cfg d (h-1) t,false))

def W : WordEventSystem (Config n) Unit := WordEventSystem.ofBeep M.system

def silentSegment (c e : Config n) (k : Nat) : Prop :=
  (W M).advance c k = e ∧ (W M).wordFrom c k = []

theorem oneSeg (c e : Config n) (h : M.step c = (e,false)) :
    silentSegment M c e 1 := by
  simp [silentSegment, W, WordEventSystem.advance, WordEventSystem.wordFrom,
    WordEventSystem.ofBeep, Machine.system, h]

theorem segAdd (c d e : Config n) (k l : Nat)
    (h : silentSegment M c d k) (h' : silentSegment M d e l) :
    silentSegment M c e (k+l) := by
  constructor
  · rw [WordEventSystem.advance_add, h.1, h'.1]
  · rw [WordEventSystem.wordFrom_add, h.1, h.2, h'.2]
    rfl

theorem scan (hA1 : ∀ h t, t h = true → M.step (cfg a h t) = (cfg a (h+1) t,false))
    (hA0 : ∀ h t, t h = false → M.step (cfg a h t) = (cfg b (h+1) t,false))
    (hB1 : ∀ h t, t h = true → M.step (cfg b h t) = (cfg a (h+1) t,false))
    (hB0 : ∀ h t, t h = false → M.step (cfg b h t) = (cfg d (h-1) t,false))
    (xs : List Bool) (hx : Prefix xs) (h : Int) (t : Int → Bool)
    (hm : Holds t h (xs ++ [false,false])) :
    silentSegment M (cfg a h t) (cfg d (h + xs.length) t) (xs.length+2) := by
  induction hx generalizing h with
  | nil =>
    simp only [List.nil_append, Holds] at hm
    have sa := oneSeg M _ _ (hA0 h t hm.1)
    have sb := oneSeg M _ _ (hB0 (h+1) t hm.2.1)
    have result := segAdd M _ _ _ 1 1 sa sb
    simpa using result
  | @one xs hx ih =>
    simp only [List.cons_append, Holds] at hm
    have sa := oneSeg M _ _ (hA1 h t hm.1)
    have sh := ih (h+1) hm.2
    have result := segAdd M _ _ _ 1 (xs.length+2) sa sh
    simpa [List.length_cons, Int.add_assoc, Int.add_comm, Int.add_left_comm, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using result
  | @zeroOne xs hx ih =>
    simp only [List.cons_append, Holds] at hm
    have sa := oneSeg M _ _ (hA0 h t hm.1)
    have sb := oneSeg M _ _ (hB1 (h+1) t hm.2.1)
    have sh := ih (h+1+1) hm.2.2
    have sab := segAdd M _ _ _ 1 1 sa sb
    have result := segAdd M _ _ _ (1+1) (xs.length+2) sab sh
    simpa [List.length_cons, Int.add_assoc, Int.add_comm, Int.add_left_comm, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using result

theorem silent_no_beep (c e : Config n) (k j : Nat)
    (h : silentSegment M c e k) (hj : j < k) : ¬ M.system.BeepFrom c j := by
  have hjk : j + 1 ≤ k := by omega
  have hp : (W M).wordFrom c (j+1) ++
      (W M).wordFrom ((W M).advance c (j+1)) (k-(j+1)) = [] := by
    rw [← WordEventSystem.wordFrom_add]
    simpa [Nat.add_sub_of_le hjk] using h.2
  have hprefix := (List.append_eq_nil_iff.mp hp).1
  have he : ((W M).step ((W M).advance c j)).2 = [] := by
    exact (List.append_eq_nil_iff.mp hprefix).2
  intro hb
  have hevent : (M.system.step (M.system.advance c j)).2 = true := hb
  have he' := he
  change (if (M.system.step ((WordEventSystem.ofBeep M.system).advance c j)).2
    then [()] else []) = [] at he'
  rw [PASoundness.ScalarWordRefinement.advance_ofBeep, hevent] at he'
  contradiction

/-- The literal scanner, for any finite zero-pair-free prefix and arbitrary
tape contents beyond the asserted cells. -/
theorem selected_scan (xs : List Bool) (hx : Prefix xs) (h : Int)
    (tape : Int → Bool) (hm : Holds tape h (xs ++ [false,false])) :
    silentSegment machine (cfg 32 h tape) (cfg 34 (h + xs.length) tape)
      (xs.length+2) :=
  scan machine 32 33 34 scan32_one scan32_zero scan33_one scan33_zero xs hx h tape hm

theorem selected_scan_positive (xs : List Bool) : 0 < xs.length + 2 := by omega

theorem selected_scan_no_beep (xs : List Bool) (hx : Prefix xs) (h : Int)
    (tape : Int → Bool) (hm : Holds tape h (xs ++ [false,false]))
    (j : Nat) (hj : j < xs.length + 2) :
    ¬ machine.system.BeepFrom (cfg 32 h tape) j :=
  silent_no_beep machine _ _ _ j (selected_scan xs hx h tape hm) hj

end Shared.Beeping.NPcoNP.NativeHalfScan
