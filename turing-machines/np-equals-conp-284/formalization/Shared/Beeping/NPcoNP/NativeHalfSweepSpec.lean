import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! The exact pointwise tape effect of the literal native-HALF backward sweep.
This proof does not identify the result with a particular bank embedding; that
connection requires its own admitted-input and representation lemmas. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.Table284

/-- Simultaneous one-cell left shift inside the scanned interval, followed
by the fresh leading one of the new reserve block. -/
def spec (t : Int → Bool) (h : Int) (k : Nat) (i : Int) : Bool :=
  if i = h then true else if h - (k : Int) ≤ i ∧ i < h then t (i+1) else t i

lemma spec_stop (t : Int → Bool) (h : Int) : spec t h 0 = put t h true := by
  funext i
  by_cases hh : i = h
  · simp [spec, put, hh]
  · have hn : ¬(h ≤ i ∧ i < h) := by omega
    simp [spec, put, hh, hn]

lemma spec_one (t : Int → Bool) (h : Int) (k : Nat) (ht : t h = true) :
    spec t (h-1) k = spec t h (k+1) := by
  funext i
  have hk : (0 : Int) ≤ k := by omega
  by_cases hh : i = h
  · subst i
    have hne : h ≠ h-1 := by omega
    have hn : ¬(h - 1 - (k:Int) ≤ h ∧ h < h - 1) := by omega
    simp [spec, hne, hn, ht]
  · by_cases hp : i = h-1
    · subst i
      have hne : h-1 ≠ h := by omega
      have hlo : h-((k:Int)+1) ≤ h-1 := by omega
      have hhi : h-1 < h := by omega
      have heq : h-1+1 = h := by omega
      simp [spec, Nat.cast_add, Nat.cast_one, hne, hlo, hhi, heq, ht]
    · have hequiv : (h-1-(k:Int) ≤ i ∧ i < h-1) ↔
          (h-((k:Int)+1) ≤ i ∧ i < h) := by omega
      simp only [spec, Nat.cast_add, Nat.cast_one, if_neg hh, if_neg hp]
      simp only [hequiv]

lemma spec_zeroOne (t : Int → Bool) (h : Int) (k : Nat)
    (ht0 : t h = false) (ht1 : t (h-1) = true) :
    spec (put (put t h true) (h-1) false) (h-2) k = spec t h (k+2) := by
  funext i
  have hk : (0 : Int) ≤ k := by omega
  by_cases hh : i = h
  · subst i
    have hn : ¬(h-2-(k:Int) ≤ h ∧ h < h-2) := by omega
    have h2 : h ≠ h-2 := by omega
    have h1 : h ≠ h-1 := by omega
    simp [spec, put, hn, h2, h1]
  · by_cases h1 : i = h-1
    · subst i
      have hlo : h-((k:Int)+2) ≤ h-1 := by omega
      have hhi : h-1 < h := by omega
      have heq : h-1+1 = h := by omega
      have hne : h-1 ≠ h := by omega
      have hne2 : h-1 ≠ h-2 := by omega
      have hn : ¬(h-2-(k:Int) ≤ h-1 ∧ h-1 < h-2) := by omega
      simp [spec, put, Nat.cast_add, hlo, hhi, heq, hne, hne2, hn, ht0]
    · by_cases h2 : i = h-2
      · subst i
        have hlo : h-((k:Int)+2) ≤ h-2 := by omega
        have hhi : h-2 < h := by omega
        have heq : h-2+1 = h-1 := by omega
        have hne : h-2 ≠ h := by omega
        simp [spec, Nat.cast_add, hlo, hhi, heq, hne, ht1]
      · have hplus1 : i+1 ≠ h-1 := by omega
        have hplus2 : i+1 ≠ h := by omega
        have hequiv : (h-2-(k:Int) ≤ i ∧ i < h-2) ↔
            (h-((k:Int)+2) ≤ i ∧ i < h) := by omega
        simp only [spec, put, Nat.cast_add, Nat.cast_ofNat, if_neg hh, if_neg h1, if_neg h2, if_neg hplus1, if_neg hplus2]
        simp only [hequiv]

theorem effect_eq_spec (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    effect s t h = spec t h (bits s).length := by
  induction s generalizing h t with
  | stop =>
    simpa [effect, bits] using (spec_stop t h).symm
  | one s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    change effect s t (h-1) = spec t h (List.length (true :: bits s))
    rw [ih (h-1) t hm.2]
    simpa using spec_one t h (bits s).length hm.1
  | zeroOne s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    have htail : downHolds (put (put t h true) (h-1) false) (h-1-1) (bits s ++ [false,false]) := by
      apply downHolds_put
      · omega
      · apply downHolds_put
        · omega
        · exact hm.2.2
    change effect s (put (put t h true) (h-1) false) (h-2) =
      spec t h (List.length (false :: true :: bits s))
    have heq : h-2 = h-1-1 := by omega
    rw [heq, ih (h-1-1) _ htail]
    simpa [Int.sub_sub, Nat.add_assoc] using spec_zeroOne t h (bits s).length hm.1 hm.2.1

/-- Concrete sweep with an explicit, pointwise whole-tape postcondition. -/
theorem sweep_spec (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 34 h t)
      (cfg 31 (h - (bits s).length - 2) (spec t h (bits s).length))
      ((bits s).length + 2) := by
  rw [← effect_eq_spec s h t hm]
  exact sweep s h t hm

theorem spec_top (t : Int → Bool) (h : Int) (k : Nat) : spec t h k h = true := by
  simp [spec]

theorem spec_inside (t : Int → Bool) (h i : Int) (k : Nat)
    (hlo : h - (k : Int) ≤ i) (hhi : i < h) : spec t h k i = t (i+1) := by
  simp [spec, hlo, hhi, show i ≠ h by omega]

theorem spec_outside (t : Int → Bool) (h i : Int) (k : Nat)
    (ho : i < h - (k : Int) ∨ h < i) : spec t h k i = t i := by
  have hne : i ≠ h := by omega
  have hn : ¬(h - (k : Int) ≤ i ∧ i < h) := by omega
  simp only [spec, if_neg hne, if_neg hn]


end Shared.Beeping.NPcoNP.NativeHalfSweep
