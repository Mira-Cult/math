import Shared.Beeping.NPcoNP.NativeHalfState10Exact
import Shared.Beeping.NPcoNP.NativeHalfState28Exact

/-! Compositional tape frames for the two exact physical scans. Any finite
word disjoint from the written interval is preserved on the full tape. -/
namespace Shared.Beeping.NPcoNP.NativeHalfScannerFrames

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact

theorem holds_transport (t u : Int → Bool) (h : Int) (xs : List Bool)
    (hx : Holds t h xs)
    (ha : ∀ p, h≤p → p<h+(xs.length : Int) → t p=u p) : Holds u h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    change t h=x ∧ Holds t (h+1) xs at hx
    change u h=x ∧ Holds u (h+1) xs
    constructor
    · have he : t h=u h := ha h (by omega) (by simp)
      rw [← he]
      exact hx.1
    · apply ih (h+1) hx.2
      intro p hlo hhi
      apply ha p
      · omega
      · simp only [List.length_cons, Nat.cast_succ] at *
        omega

theorem fill_frame (t : Int → Bool) (lo hi h : Int) (xs : List Bool)
    (hx : Holds t h xs) (hd : h+(xs.length : Int)≤lo ∨ hi≤h) :
    Holds (fillRange t lo hi) h xs := by
  apply holds_transport t _ h xs hx
  intro p hlo hhi
  have hn : ¬ (lo≤p ∧ p<hi) := by omega
  simp [fillRange,hn]

theorem clear_frame (t : Int → Bool) (lo hi h : Int) (xs : List Bool)
    (hx : Holds t h xs) (hd : h+(xs.length : Int)≤lo ∨ hi≤h) :
    Holds (clearRange t lo hi) h xs := by
  apply holds_transport t _ h xs hx
  intro p hlo hhi
  have hn : ¬ (lo≤p ∧ p<hi) := by omega
  simp [clearRange,hn]

/-- State 10 has the exact scan behavior and preserves any disjoint word. -/
theorem scan10_with_frame (k : Nat) (h a : Int) (t : Int → Bool) (xs : List Bool)
    (hz : ∀ i : Nat, i<k → t (h+(i : Int))=false)
    (hm : t (h+(k : Int))=true) (hx : Holds t a xs)
    (hd : a+(xs.length : Int)≤h ∨ h+(k : Int)≤a) :
    silentSegment machine (cfg 10 h t)
        (cfg 97 (h+(k : Int)-1) (fillRange t h (h+(k : Int)))) (k+1) ∧
      Holds (fillRange t h (h+(k : Int))) a xs :=
  ⟨scan10_exact k h t hz hm,fill_frame t h (h+(k : Int)) a xs hx hd⟩

/-- State 28 has the dual exact behavior and preserves any disjoint word. -/
theorem scan28_with_frame (k : Nat) (h a : Int) (t : Int → Bool) (xs : List Bool)
    (ho : ∀ i : Nat, i<k → t (h+(i : Int))=true)
    (hz : t (h+(k : Int))=false) (hx : Holds t a xs)
    (hd : a+(xs.length : Int)≤h ∨ h+(k : Int)≤a) :
    silentSegment machine (cfg 28 h t)
        (cfg 6 (h+(k : Int)-1) (clearRange t h (h+(k : Int)))) (k+1) ∧
      Holds (clearRange t h (h+(k : Int))) a xs :=
  ⟨scan28_exact k h t ho hz,clear_frame t h (h+(k : Int)) a xs hx hd⟩

end Shared.Beeping.NPcoNP.NativeHalfScannerFrames

#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerFrames.scan10_with_frame
#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerFrames.scan28_with_frame
