import Shared.Beeping.NPcoNP.NativeHalfScan
import Shared.Beeping.NPcoNP.NativeHalfShiftStep

/-! Exact silent finite backward sweep of the literal table's HALF cycle
states, for a leftward suffix of the stated shape. The output is an explicit
sequence of tape writes; its equality to the separately defined unary-shift
specification is a further obligation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.Table284

inductive Shape where
 | stop
 | one (s : Shape)
 | zeroOne (s : Shape)

def bits : Shape → List Bool
 | .stop => []
 | .one s => true :: bits s
 | .zeroOne s => false :: true :: bits s

def downHolds (t : Int → Bool) (h : Int) : List Bool → Prop
 | [] => True
 | b::xs => t h = b ∧ downHolds t (h-1) xs

def put (t : Int → Bool) (h : Int) (b : Bool) : Int → Bool :=
  fun i => if i = h then b else t i

lemma put_other (t : Int → Bool) (h i : Int) (b : Bool) (hi : i ≠ h) :
    put t h b i = t i := by simp [put,hi]

lemma cfg_write (q : Fin 284) (h : Int) (t : Int → Bool) (v : Bool) :
    (cfg q h t).write v = put t h v := rfl

lemma downHolds_put (t : Int → Bool) (h p : Int) (xs : List Bool) (v : Bool)
    (hp : h < p) (hm : downHolds t h xs) : downHolds (put t p v) h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    simp only [downHolds] at *
    constructor
    · rw [put_other t p h v (by omega)]; exact hm.1
    · exact ih (h-1) (by omega) hm.2

def effect : Shape → (Int → Bool) → Int → (Int → Bool)
 | .stop,t,h => put t h true
 | .one s,t,h => effect s t (h-1)
 | .zeroOne s,t,h => effect s (put (put t h true) (h-1) false) (h-2)


theorem sweep (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 34 h t)
      (cfg 31 (h - (bits s).length - 2) (effect s t h)) ((bits s).length + 2) := by
  induction s generalizing h t with
  | stop =>
    simp only [bits, List.nil_append, downHolds] at hm
    have h0 : put t h true (h-1) = false := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (shift34_zero h t hm.1)
    change silentSegment machine (cfg 34 h t) (cfg 35 (h-1) (put t h true)) 1 at sa
    have sb := oneSeg machine _ _ (shift35_zero (h-1) (put t h true) h0)
    have res := segAdd machine _ _ _ 1 1 sa sb
    simpa [bits,effect,cfg,Int.sub_sub] using res
  | one s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    have sa := oneSeg machine _ _ (shift34_one h t hm.1)
    have sh := ih (h-1) t hm.2
    have res := segAdd machine _ _ _ 1 ((bits s).length+2) sa sh
    simpa [bits,effect,cfg, List.length_cons, Int.sub_sub, Int.add_assoc, Int.add_comm, Int.add_left_comm, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using res
  | zeroOne s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    have h1 : put t h true (h-1) = true := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (shift34_zero h t hm.1)
    change silentSegment machine (cfg 34 h t) (cfg 35 (h-1) (put t h true)) 1 at sa
    have sb := oneSeg machine _ _ (shift35_one (h-1) (put t h true) h1)
    change silentSegment machine (cfg 35 (h-1) (put t h true))
      (cfg 34 (h-1-1) (put (put t h true) (h-1) false)) 1 at sb
    have htail : downHolds (put (put t h true) (h-1) false) (h-1-1) (bits s ++ [false,false]) := by
      apply downHolds_put
      · omega
      · apply downHolds_put
        · omega
        · exact hm.2.2
    have sh := ih (h-1-1) (put (put t h true) (h-1) false) htail
    have sab := segAdd machine _ _ _ 1 1 sa sb
    have res := segAdd machine _ _ _ (1+1) ((bits s).length+2) sab sh
    convert res using 1 <;> simp [bits,effect,cfg,List.length_cons,Int.sub_sub] <;> omega

end Shared.Beeping.NPcoNP.NativeHalfSweep
