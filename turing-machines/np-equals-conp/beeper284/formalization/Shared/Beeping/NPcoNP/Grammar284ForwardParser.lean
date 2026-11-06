import Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
import Shared.Beeping.NPcoNP.NativeHalfScan

/-! The producer's clean control path is read from syntax origin toward
increasing tape coordinates. Reflection reuses the checked descending parser
without changing the finite grammar or introducing a runtime oracle. This
is an observer of a tape accessor, not yet a physical dispatch proof. -/
namespace Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def reflectTape (tape : Int → Bool) (q : Int) : Bool := tape (-q)

/-- The same bounded grammar parser, reading increasing tape coordinates. -/
def parseForward (fuel : Nat) (tape : Int → Bool) (origin : Int) : Option (String × Nat) :=
  parsePreparedTape fuel (reflectTape tape) (-origin)

/-- A descending word on the reflected tape is the same finite word in
ordinary left-to-right tape order. -/
theorem reflected_word (tape : Int → Bool) (h : Int) (word : List Bool) :
    downHolds (reflectTape tape) (-h) word ↔ Holds tape h word := by
  induction word generalizing h with
  | nil => rfl
  | cons b bs ih =>
    change tape (-(-h))=b ∧ downHolds (reflectTape tape) (-h-1) bs ↔
      tape h=b ∧ Holds tape (h+1) bs
    have he : -h-1= -(h+1) := by omega
    rw [he,ih]
    simp

/-- Success is exactly a prepared producer-grammar path appearing in the
ascending physical tape word, with the complete path length. -/
theorem parseForward_iff (tape : Int → Bool) (origin : Int) (name : String) (len : Nat) :
    parseForward 52 tape origin=some (name,len) ↔
      ∃ path : List Bool, PreparedWalk path (.op name) ∧ path.length=len ∧
        Holds tape origin path := by
  simp only [parseForward,parsePreparedTape_iff,reflected_word]

/-- The finite path observed after the first-beep return denotes the
coalesced register-4 conditional decrement in the pinned grammar. -/
theorem observed_path_walk :
    PreparedWalk [true,true,false,true,false,false] (.op "3.$coalesced.4.decnz") := by
  refine ⟨[true,false,false],rfl,?_⟩
  apply follow_sound producerGrammar [true,false,false] (.node producerGrammar.root)
  decide

theorem observed_path_parse (tape : Int → Bool) (origin : Int)
    (hword : Holds tape origin [true,true,false,true,false,false]) :
    parseForward 52 tape origin=some ("3.$coalesced.4.decnz",6) := by
  apply (parseForward_iff tape origin "3.$coalesced.4.decnz" 6).2
  exact ⟨[true,true,false,true,false,false],observed_path_walk,rfl,hword⟩

#print axioms reflected_word
#print axioms parseForward_iff
#print axioms observed_path_walk
#print axioms observed_path_parse
end Shared.Beeping.NPcoNP.Grammar284ForwardParser
