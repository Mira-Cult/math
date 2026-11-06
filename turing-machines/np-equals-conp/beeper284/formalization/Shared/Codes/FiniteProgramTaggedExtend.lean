import Shared.Codes.FiniteProgramShuttleSelect
import Shared.Codes.FiniteProgramLink

/-! Finish a shuttle/selector pass by tagging its emitted word, patching the
boundary, and returning to the source. This is one buffer-extension macro,
not yet a complete loop over input symbols. -/
namespace Shared.Codes.FiniteProgramTaggedExtend
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons tagged_append)
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramSelectWord (finish selectRows_length)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)

/-- States 0-6 rewind and repair the new/old boundary. State 7 is the
non-executed continuation in this standalone valid table. -/
def recovery : Program :=
  [ ((false,false,1,0),(true,true,0,1)),
    ((false,true,0,1),(true,false,2,0)),
    ((false,false,3,0),(true,false,3,0)),
    ((true,false,4,0),(true,false,1,0)),
    ((false,false,7,0),(true,false,5,0)),
    ((false,false,6,0),(true,false,6,0)),
    ((false,true,0,1),(true,false,4,0)),
    ((false,true,0,1),(true,true,0,1)) ]

theorem recovery_valid : valid recovery = true := by decide

theorem begin (L : List Bool) :
    run recovery (0,(L,false,[])) 1 = some (.inr (1,tapeLeft L [false])) := by
  simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem new_head (L R : List Bool) :
    run recovery (1,tapeLeft (true::L) R) 1 = some (.inr (2,tapeLeft L (true::R))) := by
  simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem new_data (b : Bool) (L R : List Bool) :
    run recovery (2,tapeLeft (b::L) R) 1 = some (.inr (3,tapeLeft L (b::R))) := by
  cases b <;> simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem new_end (L R : List Bool) :
    run recovery (3,tapeLeft (true::L) R) 1 = some (.inr (1,tapeLeft L (true::R))) := by
  simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem new_reverse (xs L R : List Bool) :
    run recovery (1,tapeLeft ((tagged xs).reverse ++ L) R) (3*xs.length) =
      some (.inr (1,tapeLeft L (tagged xs ++ R))) := by
  induction xs using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton xs b ih =>
    rw [tagged_append,tagged_cons]
    simp only [tagged,List.flatMap_nil,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.cons_append]
    change run recovery (1,tapeLeft (true::b::true::((tagged xs).reverse ++ L)) R)
      (3*(xs++[b]).length) = _
    rw [show 3*(xs++[b]).length = 1+(1+(1+3*xs.length)) by simp; omega]
    rw [run_continue _ _ _ 1 _ (new_head _ R)]
    rw [run_continue _ _ _ 1 _ (new_data b _ (true::R))]
    rw [run_continue _ _ _ 1 _ (new_end _ (b::true::R))]
    simpa [tagged,List.append_assoc] using ih (true::b::true::R)

theorem patch (b : Bool) (L R : List Bool) :
    run recovery (1,tapeLeft (true::b::false::L) R) 3 =
      some (.inr (4,tapeLeft L (true::b::true::R))) := by
  rw [show 3 = 1+(1+1) by decide]
  rw [run_continue _ _ _ 1 _ (new_head _ R)]
  rw [run_continue _ _ _ 1 _ (new_data b _ (true::R))]
  simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem old_head (L R : List Bool) :
    run recovery (4,tapeLeft (true::L) R) 1 = some (.inr (5,tapeLeft L (true::R))) := by
  simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem old_data (b : Bool) (L R : List Bool) :
    run recovery (5,tapeLeft (b::L) R) 1 = some (.inr (6,tapeLeft L (b::R))) := by
  cases b <;> simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem old_end (L R : List Bool) :
    run recovery (6,tapeLeft (true::L) R) 1 = some (.inr (4,tapeLeft L (true::R))) := by
  simp [run,advance,step,recovery,tapeLeft,moveTape]

theorem old_reverse (xs L R : List Bool) :
    run recovery (4,tapeLeft ((tagged xs).reverse ++ L) R) (3*xs.length) =
      some (.inr (4,tapeLeft L (tagged xs ++ R))) := by
  induction xs using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton xs b ih =>
    rw [tagged_append,tagged_cons]
    simp only [tagged,List.flatMap_nil,List.reverse_append,List.reverse_cons,
      List.reverse_nil,List.nil_append,List.cons_append]
    change run recovery (4,tapeLeft (true::b::true::((tagged xs).reverse ++ L)) R)
      (3*(xs++[b]).length) = _
    rw [show 3*(xs++[b]).length = 1+(1+(1+3*xs.length)) by simp; omega]
    rw [run_continue _ _ _ 1 _ (old_head _ R)]
    rw [run_continue _ _ _ 1 _ (old_data b _ (true::R))]
    rw [run_continue _ _ _ 1 _ (old_end _ (b::true::R))]
    simpa [tagged,List.append_assoc] using ih (true::b::true::R)

theorem finish_step (L R : List Bool) :
    run recovery (4,tapeLeft (false::L) R) 1 = some (.inr (7,tapeLeft L (false::R))) := by
  simp [run,advance,step,recovery,tapeLeft,moveTape]

/-- Starting immediately after the selector, turn its output into tagged
blocks and return to the original source bit. -/
theorem recover (b : Bool) (word xs L : List Bool) :
    run recovery (0,((true::tagged word).reverse ++ b::false::(tagged xs).reverse ++ false::b::L,false,[]))
      (3*word.length+3*xs.length+5) =
      some (.inr (7,tapeAt L (b::false::tagged (xs++b::word) ++ [false]))) := by
  rw [show 3*word.length+3*xs.length+5 = 1+(3*word.length+(3+(3*xs.length+1))) by omega]
  rw [run_continue _ _ _ 1 _ (begin _)]
  simp only [List.reverse_cons,List.nil_append,List.append_assoc,List.cons_append]
  rw [run_continue _ _ _ _ _ (new_reverse word (true::b::false::((tagged xs).reverse ++ false::b::L)) [false])]
  rw [run_continue _ _ _ 3 _ (patch b ((tagged xs).reverse ++ false::b::L) (tagged word ++ [false]))]
  rw [run_continue _ _ _ _ _ (old_reverse xs (false::b::L) (true::b::true::(tagged word ++ [false])))]
  rw [finish_step]
  simp [tapeLeft,tapeAt,tagged_append,tagged_cons,List.append_assoc]


def codeZero (zero : List Bool) : List Bool := true::tagged zero

def stagePre (zero one : List Bool) : Program :=
  Shared.Codes.FiniteProgramShuttleSelect.program (codeZero zero) (codeZero one) []

theorem stagePre_length (zero one : List Bool) :
    (stagePre zero one).length = finish 12 (codeZero zero) (codeZero one) := by
  simp [stagePre,Shared.Codes.FiniteProgramShuttleSelect.program,
    Shared.Codes.FiniteProgramShuttleSelect.pre_length,selectRows_length,finish]
  omega

def stage (zero one : List Bool) (suffix : Program) : Program :=
  link (stagePre zero one) recovery suffix

theorem stage_eq (zero one : List Bool) (suffix : Program) :
    stage zero one suffix = Shared.Codes.FiniteProgramShuttleSelect.program (codeZero zero) (codeZero one)
      (recovery.map (shiftPair (stagePre zero one).length) ++ suffix) := by
  simp [stage,link,stagePre,Shared.Codes.FiniteProgramShuttleSelect.program,List.append_assoc]

/-- One complete finite-table update of the tagged buffer. The copied source
bit is retained as one extra tagged datum before the selected word. -/
theorem stage_run (zero one : List Bool) (suffix : Program) (b old : Bool) (xs L : List Bool) :
    let word := if b then one else zero
    run (stage zero one suffix) (0,tapeAt L (b::false::tagged xs ++ [false,old,false]))
      (6*xs.length+6*word.length+12) =
      some (.inr ((stagePre zero one).length+7,
        tapeAt L (b::false::tagged (xs++b::word) ++ [false]))) := by
  dsimp only
  let word := if b then one else zero
  have hchosen : (if b then codeZero one else codeZero zero) = true::tagged word := by
    cases b <;> rfl
  have hfirst := Shared.Codes.FiniteProgramShuttleSelect.shuttle_select (codeZero zero) (codeZero one)
    (recovery.map (shiftPair (stagePre zero one).length) ++ suffix) b old xs L
  dsimp only at hfirst
  rw [hchosen] at hfirst
  have hlen : (true::tagged word).length = 1+3*word.length := by
    simp [Shared.Codes.FiniteProgramBitShuttle.tagged_length]
    omega
  rw [hlen,← stagePre_length zero one,← stage_eq zero one suffix] at hfirst
  have htime : 6*xs.length+6*word.length+12 =
      (3*xs.length+6+(1+3*word.length))+(3*word.length+3*xs.length+5) := by omega
  rw [htime,run_continue _ _ _ _ _ hfirst]
  have hs := run_shift (stagePre zero one) recovery suffix recovery_valid
    (0,((true::tagged word).reverse ++ b::false::(tagged xs).reverse ++ false::b::L,false,[]))
    (by simp [recovery]) (3*word.length+3*xs.length+5)
  rw [recover] at hs
  simpa [stage,shiftStatus,shiftConfig,word] using hs

theorem shifted_valid (r : Row) (offset m : Nat) (hv : validRow m r = true) :
    validRow (offset+m) (Shared.Codes.FiniteProgramLink.shiftRow offset r) = true := by
  rcases r with ⟨w,d,next,tag⟩
  cases tag with
  | zero => simpa [validRow,Shared.Codes.FiniteProgramLink.shiftRow] using hv
  | succ tag => simpa [validRow,Shared.Codes.FiniteProgramLink.shiftRow] using hv

/-- The generated stage is valid when any additional suffix rows are valid
at the final table length. -/
theorem stage_valid (zero one : List Bool) (suffix : Program)
    (hsuffix : ∀ r ∈ suffix, validRow ((stagePre zero one).length+recovery.length+suffix.length) r.1 = true ∧
      validRow ((stagePre zero one).length+recovery.length+suffix.length) r.2 = true) :
    valid (stage zero one suffix) = true := by
  let offset := (stagePre zero one).length
  let tail := recovery.map (shiftPair offset) ++ suffix
  have hoff : finish 12 (codeZero zero) (codeZero one) = offset := (stagePre_length zero one).symm
  have hlen : tail.length = recovery.length+suffix.length := by simp [tail]
  have htailpos : 0 < tail.length := by rw [hlen]; simp [recovery]
  have hrec : ∀ r ∈ recovery, validRow recovery.length r.1 = true ∧ validRow recovery.length r.2 = true := by
    intro r hr
    have hv := recovery_valid
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have htail : ∀ r ∈ tail, validRow (finish 12 (codeZero zero) (codeZero one)+tail.length) r.1 = true ∧
      validRow (finish 12 (codeZero zero) (codeZero one)+tail.length) r.2 = true := by
    intro r hr
    have hr' : r ∈ recovery.map (shiftPair offset) ∨ r ∈ suffix := by simpa [tail] using hr
    rw [hoff,hlen]
    rcases hr' with hmap | hs
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hrec r' hr'
      have hm : offset+recovery.length ≤ offset+(recovery.length+suffix.length) := by omega
      constructor
      · exact Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm (shifted_valid r'.1 offset _ h₁)
      · exact Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hm (shifted_valid r'.2 offset _ h₂)
    · simpa [offset,Nat.add_assoc] using hsuffix r hs
  rw [stage_eq]
  exact Shared.Codes.FiniteProgramShuttleSelect.valid_of_continuation
    (codeZero zero) (codeZero one) tail htailpos htail

namespace Fixtures
example : run (stage [false] [true,false] [])
    (0,tapeAt [] [true,false,false,false,false]) 24 =
      some (.inr (31,tapeAt [] (true::false::tagged [true,true,false] ++ [false]))) := by decide
example : run (stage [false] [true,false] [])
    (0,tapeAt [] [false,false,true,true,true,false,true,false]) 24 =
      some (.inr (31,tapeAt [] (false::false::tagged [true,false,false] ++ [false]))) := by decide
end Fixtures

end Shared.Codes.FiniteProgramTaggedExtend
