import Shared.ComplexityBridge.TM0FiniteProgram
import Shared.Codes.FiniteProgramLink

/-! Compile a fixed binary word into actual single-tape table rows. Each row
writes one bit and moves right, regardless of the bit previously read. -/
namespace Shared.Codes.FiniteProgramWriteWord
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def row (q : Nat) (b : Bool) : Row × Row :=
  ((b,true,q+1,0),(b,true,q+1,0))

def rows : Nat → List Bool → Program
  | _, [] => []
  | q, b::bs => row q b :: rows (q+1) bs

theorem rows_length (q : Nat) (bs : List Bool) : (rows q bs).length = bs.length := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih => simp [rows,ih]

/-- Pure description of the tape after the actual write-and-move sequence. -/
def writeTape : List Bool → Tape → Tape
  | [], t => t
  | b::bs, t => writeTape bs (moveTape false b t)

theorem step_first (pre suffix : Program) (b : Bool) (bs : List Bool) (t : Tape) :
    step (pre ++ rows pre.length (b::bs) ++ suffix) (pre.length,t) =
      some (.inr (pre.length+1,moveTape false b t)) := by
  simp [step,rows,row]

/-- Any appended program is untouched; the next state is exactly the first
row after the generated block. The bound counts real table transitions. -/
theorem write_run (pre suffix : Program) (bs : List Bool) (t : Tape) :
    run (pre ++ rows pre.length bs ++ suffix) (pre.length,t) bs.length =
      some (.inr (pre.length+bs.length,writeTape bs t)) := by
  induction bs generalizing pre t with
  | nil => simp [rows,writeTape]
  | cons b bs ih =>
    let pre' : Program := pre ++ [row pre.length b]
    have heq : pre ++ rows pre.length (b::bs) ++ suffix = pre' ++ rows pre'.length bs ++ suffix := by
      simp [pre',rows,List.append_assoc]
    rw [show (b::bs).length = 1+bs.length by simp [Nat.add_comm]]
    rw [run_continue _ _ _ 1 _ (step_first pre suffix b bs t)]
    rw [heq]
    simpa [pre',writeTape,Nat.add_assoc] using ih pre' (moveTape false b t)

theorem writeTape_left (bs : List Bool) (t : Tape) :
    (writeTape bs t).1 = bs.reverse ++ t.1 := by
  induction bs generalizing t with
  | nil => simp [writeTape]
  | cons b bs ih => simp [writeTape,ih,moveTape,List.reverse_cons,List.append_assoc]

/-- Writing into a blank region leaves exactly the word, nearest last bit
first, on the left of the head and a blank region on the right. -/
theorem writeTape_blank (bs : List Bool) (left : List Bool) :
    writeTape bs (left,false,[]) = (bs.reverse ++ left,false,[]) := by
  induction bs generalizing left with
  | nil => simp [writeTape]
  | cons b bs ih => simpa [writeTape,moveTape,List.reverse_cons,List.append_assoc] using ih (b::left)

/-- A state that copies its read bit, moves left, and advances to `q+1`. -/
def leftRow (q : Nat) : Row × Row :=
  ((false,false,q+1,0),(true,false,q+1,0))

def leftRows : Nat → Nat → Program
  | _, 0 => []
  | q, n+1 => leftRow q :: leftRows (q+1) n

theorem leftRows_length (q n : Nat) : (leftRows q n).length = n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp [leftRows,ih]

def moveLeft (t : Tape) : Tape := moveTape true t.2.1 t

def rewind : Nat → Tape → Tape
  | 0, t => t
  | n+1, t => rewind n (moveLeft t)

theorem left_step_first (pre suffix : Program) (n : Nat) (t : Tape) :
    step (pre ++ leftRows pre.length (n+1) ++ suffix) (pre.length,t) =
      some (.inr (pre.length+1,moveLeft t)) := by
  cases h : t.2.1 <;> simp [step,leftRows,leftRow,moveLeft,h]

theorem left_run (pre suffix : Program) (n : Nat) (t : Tape) :
    run (pre ++ leftRows pre.length n ++ suffix) (pre.length,t) n =
      some (.inr (pre.length+n,rewind n t)) := by
  induction n generalizing pre t with
  | zero => simp [leftRows,rewind]
  | succ n ih =>
    let pre' : Program := pre ++ [leftRow pre.length]
    have heq : pre ++ leftRows pre.length (n+1) ++ suffix = pre' ++ leftRows pre'.length n ++ suffix := by
      simp [pre',leftRows,List.append_assoc]
    nth_rewrite 2 [show n+1 = 1+n by omega]
    rw [run_continue _ _ _ 1 _ (left_step_first pre suffix n t)]
    rw [heq]
    simpa [pre',rewind,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih pre' (moveLeft t)

/-- Rewinding across a known word puts its first bit under the head, without
changing any cell on either side of the traversed interval. -/
theorem rewind_word (bs left : List Bool) (head : Bool) (right : List Bool) :
    rewind bs.length (bs.reverse ++ left,head,right) =
      (left,(bs ++ [head]).head?.getD false,(bs ++ [head]).tail ++ right) := by
  induction bs using List.reverseRecOn generalizing head right with
  | nil => rfl
  | append_singleton bs b ih =>
    simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
      List.cons_append,List.length_append,List.length_cons,List.length_nil,rewind,moveLeft,moveTape]
    cases bs <;> simpa [List.append_assoc] using ih b (head::right)

/-- A literal table that writes a fixed word on blank tape and returns to
its first cell. Its continuation is located immediately after these rows. -/
def loaderPre (bs : List Bool) : Program :=
  rows 0 bs ++ leftRows bs.length bs.length

theorem loader_length (bs : List Bool) : (loaderPre bs).length = 2*bs.length := by
  simp [loaderPre,rows_length,leftRows_length]
  omega

def loadedTape (bs : List Bool) : Tape :=
  ([],(bs ++ [false]).head?.getD false,(bs ++ [false]).tail)

/-- The loader is executable table data and completes in exactly twice the
word length; no termination is assumed for its appended continuation. -/
theorem loader_run (bs : List Bool) (suffix : Program) :
    run (loaderPre bs ++ suffix) (0,([],false,[])) (2*bs.length) =
      some (.inr ((loaderPre bs).length,loadedTape bs)) := by
  have hw : run (loaderPre bs ++ suffix) (0,([],false,[])) bs.length =
      some (.inr (bs.length,(bs.reverse,false,[]))) := by
    have h := write_run [] (leftRows bs.length bs.length ++ suffix) bs ([],false,[])
    simpa [loaderPre,List.append_assoc,writeTape_blank] using h
  have hl : run (loaderPre bs ++ suffix) (bs.length,(bs.reverse,false,[])) bs.length =
      some (.inr (2*bs.length,loadedTape bs)) := by
    have h := left_run (rows 0 bs) suffix bs.length (bs.reverse,false,[])
    have hrew := rewind_word bs [] false []
    simp only [List.append_nil] at hrew
    rw [hrew] at h
    simpa [loaderPre,rows_length,loadedTape,List.append_assoc,two_mul] using h
  rw [show 2*bs.length = bs.length+bs.length by omega]
  rw [run_continue _ _ _ _ _ hw,hl,loader_length]

/-- The extra blank at the end does not change the represented tape. -/
theorem loadedTape_equiv (bs : List Bool) :
    Shared.Codes.FiniteProgramTapeEquiv.TapeRel (loadedTape bs) (initial bs).2 := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    unfold Shared.Codes.FiniteProgramTapeEquiv.TapeRel loadedTape initial
    change (⟨b,Turing.ListBlank.mk [],Turing.ListBlank.mk (bs ++ [false])⟩ : Turing.Tape Bool) =
      ⟨b,Turing.ListBlank.mk [],Turing.ListBlank.mk bs⟩
    have hr : Turing.ListBlank.mk (bs ++ [false]) = Turing.ListBlank.mk bs := by
      apply Quotient.sound
      exact Or.inr ⟨1,by simp⟩
    rw [hr]

/-- A fixed word can be loaded and passed to any valid finite program, with
an exact additive initialization cost. The word is table data fixed before
execution; this theorem does not claim input-dependent serialization. -/
theorem loader_bounded (bs : List Bool) (p suffix : Program) (hvalid : valid p = true) (n : Nat) :
    bounded (Shared.Codes.FiniteProgramLink.link (loaderPre bs) p suffix) [] (2*bs.length+n) =
      bounded p bs n := by
  apply Shared.Codes.FiniteProgramLink.bounded_after_setup_tape (loaderPre bs) p suffix hvalid
    [] bs (0,loadedTape bs) (2*bs.length) n rfl (loadedTape_equiv bs)
  have h := loader_run bs (p.map (Shared.Codes.FiniteProgramLink.shiftPair (loaderPre bs).length) ++ suffix)
  simpa [Shared.Codes.FiniteProgramLink.link,Shared.Codes.FiniteProgramLink.shiftConfig,
    initial,List.append_assoc] using h

theorem valid_loader_bounded (bs : List Bool) (p suffix : Program) (hvalid : valid p = true) (n : Nat) :
    let linked := Shared.Codes.FiniteProgramLink.link (loaderPre bs) p suffix
    valid (Shared.Codes.FiniteProgramRepair.repair linked) = true ∧
      bounded (Shared.Codes.FiniteProgramRepair.repair linked) [] (2*bs.length+n) = bounded p bs n := by
  dsimp only
  constructor
  · exact Shared.Codes.FiniteProgramRepair.repair_valid _
  · rw [Shared.Codes.FiniteProgramRepair.bounded_repair]
    exact loader_bounded bs p suffix hvalid n

namespace Fixtures
example : run (loaderPre [true,false,true]) (0,([],false,[])) 6 =
    some (.inr (6,([],true,[false,true,false]))) := by decide
example : run (loaderPre []) (0,([],false,[])) 0 = some (.inr (0,([],false,[]))) := by decide
example : bounded (Shared.Codes.FiniteProgramLink.link (loaderPre [true,false,true])
    [((false,true,0,1),(true,true,0,2))] []) [] 6 = none := by decide
example : bounded (Shared.Codes.FiniteProgramLink.link (loaderPre [true,false,true])
    [((false,true,0,1),(true,true,0,2))] []) [] 7 = some true := by decide
end Fixtures

end Shared.Codes.FiniteProgramWriteWord
