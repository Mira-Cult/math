import Shared.PNP.Record285.FrameCounterLoader
import Shared.Codes.FiniteProgramFirstEntry

/-! A concrete buffer accumulator for the raw frame. The finite regression
is not used by the theorems: the desired contract is an unbounded full-tape
simulation with a finite blank workspace and arbitrary untouched high suffix. -/
namespace Shared.PNP.Record285.FrameBufferLoader
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)

def entry0 : Row × Row := ((true,false,16,0),(true,false,27,0))
def entry1 : Row × Row := ((true,false,38,0),(true,false,49,0))
def done : Row × Row := ((false,true,0,1),(true,true,0,1))

/-- The block carries the payload bit `b` and the next unread bit `c` in
finite control. Its only cross-block jump restarts the counter at state zero. -/
def block (start : Nat) (b c : Bool) : Program :=
  let a := start
  let u := start+1
  let d := start+2
  let t := start+3
  let w := start+4
  let r := start+5
  let rd := start+6
  let anchor := start+7
  let ones := start+8
  let gap := start+9
  let restore := start+10
  [((false,false,a,0),(true,false,u,0)),
   ((false,false,d,0),(true,false,u,0)),
   ((false,false,t,0),(true,false,t,0)),
   ((true,true,w,0),(true,false,d,0)),
   ((b,true,r,0),(b,true,r,0)),
   ((false,true,anchor,0),(true,true,rd,0)),
   ((false,true,r,0),(true,true,r,0)),
   ((false,true,ones,0),(true,true,ones,0)),
   ((false,true,gap,0),(true,true,ones,0)),
   ((false,true,gap,0),(c,false,restore,0)),
   ((false,true,0,0),(true,true,0,0))]

def program : Program := FrameCounterLoader.rows ++ [entry0,entry1,done] ++
  block 16 false false ++ block 27 false true ++ block 38 true false ++ block 49 true true

theorem program_length : program.length = 60 := by decide

theorem program_valid : valid program = true := by decide

abbrev referenceCounter : Program := FrameCounterLoader.program FrameCounterLoader.dummy

theorem referenceCounter_valid : valid referenceCounter = true :=
  FrameCounterLoader.program_valid _ (by decide) (by decide)

theorem referenceCounter_length : referenceCounter.length = 16 := by decide

theorem prefix_step (d : Config) (hd : d.1 < 13) :
    step referenceCounter d = step program d := by
  have hlen : FrameCounterLoader.rows.length = 13 := by decide
  have hq : d.1 < FrameCounterLoader.rows.length := by omega
  have he : referenceCounter[d.1]? = program[d.1]? := by
    simp [referenceCounter,FrameCounterLoader.program,program,Shared.Codes.FiniteProgramLink.link,
      List.getElem?_append_left,hq]
  simp [step,he]

theorem referenceCounter_stop (q : Nat) (hq : 13 ≤ q ∧ q < 16) (tape : Tape) :
    step referenceCounter (q,tape) = some (.inl false) := by
  have h : q = 13 ∨ q = 14 ∨ q = 15 := by omega
  rcases h with rfl | rfl | rfl <;> cases hread : tape.2.1 <;>
    simp [step,referenceCounter,FrameCounterLoader.program,FrameCounterLoader.dummy,
      Shared.Codes.FiniteProgramLink.link,Shared.Codes.FiniteProgramLink.shiftPair,
      Shared.Codes.FiniteProgramLink.shiftRow,FrameCounterLoader.rows,hread]

/-- The loop table has exactly the same first counter exit as the checked
counter-plus-terminal table, even though its exits now start buffer work. -/
theorem first_counter_exit (initial last : Config) (clock : Nat)
    (hinitial : initial.1 < 13)
    (hfinal : run referenceCounter initial clock = some (.inr last)) :
    run program initial clock = some (.inr last) := by
  have hs13 : ∀ t, step referenceCounter (13,t) = some (.inl false) :=
    fun t => referenceCounter_stop 13 (by omega) t
  have hs14 : ∀ t, step referenceCounter (14,t) = some (.inl false) :=
    fun t => referenceCounter_stop 14 (by omega) t
  have hs15 : ∀ t, step referenceCounter (15,t) = some (.inl false) :=
    fun t => referenceCounter_stop 15 (by omega) t
  have hn13 := Shared.Codes.FiniteProgramFirstEntry.not_visited_before
    referenceCounter initial last clock 13 false hs13 hfinal
  have hn14 := Shared.Codes.FiniteProgramFirstEntry.not_visited_before
    referenceCounter initial last clock 14 false hs14 hfinal
  have hn15 := Shared.Codes.FiniteProgramFirstEntry.not_visited_before
    referenceCounter initial last clock 15 false hs15 hfinal
  have hc : initial.1 < referenceCounter.length := by rw [referenceCounter_length]; omega
  have heq : ∀ i ≤ clock, run referenceCounter initial i = run program initial i := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [run_succ,run_succ,← ih (by omega)]
      cases hr : run referenceCounter initial i with
      | none => rfl
      | some v => cases v with
        | inl bit => rfl
        | inr d =>
          change step referenceCounter d = step program d
          have hin := Shared.Codes.FiniteProgramLink.run_in_range
            referenceCounter referenceCounter_valid initial hc i
          rw [hr] at hin
          have hq : d.1 < 13 := by
            have h13 := hn13 i (by omega) d hr
            have h14 := hn14 i (by omega) d hr
            have h15 := hn15 i (by omega) d hr
            change d.1 < referenceCounter.length at hin
            rw [referenceCounter_length] at hin
            omega
          exact prefix_step d hq
  rw [← heq clock (by omega)]
  exact hfinal

theorem counter_cycle (b more : Bool) (gap : Nat) (left rest : List Bool) :
    run program
      (0,tapeAt (false::(List.replicate gap false ++ true::more::left)) (b::rest)) (2*gap+7) =
    if more then
      some (.inr (FrameCounterLoader.nextState b,tapeAt
        (false::(List.replicate (gap+1) false ++ false::true::left)) rest))
    else
      some (.inr (15,tapeAt (List.replicate gap false ++ true::false::left) (false::b::rest))) := by
  have h := FrameCounterLoader.counter_cycle FrameCounterLoader.dummy b more gap left rest
  cases more <;> simp only [Bool.false_eq_true,if_false,if_true] at h ⊢ <;>
    exact first_counter_exit _ _ _ (by simp) h

def base (b c : Bool) : Nat := 16 + (if b then 22 else 0) + (if c then 11 else 0)

def tagged (bits : List Bool) : List Bool := bits.flatMap (fun b => [b,true])

@[simp] theorem tagged_nil : tagged [] = [] := rfl
@[simp] theorem tagged_cons (b : Bool) (bs : List Bool) : tagged (b::bs) = b::true::tagged bs := rfl

theorem entry_step (b c : Bool) (left rest : List Bool) :
    run program (FrameCounterLoader.nextState b,tapeAt (false::left) (c::rest)) 1 =
      some (.inr (base b c,tapeAt left (false::true::rest))) := by
  cases b <;> cases c <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,FrameCounterLoader.nextState,
      entry0,entry1,done,block,base,tapeAt,moveTape]

/-- With data already cleared behind the head, the first sweep reaches the
counter or anchor without inspecting any retained suffix. -/
theorem left_gap_step (b c : Bool) (left right : List Bool) :
    run program (base b c,tapeAt (false::left) (false::right)) 1 =
      some (.inr (base b c,tapeAt left (false::false::right))) := by
  cases b <;> cases c <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

theorem left_gap (b c : Bool) (n : Nat) (left right : List Bool) :
    run program (base b c,tapeAt (List.replicate n false ++ left) (false::right)) n =
      some (.inr (base b c,tapeAt left (List.replicate (n+1) false ++ right))) := by
  induction n generalizing right with
  | zero => simp
  | succ n ih =>
    have hfirst := left_gap_step b c (List.replicate n false ++ left) right
    have hn : n+1 = 1+n := by omega
    simp only [List.replicate_succ,List.cons_append]
    rw [hn,run_continue _ _ _ _ _ hfirst,ih]
    congr 3
    simp only [List.replicate_succ,List.cons_append]
    have hrep : List.replicate n false ++ false::right = false::(List.replicate n false ++ right) := by
      have h : List.replicate n false ++ [false] = false::List.replicate n false := by
        rw [← List.replicate_succ',List.replicate_succ]
      simpa [List.append_assoc] using congrArg (fun xs => xs ++ right) h
    rw [hrep]

/-- Cross the last cleared cell and then the first counter-or-anchor one.
Both physical transitions preserve the read bit. -/
theorem enter_ones (b c next : Bool) (left right : List Bool) :
    run program (base b c,tapeAt (true::next::left) (false::right)) 2 =
      some (.inr (base b c+1,tapeAt left (next::true::false::right))) := by
  cases b <;> cases c <;> cases next <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

theorem ones_step (b c next : Bool) (left right : List Bool) :
    run program (base b c+1,tapeAt (next::left) (true::right)) 1 =
      some (.inr (base b c+1,tapeAt left (next::true::right))) := by
  cases b <;> cases c <;> cases next <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

/-- A leftward scan crosses every remaining one and stops on the explicit
zero separator beyond the anchor. The rest of the tape remains untouched. -/
theorem ones_scan (b c : Bool) (n : Nat) (left right : List Bool) :
    run program (base b c+1,tapeAt (List.replicate n true ++ false::left) (true::right)) (n+1) =
      some (.inr (base b c+1,tapeAt left (false::(List.replicate (n+1) true ++ right)))) := by
  induction n generalizing right with
  | zero => simpa using ones_step b c false left right
  | succ n ih =>
    have hfirst := ones_step b c true (List.replicate n true ++ false::left) right
    have hn : n+1+1 = 1+(n+1) := by omega
    simp only [List.replicate_succ,List.cons_append]
    rw [hn,run_continue _ _ _ _ _ hfirst,ih]
    congr 3
    simp only [List.replicate_succ,List.cons_append]
    have hrep : List.replicate n true ++ true::right = true::(List.replicate n true ++ right) := by
      have h : List.replicate n true ++ [true] = true::List.replicate n true := by
        rw [← List.replicate_succ',List.replicate_succ]
      simpa [List.append_assoc] using congrArg (fun xs => xs ++ right) h
    rw [hrep]

/-- After crossing the first one, the remaining unary marks take exactly one
step each before reaching the blank separator behind the anchor. -/
theorem reach_separator (b c : Bool) (n : Nat) (left right : List Bool) :
    run program (base b c+1,
      tapeAt (List.replicate n true ++ false::left).tail
        ((List.replicate n true ++ false::left).head?.getD false::right)) n =
      some (.inr (base b c+1,tapeAt left (false::(List.replicate n true ++ right)))) := by
  cases n with
  | zero => rfl
  | succ n =>
    simpa only [List.replicate_succ,List.cons_append,List.tail_cons,List.head?_cons,Option.getD_some]
      using ones_scan b c n left right

/-- From a bit handoff, reach the buffer separator while retaining the exact
counter, marked next bit, and all higher tape data. -/
theorem bit_to_separator (b c : Bool) (gap marks : Nat) (xs tail rest : List Bool) :
    run program (FrameCounterLoader.nextState b,
      tapeAt (false::(List.replicate gap false ++ List.replicate marks true ++
        true::false::(tagged xs ++ false::false::tail))) (c::rest)) (gap+marks+3) =
      some (.inr (base b c+1,tapeAt (tagged xs ++ false::false::tail)
        (false::(List.replicate marks true ++ true::false::List.replicate gap false ++ true::rest)))) := by
  let buf := tagged xs ++ false::false::tail
  let remaining := List.replicate marks true ++ false::buf
  have hrep : List.replicate marks true ++ true::false::buf = true::remaining := by
    have h : List.replicate marks true ++ [true] = true::List.replicate marks true := by
      rw [← List.replicate_succ',List.replicate_succ]
    dsimp [remaining]
    simpa [List.append_assoc] using congrArg (fun z => z ++ false::buf) h
  have hdecomp : remaining.head?.getD false::remaining.tail = remaining := by
    dsimp [remaining]
    cases marks <;> simp [List.replicate_succ]
  have he := entry_step b c (List.replicate gap false ++ List.replicate marks true ++ true::false::buf) rest
  have hg := left_gap b c gap (List.replicate marks true ++ true::false::buf) (true::rest)
  have hg' : run program (base b c,
      tapeAt (List.replicate gap false ++ List.replicate marks true ++ true::false::buf) (false::true::rest)) gap =
      some (.inr (base b c,tapeAt (true::remaining)
        (false::(List.replicate gap false ++ true::rest)))) := by
    simp only [List.append_assoc] at hg ⊢
    rw [hrep] at hg ⊢
    simpa only [List.replicate_succ,List.cons_append] using hg
  have hi := enter_ones b c (remaining.head?.getD false) remaining.tail
    (List.replicate gap false ++ true::rest)
  rw [hdecomp] at hi
  have hh := reach_separator b c marks buf
    (true::false::List.replicate gap false ++ true::rest)
  have ht : gap+marks+3 = 1+(gap+(2+marks)) := by omega
  rw [ht,run_continue _ _ _ _ _ he,run_continue _ _ _ _ _ hg',run_continue _ _ _ _ _ hi]
  simpa [remaining,buf,List.append_assoc] using hh

/-- The first buffer move crosses the zero separator and places the head on
the tag belonging to the nearest data cell. -/
theorem enter_buffer (b c d tag : Bool) (left right : List Bool) :
    run program (base b c+1,tapeAt (d::tag::left) (false::right)) 2 =
      some (.inr (base b c+3,tapeAt left (tag::d::false::right))) := by
  cases b <;> cases c <;> cases d <;> cases tag <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

/-- When a tag is present, cross it and the next data cell without changing
either one; `next` can be the first virtual blank beyond the buffer. -/
theorem seek_pair (b c next : Bool) (left right : List Bool) :
    run program (base b c+3,tapeAt (next::left) (true::right)) 2 =
      some (.inr (base b c+3,tapeAt left.tail (left.head?.getD false::next::true::right))) := by
  cases left <;> cases b <;> cases c <;> cases next <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

@[simp] theorem tagged_append (xs ys : List Bool) : tagged (xs++ys) = tagged xs ++ tagged ys := by
  simp [tagged,List.flatMap_append]

def returnWord (xs : List Bool) : List Bool := xs.flatMap (fun bit => [true,bit])

@[simp] theorem returnWord_nil : returnWord [] = [] := rfl
@[simp] theorem returnWord_cons (bit : Bool) (xs : List Bool) :
    returnWord (bit::xs) = true::bit::returnWord xs := rfl
@[simp] theorem returnWord_append (xs ys : List Bool) : returnWord (xs++ys) = returnWord xs ++ returnWord ys := by
  simp [returnWord,List.flatMap_append]

/-- Scan all existing tags to the first two-cell blank workspace. The tail
beyond those blank cells is arbitrary and remains entirely untouched. -/
theorem seek_buffer (b c : Bool) (xs tail right : List Bool) :
    run program (base b c+3,tapeAt (tagged xs ++ false::false::tail) (true::right))
      (2*xs.length+2) =
      some (.inr (base b c+3,tapeAt tail
        (false::false::(returnWord xs.reverse ++ true::right)))) := by
  induction xs generalizing right with
  | nil => simpa using seek_pair b c false (false::tail) right
  | cons x xs ih =>
    have hfirst := seek_pair b c x (true::(tagged xs ++ false::false::tail)) right
    simp only [List.tail_cons,List.head?_cons,Option.getD_some] at hfirst
    have ht : 2*(x::xs).length+2 = 2+(2*xs.length+2) := by simp; omega
    simp only [tagged_cons,List.cons_append]
    rw [ht,run_continue _ _ _ _ _ hfirst,ih]
    simp [List.reverse_cons,returnWord_append,List.append_assoc]

/-- Two blank cells become one tagged payload bit. All cells beyond the
workspace are preserved, and the control starts its return scan. -/
theorem write_new (b c : Bool) (tail right : List Bool) :
    run program (base b c+3,tapeAt tail (false::false::right)) 2 =
      some (.inr (base b c+5,tapeAt (b::true::tail) right)) := by
  cases b <;> cases c <;> cases right <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

/-- A return pair crosses a tag and its data bit, retaining both. -/
theorem return_pair (b c d : Bool) (left right : List Bool) :
    run program (base b c+5,tapeAt left (true::d::right)) 2 =
      some (.inr (base b c+5,tapeAt (d::true::left) right)) := by
  cases b <;> cases c <;> cases d <;> cases right <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

theorem return_buffer (b c : Bool) (xs left right : List Bool) :
    run program (base b c+5,tapeAt left (returnWord xs ++ right)) (2*xs.length) =
      some (.inr (base b c+5,tapeAt ((returnWord xs).reverse ++ left) right)) := by
  induction xs generalizing left with
  | nil => simp
  | cons d xs ih =>
    have hfirst := return_pair b c d left (returnWord xs ++ right)
    have ht : 2*(d::xs).length = 2+2*xs.length := by simp; omega
    simp only [returnWord_cons,List.cons_append]
    rw [ht,run_continue _ _ _ _ _ hfirst,ih]
    simp [returnWord_cons,List.reverse_cons,List.append_assoc]

/-- Crossing the buffer separator and the anchor returns to the counter
region, with both bits retained. -/
theorem return_anchor (b c : Bool) (left right : List Bool) :
    run program (base b c+5,tapeAt left (false::true::right)) 2 =
      some (.inr (base b c+8,tapeAt (true::false::left) right)) := by
  cases b <;> cases c <;> cases right <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

/-- One complete insertion: a new bit is appended beyond all existing tags,
using exactly two blank workspace cells and preserving the higher suffix. -/
theorem buffer_append (b c : Bool) (xs tail right : List Bool) :
    run program (base b c+1,tapeAt (tagged xs ++ false::false::tail) (false::right))
      (2*xs.length+4) =
      some (.inr (base b c+5,tapeAt (b::true::tail)
        (returnWord xs.reverse ++ false::right))) := by
  cases xs with
  | nil =>
    have he := enter_buffer b c false false tail right
    have hw := write_new b c tail (false::right)
    simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add,tagged_nil,List.nil_append,
      List.reverse_nil,returnWord_nil] using
      (show run program (base b c+1,tapeAt (false::false::tail) (false::right)) (2+2) = _ by
        rw [run_continue _ _ _ _ _ he,hw])
  | cons x xs =>
    have he := enter_buffer b c x true (tagged xs ++ false::false::tail) right
    have hs := seek_buffer b c xs tail (x::false::right)
    have hw := write_new b c tail (returnWord xs.reverse ++ true::x::false::right)
    have ht : 2*(x::xs).length+4 = 2+((2*xs.length+2)+2) := by simp; omega
    simp only [tagged_cons,List.cons_append]
    rw [ht,run_continue _ _ _ _ _ he,run_continue _ _ _ _ _ hs,hw]
    simp [List.reverse_cons,returnWord_append,List.append_assoc]

theorem reverse_returnWord (xs : List Bool) :
    (returnWord xs).reverse = tagged xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse_cons,List.reverse_append,returnWord_cons,tagged_append,ih,List.append_assoc]

theorem right_one_step (b c : Bool) (left right : List Bool) :
    run program (base b c+8,tapeAt left (true::right)) 1 =
      some (.inr (base b c+8,tapeAt (true::left) right)) := by
  cases b <;> cases c <;> cases right <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

theorem right_ones (b c : Bool) (n : Nat) (left right : List Bool) :
    run program (base b c+8,tapeAt left (List.replicate n true ++ right)) n =
      some (.inr (base b c+8,tapeAt (List.replicate n true ++ left) right)) := by
  induction n generalizing left with
  | zero => simp
  | succ n ih =>
    have hfirst := right_one_step b c left (List.replicate n true ++ right)
    have hn : n+1 = 1+n := by omega
    simp only [List.replicate_succ,List.cons_append]
    rw [hn,run_continue _ _ _ _ _ hfirst,ih]
    have hrep : List.replicate n true ++ true::left = true::(List.replicate n true ++ left) := by
      have h : List.replicate n true ++ [true] = true::List.replicate n true := by
        rw [← List.replicate_succ',List.replicate_succ]
      simpa [List.append_assoc] using congrArg (fun xs => xs ++ left) h
    rw [hrep]

theorem enter_gap (b c : Bool) (left right : List Bool) :
    run program (base b c+8,tapeAt left (false::right)) 1 =
      some (.inr (base b c+9,tapeAt (false::left) right)) := by
  cases b <;> cases c <;> cases right <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

theorem right_zero_step (b c : Bool) (left right : List Bool) :
    run program (base b c+9,tapeAt left (false::right)) 1 =
      some (.inr (base b c+9,tapeAt (false::left) right)) := by
  cases b <;> cases c <;> cases right <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

theorem right_zeros (b c : Bool) (n : Nat) (left right : List Bool) :
    run program (base b c+9,tapeAt left (List.replicate n false ++ right)) n =
      some (.inr (base b c+9,tapeAt (List.replicate n false ++ left) right)) := by
  induction n generalizing left with
  | zero => simp
  | succ n ih =>
    have hfirst := right_zero_step b c left (List.replicate n false ++ right)
    have hn : n+1 = 1+n := by omega
    simp only [List.replicate_succ,List.cons_append]
    rw [hn,run_continue _ _ _ _ _ hfirst,ih]
    have hrep : List.replicate n false ++ false::left = false::(List.replicate n false ++ left) := by
      have h : List.replicate n false ++ [false] = false::List.replicate n false := by
        rw [← List.replicate_succ',List.replicate_succ]
      simpa [List.append_assoc] using congrArg (fun xs => xs ++ left) h
    rw [hrep]

/-- Restore the saved next-input bit and restart the actual counter at the
same head position; the marker itself does not leak into the next cycle. -/
theorem restore_next (b c : Bool) (left right : List Bool) :
    run program (base b c+9,tapeAt (false::left) (true::right)) 2 =
      some (.inr (0,tapeAt (false::left) (c::right))) := by
  cases b <;> cases c <;>
    simp [run,advance,step,program,FrameCounterLoader.rows,entry0,entry1,done,block,base,tapeAt,moveTape]

/-- Return from a newly written tagged bit to the saved input marker and
restore it. The result preserves the complete counter and buffer frame. -/
theorem buffer_to_bit (b c : Bool) (gap marks : Nat) (xs tail rest : List Bool) :
    run program (base b c+5,tapeAt (b::true::tail)
      (returnWord xs.reverse ++ false::(List.replicate marks true ++
        true::false::List.replicate gap false ++ true::rest)))
      (2*xs.length+marks+gap+5) =
      some (.inr (0,tapeAt
        (false::(List.replicate gap false ++ List.replicate marks true ++
          true::false::(tagged xs ++ b::true::tail))) (c::rest))) := by
  let out := tagged xs ++ b::true::tail
  have hrep : List.replicate marks true ++ true::false::List.replicate gap false ++ true::rest =
      true::(List.replicate marks true ++ false::List.replicate gap false ++ true::rest) := by
    have h : List.replicate marks true ++ [true] = true::List.replicate marks true := by
      rw [← List.replicate_succ',List.replicate_succ]
    simpa [List.append_assoc] using congrArg
      (fun z => z ++ false::List.replicate gap false ++ true::rest) h
  have hb := return_buffer b c xs.reverse (b::true::tail)
    (false::(List.replicate marks true ++ true::false::List.replicate gap false ++ true::rest))
  simp only [List.length_reverse,reverse_returnWord,List.reverse_reverse] at hb
  simp only [List.append_assoc] at hrep hb ⊢
  rw [hrep] at hb ⊢
  have ha := return_anchor b c out
    (List.replicate marks true ++ false::List.replicate gap false ++ true::rest)
  have ho := right_ones b c marks (true::false::out) (false::List.replicate gap false ++ true::rest)
  have hg := enter_gap b c (List.replicate marks true ++ true::false::out)
    (List.replicate gap false ++ true::rest)
  have hz := right_zeros b c gap
    (false::(List.replicate marks true ++ true::false::out)) (true::rest)
  have hzero : List.replicate gap false ++ false::(List.replicate marks true ++ true::false::out) =
      false::(List.replicate gap false ++ List.replicate marks true ++ true::false::out) := by
    have h : List.replicate gap false ++ [false] = false::List.replicate gap false := by
      rw [← List.replicate_succ',List.replicate_succ]
    simpa [List.append_assoc] using congrArg
      (fun z => z ++ List.replicate marks true ++ true::false::out) h
  rw [hzero] at hz
  have hs := restore_next b c
    (List.replicate gap false ++ List.replicate marks true ++ true::false::out) rest
  dsimp only [out] at ha ho hg hz hs
  simp only [List.cons_append,List.append_assoc] at hb ha ho hg hz hs ⊢
  have ht : 2*xs.length+marks+gap+5 = (2*xs.length)+(2+(marks+(1+(gap+2)))) := by omega
  rw [ht,run_continue _ _ _ _ _ hb,run_continue _ _ _ _ _ ha,run_continue _ _ _ _ _ ho,
    run_continue _ _ _ _ _ hg,run_continue _ _ _ _ _ hz]
  simpa [out,List.append_assoc] using hs

/-- One entire physical buffer cycle stores `b`, restores the unread bit
`c`, and returns to the counter's initial state. It uses two explicit blank
cells and preserves the arbitrary suffix beyond them. -/
theorem accumulate (b c : Bool) (gap marks : Nat) (xs tail rest : List Bool) :
    run program (FrameCounterLoader.nextState b,
      tapeAt (false::(List.replicate gap false ++ List.replicate marks true ++
        true::false::(tagged xs ++ false::false::tail))) (c::rest))
      (2*gap+2*marks+4*xs.length+12) =
      some (.inr (0,tapeAt
        (false::(List.replicate gap false ++ List.replicate marks true ++
          true::false::(tagged xs ++ b::true::tail))) (c::rest))) := by
  have hs := bit_to_separator b c gap marks xs tail rest
  have ha := buffer_append b c xs tail
    (List.replicate marks true ++ true::false::List.replicate gap false ++ true::rest)
  have hr := buffer_to_bit b c gap marks xs tail rest
  have ht : 2*gap+2*marks+4*xs.length+12 =
      (gap+marks+3)+((2*xs.length+4)+(2*xs.length+marks+gap+5)) := by omega
  rw [ht,run_continue _ _ _ _ _ hs,run_continue _ _ _ _ _ ha,hr]

/-- One real counter-and-buffer iteration. The consumed bit is appended to
the tagged buffer, the next bit and arbitrary higher suffix are retained,
and the counter is ready for its next iteration. -/
theorem counter_and_accumulate (b c : Bool) (gap marks : Nat) (xs tail rest : List Bool) :
    run program (0,tapeAt
      (false::(List.replicate gap false ++ true::true::List.replicate marks true ++
        false::(tagged xs ++ false::false::tail))) (b::c::rest))
      (4*gap+2*marks+4*xs.length+23) =
      some (.inr (0,tapeAt
        (false::(List.replicate (gap+2) false ++ List.replicate marks true ++
          true::false::(tagged xs ++ b::true::tail))) (c::rest))) := by
  have hc := counter_cycle b true gap
    (List.replicate marks true ++ false::(tagged xs ++ false::false::tail)) (c::rest)
  simp only [if_true] at hc
  have hones : true::List.replicate marks true ++ false::(tagged xs ++ false::false::tail) =
      List.replicate marks true ++ true::false::(tagged xs ++ false::false::tail) := by
    have h : List.replicate marks true ++ [true] = true::List.replicate marks true := by
      rw [← List.replicate_succ',List.replicate_succ]
    simpa [List.cons_append,List.append_assoc] using
      (congrArg (fun z => z ++ false::(tagged xs ++ false::false::tail)) h).symm
  have hzeros : List.replicate (gap+1) false ++ false::
      (List.replicate marks true ++ true::false::(tagged xs ++ false::false::tail)) =
      List.replicate (gap+2) false ++
        (List.replicate marks true ++ true::false::(tagged xs ++ false::false::tail)) := by
    have hr : List.replicate (gap+2) false = List.replicate (gap+1) false ++ [false] := by
      rw [show gap+2 = (gap+1)+1 by omega,List.replicate_succ']
    rw [hr]
    simp [List.append_assoc]
  simp only [List.cons_append,List.append_assoc] at hones hzeros hc ⊢
  rw [hones] at hc ⊢
  rw [hzeros] at hc
  have ha := accumulate b c (gap+2) marks xs tail rest
  simp only [List.cons_append,List.append_assoc] at ha
  have ht : 4*gap+2*marks+4*xs.length+23 =
      (2*gap+7)+(2*(gap+2)+2*marks+4*xs.length+12) := by omega
  rw [ht,run_continue _ _ _ _ _ hc,ha]

end Shared.PNP.Record285.FrameBufferLoader
