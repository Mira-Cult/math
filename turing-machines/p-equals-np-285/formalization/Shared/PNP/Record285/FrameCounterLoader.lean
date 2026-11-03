import Shared.PNP.Record285.FrameAnchorLoader

/-! A finite-state unary counter and payload-bit handoff for raw frames. -/
namespace Shared.PNP.Record285.FrameCounterLoader
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)

def rows : Program :=
  [((true,false,1,0),(true,false,2,0)),
   ((false,false,1,0),(true,false,3,0)),
   ((false,false,2,0),(true,false,4,0)),
   ((false,true,5,0),(true,true,7,0)),
   ((false,true,6,0),(true,true,8,0)),
   ((false,true,9,0),(true,true,9,0)),
   ((false,true,10,0),(true,true,10,0)),
   ((false,true,11,0),(false,true,11,0)),
   ((false,true,12,0),(false,true,12,0)),
   ((false,true,9,0),(false,false,15,0)),
   ((false,true,10,0),(true,false,15,0)),
   ((false,true,11,0),(false,true,13,0)),
   ((false,true,12,0),(false,true,14,0))]

def program (p : Program) : Program := link rows p []

def dummy : Program := [((false,true,0,1),(true,true,0,1)),
  ((false,true,0,1),(true,true,0,1)),((false,true,0,1),(true,true,0,1))]

theorem program_valid (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length) :
    valid (program p) = true := by
  have hd : valid (link rows dummy []) = true := by decide
  exact Shared.Codes.FiniteProgramRelink.valid_relink rows dummy p hd hp hlen

theorem left_zero (p : Program) (q : Nat) (hq : q = 1 ∨ q = 2)
    (left right : List Bool) :
    run (program p) (q,tapeAt (false::left) (false::right)) 1 =
      some (.inr (q,tapeAt left (false::false::right))) := by
  rcases hq with rfl | rfl <;>
    simp [run,advance,step,program,link,rows,tapeAt,moveTape]

theorem left_scan (p : Program) (q : Nat) (hq : q = 1 ∨ q = 2)
    (n : Nat) (left right : List Bool) :
    run (program p) (q,tapeAt (List.replicate n false ++ left) (false::right)) n =
      some (.inr (q,tapeAt left (List.replicate (n+1) false ++ right))) := by
  induction n generalizing right with
  | zero => simp
  | succ n ih =>
    have hfirst := left_zero p q hq (List.replicate n false ++ left) right
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

theorem right_zero (p : Program) (q : Nat) (hq : q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12)
    (left right : List Bool) :
    run (program p) (q,tapeAt left (false::right)) 1 =
      some (.inr (q,tapeAt (false::left) right)) := by
  rcases hq with rfl | rfl | rfl | rfl <;> cases right <;>
    simp [run,advance,step,program,link,rows,tapeAt,moveTape]

theorem right_scan (p : Program) (q : Nat) (hq : q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12)
    (n : Nat) (left right : List Bool) :
    run (program p) (q,tapeAt left (List.replicate n false ++ right)) n =
      some (.inr (q,tapeAt (List.replicate n false ++ left) right)) := by
  induction n generalizing left with
  | zero => simp
  | succ n ih =>
    have hfirst := right_zero p q hq left (List.replicate n false ++ right)
    have hn : n+1 = 1+n := by omega
    simp only [List.replicate_succ,List.cons_append]
    rw [hn,run_continue _ _ _ _ _ hfirst,ih]
    have hrep : List.replicate n false ++ false::left = false::(List.replicate n false ++ left) := by
      have h : List.replicate n false ++ [false] = false::List.replicate n false := by
        rw [← List.replicate_succ',List.replicate_succ]
      simpa [List.append_assoc] using congrArg (fun xs => xs ++ left) h
    rw [hrep]

def searchState (b : Bool) : Nat := if b then 2 else 1
def afterPeek (b more : Bool) : Nat :=
  if more then (if b then 8 else 7) else (if b then 6 else 5)
def returnState (b more : Bool) : Nat :=
  if more then (if b then 12 else 11) else (if b then 10 else 9)
def nextState (b : Bool) : Nat := if b then 14 else 13

theorem mark (p : Program) (b : Bool) (left rest : List Bool) :
    run (program p) (0,tapeAt (false::left) (b::rest)) 1 =
      some (.inr (searchState b,tapeAt left (false::true::rest))) := by
  cases b <;> simp [run,advance,step,program,link,rows,searchState,tapeAt,moveTape]

/-- Reach the first one to the left, look at its neighbour, then return to
that one. The neighbour determines counter mark versus anchor. -/
theorem inspect (p : Program) (b more : Bool) (left right : List Bool) :
    run (program p) (searchState b,tapeAt (true::more::left) (false::right)) 3 =
      some (.inr (afterPeek b more,tapeAt (more::left) (true::false::right))) := by
  cases b <;> cases more <;>
    simp [run,advance,step,program,link,rows,searchState,afterPeek,tapeAt,moveTape]

theorem update_counter (p : Program) (b more : Bool) (left right : List Bool) :
    run (program p) (afterPeek b more,tapeAt left (true::false::right)) 1 =
      some (.inr (returnState b more,tapeAt ((!more)::left) (false::right))) := by
  cases b <;> cases more <;>
    simp [run,advance,step,program,link,rows,afterPeek,returnState,tapeAt,moveTape]

theorem finish_next (p : Program) (b : Bool) (left rest : List Bool) :
    run (program p) (returnState b true,tapeAt left (true::rest)) 1 =
      some (.inr (nextState b,tapeAt (false::left) rest)) := by
  cases b <;> cases rest <;>
    simp [run,advance,step,program,link,rows,returnState,nextState,tapeAt,moveTape]

theorem finish_done (p : Program) (b : Bool) (left rest : List Bool) :
    run (program p) (returnState b false,tapeAt (false::left) (true::rest)) 1 =
      some (.inr (15,tapeAt left (false::b::rest))) := by
  cases b <;> simp [run,advance,step,program,link,rows,returnState,tapeAt,moveTape]

/-- A complete counter cycle, for arbitrary finite data on both sides.
If the neighbour beyond the found one is true, one counter mark is erased,
the current payload bit is handed off in the control state, and the head
advances. Otherwise the found one is the anchor: the payload bit is restored,
the counter is exhausted, and the head stops immediately to its left. -/
theorem counter_cycle (p : Program) (b more : Bool) (gap : Nat) (left rest : List Bool) :
    run (program p)
      (0,tapeAt (false::(List.replicate gap false ++ true::more::left)) (b::rest)) (2*gap+7) =
    if more then
      some (.inr (nextState b,tapeAt
        (false::(List.replicate (gap+1) false ++ false::true::left)) rest))
    else
      some (.inr (15,tapeAt (List.replicate gap false ++ true::false::left) (false::b::rest))) := by
  have hs : searchState b = 1 ∨ searchState b = 2 := by cases b <;> simp [searchState]
  have hr : returnState b more = 9 ∨ returnState b more = 10 ∨
      returnState b more = 11 ∨ returnState b more = 12 := by
    cases b <;> cases more <;> simp [returnState]
  have hmark := mark p b (List.replicate gap false ++ true::more::left) rest
  have hleft := left_scan p (searchState b) hs gap (true::more::left) (true::rest)
  have hleft' : run (program p)
      (searchState b,tapeAt (List.replicate gap false ++ true::more::left) (false::true::rest)) gap =
      some (.inr (searchState b,tapeAt (true::more::left)
        (false::(List.replicate gap false ++ true::rest)))) := by
    simpa only [List.replicate_succ,List.cons_append] using hleft
  have hinspect := inspect p b more left (List.replicate gap false ++ true::rest)
  have hupdate := update_counter p b more (more::left) (List.replicate gap false ++ true::rest)
  have hphase : run (program p)
      (0,tapeAt (false::(List.replicate gap false ++ true::more::left)) (b::rest)) (1+gap+3+1) =
      some (.inr (returnState b more,tapeAt ((!more)::more::left)
        (List.replicate (gap+1) false ++ true::rest))) := by
    have ht : 1+gap+3+1 = 1+(gap+(3+1)) := by omega
    rw [ht,run_continue _ _ _ _ _ hmark,run_continue _ _ _ _ _ hleft',
      run_continue _ _ _ _ _ hinspect]
    simpa only [List.replicate_succ,List.cons_append] using hupdate
  have hreturn := right_scan p (returnState b more) hr (gap+1) ((!more)::more::left) (true::rest)
  have ht : 2*gap+7 = (1+gap+3+1)+((gap+1)+1) := by omega
  rw [ht,run_continue _ _ _ _ _ hphase,run_continue _ _ _ _ _ hreturn]
  cases more with
  | false =>
    simp only [Bool.false_eq_true,if_false,Bool.not_false,List.replicate_succ,List.cons_append]
    exact finish_done p b (List.replicate gap false ++ true::false::left) rest
  | true =>
    simp only [if_true,Bool.not_true]
    exact finish_next p b (List.replicate (gap+1) false ++ false::true::left) rest

/-- The three exits are actual entry states of an arbitrary valid finite
continuation, and retain the complete tape for every subsequent step. -/
theorem counter_then_continue (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length)
    (b more : Bool) (gap fuel : Nat) (left rest : List Bool) :
    run (program p)
      (0,tapeAt (false::(List.replicate gap false ++ true::more::left)) (b::rest)) (2*gap+7+fuel) =
    if more then
      Shared.Codes.FiniteProgramLink.shiftStatus 13 (run p
        ((if b then 1 else 0),tapeAt
          (false::(List.replicate (gap+1) false ++ false::true::left)) rest) fuel)
    else
      Shared.Codes.FiniteProgramLink.shiftStatus 13 (run p
        (2,tapeAt (List.replicate gap false ++ true::false::left) (false::b::rest)) fuel) := by
  cases more with
  | false =>
    have h := counter_cycle p b false gap left rest
    simp only [Bool.false_eq_true,if_false] at h ⊢
    rw [run_continue _ _ _ _ _ h]
    have hs := Shared.Codes.FiniteProgramLink.run_shift rows p [] hp
      (2,tapeAt (List.replicate gap false ++ true::false::left) (false::b::rest)) (by omega) fuel
    simpa [program,rows,Shared.Codes.FiniteProgramLink.shiftConfig] using hs
  | true =>
    have h := counter_cycle p b true gap left rest
    simp only [if_true] at h ⊢
    rw [run_continue _ _ _ _ _ h]
    cases b with
    | false =>
      have hs := Shared.Codes.FiniteProgramLink.run_shift rows p [] hp
        (0,tapeAt (false::(List.replicate (gap+1) false ++ false::true::left)) rest) (by omega) fuel
      simpa [program,rows,nextState,Shared.Codes.FiniteProgramLink.shiftConfig] using hs
    | true =>
      have hs := Shared.Codes.FiniteProgramLink.run_shift rows p [] hp
        (1,tapeAt (false::(List.replicate (gap+1) false ++ false::true::left)) rest) (by omega) fuel
      simpa [program,rows,nextState,Shared.Codes.FiniteProgramLink.shiftConfig] using hs

/-- The first cycle on an actual nonempty frame consumes its first payload
bit and clears precisely one of the source's unary counter marks. -/
theorem first_cycle_nonempty (p : Program) (b : Bool) (rest : List Bool) :
    run (program p)
      (0,tapeAt (false::(List.replicate (b::rest).length true ++ [true])) (b::rest)) 7 =
      some (.inr (nextState b,tapeAt
        (false::false::false::true::List.replicate rest.length true) rest)) := by
  have h := counter_cycle p b true 0 (List.replicate rest.length true) rest
  have hrep : List.replicate rest.length true ++ [true] = true::List.replicate rest.length true := by
    rw [← List.replicate_succ',List.replicate_succ]
  simp only [List.length_cons,List.replicate_succ,List.cons_append,hrep]
  simpa only [if_true,Nat.mul_zero,Nat.zero_add,Nat.reduceAdd,List.replicate_zero,
    List.replicate_succ,List.nil_append,List.cons_append] using h

/-- For the zero-length frame the position beyond the anchor is an implicit
blank; the real table detects the exhausted counter and restores that blank. -/
theorem first_cycle_empty (p : Program) :
    run (program p) (0,tapeAt [false,true] []) 7 =
      some (.inr (15,tapeAt [true,false] [false,false])) := by
  simp [run,advance,step,program,link,rows,tapeAt,moveTape]

/-- Blank-start anchor, prefix scan and first payload-cycle, composed into
one finite execution. No source-data projection is used in the handoff. -/
theorem blank_start_first_nonempty (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length)
    (b : Bool) (rest : List Bool) :
    run (FrameAnchorLoader.program (program p)) (initial (CanonicalInput.canonical (b::rest)))
      (2+((b::rest).length+1+7)) =
      some (.inr (3+nextState b,tapeAt
        (false::false::false::true::List.replicate rest.length true) rest)) := by
  have hc := program_valid p hp hlen
  have h := FrameAnchorLoader.anchor_scan_canonical (program p) hc (b::rest) 7
  simp only [List.cons_append] at h
  rw [first_cycle_nonempty] at h
  simpa [Shared.Codes.FiniteProgramLink.shiftStatus,Shared.Codes.FiniteProgramLink.shiftConfig] using h

theorem blank_start_first_empty (p : Program) (hp : valid p = true) (hlen : 3 ≤ p.length) :
    run (FrameAnchorLoader.program (program p)) (initial (CanonicalInput.canonical [])) (2+(0+1+7)) =
      some (.inr (18,tapeAt [true,false] [false,false])) := by
  have hc := program_valid p hp hlen
  have h := FrameAnchorLoader.anchor_scan_canonical (program p) hc [] 7
  simp only [List.length_nil,List.replicate_zero,List.nil_append] at h
  change run (FrameAnchorLoader.program (program p)) _ _ =
    Shared.Codes.FiniteProgramLink.shiftStatus 3 (run (program p) (0,tapeAt [false,true] []) 7) at h
  rw [first_cycle_empty] at h
  simpa [Shared.Codes.FiniteProgramLink.shiftStatus,Shared.Codes.FiniteProgramLink.shiftConfig] using h

end Shared.PNP.Record285.FrameCounterLoader
