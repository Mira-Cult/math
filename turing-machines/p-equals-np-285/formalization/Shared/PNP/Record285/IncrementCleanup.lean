import Shared.PNP.Record285.IncrementTerminal

/-! Event-free lexical cleanup for ordinary increment, including the entire
tape and an arbitrary finite run of trailing control ones and prepared gap. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.IncrementCleanup
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord push_run)
open Shared.PNP.Record285.IncrementPreparation (break0 dispatch0)

def lexical : Fin 285 := ⟨1,by decide⟩
def findGap : Fin 285 := ⟨55,by decide⟩
def clearGap : Fin 285 := ⟨56,by decide⟩
def restore : Fin 285 := ⟨6,by decide⟩

structure Rows (M : Machine 285) where
  lexicalOne : M.table.row lexical true = ⟨false,.left,lexical,false⟩
  lexicalZero : M.table.row lexical false = ⟨true,.right,findGap,false⟩
  findZero : M.table.row findGap false = ⟨false,.right,findGap,false⟩
  findOne : M.table.row findGap true = ⟨false,.right,clearGap,false⟩
  clearOne : M.table.row clearGap true = ⟨false,.right,clearGap,false⟩
  clearZero : M.table.row clearGap false = ⟨false,.left,restore,false⟩
  restoreZero : M.table.row restore false = ⟨true,.left,break0,false⟩
  returnZero : M.table.row break0 false = ⟨false,.left,break0,false⟩
  returnOne : M.table.row break0 true = ⟨true,.left,dispatch0,false⟩

theorem literal_rows : Rows Record285.machine := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem push_add (a b : Nat) (v : Bool) (x : Nat) :
    pushBit (a+b) v x = pushBit b v (pushBit a v x) := by
  induction a generalizing x with
  | zero => simp [pushBit]
  | succ a ih =>
    rw [show (a+1)+b = (a+b)+1 by omega,pushBit,ih,pushBit]

theorem push_false_pattern (n : Nat) (b : Bool) (tail : Nat) :
    pushBit n false (bitVal b+2*tail) = runPattern false n b tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pushBit,pushBit_affine,ih,runPattern]
    simp [bitVal]

theorem pattern_zero_add (n m : Nat) (b : Bool) (tail : Nat) :
    pushBit n false (runPattern false m b tail) = runPattern false (n+m) b tail := by
  induction n with
  | zero => simp [pushBit]
  | succ n ih =>
    rw [pushBit,pushBit_affine,ih,show (n+1)+m = (n+m)+1 by omega,runPattern]
    simp [bitVal]

/-- Uniform run including the zero-length case, with an arbitrary last bit. -/
theorem sweep_left (M : Machine 285) (q : Fin 285) (b w : Bool)
    (row : M.table.row q b = ⟨w,.left,q,false⟩)
    (n : Nat) (last : Bool) (head : Int) (tail right : Nat) :
    silent M n (atLeftWord q head (runPattern b n last tail) right) =
      some (atLeftWord q (head-n) (bitVal last+2*tail) (pushBit n w right)) := by
  cases n with
  | zero => simp [runPattern,pushBit,silent]
  | succ n =>
    have hs := run_sweep_left M q b w row n last tail right head
    have hstart : atLeftWord q head (runPattern b (n+1) last tail) right =
        ⟨q,head,runPattern b n last tail,b,right⟩ := by
      simp only [atLeftWord,runPattern_succ_read,runPattern_succ_tail]
    have hr : (bitVal last+2*tail).testBit 0 = last := by
      simpa only [runPattern] using runPattern_zero_read b last tail
    have ht : (bitVal last+2*tail)/2 = tail := by
      simpa only [runPattern] using runPattern_zero_tail b last tail
    rw [hstart]
    simpa only [atLeftWord,hr,ht,Int.natCast_succ] using hs

theorem sweep_right (M : Machine 285) (q : Fin 285) (b w : Bool)
    (row : M.table.row q b = ⟨w,.right,q,false⟩)
    (n : Nat) (last : Bool) (head : Int) (left tail : Nat) :
    silent M n (atWord q head left (runPattern b n last tail)) =
      some (atWord q (head+n) (pushBit n w left) (bitVal last+2*tail)) := by
  cases n with
  | zero => simp [runPattern,pushBit,silent]
  | succ n =>
    have hs := run_sweep_right M q b w row n last tail left head
    have hstart : atWord q head left (runPattern b (n+1) last tail) =
        ⟨q,head,left,b,runPattern b n last tail⟩ := by
      simp only [atWord,runPattern_succ_read,runPattern_succ_tail]
    have hr : (bitVal last+2*tail).testBit 0 = last := by
      simpa only [runPattern] using runPattern_zero_read b last tail
    have ht : (bitVal last+2*tail)/2 = tail := by
      simpa only [runPattern] using runPattern_zero_tail b last tail
    rw [hstart]
    simpa only [atWord,hr,ht,Int.natCast_succ] using hs

/-- Erase trailing control ones and mark the preceding zero. -/
theorem mark_control (M : Machine 285) (rows : Rows M) (n : Nat)
    (head : Int) (far right : Nat) :
    silent M (n+1) (atLeftWord lexical (head-1) (runPattern true n false far) right) =
      some (atWord findGap (head-n) (2*far+1) (pushBit n false right)) := by
  have hs := sweep_left M lexical true false rows.lexicalOne n false (head-1) far right
  have hlast : silent M 1
      (atLeftWord lexical (head-1-n) (2*far) (pushBit n false right)) =
      some (atWord findGap (head-n) (2*far+1) (pushBit n false right)) := by
    simp only [atLeftWord,even_bit,even_tail,silent,PhysicalNumeric.step,rows.lexicalZero,
      Bool.false_eq_true,if_false,bitVal,if_true,atWord]
    have hh : head-1-(n:Int)+1 = head-(n:Int) := by omega
    rw [hh]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  exact hlast

/-- Combined zeros written by the rightward cleanup, with the marked control
bit and all earlier tape retained. -/
theorem cleared_stack (z g far : Nat) :
    pushBit g false (2*pushBit z false (2*far+1)) =
      2*runPattern false (z+g) true far := by
  have hone (x : Nat) : 2*x = pushBit 1 false x := by simp [pushBit,bitVal]
  rw [hone, ← push_add z 1 false, ← push_add (z+1) g false,
    show (z+1)+g = (z+g)+1 by omega, push_add (z+g) 1 false]
  simp only [bitVal,pushBit,Bool.false_eq_true,if_false,Nat.add_zero]
  have hp := push_false_pattern (z+g) true far
  simp only [bitVal,if_true] at hp
  rw [show 2*far+1 = 1+2*far by omega,hp]

/-- Clear the prepared gap, restore the bank anchor, and start the return. -/
theorem clear_prepared (M : Machine 285) (rows : Rows M) (z g : Nat)
    (head : Int) (far tail : Nat) :
    silent M (z+g+3)
      (atWord findGap head (2*far+1) (runPattern false z true (runPattern true g false tail))) =
      some (atLeftWord break0 (head+z+g-1) (runPattern false (z+g) true far) (1+4*tail)) := by
  have hs := sweep_right M findGap false false rows.findZero z true head (2*far+1)
    (runPattern true g false tail)
  have hfirst : silent M 1
      (atWord findGap (head+z) (pushBit z false (2*far+1))
        (1+2*runPattern true g false tail)) =
      some (atWord clearGap (head+z+1) (2*pushBit z false (2*far+1))
        (runPattern true g false tail)) := by
    simp only [atWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,rows.findOne,
      Bool.false_eq_true,if_false,bitVal,if_false,Nat.add_zero]
  have herase := sweep_right M clearGap true false rows.clearOne g false (head+z+1)
    (2*pushBit z false (2*far+1)) tail
  have hlast : silent M 2
      (atWord clearGap (head+z+1+g) (2*runPattern false (z+g) true far) (2*tail)) =
      some (atLeftWord break0 (head+z+g-1) (runPattern false (z+g) true far) (1+4*tail)) := by
    simp only [atWord,atLeftWord,even_bit,even_tail,silent,PhysicalNumeric.step,
      rows.clearZero,rows.restoreZero,Bool.false_eq_true,if_false,bitVal,if_true,Nat.add_zero]
    have hh : head+(z:Int)+1+(g:Int)-1-1 = head+(z:Int)+(g:Int)-1 := by omega
    have hr : 2*(2*tail)+1 = 1+4*tail := by omega
    simp only [hh,hr]
  rw [show z+g+3 = z+(1+(g+2)) by omega,silent_add,hs]
  simp only [Option.bind_some,bitVal,if_true]
  rw [silent_add,hfirst]
  simp only [Option.bind_some]
  rw [silent_add,herase]
  simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add,cleared_stack]
  exact hlast

/-- The return scanner reaches the dispatcher just left of the new marker. -/
theorem return_dispatch (M : Machine 285) (rows : Rows M) (n : Nat)
    (head : Int) (far tail : Nat) :
    silent M (n+1)
      (atLeftWord break0 head (runPattern false n true far) (1+4*tail)) =
      some (atLeftWord dispatch0 (head-(n+1)) far
        (1+2*runPattern false n true (2*tail))) := by
  have hs := sweep_left M break0 false false rows.returnZero n true head far (1+4*tail)
  have hlast : silent M 1
      (atLeftWord break0 (head-n) (1+2*far) (pushBit n false (1+4*tail))) =
      some (atLeftWord dispatch0 (head-(n+1)) far
        (1+2*runPattern false n true (2*tail))) := by
    have hp : pushBit n false (1+4*tail) = runPattern false n true (2*tail) := by
      rw [show 1+4*tail = bitVal true+2*(2*tail) by simp [bitVal]; omega,
        push_false_pattern]
    simp only [atLeftWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,rows.returnOne,
      Bool.false_eq_true,if_false,bitVal,if_true,hp]
    have hh : head-(n:Int)-1 = head-((n:Int)+1) := by omega
    have hr : 2*runPattern false n true (2*tail)+1 =
        1+2*runPattern false n true (2*tail) := by omega
    simp only [hh,hr]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,if_true]
  exact hlast

/-- A complete cleanup: erase the finite trailing control run, restore the
unary-bank anchor and gap, and return to the dispatcher without an event. -/
theorem cleanup (M : Machine 285) (rows : Rows M) (n gap : Nat)
    (head : Int) (far tail : Nat) :
    silent M (3*n+2*gap+9)
      (atLeftWord lexical (head-1) (runPattern true n false far)
        (4*runPattern true (gap+1) false tail)) =
      some (atLeftWord dispatch0 (head-n-2) far
        (1+2*runPattern false (n+gap+2) true (2*tail))) := by
  have hm := mark_control M rows n head far (4*runPattern true (gap+1) false tail)
  have hw : pushBit n false (4*runPattern true (gap+1) false tail) =
      runPattern false (n+2) true (runPattern true gap false tail) := by
    have hb : 4*runPattern true (gap+1) false tail =
        runPattern false 2 true (runPattern true gap false tail) := by
      simp only [runPattern,bitVal,if_true,Bool.false_eq_true,if_false,Nat.zero_add]
      omega
    rw [hb,pattern_zero_add]
  rw [hw] at hm
  have hc := clear_prepared M rows (n+2) gap (head-n) far tail
  have hr := return_dispatch M rows (n+gap+2) (head+gap+1) far tail
  rw [show 3*n+2*gap+9 = (n+1)+((n+2+gap+3)+(n+gap+2+1)) by omega,
    silent_add,hm]
  simp only [Option.bind_some]
  rw [silent_add,hc]
  simp only [Option.bind_some]
  simp only [Int.natCast_add,show ((2:Nat):Int) = 2 by rfl] at hr ⊢
  have hmid : head-(n:Int)+((n:Int)+2)+(gap:Int)-1 = head+(gap:Int)+1 := by omega
  have hend : head+(gap:Int)+1-((n:Int)+(gap:Int)+2+1) = head-(n:Int)-2 := by omega
  rw [show n+2+gap = n+gap+2 by omega,hmid]
  rw [hend] at hr
  exact hr

theorem literal_cleanup (n gap : Nat) (head : Int) (far tail : Nat) :
    silent Record285.machine (3*n+2*gap+9)
      (atLeftWord lexical (head-1) (runPattern true n false far)
        (4*runPattern true (gap+1) false tail)) =
      some (atLeftWord dispatch0 (head-n-2) far
        (1+2*runPattern false (n+gap+2) true (2*tail))) :=
  cleanup Record285.machine literal_rows n gap head far tail

theorem literal_cleanup_physical (n gap : Nat) (head : Int) (far tail : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (atLeftWord lexical (head-1) (runPattern true n false far)
      (4*runPattern true (gap+1) false tail)) physical) :
    Rel (atLeftWord dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*tail)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (3*n+2*gap+9)) ∧
    ∀ t, t < 3*n+2*gap+9 →
      ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _ (literal_cleanup n gap head far tail)

/-- Split a control word, read from right to left, at its first zero. -/
def peel : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::xs => (0,xs)
  | true::xs => let p := peel xs; (p.1+1,p.2)

theorem peel_bits (xs : List Bool) (hasZero : false ∈ xs) (tail : Nat) :
    SymbolicDispatch.bits xs tail =
      runPattern true (peel xs).1 false (SymbolicDispatch.bits (peel xs).2 tail) := by
  induction xs with
  | nil => simp at hasZero
  | cons b bs ih =>
    cases b with
    | false => simp [peel,SymbolicDispatch.bits,runPattern,bitVal]
    | true =>
      have hz : false ∈ bs := by simpa using hasZero
      have h := ih hz
      cases hp : peel bs with
      | mk n rest =>
        simp only [hp] at h
        simp only [peel,hp,SymbolicDispatch.bits,bitVal,if_true,runPattern]
        rw [h]

theorem path_has_zero (code : List Bool) : false ∈ SymbolicDispatch.pathLeft code := by
  simp [SymbolicDispatch.pathLeft]

theorem path_peel_bits (code : List Bool) (leftTail : Nat) :
    SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail =
      runPattern true (peel (SymbolicDispatch.pathLeft code)).1 false
        (SymbolicDispatch.bits (peel (SymbolicDispatch.pathLeft code)).2 leftTail) :=
  peel_bits _ (path_has_zero code) leftTail

/-- Clearing a trailing run of ones and changing the next zero to one is
binary successor on the complete low-bit-first control word. -/
theorem run_carry (n far : Nat) :
    runPattern true n false far + 1 = runPattern false n true far := by
  induction n with
  | zero => simp [runPattern,bitVal,Nat.add_comm]
  | succ n ih =>
    simp only [runPattern,bitVal,if_true,Bool.false_eq_true,if_false,Nat.zero_add]
    omega

theorem control_binary_successor (xs : List Bool) (hasZero : false ∈ xs) (tail : Nat) :
    SymbolicDispatch.bits xs tail + 1 =
      runPattern false (peel xs).1 true (SymbolicDispatch.bits (peel xs).2 tail) := by
  rw [peel_bits xs hasZero tail,run_carry]

/-- If a word contains a zero, peeling never touches any appended suffix. -/
theorem peel_append (xs ys : List Bool) (hasZero : false ∈ xs) :
    peel (xs++ys) = ((peel xs).1,(peel xs).2++ys) := by
  induction xs with
  | nil => simp at hasZero
  | cons b bs ih =>
    cases b with
    | false => simp [peel]
    | true =>
      have hz : false ∈ bs := by simpa using hasZero
      have h := ih hz
      simp only [List.cons_append,peel]
      rw [h]

theorem path_peel_preserves_root (code : List Bool) (hasZero : false ∈ code) :
    peel (SymbolicDispatch.pathLeft code) =
      ((peel code.reverse).1,(peel code.reverse).2 ++ [false,true,true] ++ List.replicate 6 false) := by
  have hz : false ∈ code.reverse := by simpa using hasZero
  simpa only [SymbolicDispatch.pathLeft,List.append_assoc] using
    peel_append code.reverse ([false,true,true] ++ List.replicate 6 false) hz

def frozenHasZero (i : Nat) : Bool := decide (false ∈ SymbolicDispatch.control i)

theorem frozen_has_zero_all : (List.range 15).all frozenHasZero = true := by decide

theorem frozen_has_zero (i : Nat) (hi : i < 15) : false ∈ SymbolicDispatch.control i := by
  have h := List.all_eq_true.mp frozen_has_zero_all i (List.mem_range.mpr hi)
  simpa only [frozenHasZero,decide_eq_true_eq] using h

/-- For each frozen example, cleanup changes a code bit to the right of the
root, so the complete `110` root and its six-zero margin are preserved. -/
theorem frozen_cleanup_preserves_root (i : Nat) (hi : i < 15) :
    peel (SymbolicDispatch.pathLeft (SymbolicDispatch.control i)) =
      ((peel (SymbolicDispatch.control i).reverse).1,
        (peel (SymbolicDispatch.control i).reverse).2 ++ [false,true,true] ++ List.replicate 6 false) :=
  path_peel_preserves_root _ (frozen_has_zero i hi)

/-- The entire ordinary increment, from a clean terminal through lexical
cleanup back to the dispatcher. The checker premise certifies its control
word; the returned word is explicit and preserves both arbitrary tape tails. -/
theorem terminal_through_cleanup (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (code : List Bool)
    (hcode : SymbolicDispatch.pathCheck code before.length = true)
    (head : Int) (leftTail retained : Nat) :
    let left := SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail
    let bank := IncrementSelector.blocksBits (before++[target])
      (IncrementShift.suffixBits suffix retained)
    let selected := gap::(before++[target])
    let n := (peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    silent Record285.machine steps
      ⟨IncrementPreparation.terminal before.length,head,left,false,
        2*runPattern false gap true (2*bank)⟩ =
      some (atLeftWord dispatch0 (head-n-2) far
        (1+2*runPattern false (n+gap+2) true (2*updated))) := by
  dsimp only
  let left := SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail
  let n := (peel (SymbolicDispatch.pathLeft code)).1
  let far := SymbolicDispatch.bits (peel (SymbolicDispatch.pathLeft code)).2 leftTail
  let updated := IncrementSelector.blocksBits (before++[target+1])
    (IncrementSelector.blocksBits suffix retained)
  let selected := gap::(before++[target])
  let firstSteps := (2*gap+5) + SymbolicDispatch.pathCost code +
    2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
  have ht := IncrementTerminal.literal_terminal_increment_code gap target before suffix hindex
    code hcode head leftTail retained
  have hleft : left = runPattern true n false far := path_peel_bits code leftTail
  have hbank : IncrementSelector.blocksBits (gap::(before++[target+1]))
      (IncrementSelector.blocksBits suffix retained) = runPattern true (gap+1) false updated := by
    rw [IncrementMeaning.blocks_cons,IncrementReturn.push_run]
  dsimp only at ht
  dsimp [left] at hleft
  conv at ht =>
    rhs
    rw [hleft,hbank]
  rw [silent_add,ht]
  simp only [Option.bind_some]
  exact literal_cleanup n gap head far updated

/-- Entire ordinary increment on the physical tape, including cleanup and
absence of marked events for the whole positive finite interval. -/
theorem terminal_through_cleanup_physical (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (code : List Bool)
    (hcode : SymbolicDispatch.pathCheck code before.length = true)
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementPreparation.terminal before.length,head,
      SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))⟩ physical) :
    let selected := gap::(before++[target])
    let n := (peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    Rel (atLeftWord dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _
    (terminal_through_cleanup gap target before suffix hindex code hcode head leftTail retained)

/-- The path-check premise is discharged for one frozen control word at each
of the fifteen physical field indices. -/
theorem terminal_through_cleanup_frozen (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (head : Int) (leftTail retained : Nat) :
    let code := SymbolicDispatch.control before.length
    let left := SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail
    let bank := IncrementSelector.blocksBits (before++[target])
      (IncrementShift.suffixBits suffix retained)
    let selected := gap::(before++[target])
    let n := (peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    silent Record285.machine steps
      ⟨IncrementPreparation.terminal before.length,head,left,false,
        2*runPattern false gap true (2*bank)⟩ =
      some (atLeftWord dispatch0 (head-n-2) far
        (1+2*runPattern false (n+gap+2) true (2*updated))) :=
  terminal_through_cleanup gap target before suffix hindex
    (SymbolicDispatch.control before.length)
    (SymbolicDispatch.frozen_path_check before.length hindex) head leftTail retained

theorem terminal_through_cleanup_frozen_physical (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementPreparation.terminal before.length,head,
      SymbolicDispatch.bits (SymbolicDispatch.pathLeft (SymbolicDispatch.control before.length)) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))⟩ physical) :
    let code := SymbolicDispatch.control before.length
    let selected := gap::(before++[target])
    let n := (peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    Rel (atLeftWord dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _
    (terminal_through_cleanup_frozen gap target before suffix hindex head leftTail retained)

theorem cleanup_steps_positive (n gap : Nat) : 0 < 3*n+2*gap+9 := by omega

theorem terminal_cleanup_steps_positive (gap target : Nat) (before suffix : List Nat) (code : List Bool) :
    0 < ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost (gap::(before++[target]))+IncrementShift.cost suffix)) +
        (3*(peel (SymbolicDispatch.pathLeft code)).1+2*gap+9) := by omega

end Shared.PNP.Record285.IncrementCleanup
