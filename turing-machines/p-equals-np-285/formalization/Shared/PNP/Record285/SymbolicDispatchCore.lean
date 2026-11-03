import Shared.PNP.Record285.IncrementPreparation

/-! A finite symbolic-tape checker for literal control paths. Both tape tails
are arbitrary; a step is accepted only when the next head cell is explicit. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SymbolicDispatch
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail)

def bits : List Bool → Nat → Nat
  | [],tail => tail
  | b::bs,tail => bitVal b+2*bits bs tail

@[simp] theorem bits_read (b : Bool) (bs : List Bool) (tail : Nat) :
    (bits (b::bs) tail).testBit 0 = b := by
  cases b <;> simp [bits,bitVal]

@[simp] theorem bits_drop (b : Bool) (bs : List Bool) (tail : Nat) :
    bits (b::bs) tail / 2 = bits bs tail := by
  cases b <;> simp [bits,bitVal,odd_tail]

structure Config where
  state : Fin 285
  head : Int
  left : List Bool
  read : Bool
  right : List Bool
  deriving DecidableEq, Repr

def denote (c : Config) (origin : Int) (leftTail rightTail : Nat) : PhysicalNumeric.Config 285 :=
  ⟨c.state,origin+c.head,bits c.left leftTail,c.read,bits c.right rightTail⟩

def step (c : Config) : Option Config :=
  let row := NumericTables.target.table.row c.state c.read
  if row.beep then none else
    match row.move with
    | .left => match c.left with
      | [] => none
      | b::bs => some ⟨row.next,c.head-1,bs,b,row.write::c.right⟩
    | .right => match c.right with
      | [] => none
      | b::bs => some ⟨row.next,c.head+1,row.write::c.left,b,bs⟩

def run : Nat → Config → Option Config
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

/-- A checked symbolic step is sound for every choice of both unknown tails. -/
theorem step_sound (c d : Config) (h : step c = some d)
    (origin : Int) (leftTail rightTail : Nat) :
    silent Record285.machine 1 (denote c origin leftTail rightTail) =
      some (denote d origin leftTail rightTail) := by
  cases c with
  | mk state head left read right =>
    unfold step at h
    generalize hr : NumericTables.target.table.row state read = row at h
    cases row with
    | mk write move next beep =>
      cases beep with
      | true => simp at h
      | false =>
        cases move with
        | left =>
          cases left with
          | nil => simp at h
          | cons b bs =>
            simp only [Bool.false_eq_true,if_false,Option.some.injEq] at h
            subst d
            simp only [denote,silent,PhysicalNumeric.step,ArtifactEndpoint.literal_rows,hr,
              Bool.false_eq_true,if_false,bits_read,bits_drop]
            simp [bits,Nat.add_comm,Int.add_sub_assoc]
        | right =>
          cases right with
          | nil => simp at h
          | cons b bs =>
            simp only [Bool.false_eq_true,if_false,Option.some.injEq] at h
            subst d
            simp only [denote,silent,PhysicalNumeric.step,ArtifactEndpoint.literal_rows,hr,
              Bool.false_eq_true,if_false,bits_read,bits_drop]
            simp [bits,Nat.add_comm,Int.add_assoc]

theorem run_sound (n : Nat) (c d : Config) (h : run n c = some d)
    (origin : Int) (leftTail rightTail : Nat) :
    silent Record285.machine n (denote c origin leftTail rightTail) =
      some (denote d origin leftTail rightTail) := by
  induction n generalizing c with
  | zero =>
    simp only [run,Option.some.injEq] at h
    subst d
    rfl
  | succ n ih =>
    simp only [run] at h
    cases hs : step c with
    | none => simp [hs] at h
    | some mid =>
      simp only [hs,Option.bind_some] at h
      rw [show n+1 = 1+n by omega,silent_add,step_sound c mid hs origin leftTail rightTail]
      simp only [Option.bind_some]
      exact ih mid h

/-- Concrete control paths extracted from the literal transition table. The
checker below proves their row-level behavior; extraction itself is untrusted. -/
def codeString : Nat → String
  | 0 => "101111100111010111111111010"
  | 1 => "1011111001111111111111111010100110"
  | 2 => "1011111001111111111100100"
  | 3 => "101111100111111111111111010"
  | 4 => "101111100100101"
  | 5 => "101111111010"
  | 6 => "0"
  | 7 => "1011111001110101110110"
  | 8 => "101110"
  | 9 => "10111110011111111111111010"
  | 10 => "10111110011111111111111111010"
  | 11 => "10111110011111111111111110101011111010"
  | 12 => "101111100111110"
  | 13 => "10111110011010"
  | 14 => "101111100100100"
  | _ => ""

def control (i : Nat) : List Bool := (codeString i).toList.map (fun c => c == '1')

def controlLeft (i : Nat) : List Bool :=
  (control i).reverse ++ [false,true,true] ++ List.replicate 6 false

def dispatchStart (i : Nat) : Config :=
  ⟨IncrementPreparation.dispatch0,-1,(controlLeft i).tail,
    (controlLeft i).headD false,[true,false]⟩

def dispatchEnd (i : Nat) : Config :=
  ⟨IncrementSelector.literalState (i+2),1,false::controlLeft i,false,[]⟩

def dispatchCost (i : Nat) : Nat := 2*(control i).length+18

def dispatchCheck (i : Nat) : Bool :=
  decide (run (dispatchCost i) (dispatchStart i) = some (dispatchEnd i))


end Shared.PNP.Record285.SymbolicDispatch
