import Shared.PNP.Record285.GrammarCoreZeroPhysical

/-! Finite logical ownership graph, before coalescing 18 logical registers
into 15 physical classes. An ownership move is a paid atomic source action;
its physical implementation is a separately checked finite loop. -/
namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping

inductive Action where
  | inc (i : Nat)
  | dec (i : Nat)
  | half (i : Nat)
  | move (src dst : Nat)
  | beep
  deriving DecidableEq, Repr

structure Row where
  action : Action
  no : Nat
  yes : Nat
  deriving DecidableEq, Repr

structure State where
  index : Nat
  bank : Nat → Nat

def observe : Action → (Nat → Nat) → Bool
  | .dec i, bank => decide (bank i = 0)
  | .half i, bank => decide (bank i % 2 = 0)
  | _, _ => false

def update (action : Action) (bank : Nat → Nat) (j : Nat) : Nat :=
  match action with
  | .inc i => if j = i then bank i + 1 else bank j
  | .dec i => if j = i then bank i - 1 else bank j
  | .half i => if j = i then bank i / 2 else bank j
  | .move src dst => if j = src then 0 else if j = dst then bank dst + bank src else bank j
  | .beep => bank j

def step (rows : Array Row) (s : State) : State × Bool :=
  let row := rows[s.index]?.getD ⟨.beep,0,0⟩
  (⟨if observe row.action s.bank then row.yes else row.no,update row.action s.bank⟩,
    decide (row.action = .beep))

def system (rows : Array Row) : EventSystem State := ⟨⟨0,fun _ => 0⟩,step rows⟩

end Shared.PNP.Record285.OwnershipCore
