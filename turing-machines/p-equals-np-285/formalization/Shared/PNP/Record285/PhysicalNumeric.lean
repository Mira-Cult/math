import Shared.PNP.Record285.RelativeTape
import Shared.Beeping.Machines

/-! A full-tape numeric execution model for ordinary binary machines. This
is a step-for-step semantic bridge, not a bootstrap trace or source proof. -/
namespace Shared.PNP.Record285.PhysicalNumeric
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape

structure Config (n : Nat) where
  state : Fin n
  head : Int
  left : Nat
  read : Bool
  right : Nat
  deriving DecidableEq

/-- Both finite streams are low-bit first, adjacent to the head; missing high
bits are blank. -/
def Rel (c : Config n) (physical : Machines.Config n) : Prop :=
  c.state = physical.state ∧ c.head = physical.head ∧
    TapeRel ⟨physical.tape, physical.head, false⟩ c.left c.right c.read

def step (M : Machine n) (c : Config n) : Config n × Bool :=
  let r := M.table.row c.state c.read
  match r.move with
  | .left =>
    (⟨r.next, c.head-1, c.left/2, c.left.testBit 0, 2*c.right+bitVal r.write⟩, r.beep)
  | .right =>
    (⟨r.next, c.head+1, 2*c.left+bitVal r.write, c.right.testBit 0, c.right/2⟩, r.beep)

def initial (M : Machine n) : Config n := ⟨M.start,M.startHead,0,false,0⟩

def system (M : Machine n) : EventSystem (Config n) := ⟨initial M, step M⟩

/-- Changing the orientation of a head-relative view exchanges the two
complete half-tapes and leaves the head cell unchanged. -/
theorem swap_orientation (tape : Int → Bool) (head : Int) (left right : Nat) (read : Bool) :
    TapeRel ⟨tape,head,true⟩ left right read ↔ TapeRel ⟨tape,head,false⟩ right left read := by
  simp only [TapeRel, behindPos, aheadPos, if_true]
  constructor <;> rintro ⟨h,hl,hr⟩ <;> exact ⟨h,hr,hl⟩

/-- Every numeric step agrees with the real physical transition, preserving
the complete two-way tape, absolute head, state and transition flag. -/
theorem step_related (M : Machine n) (c : Config n) (physical : Machines.Config n)
    (h : Rel c physical) :
    Rel (step M c).1 (M.step physical).1 ∧ (step M c).2 = (M.step physical).2 := by
  rcases c with ⟨q,head,left,read,right⟩
  rcases physical with ⟨state,head',tape⟩
  rcases h with ⟨hq,hh,ht⟩
  dsimp only at hq hh ht
  subst state
  subst head'
  have hread : tape head = read := ht.1
  let r := M.table.row q read
  have hphysical := physicalStep_tapeRel ⟨tape,head,false⟩ left right read r.write
  cases hmove : r.move with
  | left =>
    have hh := hphysical true ht
    have hs := (swap_orientation (writeTape ⟨tape,head,false⟩ r.write)
      (head-1) (2*right+bitVal r.write) (left/2) (left.testBit 0)).1 (by
        simpa [physicalStep,behindNumber,aheadNumber,nextRead,Int.sub_eq_add_neg] using hh)
    change (M.table.row q read).move = .left at hmove
    simp only [step, Machine.step, hread, hmove, Move.apply]
    change Rel ⟨r.next,head-1,left/2,left.testBit 0,2*right+bitVal r.write⟩ _ ∧ True
    constructor
    · refine ⟨rfl,rfl,?_⟩
      change TapeRel ⟨writeTape ⟨tape,head,false⟩ r.write,head-1,false⟩ _ _ _
      exact hs
    · trivial
  | right =>
    have hh := hphysical false ht
    have hs : TapeRel ⟨writeTape ⟨tape,head,false⟩ r.write,head+1,false⟩
        (2*left+bitVal r.write) (right/2) (right.testBit 0) := by
      simpa [physicalStep,behindNumber,aheadNumber,nextRead] using hh
    change (M.table.row q read).move = .right at hmove
    simp only [step, Machine.step, hread, hmove, Move.apply]
    change Rel ⟨r.next,head+1,2*left+bitVal r.write,right.testBit 0,right/2⟩ _ ∧ True
    constructor
    · exact ⟨rfl,rfl,hs⟩
    · trivial

/-- Blank-start initial configurations correspond when the physical blank is
zero; all unmentioned tape cells are accounted for by `TapeRel`. -/
theorem initial_related (M : Machine n) (hblank : M.blank = false) : Rel (initial M) M.initial := by
  refine ⟨rfl,rfl,?_⟩
  simp [initial, Machine.initial, TapeRel, hblank]

theorem run_related (M : Machine n) (hblank : M.blank = false) (t : Nat) :
    Rel ((system M).run t) (M.system.run t) := by
  induction t with
  | zero => exact initial_related M hblank
  | succ t ih => exact (step_related M _ _ ih).1

theorem beep_iff (M : Machine n) (hblank : M.blank = false) (t : Nat) :
    (system M).BeepAt t ↔ M.system.BeepAt t := by
  change (step M ((system M).run t)).2 = true ↔ (M.step (M.system.run t)).2 = true
  rw [(step_related M _ _ (run_related M hblank t)).2]

/-- The same step-for-step full-configuration relation from arbitrary related
finite-support starting tapes, not just from blank. -/
theorem run_from_related (M : Machine n) (c : Config n) (physical : Machines.Config n)
    (h : Rel c physical) (t : Nat) :
    Rel ((EventSystem.mk c (step M)).run t) ((EventSystem.mk physical M.step).run t) := by
  induction t with
  | zero => exact h
  | succ t ih => exact (step_related M _ _ ih).1

theorem beep_from_iff (M : Machine n) (c : Config n) (physical : Machines.Config n)
    (h : Rel c physical) (t : Nat) :
    (EventSystem.mk c (step M)).BeepAt t ↔ (EventSystem.mk physical M.step).BeepAt t := by
  change (step M ((EventSystem.mk c (step M)).run t)).2 = true ↔
    (M.step ((EventSystem.mk physical M.step).run t)).2 = true
  rw [(step_related M _ _ (run_from_related M c physical h t)).2]

end Shared.PNP.Record285.PhysicalNumeric
