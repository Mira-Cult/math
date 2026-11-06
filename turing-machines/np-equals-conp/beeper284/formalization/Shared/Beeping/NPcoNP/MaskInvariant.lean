import Shared.Beeping.RegisterMachine
import Shared.Beeping.NPcoNP.AbstractMasks

/-! A finite-mask invariant checker for an explicitly extended register IR.
`base` uses the shared register semantics verbatim; `half` divides a register
by two and reports success on an odd input. The producer-to-IR translation,
coalescing relation, and any particular invariant certificate remain separate
obligations. -/

namespace Shared.Beeping.NPcoNP.MaskInvariant
open Shared.Beeping.NPcoNP.AbstractMasks
open PASoundness.RegisterMachine

inductive Action (registers : Nat) where
  | base : Primitive registers → Action registers
  | half : Fin registers → Action registers

def Action.execute {registers : Nat} : Action registers → Bank registers → Outcome registers
  | .base op, b => PASoundness.RegisterMachine.execute op b
  | .half r, b => ⟨write b r (b r / 2), !(b r % 2 == 0), []⟩

structure Instruction (registers states : Nat) where
  action : Action registers
  yes : Fin states
  no : Fin states

structure Program (registers states : Nat) where
  code : Vector (Instruction registers states) states
  start : Fin states

def Program.system {registers states : Nat} (p : Program registers states) :
    PASoundness.WordEventSystem (Config registers states) Bool where
  initial := ⟨p.start, fun _ => 0⟩
  step := fun c =>
    let ins := p.code[c.state]
    let out := ins.action.execute c.bank
    (⟨if out.success then ins.yes else ins.no, out.bank⟩, out.output)

abbrev MaskBank (registers : Nat) := Fin registers → Mask

def Covers {registers : Nat} (m : MaskBank registers) (b : Bank registers) : Prop :=
  ∀ r, admits (m r) (b r)

/-- Pointwise over-approximation of a selected action branch. A failed
branch may still give nonempty images for unrelated coordinates; `Enabled`
guards those cases using the tested coordinate. -/
def image {registers : Nat} (a : Action registers) (b : Bool)
    (m : MaskBank registers) (q : Fin registers) : Mask :=
  match a with
  | .base (.inc r) => if q = r then lift incImage (m r) else m q
  | .base (.decNZ r) => if q = r then lift (fun c => decImage c (!b)) (m r) else m q
  | .base (.emit _) => m q
  | .half r => if q = r then lift (fun c => halfImage c (!b)) (m r) else m q

def Enabled {registers : Nat} (a : Action registers) (b : Bool)
    (m : MaskBank registers) : Prop :=
  (∀ q, (m q).Nonempty) ∧
    match a with
    | .base (.inc _) => b = true
    | .base (.decNZ r) => (image a b m r).Nonempty
    | .base (.emit _) => b = true
    | .half r => (image a b m r).Nonempty

theorem execute_image {registers : Nat} (a : Action registers) (b : Bank registers)
    (m : MaskBank registers) (hm : Covers m b) (q : Fin registers) :
    admits (image a (a.execute b).success m q) ((a.execute b).bank q) := by
  cases a with
  | half r =>
    by_cases h : q = r
    · subst q
      simpa [Action.execute, image] using half_mask_sound (m r) (b r) (hm r)
    · simpa [Action.execute, image, write, h] using hm q
  | base op =>
    cases op with
    | inc r =>
      by_cases h : q = r
      · subst q
        simpa [Action.execute, PASoundness.RegisterMachine.execute, image] using
          inc_mask_sound (m r) (b r) (hm r)
      · simpa [Action.execute, PASoundness.RegisterMachine.execute, image, write, h] using hm q
    | decNZ r =>
      by_cases h : q = r
      · subst q
        have hx := dec_mask_sound (m r) (b r) (hm r)
        cases hr : b r with
        | zero => simpa [Action.execute, PASoundness.RegisterMachine.execute, image, hr] using hx
        | succ n => simpa [Action.execute, PASoundness.RegisterMachine.execute, image, hr] using hx
      · cases hr : b r with
        | zero => simpa [Action.execute, PASoundness.RegisterMachine.execute, image, hr, h] using hm q
        | succ n => simpa [Action.execute, PASoundness.RegisterMachine.execute, image, hr, write, h] using hm q
    | emit bit => simpa [Action.execute, PASoundness.RegisterMachine.execute, image] using hm q

theorem execute_enabled {registers : Nat} (a : Action registers) (b : Bank registers)
    (m : MaskBank registers) (hm : Covers m b) : Enabled a (a.execute b).success m := by
  refine ⟨fun q => ⟨category (b q), hm q⟩, ?_⟩
  cases a with
  | half r =>
    exact ⟨category (((Action.half r).execute b).bank r), execute_image (.half r) b m hm r⟩
  | base op =>
    cases op with
    | inc r => rfl
    | decNZ r =>
      exact ⟨category (((Action.base (.decNZ r)).execute b).bank r),
        execute_image (.base (.decNZ r)) b m hm r⟩
    | emit bit => rfl

/-- Every enabled abstract branch has its component images included in the
destination mask. Finite programs and finite masks make this a finite check. -/
def Closed {registers states : Nat} (p : Program registers states)
    (m : Fin states → MaskBank registers) : Prop :=
  ∀ s branch, Enabled p.code[s].action branch (m s) →
    ∀ q, image p.code[s].action branch (m s) q ⊆
      m (if branch then p.code[s].yes else p.code[s].no) q

theorem closed_step {registers states : Nat} (p : Program registers states)
    (m : Fin states → MaskBank registers) (hc : Closed p m)
    (c : Config registers states) (hm : Covers (m c.state) c.bank) :
    Covers (m (p.system.step c).1.state) (p.system.step c).1.bank := by
  intro q
  exact hc c.state _ (execute_enabled _ _ _ hm) q (execute_image _ _ _ hm q)

theorem closed_run {registers states : Nat} (p : Program registers states)
    (m : Fin states → MaskBank registers) (hc : Closed p m)
    (hi : Covers (m p.start) (fun _ => 0)) (t : Nat) :
    Covers (m (p.system.run t).state) (p.system.run t).bank := by
  induction t with
  | zero => exact hi
  | succ t ih => exact closed_step p m hc _ ih

theorem zero_at_state {registers states : Nat} (p : Program registers states)
    (m : Fin states → MaskBank registers) (hc : Closed p m)
    (hi : Covers (m p.start) (fun _ => 0)) (s : Fin states) (q : Fin registers)
    (hz : m s q = {Category.zero}) (t : Nat) (hs : (p.system.run t).state = s) :
    (p.system.run t).bank q = 0 := by
  have h := closed_run p m hc hi t q
  rw [hs, hz] at h
  exact only_zero h

end Shared.Beeping.NPcoNP.MaskInvariant
