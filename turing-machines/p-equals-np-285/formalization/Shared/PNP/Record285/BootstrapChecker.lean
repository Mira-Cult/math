import Shared.PNP.Record285.BootstrapSweep

/-! A small proof-checked certificate language for the first bootstrap. The
producer of a certificate is untrusted; each accepted command denotes exact,
finite, event-free physical transitions. -/
namespace Shared.PNP.Record285.BootstrapChecker
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows
open Shared.PNP.Record285.BootstrapSweep

/-- The five active states, with `none` for all other controls. -/
def smallRow (q : Fin 285) (read : Bool) : Option (Row 285) :=
  if q = A then some (if read then ⟨true,.left,C,false⟩ else ⟨true,.right,B,false⟩)
  else if q = B then some (if read then ⟨false,.left,D,false⟩ else ⟨false,.left,A,false⟩)
  else if q = C then some (if read then ⟨true,.right,exit,false⟩ else ⟨true,.left,A,false⟩)
  else if q = D then some (if read then ⟨true,.right,E,false⟩ else ⟨true,.left,B,false⟩)
  else if q = E then some (if read then ⟨false,.right,B,false⟩ else ⟨false,.right,D,false⟩)
  else none

theorem smallRow_sound (M : Machine 285) (rows : Rows M) (q : Fin 285) (read : Bool)
    (r : Row 285) (h : smallRow q read = some r) : M.table.row q read = r := by
  by_cases ha : q = A
  · subst q
    cases read <;> simp [smallRow] at h <;> subst r <;> first | exact rows.A0 | exact rows.A1
  · by_cases hb : q = B
    · subst q
      cases read <;> simp [smallRow,ha] at h <;> subst r <;> first | exact rows.B0 | exact rows.B1
    · by_cases hc : q = C
      · subst q
        cases read <;> simp [smallRow,ha,hb] at h <;> subst r <;> first | exact rows.C0 | exact rows.C1
      · by_cases hd : q = D
        · subst q
          cases read <;> simp [smallRow,ha,hb,hc] at h <;> subst r <;> first | exact rows.D0 | exact rows.D1
        · by_cases he : q = E
          · subst q
            cases read <;> simp [smallRow,ha,hb,hc,hd] at h <;> subst r <;> first | exact rows.E0 | exact rows.E1
          · simp [smallRow,ha,hb,hc,hd,he] at h

def applyRow (r : Row 285) (c : PhysicalNumeric.Config 285) : PhysicalNumeric.Config 285 :=
  match r.move with
  | .left => ⟨r.next,c.head-1,c.left/2,c.left.testBit 0,2*c.right+bitVal r.write⟩
  | .right => ⟨r.next,c.head+1,2*c.left+bitVal r.write,c.right.testBit 0,c.right/2⟩

/-- The entire single-step checker is a ten-row finite table; it does not
interpret the large serialized table during certificate reduction. -/
def single (c : PhysicalNumeric.Config 285) : Option (Nat × PhysicalNumeric.Config 285) :=
  match smallRow c.state c.read with
  | none => none
  | some r => if r.beep then none else some (1,applyRow r c)

theorem single_sound (M : Machine 285) (rows : Rows M) (c d : PhysicalNumeric.Config 285)
    (time : Nat) (h : single c = some (time,d)) : silent M time c = some d := by
  unfold single at h
  cases hr : smallRow c.state c.read with
  | none => simp [hr] at h
  | some r =>
    have heq := smallRow_sound M rows c.state c.read r hr
    cases hb : r.beep with
    | true => simp [hr,hb] at h
    | false =>
      simp [hr,hb] at h
      rcases h with ⟨rfl,rfl⟩
      unfold silent PhysicalNumeric.step
      rw [heq]
      cases hm : r.move <;> simp [hb,applyRow,hm,silent]

inductive Command where
  | single
  | scanA (k : Nat)
  | scanB (k : Nat)
  | scanD (k : Nat)
  | invalid
  deriving DecidableEq

/-- Compact external codes: zero is a single step; all other valid codes
carry the number of extra two-step pairs and one of three sweep kinds. -/
def decode (code : Nat) : Command :=
  if code = 0 then .single else
  match code % 4 with
  | 1 => .scanA (code/4)
  | 2 => .scanB (code/4)
  | 3 => .scanD (code/4)
  | _ => .invalid

def lastBit (side k : Nat) : Bool := (side / (2*4^k)).testBit 0
def tail (side k : Nat) : Nat := side / 4^(k+1)
def patternFast (k : Nat) (last : Bool) (rest : Nat) : Nat :=
  2*rep4 k + 4^k*(2*bitVal last+4*rest)
def pushFast (k digit value : Nat) : Nat := 4^k*value + digit*rep4 k

/-- Check one command and return its exact number of physical transitions. -/
def execute (cmd : Command) (c : PhysicalNumeric.Config 285) : Option (Nat × PhysicalNumeric.Config 285) :=
  match cmd with
  | .invalid => none
  | .single => single c
  | .scanA k =>
    let last := lastBit c.left k
    let rest := tail c.left k
    if c.state = A ∧ c.read = true ∧ c.left = patternFast k last rest then
      some (2*(k+1), ⟨A,c.head-2*(k+1),rest,last,pushFast (k+1) 3 c.right⟩)
    else none
  | .scanB k =>
    let last := lastBit c.left k
    let rest := tail c.left k
    if c.state = B ∧ c.read = true ∧ c.left = patternFast k last rest then
      some (2*(k+1), ⟨B,c.head-2*(k+1),rest,last,pushFast (k+1) 1 c.right⟩)
    else none
  | .scanD k =>
    let last := lastBit c.right k
    let rest := tail c.right k
    if c.state = D ∧ c.read = true ∧ c.right = patternFast k last rest then
      some (2*(k+1), ⟨D,c.head+2*(k+1),pushFast (k+1) 2 c.left,last,rest⟩)
    else none

/-- Every accepted command denotes the exact stated number of silent steps. -/
theorem execute_sound (M : Machine 285) (rows : Rows M) (cmd : Command)
    (c d : PhysicalNumeric.Config 285) (time : Nat)
    (h : execute cmd c = some (time,d)) : silent M time c = some d := by
  cases cmd with
  | invalid => simp [execute] at h
  | single => exact single_sound M rows c d time h
  | scanA k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q
      subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := sweep_A M rows k (lastBit left k) (tail left k) right head
      rw [pattern_closed] at hs
      change silent M _ ⟨A,head,patternFast k (lastBit left k) (tail left k),true,right⟩ = _ at hs
      rw [← hl] at hs
      simpa only [push_closed, pushFast] using hs
    next _ => contradiction
  | scanB k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q
      subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := sweep_B M rows k (lastBit left k) (tail left k) right head
      rw [pattern_closed] at hs
      change silent M _ ⟨B,head,patternFast k (lastBit left k) (tail left k),true,right⟩ = _ at hs
      rw [← hl] at hs
      simpa only [push_closed, pushFast] using hs
    next _ => contradiction
  | scanD k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q
      subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := sweep_D M rows k (lastBit right k) (tail right k) left head
      rw [pattern_closed] at hs
      change silent M _ ⟨D,head,left,true,patternFast k (lastBit right k) (tail right k)⟩ = _ at hs
      rw [← hl] at hs
      simpa only [push_closed, pushFast] using hs
    next _ => contradiction

/-- Verify a finite sequence of compact commands and accumulate exact time. -/
def verify : List Nat → PhysicalNumeric.Config 285 → Option (Nat × PhysicalNumeric.Config 285)
  | [], c => some (0,c)
  | code::rest, c => do
    let (time, next) ← execute (decode code) c
    let (later, final) ← verify rest next
    pure (time+later,final)

/-- The checker is sound for every certificate and every full tape represented
by its initial numeric configuration. -/
theorem verify_sound (M : Machine 285) (rows : Rows M) (codes : List Nat)
    (c d : PhysicalNumeric.Config 285) (time : Nat)
    (h : verify codes c = some (time,d)) : silent M time c = some d := by
  induction codes generalizing c d time with
  | nil =>
    simp only [verify, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  | cons code rest ih =>
    simp only [verify] at h
    cases hfirst : execute (decode code) c with
    | none => simp [hfirst] at h
    | some first =>
      rcases first with ⟨duration,next⟩
      cases hrest : verify rest next with
      | none => simp [hfirst,hrest] at h
      | some last =>
        rcases last with ⟨later,final⟩
        simp only [hfirst,hrest,bind,Option.bind] at h
        rcases h with ⟨rfl,rfl⟩
        rw [silent_add, execute_sound M rows _ _ _ _ hfirst]
        exact ih next d later hrest

/-- Consecutive checked blocks compose without rechecking their data. -/
theorem silent_compose (M : Machine n) (a b c : PhysicalNumeric.Config n) (t u : Nat)
    (h₁ : silent M t a = some b) (h₂ : silent M u b = some c) :
    silent M (t+u) a = some c := by
  rw [silent_add,h₁]
  exact h₂

end Shared.PNP.Record285.BootstrapChecker
