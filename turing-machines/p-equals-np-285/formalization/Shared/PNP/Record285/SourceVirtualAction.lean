import Shared.PNP.Record285.SourceUnarySkip
import Shared.PNP.Record285.OwnershipExpandedLoop

/-! Exact positive-time graph segments for the selected virtual action. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceVirtualAction
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceUnarySkip

def doubleCycle (src dst : Nat) (bank : Nat → Nat) : Nat → Nat :=
  update (.inc dst) (update (.inc dst) (update (.dec src) bank))

def doubleMove (src dst : Nat) (bank : Nat → Nat) : Nat → Nat := fun j =>
  if j = src then 0 else if j = dst then bank dst + 2*bank src else bank j

theorem doubleCycle_read (src dst j : Nat) (bank : Nat → Nat) (hne : src ≠ dst) :
    doubleCycle src dst bank j =
      if j = src then bank src-1 else if j = dst then bank dst+2 else bank j := by
  by_cases hs : j = src
  · subst j; simp [doubleCycle,update,hne]
  · by_cases hd : j = dst
    · subst j; simp [doubleCycle,update,Ne.symm hne]
    · simp [doubleCycle,update,hs,hd]

theorem doubleMove_zero (src dst : Nat) (bank : Nat → Nat) (hz : bank src = 0) :
    doubleMove src dst bank = bank := by
  funext j
  by_cases hs : j = src
  · subst j; simp [doubleMove,hz]
  · by_cases hd : j = dst
    · subst j; simp [doubleMove,hs,hz]
    · simp [doubleMove,hs,hd]

theorem doubleMove_cycle (src dst : Nat) (bank : Nat → Nat)
    (hne : src ≠ dst) (hp : 0 < bank src) :
    doubleMove src dst (doubleCycle src dst bank) = doubleMove src dst bank := by
  funext j
  have hv := doubleCycle_read src dst j bank hne
  have hs := doubleCycle_read src dst src bank hne
  have hd := doubleCycle_read src dst dst bank hne
  simp only [if_true] at hs
  simp only [if_neg (Ne.symm hne),if_true] at hd
  by_cases hjs : j = src
  · simp [doubleMove,hjs]
  · by_cases hjd : j = dst
    · simp only [doubleMove,if_neg hjs,if_pos hjd]
      rw [hs,hd]
      omega
    · simp only [doubleMove,if_neg hjs,if_neg hjd]
      simpa [hjs,hjd] using hv

theorem double_cycle_run (rows : Array Row) (head a b exit src dst : Nat)
    (bank : Nat → Nat) (hhead : rows[head]? = some ⟨.dec src,a,exit⟩)
    (ha : rows[a]? = some ⟨.inc dst,b,b⟩)
    (hb : rows[b]? = some ⟨.inc dst,head,head⟩) (hp : 0 < bank src) :
    Silent rows ⟨head,bank⟩ ⟨head,doubleCycle src dst bank⟩ 3 := by
  have hn : bank src ≠ 0 := by omega
  let b1 := update (.dec src) bank
  let b2 := update (.inc dst) b1
  have h1 : step rows ⟨head,bank⟩ = (⟨a,b1⟩,false) := by simp [step,hhead,observe,hn,b1]
  have h2 : step rows ⟨a,b1⟩ = (⟨b,b2⟩,false) := by simp [step,ha,observe,b2]
  have h3 : step rows ⟨b,b2⟩ = (⟨head,doubleCycle src dst bank⟩,false) := by
    simp [step,hb,observe,doubleCycle,b2,b1]
  have h := silent_trans rows _ _ _ 1 1 (silent_one rows _ _ h1) (silent_one rows _ _ h2)
  have h := silent_trans rows _ _ _ 2 1 h (silent_one rows _ _ h3)
  simpa using h

/-- A decrement/double-increment loop terminates on every finite bank and
implements an exact, silent doubled transfer. -/
theorem double_move_run (rows : Array Row) (head a b exit src dst n : Nat) (bank : Nat → Nat)
    (hhead : rows[head]? = some ⟨.dec src,a,exit⟩)
    (ha : rows[a]? = some ⟨.inc dst,b,b⟩)
    (hb : rows[b]? = some ⟨.inc dst,head,head⟩)
    (hne : src ≠ dst) (hval : bank src = n) :
    Silent rows ⟨head,bank⟩ ⟨exit,doubleMove src dst bank⟩ (3*n+1) := by
  induction n generalizing bank with
  | zero =>
    have hid := dec_at_zero src bank hval
    have hresult := doubleMove_zero src dst bank hval
    have hs : step rows ⟨head,bank⟩ = (⟨exit,bank⟩,false) := by
      simp [step,hhead,observe,hval,hid]
    simpa [hresult] using silent_one rows ⟨head,bank⟩ ⟨exit,bank⟩ hs
  | succ n ih =>
    have hp : 0 < bank src := by omega
    have hcycle := double_cycle_run rows head a b exit src dst bank hhead ha hb hp
    have hsrc : doubleCycle src dst bank src = n := by
      have hh := doubleCycle_read src dst src bank hne
      simp only [if_true] at hh
      omega
    have hrest := ih (doubleCycle src dst bank) hsrc
    rw [doubleMove_cycle src dst bank hne hp] at hrest
    have h := silent_trans rows _ _ _ 3 (3*n+1) hcycle hrest
    have htime : 3*(n+1)+1 = 3+(3*n+1) := by omega
    simpa only [htime] using h

/-- Split the decoded action into write and direction bits; register 3 then
contains the higher action bits. -/
def actionHalves (bank : Nat → Nat) : Nat → Nat :=
  let first := update (.half 3) bank
  let withWrite := if bank 3 % 2 = 0 then first else update (.inc 5) first
  update (.half 3) withWrite

def halfTime (bank : Nat → Nat) : Nat := if bank 3 % 2 = 0 then 2 else 3

def directionOdd (bank : Nat → Nat) : Prop := (bank 3/2)%2 ≠ 0

/-- The graph rows implementing the action decoder, parameterized by their
position so the reference and candidate evaluators share one proof. -/
structure ActionLayout (rows : Array Row) (base : Nat) : Prop where
  r0 : rows[base]? = some ⟨.half 3,base+1,base+2⟩
  r1 : rows[base+1]? = some ⟨.inc 5,base+2,base+2⟩
  r2 : rows[base+2]? = some ⟨.half 3,base+3,base+8⟩
  r3 : rows[base+3]? = some ⟨.dec 2,base+4,base+6⟩
  r4 : rows[base+4]? = some ⟨.inc 5,base+5,base+5⟩
  r5 : rows[base+5]? = some ⟨.inc 5,base+3,base+3⟩
  r6 : rows[base+6]? = some ⟨.dec 19,base+7,base+11⟩
  r7 : rows[base+7]? = some ⟨.inc 2,base+6,base+6⟩
  r8 : rows[base+8]? = some ⟨.dec 19,base+9,base+11⟩
  r9 : rows[base+9]? = some ⟨.inc 5,base+10,base+10⟩
  r10 : rows[base+10]? = some ⟨.inc 5,base+8,base+8⟩
  r11 : rows[base+11]? = some ⟨.dec 5,base+12,base+13⟩
  r12 : rows[base+12]? = some ⟨.inc 19,base+11,base+11⟩

theorem referenceActionLayout : ActionLayout originalRows 56 := by
  constructor <;> decide

theorem candidateActionLayout : ActionLayout originalRows 133 := by
  constructor <;> decide

/-- Both action bits are consumed in finite silent time, for every bank. -/
theorem action_halves_generic (rows : Array Row) (base : Nat)
    (layout : ActionLayout rows base) (bank : Nat → Nat) :
    Silent rows ⟨base,bank⟩
      ⟨if (bank 3/2)%2 = 0 then base+8 else base+3,actionHalves bank⟩ (halfTime bank) := by
  let first := update (.half 3) bank
  let withWrite := if bank 3 % 2 = 0 then first else update (.inc 5) first
  let last := update (.half 3) withWrite
  have h3 : withWrite 3 = bank 3/2 := by
    by_cases he : bank 3%2=0 <;> simp [withWrite,he,first,update]
  have hfirst : Silent rows ⟨base,bank⟩ ⟨base+2,withWrite⟩ (if bank 3%2=0 then 1 else 2) := by
    by_cases he : bank 3%2=0
    · have hs : step rows ⟨base,bank⟩ = (⟨base+2,withWrite⟩,false) := by
        simp [step,layout.r0,observe,he,withWrite,first]
      simpa [he] using silent_one rows _ _ hs
    · have hs : step rows ⟨base,bank⟩ = (⟨base+1,first⟩,false) := by
        simp [step,layout.r0,observe,he,first]
      have ht : step rows ⟨base+1,first⟩ = (⟨base+2,withWrite⟩,false) := by
        simp [step,layout.r1,observe,withWrite,he]
      have h := silent_trans rows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)
      simpa [he] using h
  have hsecond : step rows ⟨base+2,withWrite⟩ =
      (⟨if (bank 3/2)%2 = 0 then base+8 else base+3,last⟩,false) := by
    simp [step,layout.r2,observe,h3,last]
  have h := silent_trans rows _ _ _ _ 1 hfirst (silent_one _ _ _ hsecond)
  by_cases he : bank 3%2=0 <;> simpa [halfTime,actionHalves,he,last,withWrite,first] using h

theorem action_halves_run (bank : Nat → Nat) :
    Silent originalRows ⟨56,bank⟩
      ⟨if (bank 3/2)%2 = 0 then 64 else 59,actionHalves bank⟩ (halfTime bank) := by
  simpa using action_halves_generic originalRows 56 referenceActionLayout bank

/-- Both possible direction branches, before moving the constructed left tape
back from register 5. -/
def actionMoved (bank : Nat → Nat) : Nat → Nat :=
  let h := actionHalves bank
  if (bank 3/2)%2 = 0 then doubleMove 19 5 h
  else update (.move 19 2) (doubleMove 2 5 h)

def actionCore (bank : Nat → Nat) : Nat → Nat := update (.move 5 19) (actionMoved bank)

/-- Both direction branches terminate for any graph with this checked layout. -/
theorem action_core_generic (rows : Array Row) (base : Nat)
    (layout : ActionLayout rows base) (bank : Nat → Nat) :
    ∃ duration, 0 < duration ∧ Silent rows ⟨base,bank⟩ ⟨base+13,actionCore bank⟩ duration := by
  have hfirst := action_halves_generic rows base layout bank
  have hmove : ∃ d, 0 < d ∧
      Silent rows ⟨if (bank 3/2)%2=0 then base+8 else base+3,actionHalves bank⟩
        ⟨base+11,actionMoved bank⟩ d := by
    by_cases he : (bank 3/2)%2=0
    · have h := double_move_run rows (base+8) (base+9) (base+10) (base+11) 19 5 (actionHalves bank 19)
        (actionHalves bank) layout.r8 layout.r9 layout.r10 (by decide) rfl
      refine ⟨3*(actionHalves bank 19)+1,by omega,?_⟩
      simpa [actionMoved,he] using h
    · let mid := doubleMove 2 5 (actionHalves bank)
      have hdouble := double_move_run rows (base+3) (base+4) (base+5) (base+6) 2 5 (actionHalves bank 2)
        (actionHalves bank) layout.r3 layout.r4 layout.r5 (by decide) rfl
      have hswap := expanded_move_run rows (base+6) (base+7) (base+11) 19 2 (mid 19) mid
        layout.r6 layout.r7 (by decide) rfl
      have h := silent_trans rows _ _ _ _ _ hdouble hswap
      refine ⟨(3*(actionHalves bank 2)+1)+(2*(mid 19)+1),by omega,?_⟩
      simpa [actionMoved,he,mid] using h
  obtain ⟨d,hd,hmove⟩ := hmove
  have hfinish := expanded_move_run rows (base+11) (base+12) (base+13) 5 19 (actionMoved bank 5)
    (actionMoved bank) layout.r11 layout.r12 (by decide) rfl
  have h := silent_trans rows _ _ _ _ _ hfirst hmove
  have h := silent_trans rows _ _ _ _ _ h hfinish
  refine ⟨halfTime bank+d+(2*(actionMoved bank 5)+1),by omega,?_⟩
  exact h

/-- The original reference action reaches row 69 in finite silent time. -/
theorem action_core_run (bank : Nat → Nat) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨56,bank⟩ ⟨69,actionCore bank⟩ duration := by
  simpa using action_core_generic originalRows 56 referenceActionLayout bank

def actionLeft (bank : Nat → Nat) : Nat := if (bank 3/2)%2 = 0 then bank 19 else bank 2
def actionRight (bank : Nat → Nat) : Nat := if (bank 3/2)%2 = 0 then bank 2 else bank 19

/-- The full data effect of both direction branches, including arbitrary
initial scratch and every register outside the finite active set. -/
theorem action_core_values (bank : Nat → Nat) :
    actionCore bank 3 = bank 3/4 ∧ actionCore bank 2 = actionRight bank ∧
    actionCore bank 19 = bank 5 + bank 3%2 + 2*actionLeft bank ∧
    actionCore bank 5 = 0 ∧
    (∀ j, j ≠ 3 → j ≠ 2 → j ≠ 19 → j ≠ 5 → actionCore bank j = bank j) := by
  have hdiv : bank 3/2/2 = bank 3/4 := by omega
  by_cases he : bank 3%2=0
  · by_cases hd : (bank 3/2)%2=0 <;>
      simp [actionCore,actionMoved,actionHalves,actionLeft,actionRight,update,doubleMove,he,hd,hdiv] <;>
      intro j h3 h2 h19 h5 <;> simp [h3,h2,h19,h5]
  · have ho : bank 3%2=1 := by omega
    by_cases hd : (bank 3/2)%2=0 <;>
      simp [actionCore,actionMoved,actionHalves,actionLeft,actionRight,update,doubleMove,ho,hd,hdiv] <;>
      intro j h3 h2 h19 h5 <;> simp [h3,h2,h19,h5]

end Shared.PNP.Record285.SourceVirtualAction
