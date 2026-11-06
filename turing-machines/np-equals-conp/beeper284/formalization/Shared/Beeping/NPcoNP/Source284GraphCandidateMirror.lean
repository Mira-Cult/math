import Shared.Beeping.NPcoNP.Source284GraphCandidateReady

/-! The candidate evaluator block is checked against the reference block
under an explicit register permutation and program-counter shift. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateMirror
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
abbrev Bank := PASoundness.RegisterMachine.Bank 12
abbrev Cfg := PASoundness.RegisterMachine.Config 12 185

def swapIndex (i : Fin 12) : Fin 12 := if i=3 then 6 else if i=6 then 3 else i

def swapBank (b : Bank) : Bank := fun i => b (swapIndex i)

theorem swapIndex_involution (i : Fin 12) : swapIndex (swapIndex i)=i := by
  fin_cases i <;> decide

theorem swapBank_involution (b : Bank) : swapBank (swapBank b)=b := by
  funext i
  simp [swapBank,swapIndex_involution]

theorem swapBank_write (b : Bank) (i : Fin 12) (v : Nat) :
    swapBank (write b i v) = write (swapBank b) (swapIndex i) v := by
  funext k
  fin_cases i <;> fin_cases k <;> simp [swapBank,swapIndex,write]

def shiftState (q : Fin 185) : Fin 185 := ⟨(q.val+91)%185,Nat.mod_lt _ (by decide)⟩
def mapCfg (c : Cfg) : Cfg := ⟨shiftState c.state,swapBank c.bank⟩

@[simp] theorem swapBank_read (b : Bank) (i : Fin 12) : swapBank b (swapIndex i)=b i := by
  simp [swapBank,swapIndex_involution]

def swapAction : MaskInvariant.Action 12 → MaskInvariant.Action 12
  | .base (.inc i) => .base (.inc (swapIndex i))
  | .base (.decNZ i) => .base (.decNZ (swapIndex i))
  | .base (.emit bit) => .base (.emit bit)
  | .half i => .half (swapIndex i)

def mapInstruction (i : MaskInvariant.Instruction 12 185) : MaskInvariant.Instruction 12 185 :=
  ⟨swapAction i.action,shiftState i.yes,shiftState i.no⟩

/-- The register permutation commutes with every supported action, including
its branch and ordered output. -/
theorem action_equivariant (a : MaskInvariant.Action 12) (b : Bank) :
    (swapAction a).execute (swapBank b) =
      let out := a.execute b
      ⟨swapBank out.bank,out.success,out.output⟩ := by
  cases a with
  | half i =>
    simp [swapAction,MaskInvariant.Action.execute,swapBank_read,swapBank_write]
  | base a =>
    cases a with
    | inc i =>
      simp [swapAction,MaskInvariant.Action.execute,execute,swapBank_read,swapBank_write]
    | decNZ i =>
      cases h : b i <;>
        simp [swapAction,MaskInvariant.Action.execute,execute,swapBank_read,swapBank_write,h]
    | emit bit => rfl

/-- Kernel-checked row-for-row identity of the two 35-row blocks. -/
theorem block_instruction (k : Fin 35) :
    target.code.get ⟨141+k.val,by omega⟩ = mapInstruction (target.code.get ⟨50+k.val,by omega⟩) := by
  fin_cases k <;> rfl

/-- Each matching instruction preserves the complete ordered output word. -/
theorem block_step (k : Fin 35) (b : Bank) :
    target.system.step ⟨⟨141+k.val,by omega⟩,swapBank b⟩ =
      let r := target.system.step ⟨⟨50+k.val,by omega⟩,b⟩
      (mapCfg r.1,r.2) := by
  have h := block_instruction k
  change target.code[(⟨141+k.val,by omega⟩ : Fin 185)] =
    mapInstruction (target.code[(⟨50+k.val,by omega⟩ : Fin 185)]) at h
  simp only [MaskInvariant.Program.system] at *
  rw [h]
  simp only [mapInstruction,action_equivariant]
  cases hs : ((target.code.get ⟨50+k.val,by omega⟩).action.execute b).success <;>
    simp [mapCfg,hs]

/-- Relate one graph transition whenever the reference PC lies in the
checked block. -/
theorem step_related (c : Cfg) (hlo : 50 ≤ c.state.val) (hhi : c.state.val < 85) :
    target.system.step (mapCfg c) =
      (mapCfg (target.system.step c).1,(target.system.step c).2) := by
  cases c with
  | mk q b =>
    change 50 ≤ q.val at hlo
    change q.val < 85 at hhi
    let k : Fin 35 := ⟨q.val-50,by omega⟩
    have hq : (⟨50+k.val,by omega⟩ : Fin 185) = q := by
      apply Fin.ext
      dsimp [k]
      omega
    have hs : shiftState q = ⟨141+k.val,by omega⟩ := by
      apply Fin.ext
      simp only [shiftState,Fin.val_mk]
      dsimp [k]
      have hv : q.val+91 < 185 := by omega
      rw [Nat.mod_eq_of_lt hv]
      omega
    have h := block_step k b
    rw [hq] at h
    simpa [mapCfg,hs] using h

/-- A finite run that remains in the reference block has exactly the same
ordered word and mapped final configuration in the candidate block. -/
theorem block_advance (c : Cfg) (n : Nat)
    (h : ∀ t < n, 50 ≤ (target.system.advance c t).state.val ∧
      (target.system.advance c t).state.val < 85) :
    target.system.advance (mapCfg c) n = mapCfg (target.system.advance c n) ∧
      target.system.wordFrom (mapCfg c) n = target.system.wordFrom c n := by
  induction n with
  | zero => constructor <;> rfl
  | succ n ih =>
    have hp : ∀ t < n, 50 ≤ (target.system.advance c t).state.val ∧
        (target.system.advance c t).state.val < 85 := by
      intro t ht
      exact h t (by omega)
    have hi := ih hp
    have hr := h n (by omega)
    have hs := step_related (target.system.advance c n) hr.1 hr.2
    constructor
    · simp only [WordEventSystem.advance,hi.1,hs,Prod.fst]
    · simp only [WordEventSystem.wordFrom,hi.1,hi.2,hs,Prod.snd]

/-- Once the separately stated block-residence obligation is established,
the checked bounded reference evaluator transfers to the candidate block.
This theorem does not assert that obligation. -/
theorem conditional_candidate_evaluate (b : Bank) (description clock : Nat)
    (c : Source284Relative.Config)
    (hstay : ∀ t < Source284GraphEvaluator.evalCost description c clock,
      50 ≤ (target.system.advance
        ⟨50,Source284GraphApplyRow.regs b c.left c.right c.state description 0 0 clock⟩ t).state.val ∧
      (target.system.advance
        ⟨50,Source284GraphApplyRow.regs b c.left c.right c.state description 0 0 clock⟩ t).state.val < 85) :
    target.system.advance
      (mapCfg ⟨50,Source284GraphApplyRow.regs b c.left c.right c.state description 0 0 clock⟩)
      (Source284GraphEvaluator.evalCost description c clock) =
      mapCfg ⟨50,Source284GraphApplyRow.regs b
        (Source284Relative.run description c clock).left
        (Source284Relative.run description c clock).right
        (Source284Relative.run description c clock).state description 0 0 0⟩ ∧
    target.system.wordFrom
      (mapCfg ⟨50,Source284GraphApplyRow.regs b c.left c.right c.state description 0 0 clock⟩)
      (Source284GraphEvaluator.evalCost description c clock) = [] := by
  have h := block_advance _ _ hstay
  have hr := Source284GraphEvaluator.evaluate b description c clock
  constructor
  · rw [h.1,hr.1]
  · rw [h.2,hr.2]

end Shared.Beeping.NPcoNP.Source284GraphCandidateMirror
