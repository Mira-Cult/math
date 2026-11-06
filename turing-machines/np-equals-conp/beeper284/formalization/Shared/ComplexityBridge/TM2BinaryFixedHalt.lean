import Shared.ComplexityBridge.TM2BinaryPostCosts
import Shared.ComplexityBridge.TM0FiniteReindex

/-! Fixed halted control of the TM2 → binary TM0 translation. This file
establishes the control boundary only; it does not link a physical table or
prove a failure-complete evaluator. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BinaryFixedHalt
open Turing TM2to1
open Shared.ComplexityBridge.TM2BinaryPostCosts

variable (tm : FinTM2) {width : Nat}
variable (enc : Alphabet tm → List.Vector Bool width)
variable (dec : List.Vector Bool width → Alphabet tm)

/-- The final translated TM0 control is independent of the output stack. -/
def control : TM1to0.Λ' (TM1to1.tr enc dec (TM2to1.tr tm.m)) :=
  (none, tm.initialState)

/-- The TM2-to-TM1 relation fixes both the halted label and local state. -/
theorem related_control (output : List (tm.Γ tm.k₁))
    (mid : TM1.Cfg (Alphabet tm) (Labels tm) tm.σ)
    (hrel : TrCfg (Turing.haltList tm output) mid) :
    mid.l = none ∧ mid.var = tm.initialState := by
  cases hrel
  exact ⟨rfl, rfl⟩

/-- Both translations preserve the fixed halted control. -/
theorem translated_control
    (enc0 : enc default = List.Vector.replicate width false)
    (output : List (tm.Γ tm.k₁))
    (mid : TM1.Cfg (Alphabet tm) (Labels tm) tm.σ)
    (hrel : TrCfg (Turing.haltList tm output) mid) :
    (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m))
      (TM1to1.trCfg enc enc0 mid)).q = control tm enc dec := by
  obtain ⟨hl,hv⟩ := related_control tm output mid hrel
  cases mid with
  | mk l v tape =>
    simp only at hl hv
    simp [TM1to0.trCfg,TM1to1.trCfg,control,hl,hv]

/-- The TM0 row is halted on both possible scanned bits. -/
theorem control_halts (b : Bool) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m)) (control tm enc dec) b = none := by
  rfl

/-- The already constructed finite support contains the fixed halt control,
including when no input has a successful run. -/
theorem control_mem_support (alphabet : ∀ k, Fintype (tm.Γ k)) :
    control tm enc dec ∈ support0 tm alphabet enc dec := by
  let _ := tm.kFin
  let _ := alphabet
  let _ := tm.σFin
  classical
  dsimp only [support0, control, TM1to0.trStmts]
  apply Finset.mem_product.mpr
  exact ⟨Finset.none_mem_insertNone, Finset.mem_univ _⟩

/-- The concrete reindexed finite TM0 row returns the current head bit for
both tape symbols. Its index is fixed by the machine and the finite support,
not by the output. -/
theorem finite_halt_row (alphabet : ∀ k, Fintype (tm.Γ k)) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
    let S := support0 tm alphabet enc dec
    let hs := support0_correct tm alphabet enc dec
    let q := Shared.ComplexityBridge.TM0FiniteReindex.index M S hs (control tm enc dec)
    let N := Shared.ComplexityBridge.TM0FiniteReindex.machine M S hs
    ∀ t : Shared.Codes.FinitePrograms.Tape,
      Shared.Codes.FinitePrograms.step (Shared.ComplexityBridge.TM0FiniteProgram.program N)
        (Shared.ComplexityBridge.TM0FiniteProgram.mainIndex q,t) = some (.inl t.2.1) := by
  dsimp only
  let _ : Inhabited tm.Λ := ⟨tm.main⟩
  let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
  let S := support0 tm alphabet enc dec
  let hs := support0_correct tm alphabet enc dec
  let q := Shared.ComplexityBridge.TM0FiniteReindex.index M S hs (control tm enc dec)
  let N := Shared.ComplexityBridge.TM0FiniteReindex.machine M S hs
  intro t
  have hrow : N q t.2.1 = none := by
    change Shared.ComplexityBridge.TM0FiniteReindex.machine M S hs
      (Shared.ComplexityBridge.TM0FiniteReindex.index M S hs (control tm enc dec)) t.2.1 = none
    rw [Shared.ComplexityBridge.TM0FiniteReindex.machine_row M S hs
      (control tm enc dec) (control_mem_support tm enc dec alphabet)]
    have hm : M (control tm enc dec) t.2.1 = none :=
      control_halts tm enc dec t.2.1
    simp [hm]
  have h := Shared.ComplexityBridge.TM0FiniteProgram.halted_step N q t hrow
  simpa [Shared.Codes.FinitePrograms.run,Shared.Codes.FinitePrograms.advance] using h

end Shared.ComplexityBridge.TM2BinaryFixedHalt
