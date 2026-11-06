import Shared.ComplexityBridge.TM2PairLengths

namespace Shared.ComplexityBridge.TM2UnaryScale
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where | operand | scratch | output
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.operand,.scratch,.output] (by intro s; cases s <;> simp)
abbrev Index (coefficient : Nat) := Fin (coefficient+1)
abbrev Label (coefficient : Nat) := Index coefficient × Bool

def advance {coefficient : Nat} (i : Index coefficient) (h : i.val < coefficient) : Index coefficient := ⟨i.val+1,by omega⟩

def program (coefficient : Nat) : Label coefficient → Stmt (fun _ : Stack => Bool) (Label coefficient) Bool
  | (i,phase) => if h : i.val < coefficient then
      if phase then
        .pop .scratch (fun _ x => x.isSome)
          (.branch id (.push .operand (fun _ => true) (.goto (fun _ => (i,true))))
            (.goto (fun _ => (advance i h,false))))
      else
        .pop .operand (fun _ x => x.isSome)
          (.branch id (.push .scratch (fun _ => true) (.push .output (fun _ => true) (.goto (fun _ => (i,false)))))
            (.goto (fun _ => (i,true))))
    else .goto (fun _ => (i,phase))

def machine (coefficient : Nat) : Turing.FinTM2 where
  K := Stack
  k₀ := .operand
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label coefficient
  main := (⟨0,by omega⟩,false)
  σ := Bool
  initialState := false
  m := program coefficient

def stackVals (a scratch out : Nat) : Stack → List Bool
  | .operand => List.replicate a true
  | .scratch => List.replicate scratch true
  | .output => List.replicate out true

def cfg {coefficient : Nat} (i : Index coefficient) (phase flag : Bool) (a scratch out : Nat) : (machine coefficient).Cfg :=
  ⟨some (i,phase),flag,stackVals a scratch out⟩

set_option backward.isDefEq.respectTransparency false in
theorem scan_cons {coefficient : Nat} (i : Index coefficient) (hi : i.val < coefficient)
    (flag : Bool) (a scratch out : Nat) :
    (machine coefficient).step (cfg i false flag (a+1) scratch out) =
      some (cfg i false true a (scratch+1) (out+1)) := by
  change some (stepAux (program coefficient (i,false)) flag (stackVals (a+1) scratch out)) = _
  simp only [program,dif_pos hi,ite_false,stepAux]
  change some (Cfg.mk (some (i,false)) true
    (Function.update (Function.update (Function.update (stackVals (a+1) scratch out) .operand (List.replicate a true))
      .scratch (true::List.replicate scratch true)) .output (true::List.replicate out true))) = _
  congr 1; congr 1; funext s; cases s <;> simp [stackVals,Function.update,List.replicate_succ]

set_option backward.isDefEq.respectTransparency false in
theorem scan_nil {coefficient : Nat} (i : Index coefficient) (hi : i.val < coefficient)
    (flag : Bool) (scratch out : Nat) :
    (machine coefficient).step (cfg i false flag 0 scratch out) = some (cfg i true false 0 scratch out) := by
  change some (stepAux (program coefficient (i,false)) flag (stackVals 0 scratch out)) = _
  simp only [program,dif_pos hi,ite_false,stepAux]
  change some (Cfg.mk (some (i,true)) false (Function.update (stackVals 0 scratch out) .operand [])) = _
  congr 1; congr 1; funext s; cases s <;> simp [stackVals,Function.update]

set_option backward.isDefEq.respectTransparency false in
theorem restore_cons {coefficient : Nat} (i : Index coefficient) (hi : i.val < coefficient)
    (flag : Bool) (a scratch out : Nat) :
    (machine coefficient).step (cfg i true flag a (scratch+1) out) = some (cfg i true true (a+1) scratch out) := by
  change some (stepAux (program coefficient (i,true)) flag (stackVals a (scratch+1) out)) = _
  simp only [program,dif_pos hi,ite_true,stepAux]
  change some (Cfg.mk (some (i,true)) true
    (Function.update (Function.update (stackVals a (scratch+1) out) .scratch (List.replicate scratch true))
      .operand (true::List.replicate a true))) = _
  congr 1; congr 1; funext s; cases s <;> simp [stackVals,Function.update,List.replicate_succ]

set_option backward.isDefEq.respectTransparency false in
theorem restore_nil {coefficient : Nat} (i : Index coefficient) (hi : i.val < coefficient)
    (flag : Bool) (a out : Nat) :
    (machine coefficient).step (cfg i true flag a 0 out) = some (cfg (advance i hi) false false a 0 out) := by
  change some (stepAux (program coefficient (i,true)) flag (stackVals a 0 out)) = _
  simp only [program,dif_pos hi,ite_true,stepAux]
  change some (Cfg.mk (some (advance i hi,false)) false (Function.update (stackVals a 0 out) .scratch [])) = _
  congr 1; congr 1; funext s; cases s <;> simp [stackVals,Function.update]

theorem scan_run {coefficient : Nat} (i : Index coefficient) (hi : i.val < coefficient)
    (a : Nat) (flag : Bool) (scratch out : Nat) :
    ∃ f, runSteps (machine coefficient).step a (cfg i false flag a scratch out) =
      some (cfg i false f 0 (scratch+a) (out+a)) := by
  induction a generalizing flag scratch out with
  | zero => exact ⟨flag,by simp [runSteps]⟩
  | succ a ih =>
    obtain ⟨f,h⟩ := ih true (scratch+1) (out+1)
    refine ⟨f,?_⟩
    rw [runSteps_front,scan_cons i hi]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem restore_run {coefficient : Nat} (i : Index coefficient) (hi : i.val < coefficient)
    (scratch : Nat) (flag : Bool) (a out : Nat) :
    ∃ f, runSteps (machine coefficient).step scratch (cfg i true flag a scratch out) =
      some (cfg i true f (a+scratch) 0 out) := by
  induction scratch generalizing flag a with
  | zero => exact ⟨flag,by simp [runSteps]⟩
  | succ scratch ih =>
    obtain ⟨f,h⟩ := ih true (a+1)
    refine ⟨f,?_⟩
    rw [runSteps_front,restore_cons i hi]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- One copy restores the operand and appends its original length to output. -/
theorem copy_phase {coefficient : Nat} (i : Index coefficient) (hi : i.val < coefficient) (a out : Nat) :
    runSteps (machine coefficient).step (2*a+2) (cfg i false false a 0 out) =
      some (cfg (advance i hi) false false a 0 (out+a)) := by
  obtain ⟨f,hscan⟩ := scan_run i hi a false 0 out
  simp only [Nat.zero_add] at hscan
  have hs : runSteps (machine coefficient).step (a+1) (cfg i false false a 0 out) =
      some (cfg i true false 0 a (out+a)) := by
    rw [runSteps_add,hscan]
    change (machine coefficient).step (cfg i false f 0 a (out+a)) = _
    exact scan_nil i hi f a (out+a)
  obtain ⟨g,hrestore⟩ := restore_run i hi a false 0 (out+a)
  simp only [Nat.zero_add] at hrestore
  have hr : runSteps (machine coefficient).step (a+1) (cfg i true false 0 a (out+a)) =
      some (cfg (advance i hi) false false a 0 (out+a)) := by
    rw [runSteps_add,hrestore]
    change (machine coefficient).step (cfg i true g a 0 (out+a)) = _
    exact restore_nil i hi g a (out+a)
  have hn : 2*a+2 = (a+1)+(a+1) := by omega
  rw [hn,runSteps_add,hs]
  exact hr

def index (coefficient j : Nat) (h : j ≤ coefficient) : Index coefficient := ⟨j,by omega⟩

/-- Fixed finite control repeats the preserving copy exactly `j` times. -/
theorem iterate (coefficient j a out : Nat) (hj : j ≤ coefficient) :
    runSteps (machine coefficient).step (j*(2*a+2)) (cfg (index coefficient 0 (by omega)) false false a 0 out) =
      some (cfg (index coefficient j hj) false false a 0 (out+j*a)) := by
  induction j with
  | zero => simp [runSteps,index]
  | succ j ih =>
    have hj' : j ≤ coefficient := by omega
    let i := index coefficient j hj'
    have hi : i.val < coefficient := by dsimp [i,index]; omega
    have hphase := copy_phase i hi a (out+j*a)
    have hnext : advance i hi = index coefficient (j+1) hj := by apply Fin.ext; rfl
    rw [Nat.succ_mul,runSteps_add,ih hj']
    simpa [i,hnext,Nat.succ_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hphase

/-- Exact scaling, including coefficient zero, preserves the operand. -/
theorem scale (coefficient a out : Nat) :
    runSteps (machine coefficient).step (coefficient*(2*a+2))
      (cfg (index coefficient 0 (by omega)) false false a 0 out) =
    some (cfg (index coefficient coefficient (by omega)) false false a 0 (out+coefficient*a)) :=
  iterate coefficient coefficient a out (by omega)

theorem done_stable (coefficient : Nat) (phase flag : Bool) (a scratch out : Nat) :
    (machine coefficient).step (cfg (index coefficient coefficient (by omega)) phase flag a scratch out) =
      some (cfg (index coefficient coefficient (by omega)) phase flag a scratch out) := by
  change some (stepAux (program coefficient (index coefficient coefficient (by omega),phase)) flag (stackVals a scratch out)) = _
  simp only [program,index,Nat.lt_irrefl,↓reduceDIte,stepAux]
  rfl

example : (runSteps (machine 2).step 12 (cfg (index 2 0 (by omega)) false false 2 0 0)).map
    (fun c => c.stk .output) = some (List.replicate 4 true) := by
  change (Option.map (fun c => c.stk .output) (runSteps (machine 2).step 12
    (cfg (index 2 0 (by omega)) false false 2 0 0)) : Option (List Bool)) = _
  decide

end Shared.ComplexityBridge.TM2UnaryScale
