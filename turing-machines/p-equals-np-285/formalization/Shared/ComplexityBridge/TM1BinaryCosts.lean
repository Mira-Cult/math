import Shared.ComplexityBridge.TM1GeneralTM0Costs
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-! Quantitative TM1 alphabet reduction using mathlib's actual translation.
One target TM1 block can itself contain many bit moves; the bound below counts
whole target TM1 blocks, not primitive bit operations. -/
namespace Shared.ComplexityBridge.TM1BinaryCosts
open Turing Turing.TM1 Turing.TM1to1
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program (runSteps_add runSteps_front)

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

def maxWrites : TM1.Stmt Γ Λ σ → Nat
  | .move _ q | .load _ q => maxWrites q
  | .write _ q => 1 + maxWrites q
  | .branch _ q r => max (maxWrites q) (maxWrites r)
  | .goto _ | .halt => 0

variable {n : Nat} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
variable (enc0 : enc default = List.Vector.replicate n false) (encdec : ∀ a, dec (enc a) = a)
variable (M : Λ → TM1.Stmt Γ Λ σ)

include encdec

/-- After the initial binary TM1 block, the remaining write dispatches
finish in at most the source statement's maximal write count. -/
theorem aux_bounded (q : TM1.Stmt Γ Λ σ) (v : σ) (L R : ListBlank Γ) :
    ∃ d, d ≤ maxWrites q ∧
      runSteps (TM1.step (TM1to1.tr enc dec M)) d
        (TM1.stepAux (TM1to1.trNormal dec q) v (TM1to1.trTape' enc0 L R)) =
        some (TM1to1.trCfg enc enc0 (TM1.stepAux q v (Tape.mk' L R))) := by
  induction q generalizing v L R with
  | move dir q ih =>
    cases dir <;>
      simp only [trNormal,stepAux_move,stepAux,Tape.move_left_mk',Tape.move_right_mk',
        trTape'_move_left enc0,trTape'_move_right enc0,maxWrites] <;>
      exact ih _ _ _
  | write f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,maxWrites]
    obtain ⟨a,R,rfl⟩ := R.exists_cons
    rw [Tape.mk'_head,ListBlank.head_cons]
    have hi := ih v L (ListBlank.cons (f a v) R)
    obtain ⟨d,hd,hr⟩ := hi
    refine ⟨d+1,by omega,?_⟩
    rw [runSteps_front]
    simp only [TM1.step,TM1to1.tr,TM1.stepAux,Option.bind_some]
    rw [stepAux_write,stepAux_move,trTape'_move_left enc0]
    simpa using hr
  | load f q ih =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,maxWrites,Tape.mk'_head]
    exact ih _ _ _
  | branch f q r ihq ihr =>
    simp only [trNormal,stepAux_read dec enc0 encdec,stepAux,maxWrites,Tape.mk'_head]
    cases hf : f R.head v with
    | false =>
      obtain ⟨d,hd,hr⟩ := ihr v L R
      refine ⟨d,le_trans hd (le_max_right _ _),?_⟩
      simpa [hf,TM1.stepAux] using hr
    | true =>
      obtain ⟨d,hd,hr⟩ := ihq v L R
      refine ⟨d,le_trans hd (le_max_left _ _),?_⟩
      simpa [hf,TM1.stepAux] using hr
  | goto f =>
    refine ⟨0,by simp [maxWrites],?_⟩
    simp [trNormal,stepAux_read dec enc0 encdec,stepAux,trCfg,trTape_mk',runSteps,maxWrites]
  | halt =>
    refine ⟨0,by simp [maxWrites],?_⟩
    simp [trNormal,stepAux,trCfg,trTape_mk',runSteps,maxWrites]

/-- Each live source block becomes a positive target segment with at most
one target block plus one block for each source write. -/
theorem one_block (x x' : TM1.Cfg Γ Λ σ) (q : Λ)
    (hq : x.l = some q) (hstep : TM1.step M x = some x') :
    ∃ d, 0 < d ∧ d ≤ 1 + maxWrites (M q) ∧
      runSteps (TM1.step (TM1to1.tr enc dec M)) d (TM1to1.trCfg enc enc0 x) =
        some (TM1to1.trCfg enc enc0 x') := by
  cases x with
  | mk l v T =>
    cases l with
    | none => simp at hq
    | some q' =>
      simp only [Option.some.injEq] at hq
      subst q'
      have hx : TM1.stepAux (M q) v T = x' := by simpa [TM1.step] using hstep
      obtain ⟨L,R,rfl⟩ := T.exists_mk'
      obtain ⟨d,hd,hr⟩ := aux_bounded enc dec enc0 encdec M (M q) v L R
      refine ⟨d+1,by omega,by omega,?_⟩
      rw [runSteps_front]
      change runSteps (TM1.step (TM1to1.tr enc dec M)) d
        (TM1.stepAux (TM1to1.trNormal dec (M q)) v (TM1to1.trTape enc0 (Tape.mk' L R))) = _
      rw [trTape_mk']
      simpa [hx] using hr

noncomputable def writeLimit (S : Finset Λ) : Nat :=
  1 + S.sup (fun q => maxWrites (M q))

omit encdec in
theorem writeLimit_bound (S : Finset Λ) (q : Λ) (h : q ∈ S) :
    1 + maxWrites (M q) ≤ writeLimit M S := by
  have hm := Finset.le_sup (f := fun q => maxWrites (M q)) h
  dsimp [writeLimit]
  omega

/-- Finite supported TM1 runs have linear overhead in binary TM1 blocks. -/
theorem run_bounded (S : Finset Λ) (hs : TM1.Supports M S) (k : Nat)
    (x x' : TM1.Cfg Γ Λ σ) (hmem : x.l ∈ S.insertNone)
    (hrun : runSteps (TM1.step M) k x = some x') :
    ∃ d, k ≤ d ∧ d ≤ k * writeLimit M S ∧
      runSteps (TM1.step (TM1to1.tr enc dec M)) d (TM1to1.trCfg enc enc0 x) =
        some (TM1to1.trCfg enc enc0 x') := by
  induction k generalizing x with
  | zero =>
    change some x = some x' at hrun
    cases Option.some.inj hrun
    exact ⟨0,by omega,by simp,rfl⟩
  | succ k ih =>
    rw [runSteps_front] at hrun
    cases hstep : TM1.step M x with
    | none => rw [hstep] at hrun; contradiction
    | some mid =>
      rw [hstep] at hrun
      have hnext : mid.l ∈ S.insertNone := TM1.step_supports M hs (by rw [hstep]; rfl) hmem
      cases hq : x.l with
      | none => cases x with | mk l v T => simp only at hq; subst l; contradiction
      | some q =>
        have hqmem : q ∈ S := by rw [hq] at hmem; exact Finset.some_mem_insertNone.1 hmem
        obtain ⟨d,hdpos,hd,hfirst⟩ := one_block enc dec enc0 encdec M x mid q hq hstep
        obtain ⟨e,hepos,he,hrest⟩ := ih mid hnext hrun
        refine ⟨d+e,by omega,?_,?_⟩
        · have hbound := writeLimit_bound M S q hqmem
          rw [Nat.succ_mul]
          omega
        · rw [runSteps_add,hfirst]
          exact hrest

end Shared.ComplexityBridge.TM1BinaryCosts
