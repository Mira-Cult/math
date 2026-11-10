import PASoundness.PAtoCompactVariableTermBaseTransport
import PASoundness.PAtoCompactSuccTermTransport
import PASoundness.PAtoCompactAddTermTransport
import PASoundness.PAtoCompactMulTermTransport
import Mathlib.Tactic.FinCases

/-! Finite K base transport for concrete PA term graphs. This proves
allocator-base alignment, not arithmetic totality, functionality, or the PA
proof interpretation. -/
namespace PASoundness.PAtoCompactAllTermTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactZeroTermBaseTransport PASoundness.PAtoCompactVariableTermBaseTransport

/-- Bidirectional finite K transport under strict name freshness for every
concrete PA term. This declaration is noncomputable and is not claimed as an
executable certificate extractor. Input and output names may coincide. -/
noncomputable def termGraph_base_transport {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) : ∀ b c out,
    out < b → out < c → (∀ a ∈ t.varFinset, v a < b) →
      (∀ a ∈ t.varFinset, v a < c) →
    KDerivation (imp (termGraph v t out b).encode (termGraph v t out c).encode) ×
    KDerivation (imp (termGraph v t out c).encode (termGraph v t out b).encode) := by
  induction t with
  | var a =>
      intro b c out hob hoc hvb hvc
      have hba : v a < b := hvb a (by simp [Term.varFinset])
      have hca : v a < c := hvc a (by simp [Term.varFinset])
      exact ⟨variableTerm_base_forward v a b c out (by omega) (by omega) (by omega) (by omega),
        variableTerm_base_backward v a b c out (by omega) (by omega) (by omega) (by omega)⟩
  | @func l sym ts ih =>
      have child_mem (i : Fin l) (a : α) (ha : a ∈ (ts i).varFinset) :
          a ∈ (Term.func sym ts).varFinset := by
        simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, ha⟩
      cases sym with
      | zero =>
          intro b c out hob hoc hvb hvc
          have ht : ts = Fin.elim0 := by funext i; exact Fin.elim0 i
          subst ts
          exact ⟨zeroTerm_base_forward v b c out (by omega) (by omega),
            zeroTerm_base_backward v b c out (by omega) (by omega)⟩
      | succ =>
          intro b c out hob hoc hvb hvc
          have hvbt : ∀ a ∈ (ts 0).varFinset, v a < b :=
            fun a ha => hvb a (child_mem 0 a ha)
          have hvct : ∀ a ∈ (ts 0).varFinset, v a < c :=
            fun a ha => hvc a (child_mem 0 a ha)
          have hbd := ih 0 (b + 64) (PAtoCompactSuccTermTransport.intermediateBase b c + 64) b
            (by omega) (by unfold PAtoCompactSuccTermTransport.intermediateBase; omega)
            (by intro a ha; have := hvbt a ha; omega)
            (by intro a ha; have := hvbt a ha; unfold PAtoCompactSuccTermTransport.intermediateBase; omega)
          have hcd := ih 0 (c + 64) (PAtoCompactSuccTermTransport.intermediateBase b c + 64) c
            (by omega) (by unfold PAtoCompactSuccTermTransport.intermediateBase; omega)
            (by intro a ha; have := hvct a ha; omega)
            (by intro a ha; have := hvct a ha; unfold PAtoCompactSuccTermTransport.intermediateBase; omega)
          have ht : ![ts 0] = ts := by funext i; fin_cases i; rfl
          simpa only [ht] using PAtoCompactSuccTermTransport.succTerm_base_transport
            v (ts 0) b c out hob hoc hvbt hvct hbd.1 hbd.2 hcd.1 hcd.2
      | add =>
          intro b c out hob hoc hvb hvc
          have hbl : ∀ a ∈ (ts 0).varFinset, v a < b := fun a ha => hvb a (child_mem 0 a ha)
          have hcl : ∀ a ∈ (ts 0).varFinset, v a < c := fun a ha => hvc a (child_mem 0 a ha)
          have hbr : ∀ a ∈ (ts 1).varFinset, v a < b := fun a ha => hvb a (child_mem 1 a ha)
          have hcr : ∀ a ∈ (ts 1).varFinset, v a < c := fun a ha => hvc a (child_mem 1 a ha)
          let d := PAtoCompactAddTermTransport.intermediateBase b c
          have hbld := ih 0 (b + 64) (d + 64) b (by omega) (by dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hbl a ha; omega) (by intro a ha; have := hbl a ha; dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
          have hbrd := ih 1 (b + 64 + termCost (ts 0)) (d + 64 + termCost (ts 0)) (b + 1)
            (by omega) (by dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hbr a ha; omega) (by intro a ha; have := hbr a ha; dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
          have hcld := ih 0 (c + 64) (d + 64) c (by omega) (by dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hcl a ha; omega) (by intro a ha; have := hcl a ha; dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
          have hcrd := ih 1 (c + 64 + termCost (ts 0)) (d + 64 + termCost (ts 0)) (c + 1)
            (by omega) (by dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hcr a ha; omega) (by intro a ha; have := hcr a ha; dsimp [d, PAtoCompactAddTermTransport.intermediateBase]; omega)
          have ht : ![ts 0, ts 1] = ts := by funext i; fin_cases i <;> rfl
          simpa only [ht] using PAtoCompactAddTermTransport.addTerm_base_transport v (ts 0) (ts 1)
            b c out hob hoc hbl hcl hbr hcr hbld.1 hbld.2 hbrd.1 hbrd.2 hcld.1 hcld.2 hcrd.1 hcrd.2
      | mul =>
          intro b c out hob hoc hvb hvc
          have hbl : ∀ a ∈ (ts 0).varFinset, v a < b := fun a ha => hvb a (child_mem 0 a ha)
          have hcl : ∀ a ∈ (ts 0).varFinset, v a < c := fun a ha => hvc a (child_mem 0 a ha)
          have hbr : ∀ a ∈ (ts 1).varFinset, v a < b := fun a ha => hvb a (child_mem 1 a ha)
          have hcr : ∀ a ∈ (ts 1).varFinset, v a < c := fun a ha => hvc a (child_mem 1 a ha)
          let d := PAtoCompactMulTermTransport.intermediateBase b c
          have hbld := ih 0 (b + 64) (d + 64) b (by omega) (by dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hbl a ha; omega) (by intro a ha; have := hbl a ha; dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
          have hbrd := ih 1 (b + 64 + termCost (ts 0)) (d + 64 + termCost (ts 0)) (b + 1)
            (by omega) (by dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hbr a ha; omega) (by intro a ha; have := hbr a ha; dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
          have hcld := ih 0 (c + 64) (d + 64) c (by omega) (by dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hcl a ha; omega) (by intro a ha; have := hcl a ha; dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
          have hcrd := ih 1 (c + 64 + termCost (ts 0)) (d + 64 + termCost (ts 0)) (c + 1)
            (by omega) (by dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
            (by intro a ha; have := hcr a ha; omega) (by intro a ha; have := hcr a ha; dsimp [d, PAtoCompactMulTermTransport.intermediateBase]; omega)
          have ht : ![ts 0, ts 1] = ts := by funext i; fin_cases i <;> rfl
          simpa only [ht] using PAtoCompactMulTermTransport.mulTerm_base_transport v (ts 0) (ts 1)
            b c out hob hoc hbl hcl hbr hcr hbld.1 hbld.2 hbrd.1 hbrd.2 hcld.1 hcld.2 hcrd.1 hcrd.2

theorem termGraph_base_forward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b c out : Nat)
    (hob : out < b) (hoc : out < c)
    (hvb : ∀ a ∈ t.varFinset, v a < b) (hvc : ∀ a ∈ t.varFinset, v a < c) :
    theoremCode (certificate (termGraph_base_transport v t b c out hob hoc hvb hvc).1) =
      imp (termGraph v t out b).encode (termGraph v t out c).encode := certificate_correct _

theorem termGraph_base_backward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b c out : Nat)
    (hob : out < b) (hoc : out < c)
    (hvb : ∀ a ∈ t.varFinset, v a < b) (hvc : ∀ a ∈ t.varFinset, v a < c) :
    theoremCode (certificate (termGraph_base_transport v t b c out hob hoc hvb hvc).2) =
      imp (termGraph v t out c).encode (termGraph v t out b).encode := certificate_correct _

end PASoundness.PAtoCompactAllTermTransport

#print axioms PASoundness.PAtoCompactAllTermTransport.termGraph_base_transport
#print axioms PASoundness.PAtoCompactAllTermTransport.termGraph_base_forward_certificate
#print axioms PASoundness.PAtoCompactAllTermTransport.termGraph_base_backward_certificate
