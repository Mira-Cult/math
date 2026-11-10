import PASoundness.PAtoCompactFirstFactorSuccessorSharedOutput
import PASoundness.PAtoCompactLiteralCutAdditionAtSuccessorNames

/-! Retain one output for the literal cut, ordinary addition and the
first-factor successor product. This fixed-label construction is not yet
the guarded PA axiom or the right-factor multiplication successor law. -/
namespace PASoundness.PAtoCompactFirstFactorSuccessorAddShared

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactFirstFactorSuccessorSharedOutput
open PASoundness.PAtoCompactLiteralCutAdditionAtSuccessorNames

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- One output witnesses the guarded cut, its corresponding addition, and
new product. The old product, both factor domains, old-output domain and raw
first-factor successor are antecedents of the finite K proof. -/
noncomputable def shared_successor_add_output : KDerivation
    (imp (domainAt 300 204).encode
      (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
          (existsCode 45 (andF (domainAt 300 45)
            (andF (literalCutAt 300 32 30 45)
              (andF (addAt 300 32 30 45) (mulAt 300 205 30 45)))).encode)))))) := by
  let D := (domainAt 300 204).encode
  let G := (domainAt 300 30).encode
  let O := (domainAt 300 32).encode
  let S := successorCode 204 205 208
  let M := (mulAt 300 204 30 32).encode
  let W := andF (domainAt 300 45)
    (andF (literalCutAt 300 32 30 45) (mulAt 300 205 30 45))
  let R := andF (domainAt 300 45)
    (andF (literalCutAt 300 32 30 45)
      (andF (addAt 300 32 30 45) (mulAt 300 205 30 45)))
  let E := Formula.ex 45 R
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [M,S,O,G,D]
  have hm : Context Γ M := .head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 45 W.encode) :=
    .mp hm (.mp hs (.mp ho (.mp hg (.mp hd (.closed shared_successor_output)))))
  have hRbind : 45 ∉ R.binders := by decide
  have hRE : KDerivation (imp R.encode E.encode) := by
    simpa [E, Formula.encode, existsCode] using existsIntroduce 45 R hRbind
  have hp : Context Γ (imp W.encode E.encode) := by
    apply Context.deduction
    let Δ := W.encode :: Γ
    have hW : Context Δ W.encode := .head _ _
    have hW' : Context Δ (both (domainAt 300 45).encode
        (both (literalCutAt 300 32 30 45).encode (mulAt 300 205 30 45).encode)) := by
      simpa [W, andF, Formula.not, Formula.encode, both, neg] using hW
    have h45 := Context.conjunctionLeft hW'
    have hrest := Context.conjunctionRight hW'
    have hcut := Context.conjunctionLeft hrest
    have hmul := Context.conjunctionRight hrest
    have hadd : Context Δ (addAt 300 32 30 45).encode :=
      .mp hcut (.mp (Context.under ho _) (.closed for_successor_output))
    have hR : Context Δ R.encode := by
      have h := Context.conjunctionIntro h45
        (Context.conjunctionIntro hcut (Context.conjunctionIntro hadd hmul))
      simpa [R, andF, Formula.not, Formula.encode, both, neg] using h
    exact .mp hR (.closed hRE)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 45 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases hm' : h = M
    · subst h; exact (mulAt 300 204 30 32).vacuity 45 (by decide)
    by_cases hs' : h = S
    · subst h; exact (namedSuccessor 204 205 208).vacuity 45 (by decide)
    by_cases ho' : h = O
    · subst h; exact (domainAt 300 32).vacuity 45 (by decide)
    by_cases hg' : h = G
    · subst h; exact (domainAt 300 30).vacuity 45 (by decide)
    have hd' : h = D := by simpa [hm',hs',ho',hg'] using hh
    subst h; exact (domainAt 300 204).vacuity 45 (by decide)
  have hall := Context.generalize 45 hv hp
  have hEv : KDerivation (imp E.encode (allCode 45 E.encode)) :=
    free_vacuity 45 E (by simp [E, Formula.free])
  have he : Context Γ E.encode := Context.existsElim hEv hall hw
  exact he

theorem shared_successor_add_output_certificate :
    theoremCode (certificate shared_successor_add_output) =
      imp (domainAt 300 204).encode
        (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
          (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
            (existsCode 45 (andF (domainAt 300 45)
              (andF (literalCutAt 300 32 30 45)
                (andF (addAt 300 32 30 45) (mulAt 300 205 30 45)))).encode))))) :=
  certificate_correct _

end PASoundness.PAtoCompactFirstFactorSuccessorAddShared

#print axioms PASoundness.PAtoCompactFirstFactorSuccessorAddShared.shared_successor_add_output
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorAddShared.shared_successor_add_output_certificate
