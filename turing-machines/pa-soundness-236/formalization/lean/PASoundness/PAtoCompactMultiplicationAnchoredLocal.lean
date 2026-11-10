import PASoundness.PAtoCompactLiteralCutArbitraryTotality
import PASoundness.PAtoCompactMultiplicationSourceCandidateSuccessor
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactZeroSuccessor

/-! A conditional K reduction of the local multiplication successor witness
 to an anchored-product graph extension proof. The addition result is chosen
using the literal old product as cut. The graph-extension proof remains an
explicit input; this is not multiplication totality or a PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationAnchoredLocal
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactLiteralCutArbitraryTotality
open PASoundness.PAtoCompactMultiplicationSourceCandidateSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The still-open graph-extension obligation: if 32 is a product of 204 and
30, 205 is the successor of 204, and 45 is an anchored sum of 32 and 30, then
45 is the product of 205 and 30. All guards are literal K antecedents. -/
def graphExtensionCode : Nat :=
  imp (domainAt 300 204).encode (imp (domainAt 300 30).encode
    (imp (domainAt 300 32).encode (imp (successorCode 204 205 208)
      (imp (domainAt 300 205).encode (imp (mulAt 300 204 30 32).encode
        (imp (domainAt 300 45).encode
          (imp (literalCutAt 300 32 30 45).encode (mulAt 300 205 30 45).encode)))))))

/-- A finite K proof of the explicit graph-extension obligation gives exactly
 the local successor witness expected by multiplication induction. The
 anchored addition witness is constructed within K, not supplied as input. -/
def local_successor_of_extension (extension : KDerivation graphExtensionCode) :
    KDerivation (imp (domainAt 300 204).encode
      (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
          (existsCode 45 (andF (domainAt 300 45) (mulAt 300 205 30 45)).encode)))))) := by
  let D := (domainAt 300 204).encode
  let G := (domainAt 300 30).encode
  let O := (domainAt 300 32).encode
  let S := successorCode 204 205 208
  let M := (mulAt 300 204 30 32).encode
  let W := andF (domainAt 300 45) (literalCutAt 300 32 30 45)
  let R := andF (domainAt 300 45) (mulAt 300 205 30 45)
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
  have hnext : Context Γ (domainAt 300 205).encode :=
    .mp hs (.mp hd (.closed source_candidate_successor))
  have hw : Context Γ (existsCode 45 W.encode) :=
    .mp hg (.mp ho (.closed (literal_cut_total 300 32 30 45
      (by decide) (by decide) (by decide) (by decide) (by decide))))
  have hp : Context Γ (imp W.encode R.encode) := by
    apply Context.deduction
    let Δ := [W.encode,M,S,O,G,D]
    have hW : Context Δ W.encode := .head _ _
    have hpair : Context Δ (both (domainAt 300 45).encode (literalCutAt 300 32 30 45).encode) := by
      simpa [W,andF,Formula.encode,Formula.not,both,neg] using hW
    have h45 := Context.conjunctionLeft hpair
    have hlit := Context.conjunctionRight hpair
    have hnew : Context Δ (mulAt 300 205 30 45).encode :=
      .mp hlit (.mp h45 (.mp (.under hm _) (.mp (.under hnext _) (.mp (.under hs _)
        (.mp (.under ho _) (.mp (.under hg _) (.mp (.under hd _) (.closed extension))))))))
    have hh := Context.conjunctionIntro h45 hnew
    simpa [R,andF,Formula.encode,Formula.not,both,neg] using hh
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 45 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
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
  have hRb : 45 ∉ R.binders := by decide
  have hRE : KDerivation (imp R.encode E.encode) := existsIntroduce 45 R hRb
  have hpE : Context Γ (imp W.encode E.encode) := by
    apply Context.deduction
    have hW : Context (W.encode :: Γ) W.encode := .head _ _
    have hR : Context (W.encode :: Γ) R.encode := .mp hW (.under hp _)
    exact .mp hR (.closed hRE)
  have hall := Context.generalize 45 hv hpE
  have hEv : KDerivation (imp E.encode (allCode 45 E.encode)) :=
    free_vacuity 45 E (by simp [E,Formula.free])
  have he : Context Γ E.encode := Context.existsElim hEv hall hw
  exact he

theorem local_successor_of_extension_certificate (extension : KDerivation graphExtensionCode) :
    theoremCode (certificate (local_successor_of_extension extension)) =
      imp (domainAt 300 204).encode
        (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
          (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
            (existsCode 45 (andF (domainAt 300 45) (mulAt 300 205 30 45)).encode))))) :=
  certificate_correct (local_successor_of_extension extension)
end PASoundness.PAtoCompactMultiplicationAnchoredLocal
#print axioms PASoundness.PAtoCompactMultiplicationAnchoredLocal.local_successor_of_extension
#print axioms PASoundness.PAtoCompactMultiplicationAnchoredLocal.local_successor_of_extension_certificate
