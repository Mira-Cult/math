import PASoundness.PAtoCompactSuccessorQuotientIntro

/-! Package a candidate-preserving raw successor as an output candidate and
the exact quotient-successor formula. All inputs are finite K proof data. -/
namespace PASoundness.PAtoCompactQuotientSuccessorPackage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccessorQuotientIntro

/-- Given a candidate input, a raw successor that is a candidate satisfies
the quotient successor formula. Input/output names are syntactically bounded;
their represented objects are not assumed distinct. -/
def package (b x y : Nat) (hx : x < b + 2) (hy : y < b) :
    KDerivation (imp (domainAt b x).encode
      (imp (both (successorCode x y (b+10)) (domainAt b y).encode)
        (andF (domainAt b y) (succAt b x y)).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [both (successorCode x y (b+10)) (domainAt b y).encode, (domainAt b x).encode]
  have h : Context Γ (both (successorCode x y (b+10)) (domainAt b y).encode) := .hypothesis (by simp [Γ])
  have dx : Context Γ (domainAt b x).encode := .hypothesis (by simp [Γ])
  have dr : Context Γ (successorCode x y (b+10)) := Context.conjunctionLeft h
  have dy : Context Γ (domainAt b y).encode := Context.conjunctionRight h
  have hs : Context Γ (succAt b x y).encode :=
    .mp dy (.mp dr (.mp dx (.closed (quotient_successor_of_raw b x y hx hy))))
  have hfinal := Context.conjunctionIntro dy hs
  simpa only [Γ, andF, Formula.not, Formula.encode, both, neg] using hfinal

theorem package_certificate (b x y : Nat) (hx : x < b + 2) (hy : y < b) :
    theoremCode (certificate (package b x y hx hy)) =
      imp (domainAt b x).encode
        (imp (both (successorCode x y (b+10)) (domainAt b y).encode)
          (andF (domainAt b y) (succAt b x y)).encode) := certificate_correct _

end PASoundness.PAtoCompactQuotientSuccessorPackage

#print axioms PASoundness.PAtoCompactQuotientSuccessorPackage.package
#print axioms PASoundness.PAtoCompactQuotientSuccessorPackage.package_certificate
