import PASoundness.PAtoCompactSuccessorQuotientIntro

/-! A raw successor relation with an arbitrary fresh test binder can be
introduced into the exact allocated quotient-successor template. These are
finite K proof-data constructions, not model-theoretic arguments. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRawSuccessorBinderBridge

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactSuccessorQuotientIntro

/-- Alpha-rename the test binder of a raw successor graph. The two operand
names may coincide, but neither may be the old or the new test binder. -/
def raw_successor_rename (x y w v : Nat)
    (hwx : w ≠ x) (hwy : w ≠ y) (hvx : v ≠ x) (hvy : v ≠ y) :
    KDerivation (imp (successorCode x y w) (successorCode x y v)) := by
  by_cases hwv : w = v
  · subst v
    exact CompactHilbertBasis.identity _
  · let f := namedSuccessorBody x y w
    have hwb : w ∉ f.binders := by simp [f, namedSuccessorBody, namedBoth, namedEither, Formula.binders]
    have hvn : v ∉ f.names := by
      simp [f, namedSuccessorBody, namedBoth, namedEither, Formula.names, hvx, hvy, Ne.symm hwv]
    have ha := (universalAlpha w v f hwv hwb hvn).1
    have he : replace w v f = namedSuccessorBody x y v := by
      simp [f, namedSuccessorBody, namedBoth, namedEither, replace, rename,
        Ne.symm hwx, Ne.symm hwy]
    rw [he] at ha
    simpa [f, successorCode, namedSuccessorBody, namedBoth, namedEither,
      Formula.encode, CompactProof.both, CompactProof.neg, either] using ha

/-- An explicitly guarded raw successor, with an arbitrary fresh test binder,
is a quotient successor at the allocated template base. -/
def quotient_of_arbitrary_raw (b x y w : Nat)
    (hx : x < b+2) (hy : y < b)
    (hwx : w ≠ x) (hwy : w ≠ y) :
    KDerivation (imp (domainAt b x).encode (imp (successorCode x y w)
      (imp (domainAt b y).encode (succAt b x y).encode))) := by
  have hr := raw_successor_rename x y w (b+10) hwx hwy (by omega) (by omega)
  have hp := quotient_successor_of_raw b x y hx hy
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt b y).encode, successorCode x y w, (domainAt b x).encode]
  have dx : Context Γ (domainAt b x).encode := .hypothesis (by simp [Γ])
  have sr : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have dy : Context Γ (domainAt b y).encode := .hypothesis (by simp [Γ])
  exact .mp dy (.mp (.mp sr (.closed hr)) (.mp dx (.closed hp)))

theorem quotient_of_arbitrary_raw_certificate (b x y w : Nat)
    (hx : x < b+2) (hy : y < b) (hwx : w ≠ x) (hwy : w ≠ y) :
    theoremCode (certificate (quotient_of_arbitrary_raw b x y w hx hy hwx hwy)) =
      imp (domainAt b x).encode (imp (successorCode x y w)
        (imp (domainAt b y).encode (succAt b x y).encode)) := certificate_correct _

end PASoundness.PAtoCompactRawSuccessorBinderBridge

#print axioms PASoundness.PAtoCompactRawSuccessorBinderBridge.raw_successor_rename
#print axioms PASoundness.PAtoCompactRawSuccessorBinderBridge.quotient_of_arbitrary_raw
#print axioms PASoundness.PAtoCompactRawSuccessorBinderBridge.quotient_of_arbitrary_raw_certificate
