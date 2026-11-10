import PASoundness.PAtoCompactInjectivityFrameWitnessIntro
import PASoundness.PAtoCompactSuccBaseMultiAlpha
import PASoundness.PAtoCompactAllTermTransport

/-! Pointwise equality-frame construction from explicit successor child
witnesses and a finite K quotient-cancellation proof. No term totality,
quotient cancellation or PA-axiom derivation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectiveChildMatrix
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactInjectivityFrameWitnessIntro
attribute [local irreducible] PASoundness.CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

/-- From the two explicit child graphs, successor relations, and equivalence
of the successor outputs, a supplied finite K cancellation proof constructs
the target equality frame. The values and source variable labels may alias;
only their syntactic labels must lie below the indicated fresh base. -/
noncomputable def children_to_frame (t u : Peano.Term) (b a c : Nat)
    (ha : a < b) (hc : c < b)
    (ht : ∀ x ∈ t.varFinset, x < b) (hu : ∀ x ∈ u.varFinset, x < b)
    (cancel : let B := b+2+termCost (Peano.succ t)+termCost (Peano.succ u)+10
      KDerivation (imp (succAt B a b).encode (imp (succAt B c (b+1)).encode
        (imp (equivAt B b (b+1)).encode (equivAt B a c).encode)))) :
    let bt := b+2
    let bu := b+2+termCost (Peano.succ t)
    let be := bu+termCost (Peano.succ u)
    KDerivation (imp (andF (termGraph id t a (bt+64)) (succAt bt a b)).encode
      (imp (andF (termGraph id u c (bu+64)) (succAt bu c (b+1))).encode
        (imp (equivAt be b (b+1)).encode (equalityFrame id t u b).encode))) := by
  dsimp only at cancel ⊢
  let bt := b+2
  let bu := b+2+termCost (Peano.succ t)
  let be := bu+termCost (Peano.succ u)
  let B := be+10
  let T := (termGraph id t a (bt+64)).encode
  let U := (termGraph id u c (bu+64)).encode
  let S := (succAt bt a b).encode
  let R := (succAt bu c (b+1)).encode
  let E := (equivAt be b (b+1)).encode
  let F := (equalityFrame id t u b).encode
  have htmove := (termGraph_base_transport id t (bt+64) (b+2) a
    (by dsimp [bt]; omega) (by omega)
    (by intro x hx; simpa using Nat.lt_trans (ht x hx) (by dsimp [bt]; omega))
    (by intro x hx; simpa using Nat.lt_trans (ht x hx) (by omega))).1
  have humove := (termGraph_base_transport id u (bu+64) (b+2+termCost t) c
    (by dsimp [bu]; omega) (by omega)
    (by intro x hx; simpa using Nat.lt_trans (hu x hx) (by dsimp [bu]; omega))
    (by intro x hx; simpa using Nat.lt_trans (hu x hx) (by omega))).1
  have hsmove := (succAt_base_alpha bt B a b (by dsimp [bt]; omega)
    (by dsimp [bt]; omega) (by dsimp [B,be,bu]; omega) (by dsimp [B,be,bu]; omega)).forward
  have hrmove := (succAt_base_alpha bu B c (b+1) (by dsimp [bu]; omega)
    (by dsimp [bu]; omega) (by dsimp [B,be,bu]; omega) (by dsimp [B,be,bu]; omega)).forward
  have hemove := (equivAt_base_alpha be B b (b+1) (by dsimp [be,bu]; omega)
    (by dsimp [be,bu]; omega) (by dsimp [B,be,bu]; omega) (by dsimp [B,be,bu]; omega)).forward
  have htarget := (equivAt_base_alpha B (b+2+termCost t+termCost u) a c
    (by dsimp [B,be,bu]; omega) (by dsimp [B,be,bu]; omega) (by omega) (by omega)).forward
  have hframe := frame_from_matrix t u b a c ha hc ht hu
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,both U R,both T S]
  change Context Γ F
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hur : Context Γ (both U R) := .hypothesis (by simp [Γ])
  have hts : Context Γ (both T S) := .hypothesis (by simp [Γ])
  have htgt := Context.mp (Context.conjunctionLeft hts) (.closed htmove)
  have hugt := Context.mp (Context.conjunctionLeft hur) (.closed humove)
  have hs := Context.mp (Context.conjunctionRight hts) (.closed hsmove)
  have hr := Context.mp (Context.conjunctionRight hur) (.closed hrmove)
  have heq := Context.mp he (.closed hemove)
  have hcanc : Context Γ (equivAt B a c).encode := .mp heq (.mp hr (.mp hs (.closed cancel)))
  have hefinal := Context.mp hcanc (.closed htarget)
  have hm := Context.conjunctionIntro htgt (Context.conjunctionIntro hugt hefinal)
  apply Context.mp _ (.closed hframe)
  simpa only [matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm


theorem children_to_frame_certificate (t u : Peano.Term) (b a c : Nat)
    (ha : a < b) (hc : c < b)
    (ht : ∀ x ∈ t.varFinset, x < b) (hu : ∀ x ∈ u.varFinset, x < b)
    (cancel : let B := b+2+termCost (Peano.succ t)+termCost (Peano.succ u)+10
      KDerivation (imp (succAt B a b).encode (imp (succAt B c (b+1)).encode
        (imp (equivAt B b (b+1)).encode (equivAt B a c).encode)))) :
    let bt := b+2
    let bu := b+2+termCost (Peano.succ t)
    let be := bu+termCost (Peano.succ u)
    theoremCode (certificate (children_to_frame t u b a c ha hc ht hu cancel)) =
      imp (andF (termGraph id t a (bt+64)) (succAt bt a b)).encode
      (imp (andF (termGraph id u c (bu+64)) (succAt bu c (b+1))).encode
        (imp (equivAt be b (b+1)).encode (equalityFrame id t u b).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccInjectiveChildMatrix
#print axioms PASoundness.PAtoCompactSuccInjectiveChildMatrix.children_to_frame
#print axioms PASoundness.PAtoCompactSuccInjectiveChildMatrix.children_to_frame_certificate
