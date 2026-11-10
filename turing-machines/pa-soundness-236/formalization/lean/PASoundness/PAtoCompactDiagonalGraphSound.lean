import PASoundness.PAtoCompactDiagonalNoGarbageAlias
import PASoundness.PAtoCompactDiagonalPairCompare

/-! A supplied graph's exact no-garbage invariant implies its edges are
on-domain and diagonal. This is a finite K proof and does not construct the
graph, show coverage, or establish an isomorphism or quotient by itself. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalGraphSound
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactDiagonalNoGarbageStep PASoundness.PAtoCompactDiagonalNoGarbageAll
open PASoundness.PAtoCompactDiagonalNoGarbageAlias PASoundness.PAtoCompactDiagonalPairCompare
open PASoundness.PAtoCompactKuratowskiSyntax PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair

/-- Full pointwise consequence of the supplied no-garbage invariant. -/
def pointResult (a b : Nat) : Nat := both (member 0 a) (equal a b)

/-- Named form of the no-garbage hypothesis, for fresh-name vacuity only. -/
def namedNoGarbage : Formula := .all 9 (.imp (.member 6 9)
  (.ex 3 (namedBoth (.member 0 3) (pairFormula 9 3 3))))

theorem named_no_garbage_code : namedNoGarbage.encode = oldNoGarbage := by rfl

/-- With names 10 and 19 reserved as internal witnesses, a graph edge of the
supplied graph lies on the diagonal and its first coordinate is in input 0.
Name freshness is syntactic; the values assigned to the names may coincide. -/
def graph_sound_point (a b : Nat)
    (fresh : [a,b,0,6,9,10,19,20,21,22,23,24,27].Nodup) :
    KDerivation (imp oldNoGarbage (imp (graphFormula 6 a b).encode (pointResult a b))) := by
  have ha10 : 10 ≠ a := by intro h; subst a; simp at fresh
  have hb10 : 10 ≠ b := by intro h; subst b; simp at fresh
  have ha19 : 19 ≠ a := by intro h; subst a; simp at fresh
  have hb19 : 19 ≠ b := by intro h; subst b; simp at fresh
  have hcmp : [19,a,b,10,27,20,21,22,23,24].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  let N := oldNoGarbage
  let P := both (member 6 19) (pairFormula 19 a b).encode
  let Q := both (member 0 10) (pairFormula 19 10 10).encode
  let R := pointResult a b
  let fP := namedBoth (.member 6 19) (pairFormula 19 a b)
  let fR := namedBoth (.member 0 a) (.equal a b)
  have hvN10 : KDerivation (imp N (allCode 10 N)) := by
    have h := namedNoGarbage.vacuity 10 (by decide)
    simpa [N, named_no_garbage_code] using h
  have hvN19 : KDerivation (imp N (allCode 19 N)) := by
    have h := namedNoGarbage.vacuity 19 (by decide)
    simpa [N, named_no_garbage_code] using h
  have hvP10 : KDerivation (imp P (allCode 10 P)) := by
    have hnames : 10 ∉ fP.names := by
      simp [fP, namedBoth, namedEither, pair_formula_named, namedSingleton, namedPair,
        Formula.names, ha10, hb10]
    have h := fP.vacuity 10 hnames
    simpa [P, fP, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using h
  have hvR10 : KDerivation (imp R (allCode 10 R)) := by
    have hnames : 10 ∉ fR.names := by simp [fR, namedBoth, Formula.names, ha10, hb10]
    have h := fR.vacuity 10 hnames
    simpa [R, pointResult, fR, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using h
  have hvR19 : KDerivation (imp R (allCode 19 R)) := by
    have hnames : 19 ∉ fR.names := by simp [fR, namedBoth, Formula.names, ha19, hb19]
    have h := fR.vacuity 19 hnames
    simpa [R, pointResult, fR, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using h
  have hlocal : Context [P,N] (imp Q R) := by
    apply Context.deduction
    let Γ := [Q,P,N]
    have hq : Context Γ Q := Context.head _ _
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have hmem : Context Γ (member 0 10) := Context.conjunctionLeft hq
    have hdiag : Context Γ (pairFormula 19 10 10).encode := Context.conjunctionRight hq
    have hedge : Context Γ (pairFormula 19 a b).encode := Context.conjunctionRight hp
    have heqs : Context Γ (both (equal a 10) (equal a b)) :=
      .mp hdiag (.mp hedge (.closed (diagonal_pair_compare a b hcmp)))
    have hdomain : Context Γ (member 0 a) :=
      .mp (Context.eqSymm (Context.conjunctionLeft heqs))
        (.mp hmem (.closed (memberRightEquality 0 10 a)))
    exact Context.conjunctionIntro hdomain (Context.conjunctionRight heqs)
  have hN : Context [P,N] N := .hypothesis (by simp)
  have hP : Context [P,N] P := Context.head _ _
  have hQ : Context [P,N] (existsCode 10 Q) :=
    .mp (Context.conjunctionLeft hP) (.mp hN (.closed old_no_garbage_at_19))
  have hall10 : Context [P,N] (allCode 10 (imp Q R)) := by
    apply Context.generalize 10
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      by_cases he : z = P
      · subst z; exact hvP10
      · have : z = N := hz.resolve_left he
        subst z; exact hvN10
    · exact hlocal
  have hresult : Context [P,N] R := Context.existsElim hvR10 hall10 hQ
  have himp : Context [N] (imp P R) := Context.deduction hresult
  have hall19 : Context [N] (allCode 19 (imp P R)) := by
    apply Context.generalize 19
    · intro z hz
      have he : z = N := by simpa using hz
      subst z
      exact hvN19
    · exact himp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 a b).encode,N]
  have hg : Context Γ (existsCode 19 P) := by
    have h := Context.head [N] (graphFormula 6 a b).encode
    change Context Γ (existsCode 19 P) at h
    exact h
  have hall19' : Context Γ (allCode 19 (imp P R)) := Context.weaken hall19 (by simp [Γ])
  exact Context.existsElim hvR19 hall19' hg

/-- The binder-safe universal graph-soundness schema, with both the domain
membership and diagonal equality consequences retained. -/
def uniformSound : Nat := allCode 28 (allCode 29
  (imp (graphFormula 6 28 29).encode (pointResult 28 29)))

/-- The equality-only schema consumed by the order and bijection proofs. -/
def uniformEquality : Nat := allCode 28 (allCode 29
  (imp (graphFormula 6 28 29).encode (equal 28 29)))

/-- The graph-soundness schema follows from the supplied no-garbage property. -/
def graph_sound_all : KDerivation (imp oldNoGarbage uniformSound) := by
  let N := oldNoGarbage
  have hN28 : KDerivation (imp N (allCode 28 N)) := by
    have h := namedNoGarbage.vacuity 28 (by decide)
    simpa [N, named_no_garbage_code] using h
  have hN29 : KDerivation (imp N (allCode 29 N)) := by
    have h := namedNoGarbage.vacuity 29 (by decide)
    simpa [N, named_no_garbage_code] using h
  have hpoint : Context [N] (imp (graphFormula 6 28 29).encode (pointResult 28 29)) :=
    .mp (Context.head [] N) (.closed (graph_sound_point 28 29 (by decide)))
  have hv29 : ∀ z, z ∈ [N] → KDerivation (imp z (allCode 29 z)) := by
    intro z hz
    have he : z = N := by simpa only [List.mem_singleton] using hz
    cases he
    exact hN29
  have hv28 : ∀ z, z ∈ [N] → KDerivation (imp z (allCode 28 z)) := by
    intro z hz
    have he : z = N := by simpa only [List.mem_singleton] using hz
    cases he
    exact hN28
  have hall29 : Context [N] (allCode 29 (imp (graphFormula 6 28 29).encode (pointResult 28 29))) :=
    Context.generalize 29 hv29 hpoint
  have hall28 : Context [N] uniformSound :=
    Context.generalize 28 hv28 hall29
  apply Context.closeEmpty
  apply Context.deduction
  exact hall28

/-- Project equality from the graph-soundness schema. -/
def uniform_equality_projection : KDerivation (imp uniformSound uniformEquality) := by
  have hp : KDerivation (imp (imp (graphFormula 6 28 29).encode (pointResult 28 29))
      (imp (graphFormula 6 28 29).encode (equal 28 29))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(graphFormula 6 28 29).encode, imp (graphFormula 6 28 29).encode (pointResult 28 29)]
    have hg : Context Γ (graphFormula 6 28 29).encode := Context.head _ _
    have hi : Context Γ (imp (graphFormula 6 28 29).encode (pointResult 28 29)) :=
      .hypothesis (by simp [Γ])
    exact Context.conjunctionRight (.mp hg hi)
  exact allCongr 28 (allCongr 29 hp)

/-- Equality-only diagonal graph soundness, in the exact fixed-name interface. -/
def graph_equality_all : KDerivation (imp oldNoGarbage uniformEquality) :=
  compose graph_sound_all uniform_equality_projection

theorem graph_sound_all_certificate : theoremCode (certificate graph_sound_all) =
    imp oldNoGarbage uniformSound := certificate_correct graph_sound_all

theorem graph_equality_all_certificate : theoremCode (certificate graph_equality_all) =
    imp oldNoGarbage uniformEquality := certificate_correct graph_equality_all

end PASoundness.PAtoCompactDiagonalGraphSound

#print axioms PASoundness.PAtoCompactDiagonalGraphSound.graph_sound_point
#print axioms PASoundness.PAtoCompactDiagonalGraphSound.graph_sound_all
#print axioms PASoundness.PAtoCompactDiagonalGraphSound.graph_equality_all
#print axioms PASoundness.PAtoCompactDiagonalGraphSound.graph_sound_all_certificate
#print axioms PASoundness.PAtoCompactDiagonalGraphSound.graph_equality_all_certificate
