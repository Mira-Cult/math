import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactTransitiveWitness

/-! Conditional existential packaging for a represented composite graph.
The graph-selection and pointwise matrix derivations remain explicit proof
arguments. This module does not construct a graph or prove transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied graph-selection condition `Q` and its explicit instantiation
proof are retained as premises. `Q` may use fresh bound names for its graph
quantifiers. The three matrices and all required freshness assumptions are
literal named syntax. No graph existence or matrix transfer is derived here. -/
def transport_two_exists (f g h : Nat) (F G C T Q : Formula)
    (hfg : f ≠ g) (hfh : f ≠ h) (hgh : g ≠ h)
    (hFh : h ∉ F.names) (hGh : h ∉ G.names)
    (hFg : g ∉ F.names) (hGf : f ∉ G.names) (hQf : f ∉ Q.names) (hQg : g ∉ Q.names)
    (hTf : f ∉ T.names) (hTg : g ∉ T.names)
    (select : KDerivation (imp Q.encode
      (imp F.encode (imp G.encode (existsCode h C.encode)))))
    (step : KDerivation (imp F.encode (imp G.encode (imp C.encode T.encode)))) :
    KDerivation (imp Q.encode (imp (existsCode f F.encode)
      (imp (existsCode g G.encode) (existsCode h T.encode)))) := by
  let R := existsCode h T.encode
  have hR_g : KDerivation (imp R (allCode g R)) := by
    have hf : g ∉ (Formula.ex h T).names := by simp [Formula.names, hgh, hTg]
    simpa [R, Formula.encode] using (Formula.ex h T).vacuity g hf
  have hcore : KDerivation (imp F.encode (imp G.encode
      (imp (existsCode h C.encode) R))) := by
    have hpoint : Context [G.encode,F.encode] (imp C.encode T.encode) := by
      apply Context.deduction
      let Γ := [C.encode,G.encode,F.encode]
      have hc : Context Γ C.encode := Context.head _ _
      have hg : Context Γ G.encode := .hypothesis (by simp [Γ])
      have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
      exact .mp hc (.mp hg (.mp hf (.closed step)))
    have hv : ∀ q, q ∈ [G.encode,F.encode] → KDerivation (imp q (allCode h q)) := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      by_cases heq : q = G.encode
      · subst q; exact G.vacuity h hGh
      · have heq' : q = F.encode := hq.resolve_left heq
        subst q; exact F.vacuity h hFh
    have hall := Context.generalize h hv hpoint
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    exact exists_map_context (Context.under hall _) (Context.head _ _)
  have hlocal : KDerivation (imp Q.encode (imp F.encode (imp G.encode R))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [G.encode,F.encode,Q.encode]
    have hg : Context Γ G.encode := Context.head _ _
    have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
    have hq : Context Γ Q.encode := .hypothesis (by simp [Γ])
    have hc : Context Γ (existsCode h C.encode) := .mp hg (.mp hf (.mp hq (.closed select)))
    exact .mp hc (.mp hg (.mp hf (.closed hcore)))
  have hg_local : Context [F.encode,Q.encode] (imp G.encode R) :=
    .mp (Context.head [Q.encode] F.encode)
      (.mp (Context.under (Context.head [] Q.encode) F.encode) (.closed hlocal))
  have hg_v : ∀ q, q ∈ [F.encode,Q.encode] → KDerivation (imp q (allCode g q)) := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases heq : q = F.encode
    · subst q; exact F.vacuity g hFg
    · have heq' : q = Q.encode := hq.resolve_left heq
      subst q; exact Q.vacuity g hQg
  have hgen_g := Context.generalize g hg_v hg_local
  have hf_local : Context [Q.encode] (imp F.encode (imp (existsCode g G.encode) R)) := by
    apply Context.deduction
    apply Context.deduction
    exact Context.existsElim hR_g (Context.under hgen_g _) (Context.head _ _)
  have hf_v : ∀ q, q ∈ [Q.encode] → KDerivation (imp q (allCode f q)) := by
    intro q hq
    have he : q = Q.encode := by simpa using hq
    subst q
    exact Q.vacuity f hQf
  have hgen_f := Context.generalize f hf_v hf_local
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode g G.encode, existsCode f F.encode, Q.encode]
  have hfex : Context Γ (existsCode f F.encode) := .hypothesis (by simp [Γ])
  have hgex : Context Γ (existsCode g G.encode) := Context.head _ _
  have hall : Context Γ (allCode f (imp F.encode (imp (existsCode g G.encode) R))) :=
    .under (.under hgen_f _) _
  have hv : KDerivation (imp (imp (existsCode g G.encode) R)
      (allCode f (imp (existsCode g G.encode) R))) := by
    let U : Formula := (Formula.ex g G).imp (Formula.ex h T)
    have hu : f ∉ U.names := by
      simp [U, Formula.names, hfg, hfh, hTf, hGf]
    simpa [U, Formula.encode, R] using U.vacuity f hu
  exact .mp hgex (Context.existsElim hv hall hfex)

theorem transport_two_exists_certificate (f g h : Nat) (F G C T Q : Formula)
    (hfg : f ≠ g) (hfh : f ≠ h) (hgh : g ≠ h)
    (hFh : h ∉ F.names) (hGh : h ∉ G.names)
    (hFg : g ∉ F.names) (hGf : f ∉ G.names) (hQf : f ∉ Q.names) (hQg : g ∉ Q.names)
    (hTf : f ∉ T.names) (hTg : g ∉ T.names)
    (select : KDerivation (imp Q.encode
      (imp F.encode (imp G.encode (existsCode h C.encode)))))
    (step : KDerivation (imp F.encode (imp G.encode (imp C.encode T.encode)))) :
    theoremCode (certificate (transport_two_exists f g h F G C T Q
      hfg hfh hgh hFh hGh hFg hGf hQf hQg hTf hTg select step)) =
      imp Q.encode (imp (existsCode f F.encode)
        (imp (existsCode g G.encode) (existsCode h T.encode))) :=
  certificate_correct (transport_two_exists f g h F G C T Q
    hfg hfh hgh hFh hGh hFg hGf hQf hQg hTf hTg select step)

end PASoundness.PAtoCompactConditionalTransitivityExists

#print axioms PASoundness.PAtoCompactConditionalTransitivityExists.transport_two_exists
#print axioms PASoundness.PAtoCompactConditionalTransitivityExists.transport_two_exists_certificate
