import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactPointAdjoin

/-! A literal K successor step for the proposed addition suffix. When z' is
successor(z), s' is obtained by adjoining z to s, and z is outside the cut,
the filter graph for z minus cut transports to the filter graph for z' minus
cut. This does not assert an isomorphism, successor-axiom translation,
collection, or arithmetic totality. Code 1 is literal self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorSuffix
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def F : Formula := .all 35 (namedFilterBody 32 34 35 (Formula.member 33 35).not)
private def S : Formula := .all 39 (namedSuccessorBody 32 38 39)
private def A : Formula := namedAdjoin 34 32 40 41
private def N : Formula := (Formula.member 33 32).not
private def Q (v : Nat) : Formula := namedFilterBody 38 40 v (Formula.member 33 v).not
private theorem f_code : F.encode = filterGraph 32 34 35 (neg (member 33 35)) := by rfl
private theorem s_code : S.encode = successorCode 32 38 39 := by rfl
private theorem a_code : A.encode = adjoinCode 34 32 40 41 := by rfl
private theorem n_code : N.encode = neg (member 33 32) := by rfl
private theorem q_code : (Formula.all 35 (Q 35)).encode =
    filterGraph 38 40 35 (neg (member 33 35)) := by rfl

private def old_at : KDerivation (imp F.encode
    (both (imp (member 34 44) (both (member 32 44) (neg (member 33 44))))
      (imp (both (member 32 44) (neg (member 33 44))) (member 34 44)))) := by
  have h := filter_at 32 34 35 44 ((Formula.member 33 35).not)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [f_code,Formula.not,Formula.encode,replace,rename,neg] using h

private def successor_at : KDerivation (imp S.encode
    (both (imp (member 38 44) (either (equal 44 32) (member 32 44)))
      (imp (either (equal 44 32) (member 32 44)) (member 38 44)))) := by
  have h := universalInstance 39 44 (namedSuccessorBody 32 38 39)
    (by decide) (by decide) (by decide)
  simpa [S,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
    replace,rename,both,neg,either] using h

private def adjoin_at : KDerivation (imp A.encode
    (both (imp (member 40 44) (either (equal 44 32) (member 34 44)))
      (imp (either (equal 44 32) (member 34 44)) (member 40 44)))) := by
  let body : Formula := namedBoth
    (.imp (.member 40 41) (namedEither (.equal 41 32) (.member 34 41)))
    (.imp (namedEither (.equal 41 32) (.member 34 41)) (.member 40 41))
  have h := universalInstance 41 44 body (by decide) (by decide) (by decide)
  simpa [A,namedAdjoin,body,namedBoth,namedEither,Formula.encode,
    replace,rename,both,neg,either] using h

private def point : KDerivation (imp N.encode (imp F.encode (imp S.encode (imp A.encode (Q 44).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [A.encode,S.encode,F.encode,N.encode]
  have ha : Context Γ A.encode := .head _ _
  have hs : Context Γ S.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
  have hn : Context Γ (neg (member 33 32)) := by
    simpa [n_code] using (Context.hypothesis (Γ := Γ) (a := N.encode) (by simp [Γ]))
  have ho := Context.mp hf (.closed old_at)
  have hj := Context.mp ha (.closed adjoin_at)
  have hr := Context.mp hs (.closed successor_at)
  change Context Γ (both (imp (member 40 44) (both (member 38 44) (neg (member 33 44))))
    (imp (both (member 38 44) (neg (member 33 44))) (member 40 44)))
  apply Context.conjunctionIntro
  · apply Context.deduction
    let Δ := [member 40 44,A.encode,S.encode,F.encode,N.encode]
    have hm : Context Δ (member 40 44) := .head _ _
    have hcases : Context Δ (either (equal 44 32) (member 34 44)) :=
      .mp hm (.under (Context.conjunctionLeft hj) _)
    apply Context.disjunctionElim hcases
    · let Θ := [equal 44 32,member 40 44,A.encode,S.encode,F.encode,N.encode]
      have he : Context Θ (equal 44 32) := .head _ _
      have htarget : Context Θ (member 38 44) := by
        have hchoice : Context Θ (either (equal 44 32) (member 32 44)) := Context.disjunctionLeft he
        exact .mp hchoice (.under (.under (Context.conjunctionRight hr) _) _)
      have hn44 : Context Θ (neg (member 33 44)) := by
        apply Context.deduction
        let Ξ := [member 33 44,equal 44 32,member 40 44,A.encode,S.encode,F.encode,N.encode]
        have hv : Context Ξ (member 33 44) := .head _ _
        have heq : Context Ξ (equal 44 32) := .hypothesis (by simp [Ξ])
        have hz : Context Ξ (member 33 32) := .mp heq (.mp hv (.closed (memberRightEquality 33 44 32)))
        exact .mp hz (.under (.under (.under hn _) _) _)
      exact Context.conjunctionIntro htarget hn44
    · let Θ := [member 34 44,member 40 44,A.encode,S.encode,F.encode,N.encode]
      have hmold : Context Θ (member 34 44) := .head _ _
      have hpair : Context Θ (both (member 32 44) (neg (member 33 44))) :=
        .mp hmold (.under (.under (Context.conjunctionLeft ho) _) _)
      have htarget : Context Θ (member 38 44) :=
        .mp (Context.disjunctionRight (Context.conjunctionLeft hpair))
          (.under (.under (Context.conjunctionRight hr) _) _)
      exact Context.conjunctionIntro htarget (Context.conjunctionRight hpair)
  · apply Context.deduction
    let Δ := [both (member 38 44) (neg (member 33 44)),A.encode,S.encode,F.encode,N.encode]
    have hp : Context Δ (both (member 38 44) (neg (member 33 44))) := .head _ _
    have hcases : Context Δ (either (equal 44 32) (member 32 44)) :=
      .mp (Context.conjunctionLeft hp) (.under (Context.conjunctionLeft hr) _)
    apply Context.disjunctionElim hcases
    · let Θ := [equal 44 32,both (member 38 44) (neg (member 33 44)),A.encode,S.encode,F.encode,N.encode]
      have he : Context Θ (equal 44 32) := .head _ _
      exact .mp (Context.disjunctionLeft he) (.under (.under (Context.conjunctionRight hj) _) _)
    · let Θ := [member 32 44,both (member 38 44) (neg (member 33 44)),A.encode,S.encode,F.encode,N.encode]
      have hm : Context Θ (member 32 44) := .head _ _
      have hn44 : Context Θ (neg (member 33 44)) := .under (Context.conjunctionRight hp) _
      have hms : Context Θ (member 34 44) :=
        .mp (Context.conjunctionIntro hm hn44) (.under (.under (Context.conjunctionRight ho) _) _)
      exact .mp (Context.disjunctionRight hms) (.under (.under (Context.conjunctionRight hj) _) _)

/-- The successor result has the successor suffix represented by adjoining
the old result to the old suffix. All four graph/nonmembership hypotheses are
literal K antecedents. -/
def successor_suffix : KDerivation (imp (neg (member 33 32))
    (imp (filterGraph 32 34 35 (neg (member 33 35)))
      (imp (successorCode 32 38 39) (imp (adjoinCode 34 32 40 41)
        (filterGraph 38 40 35 (neg (member 33 35))))))) := by
  let Γ := [A.encode,S.encode,F.encode,N.encode]
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 44 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases hA : h = A.encode
    · subst h; exact A.vacuity 44 (by decide)
    · by_cases hS : h = S.encode
      · subst h; exact S.vacuity 44 (by decide)
      · by_cases hF : h = F.encode
        · subst h; exact F.vacuity 44 (by decide)
        · have hN : h = N.encode := by simpa [hA,hS,hF] using hh
          subst h; exact N.vacuity 44 (by decide)
  have hp : Context Γ (Q 44).encode := by
    have hn : Context Γ N.encode := .hypothesis (by simp [Γ])
    have hf : Context Γ F.encode := .hypothesis (by simp [Γ])
    have hs : Context Γ S.encode := .hypothesis (by simp [Γ])
    have ha : Context Γ A.encode := .head _ _
    exact .mp ha (.mp hs (.mp hf (.mp hn (.closed point))))
  have hall := Context.generalize 44 hv hp
  have hα := (universalAlpha 44 35 (Q 44) (by decide) (by decide) (by decide)).1
  have hα' : KDerivation (imp (allCode 44 (Q 44).encode) (allCode 35 (Q 35).encode)) := by
    simpa [Q,namedFilterBody,namedBoth,Formula.not,replace,rename] using hα
  have hout : Context Γ (filterGraph 38 40 35 (neg (member 33 35))) := by
    simpa [← q_code,Formula.encode] using (Context.mp hall (.closed hα'))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  simpa [Γ,n_code,f_code,s_code,a_code] using hout

theorem successor_suffix_certificate : theoremCode (certificate successor_suffix) =
    imp (neg (member 33 32)) (imp (filterGraph 32 34 35 (neg (member 33 35)))
      (imp (successorCode 32 38 39) (imp (adjoinCode 34 32 40 41)
        (filterGraph 38 40 35 (neg (member 33 35)))))) := certificate_correct successor_suffix
end PASoundness.PAtoCompactAdditionSuccessorSuffix
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffix.successor_suffix
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffix.successor_suffix_certificate
