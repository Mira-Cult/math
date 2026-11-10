import PASoundness.PAtoCompactPairTransport
import PASoundness.PAtoCompactSingletonPairCoordinates
import PASoundness.PAtoCompactUnorderedMembers

/-! Second-coordinate comparison for supplied Kuratowski decompositions
whose first coordinate has already been normalized. Finite K proof data only;
no pair existence, graph collection, or quotient interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiSecond
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair
open PASoundness.PAtoCompactUnorderedCoordinates PASoundness.PAtoCompactUnorderedMembers
open PASoundness.PAtoCompactSingletonPairCoordinates PASoundness.PAtoCompactPairTransport

/-- Two supplied Kuratowski decompositions sharing an outer representative
and the same displayed first coordinate have equal second coordinates. -/
def second_coordinate (a b b' s s' d d' p q : Nat)
    (fresh : [a,b,b',s,s',d,d',p,q].Nodup) :
    KDerivation (imp (singletonCode a s q) (imp (pairCode a b d q)
      (imp (pairCode s d p q) (imp (singletonCode a s' q)
        (imp (pairCode a b' d' q) (imp (pairCode s' d' p q) (equal b b'))))))) := by
  have hqa : q ≠ a := by intro h; subst q; simp at fresh
  have hqb : q ≠ b := by intro h; subst q; simp at fresh
  have hqb' : q ≠ b' := by intro h; subst q; simp at fresh
  have hqs : q ≠ s := by intro h; subst q; simp at fresh
  have hqs' : q ≠ s' := by intro h; subst q; simp at fresh
  have hqd : q ≠ d := by intro h; subst q; simp at fresh
  have hqd' : q ≠ d' := by intro h; subst q; simp at fresh
  have hqp : q ≠ p := by intro h; subst q; simp at fresh
  have hfS'D : [a,s',d,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hfSD' : [a,s,d',q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hfDD' : [a,d,d',q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hfPairDD' : [a,b,d,d',q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  let S := singletonCode a s q
  let D := pairCode a b d q
  let P := pairCode s d p q
  let S' := singletonCode a s' q
  let D' := pairCode a b' d' q
  let P' := pairCode s' d' p q
  let Γ := [P',D',S',P,D,S]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hs' : Context Γ S' := .hypothesis (by simp [Γ])
  have hd' : Context Γ D' := .hypothesis (by simp [Γ])
  have hp' : Context Γ P' := .hypothesis (by simp [Γ])
  have hpd : Context Γ (member p d) :=
    .mp hp (.closed (pair_right_member s d p q hqs hqd hqp))
  have hp'd := Context.mp hp' (.closed (pair_instance s' d' p q d hqs' hqd' hqp hqd))
  have hcases : Context Γ (either (equal d s') (equal d d')) :=
    .mp hpd (Context.conjunctionLeft hp'd)
  apply Context.disjunctionElim hcases
  · let E := equal d s'
    have he : Context (E :: Γ) E := Context.head Γ E
    have hsD : Context (E :: Γ) (singletonCode a d q) :=
      .mp (Context.under hs' E) (.mp (Context.eqSymm he) (.closed (singleton_transport a s' d q hfS'D)))
    have hbaBoth : Context (E :: Γ) (both (equal a a) (equal b a)) :=
      .mp (Context.under hd E) (.mp hsD (.closed
        (singleton_pair_coordinates a a b d q q hqa hqa hqb hqd hqa hqb hqd)))
    have hba : Context (E :: Γ) (equal b a) := Context.conjunctionRight hbaBoth
    have hpd' : Context (E :: Γ) (member p d') :=
      .mp (Context.under hp' E) (.closed (pair_right_member s' d' p q hqs' hqd' hqp))
    have hpd'inst := Context.mp (Context.under hp E)
      (.closed (pair_instance s d p q d' hqs hqd hqp hqd'))
    have hcases' : Context (E :: Γ) (either (equal d' s) (equal d' d)) :=
      .mp hpd' (Context.conjunctionLeft hpd'inst)
    have hb'a : Context (E :: Γ) (equal b' a) := by
      apply Context.disjunctionElim hcases'
      · let F := equal d' s
        have hf : Context (F :: E :: Γ) F := Context.head _ _
        have hsD' : Context (F :: E :: Γ) (singletonCode a d' q) :=
          .mp (Context.under (Context.under hs E) F)
            (.mp (Context.eqSymm hf) (.closed (singleton_transport a s d' q hfSD')))
        have hboth : Context (F :: E :: Γ) (both (equal a a) (equal b' a)) :=
          .mp (Context.under (Context.under hd' E) F) (.mp hsD' (.closed
            (singleton_pair_coordinates a a b' d' q q hqa hqa hqb' hqd' hqa hqb' hqd')))
        exact Context.conjunctionRight hboth
      · let F := equal d' d
        have hf : Context (F :: E :: Γ) F := Context.head _ _
        have hsD' : Context (F :: E :: Γ) (singletonCode a d' q) :=
          .mp (Context.under hsD F)
            (.mp (Context.eqSymm hf) (.closed (singleton_transport a d d' q hfDD')))
        have hboth : Context (F :: E :: Γ) (both (equal a a) (equal b' a)) :=
          .mp (Context.under (Context.under hd' E) F) (.mp hsD' (.closed
            (singleton_pair_coordinates a a b' d' q q hqa hqa hqb' hqd' hqa hqb' hqd')))
        exact Context.conjunctionRight hboth
    exact Context.eqTrans hba (Context.eqSymm hb'a)
  · let E := equal d d'
    have he : Context (E :: Γ) E := Context.head Γ E
    have hD' : Context (E :: Γ) (pairCode a b d' q) :=
      .mp (Context.under hd E) (.mp he (.closed (pair_container_transport a b d d' q hfPairDD')))
    exact .mp (Context.under hd' E) (.mp hD' (.closed
      (pair_second_coordinate a b b' d' q q hqa hqb hqb' hqd' hqa hqb hqb' hqd')))

theorem second_coordinate_certificate (a b b' s s' d d' p q : Nat)
    (fresh : [a,b,b',s,s',d,d',p,q].Nodup) :
    theoremCode (certificate (second_coordinate a b b' s s' d d' p q fresh)) =
      imp (singletonCode a s q) (imp (pairCode a b d q)
        (imp (pairCode s d p q) (imp (singletonCode a s' q)
          (imp (pairCode a b' d' q) (imp (pairCode s' d' p q) (equal b b')))))) :=
  certificate_correct (second_coordinate a b b' s s' d d' p q fresh)

end PASoundness.PAtoCompactKuratowskiSecond

#print axioms PASoundness.PAtoCompactKuratowskiSecond.second_coordinate
#print axioms PASoundness.PAtoCompactKuratowskiSecond.second_coordinate_certificate
