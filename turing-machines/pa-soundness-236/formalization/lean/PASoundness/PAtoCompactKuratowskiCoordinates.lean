import PASoundness.PAtoCompactKuratowskiFirst
import PASoundness.PAtoCompactKuratowskiSecond

/-! Coordinate uniqueness for two explicit Kuratowski decompositions sharing
one representative, as finite K proof data. Witnesses and syntax freshness
are explicit. This does not establish represented graph collection, quotient
congruence, arithmetic operations, induction, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiCoordinates
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair
open PASoundness.PAtoCompactPairTransport PASoundness.PAtoCompactKuratowskiFirst
open PASoundness.PAtoCompactKuratowskiSecond

/-- Two explicitly displayed Kuratowski decompositions of the same object
have equal first and second coordinates. All syntax names are distinct; the
represented objects and coordinates may of course coincide. -/
def coordinates (a a' b b' s s' d d' p q : Nat)
    (fresh : [a,a',b,b',s,s',d,d',p,q].Nodup) :
    KDerivation (imp (singletonCode a s q) (imp (pairCode a b d q)
      (imp (pairCode s d p q) (imp (singletonCode a' s' q)
        (imp (pairCode a' b' d' q) (imp (pairCode s' d' p q)
          (both (equal a a') (equal b b')))))))) := by
  have hfFirst : [a,a',b',s,d,s',d',p,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hfSecond : [a,b,b',s,s',d,d',p,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hfSM : [a',a,s',q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hfPF : [a',a,b',d',q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  let S := singletonCode a s q
  let D := pairCode a b d q
  let P := pairCode s d p q
  let S' := singletonCode a' s' q
  let D' := pairCode a' b' d' q
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
  have heq : Context Γ (equal a a') :=
    .mp hp' (.mp hp (.mp hd' (.mp hs' (.mp hs (.closed
      (first_coordinate a a' b' s d s' d' p q hfFirst))))))
  have hs'Norm : Context Γ (singletonCode a s' q) :=
    .mp hs' (.mp (Context.eqSymm heq) (.closed (singleton_member_transport a' a s' q hfSM)))
  have hd'Norm : Context Γ (pairCode a b' d' q) :=
    .mp hd' (.mp (Context.eqSymm heq) (.closed (pair_first_transport a' a b' d' q hfPF)))
  have hsecond : Context Γ (equal b b') :=
    .mp hp' (.mp hd'Norm (.mp hs'Norm (.mp hp (.mp hd (.mp hs (.closed
      (second_coordinate a b b' s s' d d' p q hfSecond)))))))
  exact Context.conjunctionIntro heq hsecond

theorem coordinates_certificate (a a' b b' s s' d d' p q : Nat)
    (fresh : [a,a',b,b',s,s',d,d',p,q].Nodup) :
    theoremCode (certificate (coordinates a a' b b' s s' d d' p q fresh)) =
      imp (singletonCode a s q) (imp (pairCode a b d q)
        (imp (pairCode s d p q) (imp (singletonCode a' s' q)
          (imp (pairCode a' b' d' q) (imp (pairCode s' d' p q)
            (both (equal a a') (equal b b'))))))) :=
  certificate_correct (coordinates a a' b b' s s' d d' p q fresh)

end PASoundness.PAtoCompactKuratowskiCoordinates

#print axioms PASoundness.PAtoCompactKuratowskiCoordinates.coordinates
#print axioms PASoundness.PAtoCompactKuratowskiCoordinates.coordinates_certificate
