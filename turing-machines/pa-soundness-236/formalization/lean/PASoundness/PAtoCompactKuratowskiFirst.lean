import PASoundness.PAtoCompactUnorderedCoordinates

/-! First-coordinate comparison for two explicitly supplied Kuratowski
decompositions with one outer object. This is finite K proof data, without
extensionality or representative uniqueness. The second coordinate,
existential pair packaging, graph collection and quotient remain separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiFirst
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair
open PASoundness.PAtoCompactUnorderedCoordinates

/-- The singleton/pair components of two Kuratowski decompositions of the
same outer object force the first coordinates equal. The old pair for the
first decomposition is not needed for this one coordinate. All syntax names
are distinct, while their interpreted values need not be distinct. -/
def first_coordinate (a a' b' s d s' d' p q : Nat)
    (fresh : [a,a',b',s,d,s',d',p,q].Nodup) :
    KDerivation (imp (singletonCode a s q)
      (imp (singletonCode a' s' q) (imp (pairCode a' b' d' q)
        (imp (pairCode s d p q) (imp (pairCode s' d' p q) (equal a a')))))) := by
  have hqa : q ≠ a := by intro h; subst q; simp at fresh
  have hqa' : q ≠ a' := by intro h; subst q; simp at fresh
  have hqb' : q ≠ b' := by intro h; subst q; simp at fresh
  have hqs : q ≠ s := by intro h; subst q; simp at fresh
  have hqd : q ≠ d := by intro h; subst q; simp at fresh
  have hqs' : q ≠ s' := by intro h; subst q; simp at fresh
  have hqd' : q ≠ d' := by intro h; subst q; simp at fresh
  have hqp : q ≠ p := by intro h; subst q; simp at fresh
  let S := singletonCode a s q
  let S' := singletonCode a' s' q
  let D' := pairCode a' b' d' q
  let P := pairCode s d p q
  let P' := pairCode s' d' p q
  let Γ := [P',P,D',S',S]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hs' : Context Γ S' := .hypothesis (by simp [Γ])
  have hd' : Context Γ D' := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hp' : Context Γ P' := .hypothesis (by simp [Γ])
  have hsA := Context.mp hs (.closed (singleton_instance a s q a hqa hqs hqa))
  have hsA' := Context.mp hs (.closed (singleton_instance a s q a' hqa hqs hqa'))
  have hs'A := Context.mp hs' (.closed (singleton_instance a' s' q a hqa' hqs' hqa))
  have hd'A' := Context.mp hd' (.closed (pair_instance a' b' d' q a' hqa' hqb' hqd' hqa'))
  have hpS := Context.mp hp (.closed (pair_instance s d p q s hqs hqd hqp hqs))
  have hp'S := Context.mp hp' (.closed (pair_instance s' d' p q s hqs' hqd' hqp hqs))
  have hsa : Context Γ (member s a) :=
    .mp (.closed (equalityReflexive a)) (Context.conjunctionRight hsA)
  have hd'a'pair : Context Γ (either (equal a' a') (equal a' b')) :=
    Context.disjunctionLeft (b := equal a' b') (.closed (equalityReflexive a'))
  have hd'a' : Context Γ (member d' a') := .mp hd'a'pair (Context.conjunctionRight hd'A')
  have hpspair : Context Γ (either (equal s s) (equal s d)) :=
    Context.disjunctionLeft (b := equal s d) (.closed (equalityReflexive s))
  have hps : Context Γ (member p s) := .mp hpspair (Context.conjunctionRight hpS)
  have hcases : Context Γ (either (equal s s') (equal s d')) :=
    .mp hps (Context.conjunctionLeft hp'S)
  apply Context.disjunctionElim hcases
  · have he : Context (equal s s' :: Γ) (equal s s') := Context.head Γ _
    have hmem : Context (equal s s' :: Γ) (member s' a) :=
      .mp (Context.under hsa _) (.mp he (.closed (memberLeftEquality s s' a)))
    exact .mp hmem (Context.conjunctionLeft (Context.under hs'A _))
  · have he : Context (equal s d' :: Γ) (equal s d') := Context.head Γ _
    have hmem : Context (equal s d' :: Γ) (member s a') :=
      .mp (Context.under hd'a' _) (.mp (Context.eqSymm he) (.closed (memberLeftEquality d' s a')))
    exact Context.eqSymm (.mp hmem (Context.conjunctionLeft (Context.under hsA' _)))

theorem first_coordinate_certificate (a a' b' s d s' d' p q : Nat)
    (fresh : [a,a',b',s,d,s',d',p,q].Nodup) :
    theoremCode (certificate (first_coordinate a a' b' s d s' d' p q fresh)) =
      imp (singletonCode a s q)
        (imp (singletonCode a' s' q) (imp (pairCode a' b' d' q)
          (imp (pairCode s d p q) (imp (pairCode s' d' p q) (equal a a'))))) :=
  certificate_correct (first_coordinate a a' b' s d s' d' p q fresh)

end PASoundness.PAtoCompactKuratowskiFirst

#print axioms PASoundness.PAtoCompactKuratowskiFirst.first_coordinate
#print axioms PASoundness.PAtoCompactKuratowskiFirst.first_coordinate_certificate
