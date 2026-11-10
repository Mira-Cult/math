import PASoundness.PAtoCompactDiagonalNoGarbageAll

/-! Capture-safe instantiation of the supplied diagonal no-garbage invariant.
This finite K proof renames the diagonal endpoint witness to avoid the graph
coordinate 3; it neither constructs a graph nor establishes an isomorphism. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalNoGarbageAlias
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactDiagonalNoGarbageStep PASoundness.PAtoCompactDiagonalNoGarbageAll

/-- At graph-entry name 19 the old invariant supplies a diagonal endpoint
witness under the fresh binder 10, avoiding the caller's coordinate name 3. -/
def old_no_garbage_at_19 : KDerivation (imp oldNoGarbage
    (imp (member 6 19) (existsCode 10
      (both (member 0 10) (pairFormula 19 10 10).encode)))) := by
  let f : Formula := .imp (.member 6 9)
    (.ex 3 (namedBoth (.member 0 3) (pairFormula 9 3 3)))
  have hi := CompactNamed.universalInstance 9 19 f (by decide) (by decide) (by decide)
  have hf : f.encode = imp (member 6 9) oldEntry := by rfl
  have hr : CompactNamed.replace 9 19 f =
      .imp (.member 6 19) (.ex 3 (namedBoth (.member 0 3) (pairFormula 19 3 3))) := by decide
  rw [hf, hr] at hi
  have hi' : KDerivation (imp oldNoGarbage
      (imp (member 6 19) (existsCode 3
        (both (member 0 3) (pairFormula 19 3 3).encode)))) := by
    simpa [oldNoGarbage, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using hi
  let g : Formula := namedBoth (.member 0 3) (pairFormula 19 3 3)
  have ha := (CompactNamed.existentialAlpha 3 10 g (by decide) (by decide) (by decide)).1
  have hg : CompactNamed.replace 3 10 g =
      namedBoth (.member 0 10) (pairFormula 19 10 10) := by decide
  rw [hg] at ha
  have ha' : KDerivation (imp (existsCode 3
      (both (member 0 3) (pairFormula 19 3 3).encode))
      (existsCode 10 (both (member 0 10) (pairFormula 19 10 10).encode))) := by
    simpa [g, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 6 19,oldNoGarbage]
  have hn : Context Γ oldNoGarbage := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 6 19) := Context.head _ _
  exact .mp (.mp hm (.mp hn (.closed hi'))) (.closed ha')

theorem old_no_garbage_at_19_certificate : theoremCode (certificate old_no_garbage_at_19) =
    imp oldNoGarbage (imp (member 6 19) (existsCode 10
      (both (member 0 10) (pairFormula 19 10 10).encode))) :=
  certificate_correct old_no_garbage_at_19

end PASoundness.PAtoCompactDiagonalNoGarbageAlias

#print axioms PASoundness.PAtoCompactDiagonalNoGarbageAlias.old_no_garbage_at_19
#print axioms PASoundness.PAtoCompactDiagonalNoGarbageAlias.old_no_garbage_at_19_certificate
