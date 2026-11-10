import PASoundness.PAtoCompactMulReversalSyntax

/-! Naturality and variable preservation of the multiplication reversal on
PA terms. These are identities of finite syntax, not object-level proofs or
claims about the semantics of multiplication. -/

namespace PASoundness.PAtoCompactMulReversalTermNaturality

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactMulReversalSyntax

/-- Reversal commutes with arbitrary renaming of term variables. -/
theorem reverseTerm_relabel {α β : Type} (t : Peano.language.Term α) (r : α → β) :
    reverseTerm (t.relabel r) = (reverseTerm t).relabel r := by
  induction t with
  | var x => rfl
  | @func n symbol ts ih =>
      cases symbol with
      | zero =>
          change Term.func Peano.FunctionSymbol.zero Fin.elim0 = Term.func Peano.FunctionSymbol.zero (fun i => (Fin.elim0 i : Peano.language.Term α).relabel r)
          congr 1
          funext i
          exact Fin.elim0 i
      | succ =>
          change Term.func Peano.FunctionSymbol.succ (fun i => reverseTerm ((ts i).relabel r)) =
            Term.func Peano.FunctionSymbol.succ (fun i => (reverseTerm (ts i)).relabel r)
          congr 1
          funext i
          exact ih i
      | add =>
          change Term.func Peano.FunctionSymbol.add (fun i => reverseTerm ((ts i).relabel r)) =
            Term.func Peano.FunctionSymbol.add (fun i => (reverseTerm (ts i)).relabel r)
          congr 1
          funext i
          exact ih i
      | mul =>
          change Term.func Peano.FunctionSymbol.mul (fun i => reverseTerm ((ts i.rev).relabel r)) =
            Term.func Peano.FunctionSymbol.mul (fun i => (reverseTerm (ts i.rev)).relabel r)
          congr 1
          funext i
          exact ih i.rev

/-- Reversal commutes with substitution when each substituted term is also
reversed. No restriction on variables or their overlap is required. -/
theorem reverseTerm_subst {α β : Type} (t : Peano.language.Term α)
    (σ : α → Peano.language.Term β) :
    reverseTerm (t.subst σ) = (reverseTerm t).subst (fun a => reverseTerm (σ a)) := by
  induction t with
  | var x => rfl
  | @func n symbol ts ih =>
      cases symbol with
      | zero =>
          change Term.func Peano.FunctionSymbol.zero Fin.elim0 = Term.func Peano.FunctionSymbol.zero
            (fun i => (Fin.elim0 i : Peano.language.Term α).subst (fun a => reverseTerm (σ a)))
          congr 1
          funext i
          exact Fin.elim0 i
      | succ =>
          change Term.func Peano.FunctionSymbol.succ (fun i => reverseTerm ((ts i).subst σ)) =
            Term.func Peano.FunctionSymbol.succ (fun i => (reverseTerm (ts i)).subst (fun a => reverseTerm (σ a)))
          congr 1
          funext i
          exact ih i
      | add =>
          change Term.func Peano.FunctionSymbol.add (fun i => reverseTerm ((ts i).subst σ)) =
            Term.func Peano.FunctionSymbol.add (fun i => (reverseTerm (ts i)).subst (fun a => reverseTerm (σ a)))
          congr 1
          funext i
          exact ih i
      | mul =>
          change Term.func Peano.FunctionSymbol.mul (fun i => reverseTerm ((ts i.rev).subst σ)) =
            Term.func Peano.FunctionSymbol.mul (fun i => (reverseTerm (ts i.rev)).subst (fun a => reverseTerm (σ a)))
          congr 1
          funext i
          exact ih i.rev

/-- Reversal preserves the full finite set of variables occurring in a term. -/
theorem reverseTerm_varFinset {α : Type} [DecidableEq α] (t : Peano.language.Term α) :
    (reverseTerm t).varFinset = t.varFinset := by
  induction t with
  | var x => rfl
  | @func n symbol ts ih =>
      cases symbol with
      | zero => simp [reverseTerm, Term.varFinset]
      | succ => simp only [reverseTerm, Term.varFinset, ih]
      | add => simp only [reverseTerm, Term.varFinset, ih]
      | mul =>
          ext a
          simp only [reverseTerm, Term.varFinset, Finset.mem_biUnion,
            Finset.mem_univ, true_and, ih]
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨i.rev, hi⟩
          · rintro ⟨i, hi⟩
            exact ⟨i.rev, by simpa only [Fin.rev_rev] using hi⟩

/-- For terms whose variables distinguish free and bound names, reversal
preserves the finite set of free names. -/
theorem reverseTerm_varFinsetLeft {α β : Type} [DecidableEq α]
    (t : Peano.language.Term (α ⊕ β)) :
    (reverseTerm t).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x => rfl
  | @func n symbol ts ih =>
      cases symbol with
      | zero => simp [reverseTerm, Term.varFinsetLeft]
      | succ => simp only [reverseTerm, Term.varFinsetLeft, ih]
      | add => simp only [reverseTerm, Term.varFinsetLeft, ih]
      | mul =>
          ext a
          simp only [reverseTerm, Term.varFinsetLeft, Finset.mem_biUnion,
            Finset.mem_univ, true_and, ih]
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨i.rev, hi⟩
          · rintro ⟨i, hi⟩
            exact ⟨i.rev, by simpa only [Fin.rev_rev] using hi⟩

end PASoundness.PAtoCompactMulReversalTermNaturality

#print axioms PASoundness.PAtoCompactMulReversalTermNaturality.reverseTerm_relabel
#print axioms PASoundness.PAtoCompactMulReversalTermNaturality.reverseTerm_subst
#print axioms PASoundness.PAtoCompactMulReversalTermNaturality.reverseTerm_varFinset
#print axioms PASoundness.PAtoCompactMulReversalTermNaturality.reverseTerm_varFinsetLeft
