import PASoundness.M236ListSource
import PASoundness.M236Reverse
/-! Selected value in an alternative list order, without a physical premise. -/
namespace PASoundness.M236ListSource
open PASoundness.Observer

/-- Each positive-rank game has its own possibly noncomputable winning strategy. -/
theorem trace_accept_iff_strategies (value : Address → Bool) :
    M236Observer.TraceAccept (source value) ↔ ∀ n, 0 < n → ∀ p,
      ∃ s : M236Observer.Strategy .ex n,
        M236Observer.Winning s (fun xs => value ⟨n, p, xs⟩ = false) :=
  (trace_accept_reindex value).trans (M236Observer.source_trace_accept_iff_strategies value)

/-- In the alternative list-stage order, the abstract ordered-atom source is
accepted exactly when all compact derivations are true in the standard
finite-set coding. This structural equivalence assumes neither soundness nor
an implementation by the selected physical machine. -/
theorem selected_source_iff_compact_sound :
    M236Observer.TraceAccept (source M236Game.selectedValue) ↔ M236Reverse.CompactSound :=
  (trace_accept_reindex M236Game.selectedValue).trans M236Reverse.source_accept_iff_compact_sound

end PASoundness.M236ListSource
