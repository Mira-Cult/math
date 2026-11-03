import Shared.PNP.Record285.InitializationComposition

/-! Assemble four explicitly supplied finite-check shards. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.InitializationShardComposition
open Shared.PNP.Record285.InitializationRounds

theorem ranges_cover
    (h0 : (List.range' 2 476).all checkRound = true)
    (h1 : (List.range' 478 476).all checkRound = true)
    (h2 : (List.range' 954 476).all checkRound = true)
    (h3 : (List.range' 1430 476).all checkRound = true) :
    ∀ n, 2 ≤ n → n < 1906 → checkRound n = true := by
  have a : (List.range' 2 952).all checkRound = true := range_join 2 476 476 h0 h1
  have b : (List.range' 954 952).all checkRound = true := range_join 954 476 476 h2 h3
  have all : (List.range' 2 1904).all checkRound = true := range_join 2 952 952 a b
  intro n hlo hhi
  apply List.all_eq_true.mp all n
  rw [List.mem_range']
  exact ⟨n-2, by omega, by omega⟩

end Shared.PNP.Record285.InitializationShardComposition
