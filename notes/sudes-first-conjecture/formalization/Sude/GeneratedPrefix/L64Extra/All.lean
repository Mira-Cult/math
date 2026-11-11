import Sude.GeneratedPrefix.L64Extra.PrimeStage23
import Sude.GeneratedPrefix.L32Primes.All

/-! The first 64 source pairs per L stage; full FPF acceptance remains open. -/
namespace Sude.GeneratedPrefix.L64Extra
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem extra_prime (x : (Fin 24 × Fin 32) × Bool) : Nat.Prime (endpoint x) := by
  rcases x with ⟨⟨j, i⟩, side⟩
  fin_cases j
  · exact PrimeStage00.prime i side
  · exact PrimeStage01.prime i side
  · exact PrimeStage02.prime i side
  · exact PrimeStage03.prime i side
  · exact PrimeStage04.prime i side
  · exact PrimeStage05.prime i side
  · exact PrimeStage06.prime i side
  · exact PrimeStage07.prime i side
  · exact PrimeStage08.prime i side
  · exact PrimeStage09.prime i side
  · exact PrimeStage10.prime i side
  · exact PrimeStage11.prime i side
  · exact PrimeStage12.prime i side
  · exact PrimeStage13.prime i side
  · exact PrimeStage14.prime i side
  · exact PrimeStage15.prime i side
  · exact PrimeStage16.prime i side
  · exact PrimeStage17.prime i side
  · exact PrimeStage18.prime i side
  · exact PrimeStage19.prime i side
  · exact PrimeStage20.prime i side
  · exact PrimeStage21.prime i side
  · exact PrimeStage22.prime i side
  · exact PrimeStage23.prime i side

end Sude.GeneratedPrefix.L64Extra
