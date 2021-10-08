import number_theory.padics.padic_integers
import topology.algebra.ring

noncomputable theory
instance (p : nat.primes) : fact (nat.prime p) := ⟨p.2⟩
def pi_Z_p := Π p : nat.primes, ℤ_[p]
instance : ring pi_Z_p := pi.ring
instance : topological_space pi_Z_p := Pi.topological_space
-- Next line doesn't work
--instance : topological_ring pi_Z_p := pi.topological_ring
-- But this does:
instance foo : topological_ring (Π p : nat.primes, ℤ_[p]) := pi.topological_ring
