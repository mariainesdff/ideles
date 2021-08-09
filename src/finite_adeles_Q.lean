import data.nat.prime
import data.set.finite
import number_theory.padics

open nat

instance (p : primes) : fact (nat.prime p) := ⟨p.2⟩

structure A_Q_f : Type :=
(x : Π p : primes, ℚ_[p])
(fin_supp : set.finite({ p : primes | padic_norm_e (x p) > 1}))

noncomputable instance inhabited_pre : inhabited A_Q_f :=
begin
  use λ p, (1: ℚ_[p]),
  have h : {p : primes | padic_norm_e (1 : ℚ_[p]) > 1} = ∅, {
    rw set.eq_empty_iff_forall_not_mem,
    rintros p ⟨-, hp⟩,
    exact hp (le_of_eq padic_norm_e.one'),
  },
  rw h,
  exact set.finite_empty,
end

-- next challenge : topological ring!
