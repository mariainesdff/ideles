import data.nat.prime
import data.set.finite
import number_theory.padics

/-- The type of primes in ℕ -/
def P := {p : ℕ // nat.prime p}

instance (p: P) : fact (nat.prime p.1) := ⟨p.2⟩

structure A_Q_f : Type :=
(x : Π p : P, ℚ_[p.1])
(fin_supp : set.finite({ p : P | padic_norm_e (x p) > 1}))

noncomputable instance inhabited_pre : inhabited A_Q_f :=
begin
  use λ p, (1: ℚ_[p.1]),
  have h : {p : P | padic_norm_e (1 : ℚ_[p.1]) > 1} = ∅, {
    rw set.eq_empty_iff_forall_not_mem,
    intros p hp,
    have h1: ¬ padic_norm_e 1 ≤  1, { exact hp.right},
    have h2: padic_norm_e (1 : ℚ_[p.1]) = 1, {
      exact padic_norm_e.one'
    },
    exact h1 (le_of_eq h2),
  },
  rw h,
  exact set.finite_empty,
end

-- next challenge : topological ring!
-- my suggestion:
-- (1) add_comm_group
-- (2) comm_ring
-- (3) topological_space
-- (4) topological_ring

instance : add_comm_group A_Q_f :=
{ add := sorry,
  add_assoc := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  neg := sorry,
  add_left_neg := sorry,
  add_comm := sorry }

