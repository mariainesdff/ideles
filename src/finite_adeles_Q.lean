import data.nat.prime
import data.set.finite
import number_theory.padics

def P := {p :  ℕ | fact (prime p)}
variables [∀ p: P, fact (nat.prime p)]
--variables [Π p: P, has_one (ℚ_[p])]

structure A_Q_f : Type :=
(x : Π p : P, ℚ_[p])
(fin_supp : set.finite({ p : P | padic_norm_e (x p) > 1}))

noncomputable instance inhabited_pre : inhabited A_Q_f :=
begin
  use λ p, (1: ℚ_[p]),
  have h : {p : ↥P | @padic_norm_e p (_inst_1 p) 1 > 1} = ∅, {
    rw set.eq_empty_iff_forall_not_mem,
    intros p hp,
    have h1: ¬ padic_norm_e 1 ≤  1, { exact hp.right},
    have h2: @padic_norm_e p (_inst_1 p) 1 = 1, {
      exact @padic_norm_e.one' p (_inst_1 p)
    },
    exact h1 (le_of_eq h2),
  },
  rw h,
  exact set.finite_empty,
end


/-type mismatch at application
  le_of_eq h2
term
  h2
has type
  padic_norm_e 1 = 1
but is expected to have type
  padic_norm_e 1 = 1 -/

/-
instance inhabited_pre : inhabited A_Q_f :=
begin
  use λ p, (1: ℚ_[p]),
  have h : {p : ↥P | @padic_norm_e p (_inst_1 p) 1 > 1} = ∅, {
    rw set.eq_empty_iff_forall_not_mem,
    intros p hp,
    have h1: ¬ padic_norm_e 1 ≤  1, { exact hp.right},
    --have h2: @padic_norm_e p (_inst_1 p) 1 = 1, {
    have h2: padic_norm_e  1 = 1, {
      exact @padic_norm_e.one' p (_inst_1 p)
    },
    --exact h1 (le_of_eq h2),
    sorry,
  },
  rw h,
  exact set.finite_empty,
end-/