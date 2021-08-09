import data.nat.prime
import data.set.finite
import data.real.nnreal
import ring_theory.valuation.basic
import ring_theory.valuation.integers

universes u v
variables (R : Type u)[ring R] (Γ₀ : Type v)[linear_ordered_comm_monoid_with_zero Γ₀] 

instance : setoid (valuation R Γ₀) :=
{ r := λ x y, valuation.is_equiv x y,
iseqv := begin
  --show equivalence relation,
  split,
  {--show reflexive,
   intro x,
   exact valuation.is_equiv.refl
  },
  split,
  {-- show symmetric,
   intros x y,
   exact valuation.is_equiv.symm},
   {-- show transitive,
   intros x y z,
   exact valuation.is_equiv.trans},
end}

@[reducible]
def vals  : Type* :=
quotient (valuation.setoid R Γ₀)

variable (v: vals R Γ₀)
#check v

/-
variables [linear_ordered_field nnreal][Π v: vals_Q, is_absolute_value v.to_fun]

structure A_Q_f : Type :=
(x : Π v : vals_Q, @cau_seq.completion.Cauchy _ _ _ _ v.to_fun _)
(fin_supp : set.finite({ v : vals | (x v) ∈ v.integers}))
-/
