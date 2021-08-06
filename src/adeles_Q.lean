import data.nat.prime
import number_theory.padics
import restricted_product

universe v

def P := {p: ℕ | fact (prime p)}
variables [∀ p: P, fact (nat.prime p)]

def Q := λ (p : P), ℚ_[p]
variables [Π (p :  P), topological_space (Q p)]
[Π (p :  P), group (Q p)][∀ (p :  P), topological_group (Q p)]

def Z := λ (p : P), ℤ_[p]
variables [Π (p :  P), topological_space (Z p)]
[Π (p :  P), group (Z p)][∀ (p :  P), topological_group (Z p)]

variables [∀ (p : P), has_coe (Z p) (Q p)] 

-- Finite adeles
def A_Q_f := restricted_product P Q Z

--def inh := restricted_product.inhabited P Q Z


