/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import field_theory.krull_topology
import field_theory.is_alg_closed.algebraic_closure
import group_theory.abelianization

/-!
# The topological abelianization of the absolute Galois group.
We define the topological abelianization of the absolute Galois group of a field `K`.
In order to fo this, we needed to formalize the definition `subgroup.connected_component_of_one` and
the lemmas `topological_group.continuous_conj` and `subgroup.is_normal_topological_closure`, which
have already been integrated into mathlib.

## Main definitions
- `G_K` : The Galois group of the field extension `K^al/K`, where `K^al` is an algebraic closure
  of `K`. 
- `G_K_ab` : The topological abelianization of `G_K`, that is, the quotient of `G_K` by the 
  topological closure of its commutator subgroup.

## Tags
number field, galois group, abelianization
-/

variables (K: Type*) [field K]

/-- The absolute Galois group of `G`, defined as the Galois group of the field extension `K^al/K`, 
  where `K^al` is an algebraic closure of `K`. -/
def G_K := ((algebraic_closure K) ≃ₐ[K] (algebraic_closure K))

noncomputable instance : group (G_K K) := alg_equiv.aut
/-- `G_K` is a topological space with the Krull topology. -/

noncomputable instance : topological_space (G_K K) := krull_topology K (algebraic_closure K)
/-- `G_K` is a topological group with the Krull topology. -/

instance : topological_group (G_K K) := infer_instance

/-! Topological abelianization -/

instance G_K.is_normal_commutator_closure : (commutator (G_K K)).topological_closure.normal := 
subgroup.is_normal_topological_closure (commutator (G_K K))

/-- The topological abelianization of `G_K`, that is, the quotient of `G_K` by the 
  topological closure of its commutator subgroup. -/
def G_K_ab := (G_K K) ⧸ (subgroup.topological_closure (commutator (G_K K)))

noncomputable instance : group (G_K_ab K) :=
quotient_group.quotient.group (commutator (G_K K)).topological_closure

/-- `G_K_ab` is a topological space with the quotient topology. -/
noncomputable instance : topological_space (G_K_ab K) :=
quotient_group.quotient.topological_space (subgroup.topological_closure (commutator (G_K K)))

/-- `G_K_ab` is a topological group with the quotient topology. -/
instance : topological_group (G_K_ab K) :=
topological_group_quotient (commutator (G_K K)).topological_closure
