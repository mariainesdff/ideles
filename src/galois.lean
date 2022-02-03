/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import krull_topology
import field_theory.is_alg_closed.algebraic_closure
import group_theory.abelianization

/-!
# The topological abelianization of the absolute Galois group.
We define the topological abelianization of the absolute Galois group of a field `K`.
We prove some lemmas about (topological) groups needed for this definition.

## Main definitions
- `G_K` : The Galois group of the field extension `K^al/K`, where `K^al` is the algebraic closure
  of `K`. 
- `G_K_ab` : The topological abelianization of `G_K`, that is, the quotient of `G_K` by the 
  topological closure of its commutator subgroup.
- `subgroup.connected_component_of_one` : The connected component of the identity in a topological 
  group, regarded as a subgroup.

## Main results
- `topological_group.continuous_conj` : Conjugation in a topological group is continuous.
- `subgroup.is_normal_topological_closure` : If `N` is a normal subgroup of the topological group
  `G`, then the topological closure of `N` is a normal subgroup of `G`.

## Tags
number field, galois group, abelianization
-/

variables (K: Type*) [field K]

/-- The absolute Galois group of `G`, defined as the Galois group of the field extension `K^al/K`, 
  where `K^al` is the algebraic closure of `K`. -/
def G_K := ((algebraic_closure K) ≃ₐ[K] (algebraic_closure K))
noncomputable instance : group (G_K K) := alg_equiv.aut
/-- `G_K` is a topological space with the Krull topology. -/
noncomputable instance : topological_space (G_K K) := krull_topology K (algebraic_closure K)
/-- `G_K` is a topological group with the Krull topology. -/
instance : topological_group (G_K K) := krull_topological_group K (algebraic_closure K)

/-- Conjugation in a topological group is continuous.-/
@[to_additive "Conjugation in a topological additive group is continuous."]
lemma topological_group.continuous_conj {G : Type*} [topological_space G] [group G]
  [topological_group G] (g : G) : continuous  (λ (h : G), g*h*g⁻¹) := 
begin
  have h_comp : (λ (h : G), g*h*g⁻¹) = (λ (h : G), g*h) ∘ (λ (h : G), h*g⁻¹),
  { ext h,
    rw [function.comp_app, mul_assoc]},
  rw h_comp,
  apply continuous.comp ( continuous_mul_left g) (continuous_mul_right g⁻¹),
end

/-- The topological closure of a normal subgroup is normal.-/
@[to_additive "The topological closure of a normal additive subgroup is normal."]
lemma subgroup.is_normal_topological_closure {G : Type*} [topological_space G] [group G]
  [topological_group G] (N : subgroup G) [N.normal] :
  (subgroup.topological_closure N).normal := 
{ conj_mem := 
  begin
    intros n hn g,
    apply mem_closure_of_continuous (topological_group.continuous_conj g) hn,
    intros m hm,    
    apply subset_closure,
    exact subgroup.normal.conj_mem infer_instance m hm g,
  end }

/-- The connected component of 1 is a subgroup of `G`. -/
@[to_additive "The connected component of 0 is a subgroup of `G`."] 
def subgroup.connected_component_of_one (G : Type*) [topological_space G] [group G]
  [topological_group G] : subgroup G := 
{ carrier  := connected_component (1 : G),
  one_mem' := mem_connected_component,
  mul_mem' := λ g h hg hh,
  begin
    rw connected_component_eq hg,
    have : g ∈ connected_component (g*h),
    { apply continuous.image_connected_component_subset (continuous_mul_left g),
      rw ← connected_component_eq hh,
      use [(1 : G), mem_connected_component],
      simp only [mul_one], },
    rw ← connected_component_eq this,
    exact mem_connected_component,
  end,
  inv_mem' := λ g hg,
  begin
    rw ← one_inv,
    apply continuous.image_connected_component_subset continuous_inv,
    rw set.mem_image,
    use [g, hg],
    apply_instance,
  end }

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
