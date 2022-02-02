/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ideles_K
import galois

/-!
# Main Theorem of Global Class Field Theory
We state the main theorem of global class field theory for number fields. 
Given a number field `K`, denote by `G_K_ab` the topological abelianization of its absolute Galois
group. The main theorem of global class field theory states that `G_K_ab` is isomorphic to the 
quotient `C_K_1` of the idèle class group of `K` by its identity component, as topological groups. 
-/

noncomputable theory

variables (K : Type) [field K] [number_field K]

/-- The first part of the theorem is the claim that `G_K_ab` is isomorphic to `C_K_1` as groups.-/
theorem main_theorem_of_global_CFT.group_isomorphism :
  (number_field.C_K K) ⧸ (subgroup.connected_component_of_one (number_field.C_K K)) ≃* (G_K_ab K) :=
sorry

/-- The second part claims that the above isomorphism of abstract groups is also a homeomorphism,
and hence it is an isomorphism of topological groups. -/
theorem main_theorem_of_global_CFT.homeomorph :
  homeomorph ((number_field.C_K K) ⧸ (subgroup.connected_component_of_one (number_field.C_K K)))
    (G_K_ab K) := 
{ continuous_to_fun  := sorry,
  continuous_inv_fun := sorry,
  ..(main_theorem_of_global_CFT.group_isomorphism K) }
