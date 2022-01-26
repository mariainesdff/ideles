/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ideles_K
import galois

variables (K : Type) [field K] [number_field K]

theorem main_theorem_of_global_CFT.group_isomorphism :
  (number_field.C_K K) ⧸ (subgroup.connected_component_of_one (number_field.C_K K)) ≃* (G_K_ab K) :=
sorry

noncomputable theorem main_theorem_of_global_CFT.homeomorph :
  homeomorph ((number_field.C_K K) ⧸ (subgroup.connected_component_of_one (number_field.C_K K)))
    (G_K_ab K) := 
{ continuous_to_fun  := sorry,
  continuous_inv_fun := sorry,
  ..(main_theorem_of_global_CFT.group_isomorphism K) }