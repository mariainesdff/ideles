import ideles_K
import galois

variables (K : Type) [field K] [number_field K]

def main_theorem_of_global_CFT.group_isomorphism :
  (number_field.C_K K) ⧸ (subgroup.connected_component_of_one (number_field.C_K K)) ≃* (G_K_ab K) :=
sorry

noncomputable theorem main_theorem_of_global_CFT.homeomorph :
  homeomorph ((number_field.C_K K) ⧸ (subgroup.connected_component_of_one (number_field.C_K K)))
    (G_K_ab K) := 
{ continuous_to_fun  := sorry,
  continuous_inv_fun := sorry,
  ..(main_theorem_of_global_CFT.group_isomorphism K) }