import ideles_K
import galois

variables (K : Type) [field K] [number_field K]

theorem main_theorem_of_CFT :
  (number_field.C_K K) ⧸ (subgroup.connected_component_of_one (number_field.C_K K)) ≃* (G_K_ab K) :=
sorry