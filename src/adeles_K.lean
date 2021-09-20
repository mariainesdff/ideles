import ring_theory.tensor_product
import adeles

noncomputable theory

open_locale tensor_product

variables (K : Type*) [field K] [char_zero K] [finite_dimensional ℚ K]

/-! Finite adeles of K -/
def finite_adeles_map : Type* := K ⊗[ℚ] A_Q_f

instance : ring (finite_adeles_map K) := algebra.tensor_product.tensor_product.ring

/-! Adeles of K -/
def adeles_map : Type* := K ⊗[ℚ] A_Q

instance : ring (adeles_map K) := algebra.tensor_product.tensor_product.ring