import data.real.basic
import number_theory.function_field
import number_theory.number_field
import ring_theory.tensor_product
import adeles_R

import topology.metric_space.basic

noncomputable theory

open_locale tensor_product

namespace number_field

variables (K : Type) [field K] [number_field K]

def A_K_f := finite_adele_ring' (ring_of_integers K) K
def A_K := (A_K_f K) × (K ⊗[ℚ] ℝ)

instance : comm_ring (A_K_f K) := 
finite_adele_ring'.comm_ring (ring_of_integers K) K
instance : comm_ring (A_K K) := prod.comm_ring
instance : topological_space (A_K_f K) := 
finite_adele_ring'.topological_space (ring_of_integers K) K
instance : topological_ring (A_K_f K) := 
finite_adele_ring'.topological_ring (ring_of_integers K) K
instance : topological_space (K ⊗[ℚ] ℝ) := sorry
instance : topological_ring (K ⊗[ℚ] ℝ) := sorry
instance : topological_space (A_K K) := prod.topological_space
instance : topological_ring (A_K K) := prod.topological_ring

variables (n : Type*) [fintype n] 
instance : ring (n → ℝ) := pi.ring 
instance : topological_space (n → ℝ) := Pi.topological_space
instance : has_continuous_add (n → ℝ) := pi.has_continuous_add'
instance : has_continuous_mul (n → ℝ) := pi.has_continuous_mul'
instance : topological_ring (n → ℝ) := topological_ring.mk

def inj_K_f : K → A_K_f K := inj_K (ring_of_integers K) K
def inj_K_f.ring_hom : ring_hom K (A_K_f K) := inj_K.ring_hom (ring_of_integers K) K

def inj_K : K → A_K K := λ x, ⟨inj_K_f K x, algebra.tensor_product.include_left x⟩
def inj_K.ring_hom : ring_hom K (A_K K) := 
ring_hom.prod (inj_K_f.ring_hom K) (@algebra.tensor_product.include_left ℚ _ K _ _ ℝ _ _ )

end number_field

namespace function_field

variables (Fq F : Type) [field Fq] [field F] [algebra (polynomial Fq) F] [algebra (ratfunc Fq) F] 
  [function_field Fq F] [algebra (fraction_ring (polynomial Fq)) F]
   [is_scalar_tower (polynomial Fq) (ratfunc Fq) F] [is_separable (ratfunc Fq) F]

def A_F_f := finite_adele_ring' (ring_of_integers Fq F) F
--def A_F := (A_F_f Fq F)

instance : comm_ring (A_F_f Fq F) := 
finite_adele_ring'.comm_ring (ring_of_integers Fq F) F
/- instance : comm_ring (A_F Fq F) :=  
finite_adele_ring'.comm_ring (ring_of_integers Fq F) F
 -/
end function_field