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
def A_K := (A_K_f K) × (ℝ ⊗[ℚ] K) --(K ⊗[ℚ] ℝ)

variables (n : ℕ) 
instance : ring (fin n → ℝ) := pi.ring
instance : topological_space (fin n → ℝ) := Pi.topological_space
instance : has_continuous_add (fin n → ℝ) := pi.has_continuous_add'
instance : has_continuous_mul (fin n → ℝ) := pi.has_continuous_mul'
instance : topological_ring (fin n → ℝ) := topological_ring.mk


open_locale big_operators

def linear_equiv.Q_basis : (fin (finite_dimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
linear_equiv.symm (basis.equiv_fun (finite_dimensional.fin_basis ℚ K))

def linear_map.Rn_to_R_tensor_Qn : (fin (finite_dimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] 
(ℝ ⊗[ℚ] (fin (finite_dimensional.finrank ℚ K) → ℚ)) :=
{ to_fun    := λ x, ∑ (m : fin (finite_dimensional.finrank ℚ K)), tensor_product.mk _ _ _ (x m)
      (λ k : (fin (finite_dimensional.finrank ℚ K)), (1 : ℚ)),
  map_add'  := λ x y, by simp only [map_add, tensor_product.mk_apply, pi.add_apply,
    linear_map.add_apply, finset.sum_add_distrib],
  map_smul' := λ r x, begin
    simp only [tensor_product.mk_apply, ring_hom.id_apply, pi.smul_apply, finset.smul_sum], refl,
  end,}

lemma linear_map.base_change :
(ℝ ⊗[ℚ] (fin (finite_dimensional.finrank ℚ K) → ℚ))  →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
linear_map.base_change ℝ (linear_equiv.Q_basis K).to_linear_map


def linear_map.Rn_to_R_tensor_K : (fin (finite_dimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] K) := 
linear_map.comp (linear_map.base_change K) (linear_map.Rn_to_R_tensor_Qn K)

instance : comm_ring (A_K_f K) := 
finite_adele_ring'.comm_ring (ring_of_integers K) K
instance : comm_ring (A_K K) := prod.comm_ring
instance : topological_space (A_K_f K) := 
finite_adele_ring'.topological_space (ring_of_integers K) K
instance : topological_ring (A_K_f K) := 
finite_adele_ring'.topological_ring (ring_of_integers K) K
def infinite_adeles.ring_topology : ring_topology (ℝ ⊗[ℚ] K) := 
ring_topology.coinduced (linear_map.Rn_to_R_tensor_K K)
instance : topological_space (ℝ ⊗[ℚ] K) := (infinite_adeles.ring_topology K).to_topological_space
instance : topological_ring (ℝ ⊗[ℚ] K) := (infinite_adeles.ring_topology K).to_topological_ring
instance : topological_space (A_K K) := prod.topological_space
instance : topological_ring (A_K K) := prod.topological_ring

def inj_K_f : K → A_K_f K := inj_K (ring_of_integers K) K
def inj_K_f.ring_hom : ring_hom K (A_K_f K) := inj_K.ring_hom (ring_of_integers K) K

lemma inj_K_f.ring_hom.v_comp (v : maximal_spectrum (ring_of_integers K)) (k : K) :
  ((inj_K_f.ring_hom K) k).val v = (coe : K → (K_v K v)) k := rfl

def inj_K : K → A_K K := λ x, ⟨inj_K_f K x, algebra.tensor_product.include_right x⟩
def inj_K.ring_hom : ring_hom K (A_K K) := 
ring_hom.prod (inj_K_f.ring_hom K) (@algebra.tensor_product.include_right ℚ _ ℝ _ _ K _ _ )

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