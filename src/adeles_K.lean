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

/- def foo : (fin (finite_dimensional.finrank ℚ K) → ℚ) → K :=
(basis.equiv_fun (finite_dimensional.fin_basis ℚ K)).inv_fun -/

def linear_equiv.Q_basis : (fin (finite_dimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
linear_equiv.symm (basis.equiv_fun (finite_dimensional.fin_basis ℚ K))

--instance : module ℝ (ℝ ⊗[ℚ] K) := infer_instance

open_locale big_operators

instance : module ℚ (fin (finite_dimensional.finrank ℚ K) → ℝ) := sorry

lemma sdfg : (ℝ ⊗[ℚ] (fin (finite_dimensional.finrank ℚ K) → ℚ)) →ₗ[ℝ] 
  (fin (finite_dimensional.finrank ℚ K) → ℝ) :=
begin
  sorry
end

lemma foo' : (fin (finite_dimensional.finrank ℚ K) → ℝ) ≃ₗ[ℝ] 
(ℝ ⊗[ℚ] (fin (finite_dimensional.finrank ℚ K) → ℚ)) :=
{ to_fun := λ x, ∑ (m : fin (finite_dimensional.finrank ℚ K)), tensor_product.mk _ _ _ (x m)
      (λ k : (fin (finite_dimensional.finrank ℚ K)), (1 : ℚ)),
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := 
  begin
    exact (sdfg K).to_fun,

  end,
  left_inv := sorry,
  right_inv := sorry }

lemma linear_equiv.base_change.to_fun' :
(ℝ ⊗[ℚ] (fin (finite_dimensional.finrank ℚ K) → ℚ))  →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
linear_map.base_change ℝ (linear_equiv.Q_basis K).to_linear_map

lemma linear_equiv.base_change : 
(ℝ ⊗[ℚ] (fin (finite_dimensional.finrank ℚ K) → ℚ))  ≃ₗ[ℝ] (ℝ ⊗[ℚ] K) := 
{ inv_fun   := linear_map.base_change ℝ ((linear_equiv.Q_basis K).to_linear_map.inverse
    (linear_equiv.Q_basis K).inv_fun (linear_equiv.Q_basis K).left_inv 
    (linear_equiv.Q_basis K).right_inv),
  left_inv  := 
  begin
    simp only [linear_map.to_fun_eq_coe, linear_equiv.inv_fun_eq_symm],
    refine function.left_inverse_iff_comp.mpr _,
    ext x,
    rcases x,

    
    sorry,
  end,
  right_inv := sorry,
  ..linear_map.base_change ℝ (linear_equiv.Q_basis K).to_linear_map }

def bar : (fin (finite_dimensional.finrank ℚ K) → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] K) := sorry
/- begin
  use ((bar' K).to_fun ∘ (foo' K).to_fun),
  sorry
end -/
--linear_equiv.symm (basis.equiv_fun (finite_dimensional.fin_basis ℚ K))

/- lemma foo' : K →+* (fin (finite_dimensional.finrank ℚ K) → ℚ) :=
{ to_fun := 
  begin
    set B := finite_dimensional.fin_basis ℚ K with hB,
    have hf :=  basis.equiv_fun B,
    use hf.to_fun,
  end,
  map_one' :=
  begin
    simp only,
    rw [linear_equiv.to_fun_eq_coe, basis.equiv_fun_apply],
    --unfold_projs,
    ext,
    simp only [pi.one_apply],
    rw basis.repr,
    sorry,
  end,
  map_mul' := sorry,
  map_zero' := 
  begin
    simp only [linear_equiv.to_fun_eq_coe, map_zero],
  end,
  map_add' := sorry }

  instance : algebra ℚ K := infer_instance -/


instance : comm_ring (A_K_f K) := 
finite_adele_ring'.comm_ring (ring_of_integers K) K
instance : comm_ring (A_K K) := prod.comm_ring
instance : topological_space (A_K_f K) := 
finite_adele_ring'.topological_space (ring_of_integers K) K
instance : topological_ring (A_K_f K) := 
finite_adele_ring'.topological_ring (ring_of_integers K) K
instance : topological_space (ℝ ⊗[ℚ] K) := sorry
instance : topological_ring (ℝ ⊗[ℚ] K) := sorry
instance : topological_space (A_K K) := prod.topological_space
instance : topological_ring (A_K K) := prod.topological_ring

/- variables (n : Type*) [fintype n] 
instance : ring (n → ℝ) := pi.ring 
instance : topological_space (n → ℝ) := Pi.topological_space
instance : has_continuous_add (n → ℝ) := pi.has_continuous_add'
instance : has_continuous_mul (n → ℝ) := pi.has_continuous_mul'
instance : topological_ring (n → ℝ) := topological_ring.mk -/



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