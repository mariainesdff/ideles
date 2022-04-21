/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import data.real.basic
import number_theory.number_field
import ring_theory.tensor_product
import topology.metric_space.basic
import adeles_R

/-!
# The ring of adèles of a number field
We define the ring of finite adèles and the ring of adèles of a number field, both of which are
topological commutative rings.

## Main definitions
- `number_field.A_K_f` : The finite adèle ring of the number field `K`.
- `number_field.A_K`   : The adèle ring of the number field `K`.
- `number_field.inj_K_f` : The map from `K` to `A_K_f K` sending `k ∈ K ↦ (k)_v`
- `number_field.inj_K` :  The map from `K` to `A_K K` sending `k ∈ K ↦ ((k)_v, 1 ⊗ k)`.

## Main results
- `number_field.inj_K_f.injective` : The map `inj_K_f` is injective.
- `number_field.inj_K_f.ring_hom` : The injection `inj_K_f` is a ring homomorphism from `K` to
  `A_K_f K`. Hence we can regard `K` as a subring of `A_K_f K`.
- `number_field.inj_K.injective` : The map `inj_K` is injective.
- `number_field.inj_K.ring_hom` : The injection `inj_K` is a ring homomorphism from `K` to `A_K K`.
  Hence we can regard `K` as a subring of `A_K K`.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adèle ring, number field
-/

noncomputable theory

open function

open_locale tensor_product

namespace number_field
/-! ### The adèle ring of a number field
We define the (finite) adèle ring of a number field `K`, with its topological ring structure. -/
variables (K : Type) [field K] [number_field K]

/-- The finite adèle ring of `K`.-/
def A_K_f := finite_adele_ring' (ring_of_integers K) K
/-- The adèle ring of `K`.-/
def A_K := (A_K_f K) × (ℝ ⊗[ℚ] K)

-- We define the topological ring structure on `ℝ ⊗[ℚ] K`.
-- ℝ^n is a topological ring with the product topology.
variables (n : ℕ) 
instance : ring (fin n → ℝ) := pi.ring
instance : topological_space (fin n → ℝ) := Pi.topological_space
instance : has_continuous_add (fin n → ℝ) := pi.has_continuous_add'
instance : has_continuous_mul (fin n → ℝ) := pi.has_continuous_mul'
instance : topological_semiring (fin n → ℝ) := topological_semiring.mk
instance : topological_ring (fin n → ℝ) := topological_ring.mk

open_locale big_operators
/-- `K` is isomorphic to `ℚ^(dim_ℚ(K))`. -/
def linear_equiv.Q_basis : (fin (finite_dimensional.finrank ℚ K) → ℚ) ≃ₗ[ℚ] K :=
linear_equiv.symm (basis.equiv_fun (finite_dimensional.fin_basis ℚ K))

/-- The natural linear map from `ℝ^n` to `ℝ ⊗[ℚ] ℚ^n`. -/
def linear_map.Rn_to_R_tensor_Qn (n : ℕ) : (fin n → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] (fin n → ℚ)) :=
{ to_fun    := λ x, ∑ (m : fin n), tensor_product.mk _ _ _ (x m) (λ k : (fin n), (1 : ℚ)),
  map_add'  := λ x y, by simp only [map_add, tensor_product.mk_apply, pi.add_apply,
    linear_map.add_apply, finset.sum_add_distrib],
  map_smul' := λ r x, begin
    simp only [tensor_product.mk_apply, ring_hom.id_apply, pi.smul_apply, finset.smul_sum], refl,
  end, }

/-- The map `ℝ ⊗[ℚ] ℚ^(dim_ℚ(K)) → ℝ ⊗[ℚ] K` obtained as a base change of `linear_equiv.Q_basis`. -/
def linear_map.base_change :
(ℝ ⊗[ℚ] (fin (finite_dimensional.finrank ℚ K) → ℚ)) →ₗ[ℝ] (ℝ ⊗[ℚ] K) :=
linear_map.base_change ℝ (linear_equiv.Q_basis K).to_linear_map

/-- The resulting linear map from `ℝ^(dim_ℚ(K))` to `ℝ ⊗[ℚ] K`. -/
def linear_map.Rn_to_R_tensor_K : (fin (finite_dimensional.finrank ℚ K) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] K) := 
linear_map.comp (linear_map.base_change K) (linear_map.Rn_to_R_tensor_Qn _)

instance : comm_ring (A_K_f K) := 
finite_adele_ring'.comm_ring (ring_of_integers K) K
instance : comm_ring (A_K K) := prod.comm_ring
instance : inhabited (A_K_f K) := ⟨0⟩
instance : inhabited (A_K K) := ⟨0⟩
instance : topological_space (A_K_f K) := 
finite_adele_ring'.topological_space (ring_of_integers K) K
instance : topological_ring (A_K_f K) := 
finite_adele_ring'.topological_ring (ring_of_integers K) K
/-- The topological ring structure on `ℝ ⊗[ℚ] K`. -/
def infinite_adeles.ring_topology : ring_topology (ℝ ⊗[ℚ] K) := 
ring_topology.coinduced (linear_map.Rn_to_R_tensor_K K)
instance : topological_space (ℝ ⊗[ℚ] K) := (infinite_adeles.ring_topology K).to_topological_space
instance : topological_ring (ℝ ⊗[ℚ] K) := (infinite_adeles.ring_topology K).to_topological_ring
instance : topological_space (A_K K) := prod.topological_space
instance : topological_ring (A_K K) := prod.topological_ring

/-- The ring ℤ is not a field. -/
lemma int.not_field : ¬ is_field ℤ := 
begin
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use ideal.span{(2 : ℤ)},
  split,
  { simp only [bot_lt_iff_ne_bot, ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, 
      ideal.span_singleton_eq_bot] },
  { rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ideal.mem_span_singleton],
    intro h2,
    have h2_nonneg: 0 ≤ (2 : ℤ) := by simp only [zero_le_bit0, zero_le_one],
    have : (2 : ℤ) = 1 := int.eq_one_of_dvd_one h2_nonneg h2,
    linarith, },
end

/-- The ring of integers of a number field is not a field. -/
lemma ring_of_integers.not_field : ¬ is_field (ring_of_integers K) :=
begin
  have h_int :  algebra.is_integral ℤ (ring_of_integers K),
  { apply is_integral_closure.is_integral_algebra ℤ K,
    { apply_instance },
    { exact ring_of_integers.is_integral_closure },
    { apply_instance }} ,
  have h_inj: function.injective ⇑(algebra_map ℤ ↥(ring_of_integers K)),
  { rw [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_bot_iff_eq_zero],
    intros a ha,
    rw [ring_hom.eq_int_cast, int.cast_eq_zero] at ha,
    exact ha, },
  by_contra hf,
  rw ← is_integral.is_field_iff_is_field h_int h_inj at hf,
  exact int.not_field hf,
end

/-- There exists a nonzero prime ideal of the ring of integers of a number field. -/
instance : inhabited (maximal_spectrum (ring_of_integers K)) := 
begin
  set M := classical.some(ideal.exists_maximal (ring_of_integers K)) with hM_def,
  set hM := classical.some_spec(ideal.exists_maximal (ring_of_integers K)),
  use [M, ideal.is_maximal.is_prime hM],
  { simp only [ideal.zero_eq_bot, ne.def],
    apply ring.ne_bot_of_is_maximal_of_not_is_field hM (ring_of_integers.not_field K),
  }
end

/-- The map from `K` to `A_K_f K` sending `k ∈ K ↦ (k)_v`. -/
def inj_K_f : K → A_K_f K := inj_K (ring_of_integers K) K

lemma inj_K_f.injective : injective (inj_K_f K) := inj_K.injective _ _

/-- The injection `inj_K_f` is a ring homomorphism from `K` to `A_K_f K`. Hence we can regard `K`
as a subring of `A_K_f K`. -/
def inj_K_f.ring_hom : ring_hom K (A_K_f K) := inj_K.ring_hom (ring_of_integers K) K

lemma inj_K_f.ring_hom.v_comp (v : maximal_spectrum (ring_of_integers K)) (k : K) :
  ((inj_K_f.ring_hom K) k).val v = (coe : K → v.adic_completion K) k := rfl

/-- The map from `K` to `A_K K` sending `k ∈ K ↦ ((k)_v, 1 ⊗ k)`. -/
def inj_K : K → A_K K := λ x, ⟨inj_K_f K x, algebra.tensor_product.include_right x⟩

lemma inj_K.injective : injective (inj_K K) := 
begin
  intros x y hxy,
  rw [inj_K, prod.mk.inj_iff] at hxy,
  exact inj_K_f.injective K hxy.1,
end

/-- The injection `inj_K` is a ring homomorphism from `K` to `A_K K`. Hence we can regard `K`
as a subring of `A_K K`. -/
def inj_K.ring_hom : ring_hom K (A_K K) := 
ring_hom.prod (inj_K_f.ring_hom K) (@algebra.tensor_product.include_right ℚ _ ℝ _ _ K _ _ )

end number_field