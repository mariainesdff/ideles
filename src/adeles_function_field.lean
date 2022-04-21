/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import data.real.basic
import number_theory.function_field
import ring_theory.tensor_product
import function_field
import topology.metric_space.basic

/-!
# The ring of adèles of a function field
We define the ring of finite adèles and the ring of adèles of a function field, both of which are
topological commutative rings.

## Main definitions
- `function_field.A_F_f` : The finite adèle ring of the function field `F`.
- `function_field.A_F`   : The adèle ring of the function field `F`.
- `function_field.inj_F_f` : The map from `K` to `A_F_f k F` sending `k ∈ K ↦ (k)_v`
- `function_field.inj_F` :  The map from `K` to `A_F k F` sending `k ∈ K ↦ ((k)_v, 1 ⊗ k)`.

## Main results
- `function_field.inj_F_f.injective` : The map `inj_F_f` is injective.
- `function_field.inj_F_f.ring_hom` : The injection `inj_F_f` is a ring homomorphism from `K` to
  `A_F_f k F`. Hence we can regard `K` as a subring of `A_F_f k F`.
- `function_field.inj_F.injective` : The map `inj_F` is injective.
- `function_field.inj_F.ring_hom` : The injection `inj_F` is a ring homomorphism from `K` to
  `A_F k F`. Hence we can regard `K` as a subring of `A_F k F`.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
adèle ring, function field
-/

noncomputable theory

open function

open_locale tensor_product polynomial

namespace function_field
/-! ### The adèle ring of a function field
We define the (finite) adèle ring of a function field `F`, with its topological ring structure. -/
variables (k F : Type) [field k] [field F] [algebra (polynomial k) F] [algebra (ratfunc k) F] 
  [function_field k F] [is_scalar_tower (polynomial k) (ratfunc k) F] 
  [is_separable (ratfunc k) F]

instance : algebra (ratfunc k) (kt_infty k) := ring_hom.to_algebra
  (@uniform_space.completion.coe_ring_hom (ratfunc k) _ (usq' k) (trq' k) (ugq' k))

/-- The finite adèle ring of `F`.-/
def A_F_f := finite_adele_ring' (ring_of_integers k F) F
/-- The finite adèle ring of `F`.-/
def A_F := (A_F_f k F) × ((kt_infty k) ⊗[ratfunc k] F)

open_locale big_operators

/-- `F` is isomorphic to `k(t)^(dim_(F_q(t))(F))`. -/
def linear_equiv.kt_basis :
  (fin (finite_dimensional.finrank (ratfunc k) F) → (ratfunc k)) ≃ₗ[(ratfunc k)] F :=
linear_equiv.symm (basis.equiv_fun (finite_dimensional.fin_basis (ratfunc k) F))

/-- The natural linear map from `k((t⁻¹))^n` to `k((t⁻¹)) ⊗[k(t)] k(t)^n`. -/
def linear_map.kt_inftyn_to_kt_infty_tensor_ktn (n : ℕ):
  (fin n → (kt_infty k)) →ₗ[(kt_infty k)] 
    ((kt_infty k) ⊗[(ratfunc k)] (fin n→ (ratfunc k))) := 
{ to_fun    := λ x, ∑ (m : fin n), tensor_product.mk _ _ _ (x m) 
    (λ m : (fin n), (1 : (ratfunc k))),
  map_add'  := λ x y, by simp only [map_add, tensor_product.mk_apply, pi.add_apply,
    linear_map.add_apply, finset.sum_add_distrib],
  map_smul' := λ r x, begin
    simp only [tensor_product.mk_apply, ring_hom.id_apply, pi.smul_apply, finset.smul_sum], refl,
end, }

/-- The linear map from `k((t⁻¹)) ⊗[k(t)] k(t)^(dim_(F_q(t))(F))` to `k((t⁻¹)) ⊗[k(t)] F`
obtained as a base change of `linear_equiv.kt_basis`. -/
def linear_map.base_change : ((kt_infty k) ⊗[ratfunc k]
  (fin (finite_dimensional.finrank (ratfunc k) F) → ratfunc k)) →ₗ[kt_infty k]
    ((kt_infty k) ⊗[ratfunc k] F) :=
linear_map.base_change (kt_infty k) (linear_equiv.kt_basis k F).to_linear_map

/-- The resulting linear map from `k((t⁻¹))^(dim_(F_q(t))(F))` to `k((t⁻¹)) ⊗[k(t)] F`. -/
def linear_map.kt_inftyn_to_kt_infty_tensor_F : (fin (finite_dimensional.finrank (ratfunc k) F) →
  (kt_infty k)) →ₗ[kt_infty k] ((kt_infty k) ⊗[ratfunc k] F) := 
linear_map.comp (linear_map.base_change k F) (linear_map.kt_inftyn_to_kt_infty_tensor_ktn k _)

instance : comm_ring (A_F_f k F) := finite_adele_ring'.comm_ring (ring_of_integers k F) F
instance : comm_ring (A_F k F) := prod.comm_ring
instance : inhabited (A_F_f k F) := ⟨0⟩
instance : inhabited (A_F k F) := ⟨0⟩
instance : topological_space (A_F_f k F) := 
finite_adele_ring'.topological_space (ring_of_integers k F) F
instance : topological_ring (A_F_f k F) := 
finite_adele_ring'.topological_ring (ring_of_integers k F) F
/-- The topological ring structure on the infinite places of `F`. -/
def infinite_adeles.ring_topology : ring_topology ((kt_infty k) ⊗[ratfunc k] F) :=
ring_topology.coinduced (linear_map.kt_inftyn_to_kt_infty_tensor_F k F)
instance : topological_space ((kt_infty k) ⊗[ratfunc k] F) :=
(infinite_adeles.ring_topology k F).to_topological_space
instance : topological_ring ((kt_infty k) ⊗[ratfunc k] F) :=
(infinite_adeles.ring_topology k F).to_topological_ring
instance : topological_space (A_F k F) := prod.topological_space
instance : topological_ring (A_F k F) := prod.topological_ring

lemma algebra_map_injective :
  function.injective ⇑(algebra_map k[X] (ring_of_integers k F)) :=
begin
  have hinj : function.injective ⇑(algebra_map k[X] F),
  { rw is_scalar_tower.algebra_map_eq k[X] (ratfunc k) F,
    exact function.injective.comp ((algebra_map (ratfunc k) F).injective)
      (is_fraction_ring.injective k[X] (ratfunc k)), },
  rw (algebra_map k[X] ↥(ring_of_integers k F)).injective_iff,
  intros p hp,
  rw [← subtype.coe_inj, subalgebra.coe_zero] at hp,
  rw (algebra_map k[X] F).injective_iff at hinj,
  exact hinj p hp,
end

/-- The ring of integers of polynomials over `k` is not a field. -/
lemma kX_not_is_field : ¬ is_field k[X] :=
begin
  nontriviality k,
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use ideal.span {polynomial.X},
  split,
  { rw [bot_lt_iff_ne_bot, ne.def, ideal.span_singleton_eq_bot],
    exact polynomial.X_ne_zero, },
  { rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ideal.mem_span_singleton,
      polynomial.X_dvd_iff, polynomial.coeff_one_zero],
    exact one_ne_zero, }
end

/-- The ring of integers of a function field is not a field. -/
lemma not_is_field : ¬ is_field (ring_of_integers k F) :=
by simpa [← (is_integral.is_field_iff_is_field
  (is_integral_closure.is_integral_algebra k[X] F)
  (algebra_map_injective k F))] using (kX_not_is_field k)

/-- There exists a nonzero prime ideal of the ring of integers of a function field. -/
instance : inhabited (maximal_spectrum (ring_of_integers k F)) := 
begin
  set M := classical.some(ideal.exists_maximal (ring_of_integers k F)) with hM_def,
  set hM := classical.some_spec(ideal.exists_maximal (ring_of_integers k F)),
  use [M, ideal.is_maximal.is_prime hM],
  { simp only [ideal.zero_eq_bot, ne.def],
    apply ring.ne_bot_of_is_maximal_of_not_is_field hM (not_is_field k F), }
end

/-- The map from `F` to `A_F_f k F` sending `x ∈ F ↦ (x)_v`. -/
def inj_F_f : F → A_F_f k F := inj_K (ring_of_integers k F) F

lemma inj_F_f.injective : injective (inj_F_f k F) := inj_K.injective _ _

/-- The injection `inj_F_f` is a ring homomorphism from `F` to `A_F_f k F`. Hence we can regard `F`
as a subring of `A_F_f k F`. -/
def inj_F_f.ring_hom : ring_hom F (A_F_f k F) := inj_K.ring_hom (ring_of_integers k F) F

lemma inj_F_f.ring_hom.v_comp (v : maximal_spectrum (ring_of_integers k F)) (x : F) :
  ((inj_F_f.ring_hom k F) x).val v = (coe : F → v.adic_completion F) x := rfl

/-- The map from `F` to `A_F k F` sending `x ∈ F ↦ ((x)_v, 1 ⊗ x)`. -/
def inj_F : F → A_F k F := λ x, ⟨inj_F_f k F x, algebra.tensor_product.include_right x⟩

lemma inj_F.injective : injective (inj_F k F) := 
begin
  intros x y hxy,
  rw [inj_F, prod.mk.inj_iff] at hxy,
  exact inj_F_f.injective k F hxy.1,
end

/-- The injection `inj_F` is a ring homomorphism from `F` to `A_F k F`. Hence we can regard `F`
as a subring of `A_F k F`. -/
def inj_F.ring_hom : ring_hom F (A_F k F) := 
ring_hom.prod (inj_F_f.ring_hom k F)
  (@algebra.tensor_product.include_right (ratfunc k) _ (kt_infty k) _ _ F _ _ )

end function_field