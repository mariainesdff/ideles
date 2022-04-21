/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.class_group
import adeles_function_field
import ideles_R

/-!
# The group of idèles of a function field
We define the group of finite idèles and the group of idèles of a function field `F`, both of which
are topological commutative groups.

We also prove that `F*` can be regarded as a subgroup of `I_F_f` and `I_F` and define the idèle
class group of `F` as the quotient `I_F/F*`. We then show that the ideal class group of `F` is
isomorphic to an explicit quotient of `C_F` as topological groups, by constructing a continuous
surjective group homomorphism from `C_F` to the ideal class group `Cl(F)` of `F` and
computing its kernel.

## Main definitions
- `function_field.I_F_f` : The finite idèle group of the function field `F`.
- `function_field.I_F`   : The idèle group of the function field `F`.
- `function_field.C_F`   : The idèle class group of the function field `F`.
- `function_field.C_F.map_to_class_group` : The natural group homomorphism from `C_F` to `Cl(F)`.

## Main results
- `function_field.C_F.map_to_class_group.surjective` : The natural map `C_F → Cl(F)` is surjective.
- `function_field.C_F.map_to_class_group.continuous` : The natural map `C_F → Cl(F)` is continuous.
- `function_field.C_F.map_to_class_group.mem_kernel_iff` : We compute the kernel of `C_F → Cl(F)`.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
idèle group, number field, function field
-/

noncomputable theory

open set function
open_locale tensor_product

namespace function_field
/-! ### The idèle group of a function field
We define the (finite) idèle group of a function field `F`, with its topological group structure. -/

variables (k F : Type) [field k] [field F] [algebra (polynomial k) F] [algebra (ratfunc k) F] 
  [function_field k F] [is_scalar_tower (polynomial k) (ratfunc k) F] 
  [is_separable (ratfunc k) F]

/-- The finite idèle group of the function field `F`. -/
def I_F_f := units (A_F_f k F)
/-- The idèle group of the function field `F`.-/
def I_F := units (A_F k F)

instance : comm_group (I_F_f k F) := units.comm_group
instance : comm_group (I_F k F) := units.comm_group
instance : topological_space (I_F_f k F) := 
finite_idele_group'.topological_space (ring_of_integers k F) F
instance : topological_group (I_F_f k F) :=
finite_idele_group'.topological_group (ring_of_integers k F) F
instance : topological_space (I_F k F) := units.topological_space
instance : topological_group (I_F k F) := units.topological_group

/-- `I_F` is isomorphic to the product `I_F_f × ((kt_infty k) ⊗[ratfunc k] F)*`, as groups. -/
def I_F.as_prod : I_F k F ≃* (I_F_f k F) × units ((kt_infty k) ⊗[ratfunc k] F) := 
by apply @mul_equiv.prod_units (A_F_f k F) ((kt_infty k) ⊗[ratfunc k] F) _ _ 

/-- `I_F` is homeomorphic to the product `I_F_f × ((kt_infty k) ⊗[ratfunc k] F)*`. -/
def I_F.as_prod.homeo : homeomorph (I_F k F) ((I_F_f k F) × units ((kt_infty k) ⊗[ratfunc k] F)) := 
units.homeomorph.prod_units

variables {k F}
lemma I_F.as_prod.continuous : continuous ((I_F.as_prod k F).to_fun) :=
(I_F.as_prod.homeo k F).continuous_to_fun
lemma I_F.as_prod.continuous_inv : continuous ((I_F.as_prod k F).inv_fun) :=
(I_F.as_prod.homeo k F).continuous_inv_fun

/-- Construct an idèle of `F` given a finite idèle and a unit of `(kt_infty k) ⊗[ratfunc k] F`. -/
def I_F.mk (x : I_F_f k F) (u : units ((kt_infty k) ⊗[ratfunc k] F)) : I_F k F :=
(I_F.as_prod k F).inv_fun (prod.mk x u)

variables (k F)

 /-- The projection from `I_F` to `I_F_f`, as a group homomorphism. -/
def I_F.fst : monoid_hom (I_F k F) (I_F_f k F) := 
{ to_fun := λ x, ((I_F.as_prod k F).to_fun x).1,
  map_one' := by {rw [mul_equiv.to_fun_eq_coe, mul_equiv.map_one, prod.fst_one]},
  map_mul' := λ x y, by {simp only [prod.fst_mul, mul_equiv.to_fun_eq_coe, mul_equiv.map_mul]}}

variables {k F}
/-- The projection map `I_F.fst` is surjective. -/
lemma I_F.fst.surjective : function.surjective (I_F.fst k F) := 
begin
  intro x,
  use I_F.mk x (1 : units ((kt_infty k) ⊗[ratfunc k] F)),
  rw [I_F.fst, monoid_hom.coe_mk, mul_equiv.to_fun_eq_coe, I_F.mk, 
    mul_equiv.inv_fun_eq_symm, mul_equiv.apply_symm_apply],
end

/-- The projection map `I_F.fst` is continuous. -/
lemma I_F.fst.continuous : continuous (I_F.fst k F) := 
continuous.comp continuous_fst I_F.as_prod.continuous

lemma right_inv (x : units F) : (inj_F.ring_hom k F) x.val * (inj_F.ring_hom k F) x.inv = 1 := 
begin
  rw [← (inj_F.ring_hom k F).map_mul, units.val_eq_coe, units.inv_eq_coe_inv, units.mul_inv],
  exact (inj_F.ring_hom k F).map_one
end

lemma left_inv (x : units F) : (inj_F.ring_hom k F) x.inv * (inj_F.ring_hom k F) x.val  = 1 := 
by rw [mul_comm, right_inv]

variables (k F)
/-- The map from `F^*` to `I_F` sending `x` to `((x)_v, 1 ⊗ x)`. -/
def inj_units_F : units F → I_F k F := units.map (inj_F.ring_hom k F).to_monoid_hom

variables {k F}
@[simp] lemma inj_units_F.map_one : inj_units_F k F 1 = 1 := by rw [inj_units_F, map_one]

@[simp] lemma inj_units_F.map_mul (x y : units F) : 
  inj_units_F k F (x*y) = (inj_units_F k F x) * (inj_units_F k F y) := by rw [inj_units_F, map_mul]

variables (k F)
/-- `inj_units_F` is a group homomorphism. -/
def inj_units_F.group_hom : monoid_hom (units F) (I_F k F) := 
{ to_fun    := inj_units_F k F,
  map_one'  := inj_units_F.map_one,
  map_mul'  := inj_units_F.map_mul, }

/-- `inj_units_F` is injective. -/
lemma inj_units_F.injective : injective (inj_units_F k F) :=
begin
  intros x y hxy,
  simp only [inj_units_F, units.map, monoid_hom.mk', ring_hom.coe_monoid_hom, monoid_hom.coe_mk,
    ← units.eq_iff, units.coe_mk] at hxy,
  ext,
  exact inj_F.injective k F hxy,
end

/-- The idèle class group of `F` is the quotient of `I_F` by the group `F*` of principal idèles. -/
def C_F := (I_F k F) ⧸ (inj_units_F.group_hom k F).range

instance : comm_group (C_F k F) := 
quotient_group.has_quotient.quotient.comm_group ((inj_units_F.group_hom k F).range)

instance : topological_space (C_F k F) := quotient.topological_space

instance : topological_group (C_F k F) :=
topological_group_quotient ((inj_units_F.group_hom k F).range)

/-- The `v`-adic absolute value of the `v`th component of the idèle `x`. -/
def v_comp_val (x : I_F k F) (v : maximal_spectrum (ring_of_integers k F)) :
  with_zero (multiplicative ℤ) := valued.v (x.val.1.val v)

/-- The `v`-adic absolute value of the inverse of the `v`th component of the idèle `x`. -/
def v_comp_inv (x : I_F k F) (v : maximal_spectrum (ring_of_integers k F)) :
  with_zero (multiplicative ℤ) := valued.v (x.inv.1.val v)

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`x_v ∉ R_v` or `x⁻¹_v ∉ R_v`. -/ 
lemma I_F_f.restricted_product (x : I_F_f k F) : finite 
  ({ v : maximal_spectrum (ring_of_integers k F) | ¬ (x.val.val v) ∈ v.adic_completion_integers F }
  ∪ { v : maximal_spectrum (ring_of_integers k F) | 
    ¬ (x.inv.val v) ∈ v.adic_completion_integers F }) :=
restricted_product (ring_of_integers k F) F x

lemma prod_val_inv_eq_one (x : I_F k F) (v : maximal_spectrum (ring_of_integers k F)) : 
  (x.val.fst.val v) * (x.inv.fst.val v) = 1  :=
begin
  rw [← pi.mul_apply, mul_apply_val, ← prod.fst_mul, units.val_inv,
    prod.fst_one, subtype.val_eq_coe, ← one_def, subtype.coe_mk],
  refl,
end

lemma valuation.prod_val_inv_eq_one (x : I_F k F) (v : maximal_spectrum (ring_of_integers k F)) : 
  (v_comp_val k F x v) * (v_comp_inv k F x v) = 1 :=
begin
  simp only [v_comp_val, v_comp_inv],
  rw [← valued.v.map_mul, prod_val_inv_eq_one k F x v],
  exact valuation.map_one _,
end

lemma v_comp.ne_zero (x : I_F k F) (v : maximal_spectrum (ring_of_integers k F)) :
  (x.val.1.val v) ≠ 0 := left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one k F x v)

/-- For any idèle `x`, there are finitely many maximal ideals `v` of `R` for which `x_v ∉ R_v` or
`x⁻¹_v ∉ R_v`. -/ 
lemma I_F.restricted_product (x : I_F k F) : finite ({ v : maximal_spectrum (ring_of_integers k F) |
    (¬ (x.val.1.val v) ∈ v.adic_completion_integers F) } ∪ { v : maximal_spectrum
    (ring_of_integers k F) | ¬ (x.inv.1.val v) ∈ v.adic_completion_integers F}) :=
finite.union x.val.1.property x.inv.1.property

/-- For any idèle `x`, there are finitely many maximal ideals `v` of `R` for which `|x_v|_v ≠ 1`. -/
lemma I_F.finite_exponents (x : I_F k F) :
  finite { v : maximal_spectrum (ring_of_integers k F) | v_comp_val k F x v ≠ 1 } :=
begin
  have h_subset : { v : maximal_spectrum (ring_of_integers k F) | v_comp_val k F x v ≠ 1 } ⊆ 
  { v : maximal_spectrum (ring_of_integers k F) | ¬ (x.val.1.val v) ∈ v.adic_completion_integers F } ∪
  { v : maximal_spectrum (ring_of_integers k F) | ¬ (x.inv.1.val v) ∈ v.adic_completion_integers F },
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq, adic_completion.is_integer,
      adic_completion.is_integer],
    rw mem_set_of_eq at hv,
    cases (lt_or_gt_of_ne hv) with hlt hgt,
    { right,
      have h_one : (v_comp_val k F x v) * (v_comp_inv k F x v) = 1 := 
      valuation.prod_val_inv_eq_one k F x v,
      have h_inv : 1 < v_comp_inv k F x v,
      { have hx : v_comp_val k F x v ≠ 0,
        { rw [v_comp_val, valuation.ne_zero_iff],
          exact v_comp.ne_zero k F x v,},
        rw mul_eq_one_iff_inv_eq₀ hx at h_one,
        rw [← h_one, ← with_zero.inv_one, inv_lt_inv₀ (ne.symm zero_ne_one) hx],
        exact hlt, },
      exact not_le.mpr h_inv,},
    { left, exact not_le.mpr hgt, }},
  exact finite.subset (I_F.restricted_product k F x) h_subset,
end

/-- The natural map from `I_F_f` to the group of invertible fractional ideals of `F`, sending a 
finite idèle `x` to the product `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive 
`v`-adic valuation. -/
def I_F_f.map_to_fractional_ideals : monoid_hom
  (I_F_f k F) (units (fractional_ideal (non_zero_divisors (ring_of_integers k F)) F)) := 
map_to_fractional_ideals (ring_of_integers k F) F

variables {k F}
/-- `I_F_f.map_to_fractional_ideals` is surjective. -/
lemma I_F_f.map_to_fractional_ideals.surjective :
  function.surjective (I_F_f.map_to_fractional_ideals k F) :=
@map_to_fractional_ideals.surjective (ring_of_integers k F) F _ _ _ _ _ _

/-- A finite idèle `x` is in the kernel of `I_F_f.map_to_fractional_ideals` if and only if 
`|x_v|_v = 1` for all `v`. -/
lemma I_F_f.map_to_fractional_ideals.mem_kernel_iff (x : I_F_f k F) : 
  I_F_f.map_to_fractional_ideals k F x = 1 ↔ 
  ∀ v : maximal_spectrum (ring_of_integers k F), 
    finite_idele.to_add_valuations (ring_of_integers k F) F x v = 0 := 
@map_to_fractional_ideals.mem_kernel_iff (ring_of_integers k F) F _ _ _ _ _ _ x

/-- `I_F_f.map_to_fractional_ideals` is continuous. -/
lemma I_F_f.map_to_fractional_ideals.continuous :
  continuous (I_F_f.map_to_fractional_ideals k F) :=
@map_to_fractional_ideals.continuous (ring_of_integers k F) F _ _ _ _ _ _

variables (k F)
/-- The natural map from `I_F` to the group of invertible fractional ideals of `F`. -/
def I_F.map_to_fractional_ideals : 
  monoid_hom (I_F k F) (units (fractional_ideal (non_zero_divisors (ring_of_integers k F)) F)) := 
monoid_hom.comp (I_F_f.map_to_fractional_ideals k F) (I_F.fst k F)

variables {k F}
/-- `I_F.map_to_fractional_ideals` is surjective. -/
lemma I_F.map_to_fractional_ideals.surjective :
  function.surjective (I_F.map_to_fractional_ideals k F) :=
function.surjective.comp I_F_f.map_to_fractional_ideals.surjective I_F.fst.surjective

/-- An idèle `x` is in the kernel of `I_F_f.map_to_fractional_ideals` if and only if `|x_v|_v = 1`
for all `v`. -/
lemma I_F.map_to_fractional_ideals.mem_kernel_iff (x : I_F k F) : 
  I_F.map_to_fractional_ideals k F x = 1 ↔ 
  ∀ v : maximal_spectrum (ring_of_integers k F), 
    finite_idele.to_add_valuations (ring_of_integers k F) F (I_F.fst k F x) v = 0 :=
I_F_f.map_to_fractional_ideals.mem_kernel_iff (I_F.fst k F x)

/-- `I_F.map_to_fractional_ideals` is continuous. -/
lemma I_F.map_to_fractional_ideals.continuous :
  continuous (I_F.map_to_fractional_ideals k F) :=
continuous.comp I_F_f.map_to_fractional_ideals.continuous I_F.fst.continuous

variables (k F)
/-- The map from `I_F_f` to the ideal  class group of `F` induced by 
`I_F_f.map_to_fractional_ideals`. -/
def I_F_f.map_to_class_group :
  (I_F_f k F) → (class_group (ring_of_integers k F) F) := 
λ x, quotient_group.mk (I_F_f.map_to_fractional_ideals k F x)

instance : topological_space (class_group ↥(ring_of_integers k F) F) := ⊥

instance : topological_group (class_group ↥(ring_of_integers k F) F) := 
{ continuous_mul := continuous_of_discrete_topology,
  continuous_inv := continuous_of_discrete_topology, }

variables {k F}
lemma I_F_f.map_to_class_group.surjective : surjective (I_F_f.map_to_class_group k F) := 
surjective.comp quotient.surjective_quotient_mk' I_F_f.map_to_fractional_ideals.surjective

lemma I_F_f.map_to_class_group.continuous : continuous (I_F_f.map_to_class_group k F) := 
continuous.comp continuous_bot (I_F_f.map_to_fractional_ideals.continuous)

variables (k F)
/-- The map from `I_F` to the ideal  class group of `K` induced by 
`I_F.map_to_fractional_ideals`. -/
def I_F.map_to_class_group :
  (I_F k F) → (class_group (ring_of_integers k F) F) :=
λ x, quotient_group.mk' _ (I_F.map_to_fractional_ideals k F x)

variables {k F}
lemma I_F.map_to_class_group.surjective : surjective (I_F.map_to_class_group k F) := 
surjective.comp quotient.surjective_quotient_mk' I_F.map_to_fractional_ideals.surjective

lemma I_F.map_to_class_group.continuous : continuous (I_F.map_to_class_group k F) := 
continuous.comp continuous_bot I_F.map_to_fractional_ideals.continuous

variables {k F}
lemma I_F.map_to_class_group.map_one : I_F.map_to_class_group k F 1 = 1 :=
by {simp only [I_F.map_to_class_group, monoid_hom.map_one] }

lemma I_F.map_to_class_group.map_mul (x y : I_F k F) : I_F.map_to_class_group k F (x * y) = 
  I_F.map_to_class_group k F x * I_F.map_to_class_group k F y :=
by {simp only [I_F.map_to_class_group, monoid_hom.map_mul] }

/-- The map from `I_F` to the ideal  class group of `F` induced by 
`I_F.map_to_fractional_ideals` is a group homomorphism. -/
def I_F.monoid_hom_to_class_group : (I_F k F) →* (class_group (ring_of_integers k F) F) := 
{ to_fun   := I_F.map_to_class_group k F,
  map_one' := I_F.map_to_class_group.map_one,
  map_mul' := λ x y, I_F.map_to_class_group.map_mul x y }

lemma I_F_f.unit_image.mul_inv (x : units F) :
  ((inj_F_f.ring_hom k F) x.val) * ((inj_F_f.ring_hom k F) x.inv) = 1 :=
by rw [← ring_hom.map_mul, units.val_eq_coe, units.inv_eq_coe_inv, units.mul_inv, ring_hom.map_one]

lemma I_F_f.unit_image.inv_mul (x : units F):
  ((inj_F_f.ring_hom k F) x.inv) * ((inj_F_f.ring_hom k F) x.val) = 1 :=
by rw [mul_comm, I_F_f.unit_image.mul_inv]

open_locale classical

/-- `I_F_f.map_to_fractional_ideals` sends the principal finite idèle `(x)_v` corresponding to 
`x ∈ F*` to the principal fractional ideal generated by `x`. -/
lemma I_F_f.map_to_fractional_ideal.map_units (x : units F) : 
  fractional_ideal.span_singleton (non_zero_divisors ↥(ring_of_integers k F)) (x : F) = 
  ((I_F_f.map_to_fractional_ideals k F) (units.mk ((inj_F_f.ring_hom k F) x.val)
  ((inj_F_f.ring_hom k F) x.inv) (I_F_f.unit_image.mul_inv x) (I_F_f.unit_image.inv_mul x))) := 
begin
  set I := (fractional_ideal.span_singleton (non_zero_divisors ↥(ring_of_integers k F)) (x : F))
    with hI_def,
  have hI : I ≠ 0,
  { rw [hI_def, fractional_ideal.span_singleton_ne_zero_iff],
    exact units.ne_zero x },
  rw ← fractional_ideal.factorization_principal I hI x hI_def,
  apply finprod_congr,
  intro v,
  apply congr_arg,
  rw finite_idele.to_add_valuations,
  simp only,
  rw [with_zero.to_integer, ← injective.eq_iff multiplicative.of_add.injective, of_add_neg,
    of_add_to_add, ← neg_sub_neg, of_add_sub, ← inv_div'],
  apply congr_arg,
  have hv : valued.v (((inj_F_f.ring_hom k F) x.val).val v) ≠ (0 : with_zero (multiplicative ℤ)),
  { rw [valuation.ne_zero_iff, inj_F_f.ring_hom.v_comp, units.val_eq_coe,
      ← uniform_space.completion.coe_zero,
      injective.ne_iff (@uniform_space.completion.coe_inj F v.us' v.ss)],
    exact units.ne_zero x },
  let z :=  classical.some (with_zero.to_integer._proof_1 hv),
  let hz :=  classical.some_spec (with_zero.to_integer._proof_1 hv),
  rw [← with_zero.coe_inj, hz, v.valued_adic_completion_def, inj_F_f.ring_hom,
    inj_K.ring_hom_apply, inj_K_apply, valued.extension_extends, units.val_eq_coe,
    v.v_valued_K_def, maximal_spectrum.valuation_def],
  simp only,
  rw [with_zero.coe_div, maximal_spectrum.int_valuation_def_if_neg v
    (non_zero_divisors.coe_ne_zero _), maximal_spectrum.int_valuation_def_if_neg],
  { rw [ne.def, ← @is_fraction_ring.mk'_eq_zero_iff_eq_zero _ _ F _ _ _ _ _],
    convert units.ne_zero x,
    exact classical.some_spec (classical.some_spec
    (maximal_spectrum.valuation_def._proof_1 (x : F))), },
end

/-- `I_F.map_to_fractional_ideals` sends the principal idèle `(x)_v` corresponding to `x ∈ F*` to 
the principal fractional ideal generated by `x`. -/
lemma I_F.map_to_fractional_ideals.map_units_F (x : units F) : 
  fractional_ideal.span_singleton (non_zero_divisors ↥(ring_of_integers k F)) (x : F) = 
  ↑((I_F.map_to_fractional_ideals k F) ((inj_units_F.group_hom k F) x)) := 
I_F_f.map_to_fractional_ideal.map_units x

/-- The kernel of `I_F.map_to_fractional_ideals` contains the principal idèles `(x)_v`, for 
`x ∈ F*`. -/
lemma I_F.map_to_class_group.map_units_F (x : units F) :
  I_F.map_to_class_group k F ((inj_units_F.group_hom k F) x) = 1 :=
begin
  simp only [I_F.map_to_class_group],
  rw [quotient_group.mk'_apply, quotient_group.eq_one_iff, monoid_hom.mem_range],
  simp only [to_principal_ideal_eq_iff], 
  use x,
  exact I_F.map_to_fractional_ideals.map_units_F x,
end

/-- Every nonzero element in a field is a unit. -/
def field.units.mk' {F : Type*} [field F] (k : F) (hk : k ≠ 0) : units F :=
{ val     := k,
  inv     := k⁻¹,
  val_inv := mul_inv_cancel hk,
  inv_val := inv_mul_cancel hk}

lemma I_F.map_to_fractional_ideals.apply (x : I_F k F) : (((I_F.map_to_fractional_ideals k F) x) : 
  fractional_ideal (non_zero_divisors ↥(ring_of_integers k F)) F) = 
  finprod (λ (v : maximal_spectrum ↥(ring_of_integers k F)), 
    (v.as_ideal : fractional_ideal (non_zero_divisors ↥(ring_of_integers k F)) F)^
    finite_idele.to_add_valuations ↥(ring_of_integers k F) F ((I_F.fst k F) x) v) := rfl

/-- If the image of `x ∈ I_F` under `I_F.map_to_class_group` is the principal fractional ideal
generated by `u ∈ F*`, then for every maximal ideal `v` of the ring of integers of `F`,
`|x_v|_v = |u|_v`. -/
lemma I_F.map_to_class_group.valuation_mem_kernel (x : I_F k F) (u : units F)
  (v : maximal_spectrum (ring_of_integers k F))
  (hux : fractional_ideal.span_singleton (non_zero_divisors ↥(ring_of_integers k F)) (u : F) = 
    (((I_F.map_to_fractional_ideals k F) x) :
      fractional_ideal (non_zero_divisors ↥(ring_of_integers k F)) F)) :
  valued.v (((I_F.fst k F) x).val.val v) = valued.v ((coe : F → v.adic_completion F) u.val) :=
begin
  set nu := classical.some (is_localization.mk'_surjective
    (non_zero_divisors ↥(ring_of_integers k F)) (u : F)) with h_nu,
  set du' := classical.some (classical.some_spec (is_localization.mk'_surjective 
    (non_zero_divisors ↥(ring_of_integers k F)) (u : F))) with h_du',
  set du : ↥(ring_of_integers k F) := ↑du' with h_du,
  have h := classical.some_spec (classical.some_spec (is_localization.mk'_surjective
    (non_zero_divisors ↥(ring_of_integers k F)) (u : F))),
  rw [← h_du', ← h_nu] at h,
  have h_nu_ne_zero : nu ≠ 0,
  { intro h_contr,
    rw [h_contr, is_localization.mk'_zero] at h,
    exact (units.ne_zero u) (eq.symm h)},
  have h_du_ne_zero : du ≠ 0,
  { rw h_du,
    exact non_zero_divisors.coe_ne_zero _, },
  rw I_F.map_to_fractional_ideals.apply at hux,
  { have h_exps_v:  ((associates.mk v.as_ideal).count 
      (associates.mk (ideal.span {nu})).factors : ℤ) - 
      ((associates.mk v.as_ideal).count (associates.mk (ideal.span {du})).factors : ℤ) = 
      finite_idele.to_add_valuations ↥(ring_of_integers k F) F ((I_F.fst k F) x) v,
    { rw [← fractional_ideal.count_finprod F v (finite_idele.to_add_valuations
        ↥(ring_of_integers k F) F ((I_F.fst k F) x)) (finite_add_support _ _ _), ← hux,  eq_comm],
      apply fractional_ideal.count_well_defined F v,
      { rw fractional_ideal.span_singleton_ne_zero_iff,
        exact units.ne_zero u, },
      { rw [fractional_ideal.coe_ideal_span_singleton, 
          fractional_ideal.span_singleton_mul_span_singleton, ← h, is_fraction_ring.mk'_eq_div, 
          h_du, div_eq_inv_mul], }},
    simp only [finite_idele.to_add_valuations, with_zero.to_integer, eq_neg_iff_eq_neg, neg_sub]
      at h_exps_v,
    conv_rhs {rw [v.valued_adic_completion_def, units.val_eq_coe], },
    rw [valued.extension_extends, v.v_valued_K_def],
    simp only [maximal_spectrum.valuation_def],
    rw [← h_du, ← h_nu, maximal_spectrum.int_valuation_def_if_neg, 
    maximal_spectrum.int_valuation_def_if_neg, ← with_zero.coe_div, ← of_add_sub, neg_sub_neg,
    ← h_exps_v, of_add_to_add, eq_comm],
    exact classical.some_spec (with_zero.to_integer._proof_1 _),
    { exact h_du_ne_zero },
    { exact h_nu_ne_zero }},
end

/-- An element `x ∈ I_F` is in the kernel of `C_F → Cl(F)` if and only if there exist `u ∈ F*` and
`y ∈ I_F` such that `x = u*y` and `|y_v|_v = 1` for all `v`. -/
lemma I_F.map_to_class_group.mem_kernel_iff (x : I_F k F) : 
  I_F.map_to_class_group k F x = 1 ↔ ∃ (u : F) (hu : u ≠ 0),
  ∀ v : maximal_spectrum (ring_of_integers k F), 
    (finite_idele.to_add_valuations ↥(ring_of_integers k F) F ((I_F.fst k F) x) v) 
    = -with_zero.to_integer (units.valuation_ne_zero (ring_of_integers k F) F v hu) :=
begin
  rw [I_F.map_to_class_group, quotient_group.coe_mk', quotient_group.eq_one_iff,
      monoid_hom.mem_range],
    simp_rw [to_principal_ideal_eq_iff],
  refine ⟨λ h, _, λ h, _⟩,
 { obtain ⟨u, hu⟩ := h,
    use [(u : F), units.ne_zero u],
    intro v,
    rw [finite_idele.to_add_valuations, neg_inj, with_zero.to_integer,
      with_zero.to_integer, injective.eq_iff multiplicative.to_add.injective],
    apply classical.some_spec2,
    intros a ha,
    rw eq_comm,
    apply classical.some_spec2,
    intros b hb,
    have h_valuations : valued.v (((I_F.fst k F) x).val.val v) =
      valued.v ((coe : F → v.adic_completion F) (u : F)),
    { apply I_F.map_to_class_group.valuation_mem_kernel x u v hu },
    rw [← h_valuations, ← hb] at ha,
    rw ← with_zero.coe_inj,
    exact ha, }, 
  { obtain ⟨u, hu, h_vals⟩ := h,
    use field.units.mk' u hu,
    rw [I_F.map_to_fractional_ideals.map_units_F, I_F.map_to_fractional_ideals,
      I_F_f.map_to_fractional_ideals, map_to_fractional_ideals, monoid_hom.coe_comp,
      comp_app, monoid_hom.coe_mk,map_to_fractional_ideals.def, units.coe_mk],
    simp only [map_to_fractional_ideals.val],
    apply finprod_congr,
    intro v,
    rw h_vals v,
    refl, }
  end

variables (k F)
/-- The map `C_F → Cl(F)` induced by `I_F.map_to_class_group`. -/
def C_F.map_to_class_group :
  (C_F k F) →* (class_group (ring_of_integers k F) F) :=
begin
  apply quotient_group.lift (inj_units_F.group_hom k F).range I_F.monoid_hom_to_class_group _,
  { intros x hx,
    obtain ⟨u, hu⟩ := hx,
    rw ← hu,
    exact I_F.map_to_class_group.map_units_F u, },
end

/-- The natural map `C_F → Cl(F)` is surjective. -/
lemma C_F.map_to_class_group.surjective :
  surjective (C_F.map_to_class_group k F) :=
begin
  intro y,
  obtain ⟨x, hx⟩ := I_F.map_to_class_group.surjective y,
  use [quotient_group.mk x, hx],
end

/-- The natural map `C_F → Cl(F)` is continuous. -/
lemma C_F.map_to_class_group.continuous :
  continuous (C_F.map_to_class_group k F) := 
continuous_quot_lift (quotient_group.lift._proof_1
  (inj_units_F.group_hom k F).range I_F.monoid_hom_to_class_group
  (C_F.map_to_class_group._proof_4 k F)) I_F.map_to_class_group.continuous

/-- An element `x ∈ C_F` is in the kernel of `C_F → Cl(F)` if and only if `x` comes from an idèle 
of the form `u*y`, with `u ∈ F*` and `|y_v|_v = 1` for all `v`. -/
lemma C_F.map_to_class_group.mem_kernel_iff (x : C_F k F) : 
  C_F.map_to_class_group k F x = 1 ↔ 
  ∃ (u : F) (hu : u ≠ 0), ∀ v : maximal_spectrum (ring_of_integers k F), 
    (finite_idele.to_add_valuations ↥(ring_of_integers k F) F 
      ((I_F.fst k F) (classical.some (quot.exists_rep x))) v) 
      = -with_zero.to_integer (units.valuation_ne_zero (ring_of_integers k F) F v hu) :=
begin
  set z := classical.some (quot.exists_rep x) with hz_def,
  have hz := classical.some_spec (quot.exists_rep x),
  have : C_F.map_to_class_group k F x =
    I_F.map_to_class_group k F (classical.some (quot.exists_rep x)),
  { rw [← hz_def, ← hz, C_F.map_to_class_group, ← hz_def, quotient_group.lift_quot_mk],
    refl },
  rw this,
  exact I_F.map_to_class_group.mem_kernel_iff _,
end

end function_field