import ring_theory.class_group
import adeles_K
import ideles_R

noncomputable theory

open set function
open_locale tensor_product

section units
variables (R S : Type*) [ring R] [ topological_space R] [topological_ring R] [ring S] 
  [topological_space S] [topological_ring S]

def prod_units.mul_equiv : mul_equiv (units (R × S)) ((units R) × (units S)) := 
{ to_fun    := λ x, prod.mk
    (units.mk (x : R × S).1 ((x⁻¹ : units (R × S)) : R × S).1 
      (by {rw [← prod.fst_mul, units.mul_inv, prod.fst_one]})
      (by {rw [← prod.fst_mul, units.inv_mul, prod.fst_one]}))
    (units.mk (x : R × S).2 ((x⁻¹ : units (R × S)) : R × S).2
      (by {rw [← prod.snd_mul, units.mul_inv, prod.snd_one]})
        (by {rw [← prod.snd_mul, units.inv_mul, prod.snd_one]})),
  inv_fun   := λ x, units.mk (prod.mk (x.1 : R) (x.2 : S)) 
    (prod.mk (((x.1)⁻¹ : units R) : R) (((x.2)⁻¹ : units S) : S))
    (by { rw [prod.mk_mul_mk, units.mul_inv, units.mul_inv], refl })
    (by { rw [prod.mk_mul_mk, units.inv_mul, units.inv_mul], refl }),
  left_inv  := λ x, by simp only [prod.mk.eta, units.coe_mk, units.mk_coe],
  right_inv := λ x, by simp only [prod.mk.eta, units.coe_mk, units.mk_coe],
  map_mul'  := λ x y, 
  by { simp only [prod.fst_mul, prod.snd_mul, units.coe_mk, units.coe_mul], refl }}

variables {R S}
lemma prod_units.mul_equiv.continuous : continuous ⇑(prod_units.mul_equiv R S) :=
begin
  apply continuous.prod_mk,
  { apply continuous_induced_rng,
    apply continuous.prod_mk,
    { simp only [units.coe_mk],
      have h_comp : (λ (x : units (R × S)), (x : R × S).1) = (λ x : (R × S), x.1 ) ∘
        (λ x : (R × S) × (R × S)ᵐᵒᵖ, x.1) ∘ (embed_product (R × S)) := rfl,
      rw h_comp,
      apply continuous.comp continuous_fst
        (continuous.comp continuous_fst continuous_induced_dom) },
    { simp only [units.coe_mk, units.inv_mk],
      have h_comp : (λ (x : units (R × S)), (mul_opposite.op ((x⁻¹ : units (R × S)) : R × S).1)) = 
        (λ x : (R × S)ᵐᵒᵖ, (mul_opposite.op (mul_opposite.unop x).1)) ∘
        (λ x : (R × S) × (R × S)ᵐᵒᵖ, x.2) ∘ (embed_product (R × S)) := rfl,
      rw h_comp,
      apply continuous.comp
        (continuous.comp continuous_op (continuous.comp continuous_fst continuous_unop))
        (continuous.comp continuous_snd continuous_induced_dom) }},
  { apply continuous_induced_rng,
    apply continuous.prod_mk,
    { apply continuous.comp continuous_snd units.continuous_coe },
    { apply continuous.comp continuous_op
       (continuous.comp continuous_snd (continuous.comp units.continuous_coe continuous_inv)),
      apply_instance,}},
end

lemma prod_units.mul_equiv.inv_continuous : continuous ⇑((prod_units.mul_equiv R S).symm) :=
begin
  simp only [prod_units.mul_equiv, ← mul_equiv.inv_fun_eq_symm],
  apply continuous_induced_rng,
  apply continuous.prod_mk,
  { apply continuous.prod_mk (continuous.comp units.continuous_coe continuous_fst)
      (continuous.comp units.continuous_coe continuous_snd), },
  { apply continuous.comp continuous_op,
    apply continuous.comp units.continuous_coe,
    apply continuous_induced_rng,
    apply continuous.prod_mk,
    { apply continuous.prod_mk
        (continuous.comp units.continuous_coe (continuous.comp continuous_inv continuous_fst))
        (continuous.comp units.continuous_coe (continuous.comp continuous_inv continuous_snd));
      apply_instance },
    { apply continuous.comp continuous_op
        (continuous.prod_mk (continuous.comp units.continuous_coe continuous_fst)
          (continuous.comp units.continuous_coe continuous_snd)) }}
end

def prod_units.homeo : homeomorph (units (R × S)) ((units R) × (units S)) := 
{ continuous_to_fun  := prod_units.mul_equiv.continuous,
  continuous_inv_fun := prod_units.mul_equiv.inv_continuous,
  ..prod_units.mul_equiv R S }

end units

namespace number_field

variables (K : Type) [field K] [number_field K]

def I_K_f := units (A_K_f K)
def I_K := units (A_K K)
instance : comm_group (I_K_f K) := units.comm_group
instance : comm_group (I_K K) := units.comm_group
instance : topological_space (I_K_f K) := 
finite_idele_group'.topological_space (ring_of_integers K) K
instance : topological_group (I_K_f K) :=
finite_idele_group'.topological_group (ring_of_integers K) K
instance : topological_space (I_K K) := units.topological_space
instance : topological_group (I_K K) := units.topological_group

lemma I_K_f.def : I_K_f K = units (A_K_f K) := rfl
lemma I_K.def : I_K K = units (A_K K) := rfl

def I_K.as_prod : I_K K ≃* (I_K_f K) × units (K ⊗[ℚ] ℝ) := 
by apply prod_units.mul_equiv (A_K_f K) (K ⊗[ℚ] ℝ)


def I_K.as_prod.homeo : homeomorph (I_K K) ((I_K_f K) × units (K ⊗[ℚ] ℝ)) := 
prod_units.homeo

variable {K}
lemma I_K.as_prod.continuous : continuous ((I_K.as_prod K).to_fun) :=
(I_K.as_prod.homeo K).continuous_to_fun
lemma I_K.as_prod.continuous_inv : continuous ((I_K.as_prod K).inv_fun) :=
(I_K.as_prod.homeo K).continuous_inv_fun

def I_K.mk (x : I_K_f K) (u : units (K ⊗[ℚ] ℝ)) : I_K K := (I_K.as_prod K).inv_fun (prod.mk x u)

variable (K)
def I_K.fst : monoid_hom (I_K K) (I_K_f K) := 
{ to_fun := λ x, ((I_K.as_prod K).to_fun x).1,
  map_one' := by {rw [mul_equiv.to_fun_eq_coe, mul_equiv.map_one, prod.fst_one]},
  map_mul' := λ x y, by {simp only [prod.fst_mul, mul_equiv.to_fun_eq_coe, mul_equiv.map_mul]}}

variable {K}
lemma I_K.fst.surjective : function.surjective (I_K.fst K) := 
begin
  intro x,
  use I_K.mk x (1 : units (K ⊗[ℚ] ℝ)),
  rw [I_K.fst, monoid_hom.coe_mk, mul_equiv.to_fun_eq_coe, I_K.mk, 
    mul_equiv.inv_fun_eq_symm, mul_equiv.apply_symm_apply],
end

lemma I_K.fst.continuous : continuous (I_K.fst K) := 
continuous.comp continuous_fst I_K.as_prod.continuous

lemma right_inv (x : units K) : (inj_K.ring_hom K) x.val * (inj_K.ring_hom K) x.inv = 1 := 
begin
  rw [← (inj_K.ring_hom K).map_mul, units.val_eq_coe, units.inv_eq_coe_inv, units.mul_inv],
  exact (inj_K.ring_hom K).map_one
end

lemma left_inv (x : units K) : (inj_K.ring_hom K) x.inv * (inj_K.ring_hom K) x.val  = 1 := 
by rw [mul_comm, right_inv]

variable (K)
def inj_units_K : units K → I_K K := λ x, ⟨number_field.inj_K.ring_hom K x.val, 
  number_field.inj_K.ring_hom K x.inv, right_inv x, left_inv x⟩

variable {K}
@[simp]
lemma inj_units_K.map_one : inj_units_K K 1 = 1 := 
by {rw inj_units_K, simp only [inj_K.map_one], refl,}

@[simp]
lemma inj_units_K.map_mul (x y : units K) : 
  inj_units_K K (x*y) = (inj_units_K K x) * (inj_units_K K y) := 
begin
  rw inj_units_K, ext;
  simp_rw [units.val_eq_coe, units.coe_mul, units.coe_mk, (inj_K.ring_hom K).map_mul],
end

variable (K)
def inj_units_K.group_hom : monoid_hom (units K) (I_K K) := 
{ to_fun    := inj_units_K K,
  map_one'  := inj_units_K.map_one,
  map_mul'  := inj_units_K.map_mul, }

def C_K := quotient_group.quotient (inj_units_K.group_hom K).range

--instance : group (C_K K) := infer_instance

def v_comp_val (x : I_K K) (v : maximal_spectrum (ring_of_integers K)) :
  with_zero (multiplicative ℤ) := valued.v (x.val.1.val v)

def v_comp_inv (x : I_K K) (v : maximal_spectrum (ring_of_integers K)) :
  with_zero (multiplicative ℤ) := valued.v (x.inv.1.val v)

-- I_K_f
lemma I_K_f.restricted_product (x : I_K_f K) :
  finite ({ v : maximal_spectrum (ring_of_integers K) | (¬ (x.val.val v) ∈ R_v K v) } ∪ 
    { v : maximal_spectrum (ring_of_integers K) | ¬ (x.inv.val v) ∈ R_v K v }) :=
restricted_product (ring_of_integers K) K x

lemma prod_val_inv_eq_one (x : I_K K) (v : maximal_spectrum (ring_of_integers K)): 
  (x.val.fst.val v) * (x.inv.fst.val v) = 1  :=
begin
  rw [← pi.mul_apply, mul_apply_val, ← prod.fst_mul, units.val_inv,
    prod.fst_one, subtype.val_eq_coe, ← one_def, subtype.coe_mk],
  refl,
end

lemma valuation.prod_val_inv_eq_one (x : I_K K) (v : maximal_spectrum (ring_of_integers K)): 
  (v_comp_val K x v) * (v_comp_inv K x v) = 1 :=
begin
  simp only [v_comp_val, v_comp_inv],
  rw [← valued.v.map_mul, prod_val_inv_eq_one K x v],
  exact valuation.map_one _,
end

lemma v_comp.ne_zero (x : I_K K) (v : maximal_spectrum (ring_of_integers K)) :
  (x.val.1.val v) ≠ 0 := left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one K x v)

lemma restricted_product (x : I_K K) :
  finite ({ v : maximal_spectrum (ring_of_integers K) | (¬ (x.val.1.val v) ∈ R_v K v) } ∪ 
    { v : maximal_spectrum (ring_of_integers K) | ¬ (x.inv.1.val v) ∈ R_v K v }) :=
finite.union x.val.1.property x.inv.1.property

lemma finite_exponents (x : I_K K) :
  finite { v : maximal_spectrum (ring_of_integers K) | v_comp_val K x v ≠ 1 } :=
begin
  have h_subset : { v : maximal_spectrum (ring_of_integers K) | v_comp_val K x v ≠ 1 } ⊆ 
  { v : maximal_spectrum (ring_of_integers K) | ¬ (x.val.1.val v) ∈ R_v K v } ∪ 
  { v : maximal_spectrum (ring_of_integers K) | ¬ (x.inv.1.val v) ∈ R_v K v },
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq, K_v.is_integer, K_v.is_integer],
    rw mem_set_of_eq at hv,
    cases (lt_or_gt_of_ne hv) with hlt hgt,
    { right,
      have h_one : (v_comp_val K x v) * (v_comp_inv K x v) = 1 := 
      valuation.prod_val_inv_eq_one K x v,
      have h_inv : 1 < v_comp_inv K x v,
      { have hx : v_comp_val K x v ≠ 0,
        { rw [v_comp_val, valuation.ne_zero_iff],
          exact v_comp.ne_zero K x v,},
        rw mul_eq_one_iff_inv_eq₀ hx at h_one,
        rw [← h_one, ← with_zero.inv_one, inv_lt_inv₀ (ne.symm zero_ne_one) hx],
        exact hlt, },
      exact not_le.mpr h_inv,},
    { left, exact not_le.mpr hgt, }},
  exact finite.subset (restricted_product K x) h_subset,
end


def I_K_f.map_to_fractional_ideals : monoid_hom
  (I_K_f K) (units (fractional_ideal (non_zero_divisors (ring_of_integers K)) K)) := 
map_to_fractional_ideals (ring_of_integers K) K

variable {K}
lemma I_K_f.map_to_fractional_ideals.surjective :
  function.surjective (I_K_f.map_to_fractional_ideals K) :=
--map_to_fractional_ideals.surjective (ring_of_integers K) K
@map_to_fractional_ideals.surjective (ring_of_integers K) K _ _ _ _ _ _

lemma I_K_f.map_to_fractional_ideals.mem_kernel_iff (x : I_K_f K) : 
  I_K_f.map_to_fractional_ideals K x = 1 ↔ 
  ∀ v : maximal_spectrum (ring_of_integers K), 
    finite_idele.to_add_valuations (ring_of_integers K) K x v = 0 := 
@map_to_fractional_ideals.mem_kernel_iff (ring_of_integers K) K _ _ _ _ _ _ x

lemma I_K_f.map_to_fractional_ideals.continuous :
  continuous (I_K_f.map_to_fractional_ideals K) :=
--map_to_fractional_ideals.continuous (ring_of_integers K) K
@map_to_fractional_ideals.continuous (ring_of_integers K) K _ _ _ _ _ _

variable (K)
def I_K.map_to_fractional_ideals : 
  monoid_hom (I_K K) (units (fractional_ideal (non_zero_divisors (ring_of_integers K)) K)) := 
monoid_hom.comp (I_K_f.map_to_fractional_ideals K) (I_K.fst K)

variable {K}
lemma I_K.map_to_fractional_ideals.surjective :
  function.surjective (I_K.map_to_fractional_ideals K) :=
function.surjective.comp I_K_f.map_to_fractional_ideals.surjective I_K.fst.surjective

lemma I_K.map_to_fractional_ideals.mem_kernel_iff (x : I_K K) : 
  I_K.map_to_fractional_ideals K x = 1 ↔ 
  ∀ v : maximal_spectrum (ring_of_integers K), 
    finite_idele.to_add_valuations (ring_of_integers K) K (I_K.fst K x) v = 0 :=
I_K_f.map_to_fractional_ideals.mem_kernel_iff (I_K.fst K x)

lemma I_K.map_to_fractional_ideals.continuous :
  continuous (I_K.map_to_fractional_ideals K) :=
continuous.comp I_K_f.map_to_fractional_ideals.continuous I_K.fst.continuous

variable (K)
def I_K_f.map_to_class_group :
  (I_K_f K) → (class_group (ring_of_integers K) K) := 
λ x, quotient_group.mk (I_K_f.map_to_fractional_ideals K x)

instance : topological_space (class_group ↥(ring_of_integers K) K) := ⊥
instance : topological_group (class_group ↥(ring_of_integers K) K) := 
{ continuous_mul := continuous_of_discrete_topology,
  continuous_inv := continuous_of_discrete_topology, }

variable {K}
lemma I_K_f.map_to_class_group.surjective : surjective (I_K_f.map_to_class_group K) := 
surjective.comp quotient.surjective_quotient_mk' I_K_f.map_to_fractional_ideals.surjective

lemma I_K_f.map_to_class_group.continuous : continuous (I_K_f.map_to_class_group K) := 
continuous.comp continuous_bot (I_K_f.map_to_fractional_ideals.continuous)

variable (K)
def I_K.map_to_class_group :
  (I_K K) → (class_group (ring_of_integers K) K) := 
λ x, quotient_group.mk (I_K.map_to_fractional_ideals K x)

variable {K}
lemma I_K.map_to_class_group.surjective : surjective (I_K.map_to_class_group K) := 
surjective.comp quotient.surjective_quotient_mk' I_K.map_to_fractional_ideals.surjective

lemma I_K.map_to_class_group.continuous : continuous (I_K.map_to_class_group K) := 
continuous.comp continuous_bot I_K.map_to_fractional_ideals.continuous

-- Timeout
--set_option trace.class_instances true
def I_K.monoid_hom_to_class_group : (I_K K) →* (class_group (ring_of_integers K) K) := 
{ to_fun   := I_K.map_to_class_group K,
  map_one' := sorry,
  map_mul' := sorry }

end number_field

#exit

namespace function_field

variables (Fq F : Type) [field Fq] [field F] [algebra (polynomial Fq) F] [algebra (ratfunc Fq) F] 
  [function_field Fq F] [algebra (fraction_ring (polynomial Fq)) F]
   [is_scalar_tower (polynomial Fq) (ratfunc Fq) F] [is_separable (ratfunc Fq) F]

def I_F_f := units (A_F_f Fq F)
--def I_F := units (A_F Fq F)

instance : comm_group (I_F_f Fq F) := units.comm_group
--instance : comm_group (I_F Fq F) := units.comm_group

end function_field