import adeles_K
import ideles_R

noncomputable theory

open set
open_locale tensor_product

namespace number_field

variables (K : Type) [field K] [number_field K]

def I_K_f := units (A_K_f K)
def I_K := units (A_K K)
instance : comm_group (I_K_f K) := units.comm_group
instance : comm_group (I_K K) := units.comm_group

lemma I_K_f.def : I_K_f K = units (A_K_f K) := rfl
lemma I_K.def : I_K K = units (A_K K) := rfl

lemma I_K.as_prod : I_K K ≃* (I_K_f K) × units (K ⊗[ℚ] ℝ) := 
begin
  have h : units (A_K_f K ×  K ⊗[ℚ] ℝ) ≃* (units (A_K_f K) × units (K ⊗[ℚ] ℝ)) := 
  mul_equiv.prod_units,
  convert h,
end

def I_K.proj1 : monoid_hom (I_K K) (I_K_f K) := 
{ to_fun := λ x, ((I_K.as_prod K).to_fun x).1,
  map_one' := by {rw [mul_equiv.to_fun_eq_coe, mul_equiv.map_one, prod.fst_one]},
  map_mul' := λ x y, by {simp only [prod.fst_mul, mul_equiv.to_fun_eq_coe, mul_equiv.map_mul]}}

lemma right_inv (x : units K) : (inj_K.ring_hom K) x.val * (inj_K.ring_hom K) x.inv = 1 := 
begin
  rw [← (inj_K.ring_hom K).map_mul, units.val_eq_coe, units.inv_eq_coe_inv, units.mul_inv],
  exact (inj_K.ring_hom K).map_one
end

lemma left_inv (x : units K) : (inj_K.ring_hom K) x.inv * (inj_K.ring_hom K) x.val  = 1 := 
by rw [mul_comm, right_inv]

def inj_units_K : units K → I_K K := λ x, ⟨number_field.inj_K.ring_hom K x.val, 
  number_field.inj_K.ring_hom K x.inv, right_inv K x, left_inv K x⟩

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

def inj_units_K.group_hom : monoid_hom (units K) (I_K K) := 
{ to_fun    := inj_units_K K,
  map_one'  := inj_units_K.map_one K,
  map_mul'  := inj_units_K.map_mul K, }

def C_K := quotient_group.quotient (inj_units_K.group_hom K).range

def v_comp_val (x : I_K K) (v : maximal_spectrum (ring_of_integers K)) :
  with_zero (multiplicative ℤ) := valued.v (x.val.1.val v)
--@valued.extension K _ (v_valued_K v) (x.val.1.val v)

def v_comp_inv (x : I_K K) (v : maximal_spectrum (ring_of_integers K)) :
  with_zero (multiplicative ℤ) := valued.v (x.inv.1.val v)
--@valued.extension K _ (v_valued_K v) (x.inv.1.val v)

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
  
def I_K.map_to_fractional_ideals : 
  monoid_hom (I_K K) (units (fractional_ideal (non_zero_divisors (ring_of_integers K)) K)) := 
monoid_hom.comp (I_K_f.map_to_fractional_ideals K) (I_K.proj1 K)

end number_field

namespace function_field

variables (Fq F : Type) [field Fq] [field F] [algebra (polynomial Fq) F] [algebra (ratfunc Fq) F] 
  [function_field Fq F] [algebra (fraction_ring (polynomial Fq)) F]
   [is_scalar_tower (polynomial Fq) (ratfunc Fq) F] [is_separable (ratfunc Fq) F]

def I_F_f := units (A_F_f Fq F)
--def I_F := units (A_F Fq F)

instance : comm_group (I_F_f Fq F) := units.comm_group
--instance : comm_group (I_F Fq F) := units.comm_group

end function_field