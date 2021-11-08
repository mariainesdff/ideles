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

lemma prod_val_inv_eq_one (x : I_K K) (v : maximal_spectrum (ring_of_integers K)): 
  (v_comp_val K x v) * (v_comp_inv K x v) = 1 :=
begin
  simp only [v_comp_val, v_comp_inv],
  rw ← valued.v.map_mul,
  rw ← pi.mul_apply,
  dsimp only,
  rw mul_apply_val,
  rw ← prod.fst_mul,
  rw units.val_inv,
  rw prod.fst_one,
  rw subtype.val_eq_coe,
  --rw subring.coe_one,
  --rw mul_apply _ K,
  --rw subtype.val_eq_coe,
  --rw subtype.val_eq_coe,
  --simp_rw ← subring.coe_mul,
  --
  --squeeze_simp,
  sorry
end


lemma restricted_product (x : I_K K) :
  finite ({ v : maximal_spectrum (ring_of_integers K) | (¬ (x.val.1.val v) ∈ R_v K v) } ∪ 
    { v : maximal_spectrum (ring_of_integers K) | ¬ (x.inv.1.val v) ∈ R_v K v }) :=
finite.union x.val.1.property x.inv.1.property

--x.val.1.property

lemma finite_exponents (x : I_K K) :
  finite { v : maximal_spectrum (ring_of_integers K) | v_comp_val K x v ≠ 1 } :=
begin
  have h_subset : { v : maximal_spectrum (ring_of_integers K) | v_comp_val K x v ≠ 1 } ⊆ 
  { v : maximal_spectrum (ring_of_integers K) | ¬ (x.val.1.val v) ∈ R_v K v } ∪ 
  { v : maximal_spectrum (ring_of_integers K) | ¬ (x.inv.1.val v) ∈ R_v K v },
  { intros v hv,
    rw mem_union,
    rw mem_set_of_eq, rw mem_set_of_eq,
    rw mem_set_of_eq at hv,
    cases (lt_or_gt_of_ne hv) with hlt hgt,
    { right,
      sorry },
    { left,
      rw K_v.is_integer,
      exact not_le.mpr hgt, }},
  exact finite.subset (restricted_product K x) h_subset,
end
  
def map_to_fractional_ideals : 
  I_K K → (fractional_ideal (non_zero_divisors (ring_of_integers K)) K) := λ x,
begin
  sorry
end


end number_field

namespace function_field

variables (Fq F : Type) [field Fq] [fintype Fq] [field F] [algebra (polynomial Fq) F]
  [algebra (fraction_ring (polynomial Fq)) F] [is_separable (fraction_ring (polynomial Fq)) F]
  [function_field Fq F] [is_scalar_tower (polynomial Fq) (fraction_ring (polynomial Fq)) F] 

def I_F_f := units (A_F_f Fq F)
def I_F := units (A_F Fq F)

instance : comm_group (I_F_f Fq F) := units.comm_group
instance : comm_group (I_F Fq F) := units.comm_group

end function_field