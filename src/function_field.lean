/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import adeles_R
import number_theory.function_field

/-!
# The valuation at infinity on Fq(t).
The valuation at infinity is the nonarchimedean valuation on `Fq(t)` with uniformizer `1/t`. 
Explicitly, if `f/g ∈ Fq(t)` is a nonzero quotient of polynomials, its valuation at infinity is
`multiplicative.of_add(degree(f) - degree(g))`.

## Main definitions
- `infty_valuation` : The valuation at infinity on `Fq(t)`.
- `Fqt_infty` : The completion `Fq((t⁻¹))` of `Fq(t)` with respect to `infty_valuation`.

## Tags
function field, valuation
-/

noncomputable theory

open_locale classical

variables (Fq : Type) [field Fq]
/-- The valuation at infinity is the nonarchimedean valuation on `Fq(t)` with uniformizer `1/t`. -/
def infty_valuation_def (r : ratfunc Fq) : with_zero (multiplicative ℤ) :=
ite (r = 0) 0 (multiplicative.of_add ((r.num.nat_degree : ℤ) - r.denom.nat_degree))

lemma infty_valuation.map_zero' : infty_valuation_def Fq 0 = 0 := 
by { rw [infty_valuation_def, if_pos], refl, }

lemma infty_valuation.map_one' : infty_valuation_def Fq 1 = 1 := 
begin
  rw [infty_valuation_def, if_neg (zero_ne_one.symm : (1 : ratfunc Fq) ≠ 0)],
  simp only [polynomial.nat_degree_one, ratfunc.num_one, int.coe_nat_zero, sub_zero, ratfunc.denom_one, of_add_zero,
  with_zero.coe_one],
end

lemma infty_valuation.map_mul' (x y : ratfunc Fq) :
  infty_valuation_def Fq (x * y) = infty_valuation_def Fq x * infty_valuation_def Fq y :=
begin
  rw [infty_valuation_def, infty_valuation_def, infty_valuation_def],
  by_cases hx : x = 0,
  { rw [hx, zero_mul, if_pos (eq.refl _), zero_mul] },
  { by_cases hy : y = 0,
    { rw [hy, mul_zero, if_pos (eq.refl _), mul_zero] },
    { rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← with_zero.coe_mul,
        with_zero.coe_inj, ← of_add_add],
      apply congr_arg,
      rw [add_sub, sub_add, sub_sub_assoc_swap, sub_sub, sub_eq_sub_iff_add_eq_add],
      norm_cast,
      rw [← polynomial.nat_degree_mul x.denom_ne_zero y.denom_ne_zero,
        ← polynomial.nat_degree_mul (ratfunc.num_ne_zero (mul_ne_zero hx hy))
          (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
        ← polynomial.nat_degree_mul (ratfunc.num_ne_zero hx) (ratfunc.num_ne_zero hy),
        ← polynomial.nat_degree_mul (mul_ne_zero (ratfunc.num_ne_zero hx) (ratfunc.num_ne_zero hy))
          (x * y).denom_ne_zero, ratfunc.num_denom_mul],}}
end

variable {Fq}
/-- Equivalent fractions have the same valuation -/
lemma infty_valuation_well_defined {r₁ r₂ s₁ s₂ : polynomial Fq} (hr₁ : r₁ ≠ 0) (hs₁ : s₁ ≠ 0) 
  (hr₂ : r₂ ≠ 0) (hs₂ : s₂ ≠ 0) (h_eq : r₁*s₂ = r₂*s₁) :
  (r₁.nat_degree : ℤ) - s₁.nat_degree = (r₂.nat_degree : ℤ) - s₂.nat_degree :=
begin
  rw sub_eq_sub_iff_add_eq_add,
  norm_cast,
  rw [← polynomial.nat_degree_mul hr₁ hs₂, ← polynomial.nat_degree_mul hr₂ hs₁, h_eq],
end

lemma ratfunc.num_add_ne_zero {x y : ratfunc Fq} (hxy : x + y ≠ 0) :
  x.num * y.denom + x.denom * y.num ≠ 0 :=
begin
  intro h_zero,
  have h := ratfunc.num_denom_add x y,
  rw [h_zero, zero_mul] at h,
  exact (mul_ne_zero (ratfunc.num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h,
end

lemma infty_valuation_add_rw {x y : ratfunc Fq} (hxy : x + y ≠ 0) :
  ((x + y).num.nat_degree : ℤ) - ((x + y).denom.nat_degree)  = 
  ((x.num) * y.denom + (x.denom) * y.num).nat_degree - ((x.denom) * y.denom).nat_degree :=
infty_valuation_well_defined (ratfunc.num_ne_zero hxy) ((x + y).denom_ne_zero)
    (ratfunc.num_add_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (ratfunc.num_denom_add x y)

lemma infty_valuation_rw {x : ratfunc Fq} (hx : x ≠ 0) {s : polynomial Fq} (hs : s ≠ 0):
  (x.num.nat_degree : ℤ) - (x.denom.nat_degree)  = 
  ((x.num)*s).nat_degree - (s*(x.denom)).nat_degree :=
begin
  apply infty_valuation_well_defined (ratfunc.num_ne_zero hx) x.denom_ne_zero
    (mul_ne_zero (ratfunc.num_ne_zero hx) hs) (mul_ne_zero hs x.denom_ne_zero),
  rw mul_assoc,
end

variable (Fq)
lemma infty_valuation.map_add' (x y : ratfunc Fq) :
  infty_valuation_def Fq (x + y) ≤ max (infty_valuation_def Fq x) (infty_valuation_def Fq y) :=
begin
  by_cases hx : x = 0,
    { rw [hx, zero_add],
      conv_rhs {rw [infty_valuation_def, if_pos (eq.refl _)]},
      rw max_eq_right (with_zero.zero_le (infty_valuation_def Fq y)),
      exact le_refl _, },
    { by_cases hy : y = 0,
        { rw [hy, add_zero],
          conv_rhs {rw [max_comm, infty_valuation_def, if_pos (eq.refl _)]},
          rw max_eq_right (with_zero.zero_le (infty_valuation_def Fq x)), 
          exact le_refl _ },
        { by_cases hxy : x + y = 0,
          { rw [infty_valuation_def, if_pos hxy], exact zero_le',},
          { rw [infty_valuation_def, infty_valuation_def, infty_valuation_def, if_neg hx,
              if_neg hy, if_neg hxy, infty_valuation_add_rw hxy,
              infty_valuation_rw hx y.denom_ne_zero, mul_comm y.denom,
              infty_valuation_rw hy x.denom_ne_zero, le_max_iff, with_zero.coe_le_coe, of_add_le,
              with_zero.coe_le_coe, of_add_le, sub_le_sub_iff_right, int.coe_nat_le,
              sub_le_sub_iff_right, int.coe_nat_le, ← le_max_iff, mul_comm y.num],
            exact polynomial.nat_degree_add_le _ _, }}},
end

/-- The valuation at infinity on `Fq(t)`. -/
def infty_valuation  : valuation (ratfunc Fq) (with_zero (multiplicative ℤ)) :=
{ to_fun    := infty_valuation_def Fq, 
  map_zero' := infty_valuation.map_zero' Fq,
  map_one'  := infty_valuation.map_one' Fq,
  map_mul'  := infty_valuation.map_mul' Fq,
  map_add'  := infty_valuation.map_add' Fq }

/-- The valued field `Fq(t)` with the valuation at infinity. -/
def infty_valued_Fqt : valued (ratfunc Fq) := 
{ Γ₀  := (with_zero (multiplicative ℤ)),
  grp := infer_instance,
  v   := infty_valuation Fq }

lemma infty_valued_Fqt.def {x : ratfunc Fq} :
  @valued.v (ratfunc Fq) _ (infty_valued_Fqt Fq) (x) = infty_valuation_def Fq x := rfl

/-- The topology structure on `Fq(t)` induced by the valuation at infinity. -/
def tsq' : topological_space (ratfunc Fq) :=
@valued.topological_space (ratfunc Fq) _ (infty_valued_Fqt Fq)
lemma tdrq' : @topological_division_ring (ratfunc Fq) _ (tsq' Fq) := 
@valued.topological_division_ring (ratfunc Fq) _ (infty_valued_Fqt Fq)
lemma trq' : @topological_ring (ratfunc Fq) (tsq' Fq) _ := infer_instance
lemma tgq' : @topological_add_group (ratfunc Fq) (tsq' Fq) _ := infer_instance
/-- The uniform structure on `Fq(t)` induced by the valuation at infinity. -/
def usq' : uniform_space (ratfunc Fq) := 
@topological_add_group.to_uniform_space (ratfunc Fq) _ (tsq' Fq) (tgq' Fq)
lemma ugq' : @uniform_add_group (ratfunc Fq) (usq' Fq) _ := 
@topological_add_group_is_uniform (ratfunc Fq) _ (tsq' Fq) (tgq' Fq)
lemma cfq' : @completable_top_field (ratfunc Fq) _ (usq' Fq) :=
@valued.completable (ratfunc Fq) _ (infty_valued_Fqt Fq)
lemma ssq' : @separated_space (ratfunc Fq) (usq' Fq) :=
@valued_ring.separated (ratfunc Fq) _ (infty_valued_Fqt Fq)

/-- The completion `Fq((t⁻¹))`  of `Fq(t)` with respect to the valuation at infinity. -/
def Fqt_infty := @uniform_space.completion (ratfunc Fq) (usq' Fq)
instance : field (Fqt_infty Fq) :=
@field_completion (ratfunc Fq) _ (usq' Fq) (tdrq' Fq) _ (ugq' Fq)

/-- The valuation at infinity on `Fq(t)` extends to a valuation on `Fqt_infty`. -/
instance valued_Fqt_infty : valued (Fqt_infty Fq) := 
{ Γ₀  := with_zero (multiplicative ℤ),
  grp := infer_instance,
  v   := @valued.extension_valuation (ratfunc Fq) _ (infty_valued_Fqt Fq) }

lemma valued_Fqt_infty.def {x : Fqt_infty Fq} :
  valued.v (x) = @valued.extension (ratfunc Fq) _ (infty_valued_Fqt Fq) x := rfl

instance tsq : topological_space (Fqt_infty Fq) :=
@valued.topological_space (Fqt_infty Fq) _ (valued_Fqt_infty Fq)
instance tdrq : @topological_division_ring (Fqt_infty Fq) _ (tsq Fq) := 
@valued.topological_division_ring (Fqt_infty Fq) _ (valued_Fqt_infty Fq)
instance trq : @topological_ring (Fqt_infty Fq) (tsq Fq) _ := (tdrq Fq).to_topological_ring
instance tgq : @topological_add_group (Fqt_infty Fq) (tsq Fq) _ := 
@topological_ring.to_topological_add_group (Fqt_infty Fq) _ (tsq Fq) (trq Fq)
instance usq : uniform_space (Fqt_infty Fq) := 
@topological_add_group.to_uniform_space (Fqt_infty Fq) _ (tsq Fq) (tgq Fq)
instance ugq : @uniform_add_group (Fqt_infty Fq) (usq Fq) _ := 
@topological_add_group_is_uniform (Fqt_infty Fq) _ (tsq Fq) (tgq Fq)
