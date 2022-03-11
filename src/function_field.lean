/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import adeles_R
import number_theory.function_field

/-!
# The valuation at infinity on k(t)
For a field `k`, the valuation at infinity on the function field `k(t)` is the nonarchimedean
valuation on `k(t)` with uniformizer `1/t`. Explicitly, if `f/g ∈ k(t)` is a nonzero quotient of
polynomials, its valuation at infinity is `multiplicative.of_add(degree(f) - degree(g))`.

## Main definitions
- `infty_valuation` : The valuation at infinity on `k(t)`.
- `kt_infty` : The completion `k((t⁻¹))` of `k(t)` with respect to `infty_valuation`.

## Tags
function field, valuation
-/

noncomputable theory

open_locale classical
open multiplicative

variables (k : Type) [field k]
/-- The valuation at infinity is the nonarchimedean valuation on `k(t)` with uniformizer `1/t`. -/
def infty_valuation_def (r : ratfunc k) : with_zero (multiplicative ℤ) :=
ite (r = 0) 0 (multiplicative.of_add ((r.num.nat_degree : ℤ) - r.denom.nat_degree))

lemma infty_valuation.map_zero' : infty_valuation_def k 0 = 0 := 
by { rw [infty_valuation_def, if_pos], refl, }

lemma infty_valuation.map_one' : infty_valuation_def k 1 = 1 := 
begin
  rw [infty_valuation_def, if_neg (zero_ne_one.symm : (1 : ratfunc k) ≠ 0)],
  simp only [polynomial.nat_degree_one, ratfunc.num_one, int.coe_nat_zero, sub_zero, 
    ratfunc.denom_one, of_add_zero, with_zero.coe_one],
end

lemma infty_valuation.map_mul' (x y : ratfunc k) :
  infty_valuation_def k (x * y) = infty_valuation_def k x * infty_valuation_def k y :=
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

variable {k}
/-- Equivalent fractions have the same valuation -/
lemma infty_valuation_well_defined {r₁ r₂ s₁ s₂ : polynomial k} (hr₁ : r₁ ≠ 0) (hs₁ : s₁ ≠ 0) 
  (hr₂ : r₂ ≠ 0) (hs₂ : s₂ ≠ 0) (h_eq : r₁*s₂ = r₂*s₁) :
  (r₁.nat_degree : ℤ) - s₁.nat_degree = (r₂.nat_degree : ℤ) - s₂.nat_degree :=
begin
  rw sub_eq_sub_iff_add_eq_add,
  norm_cast,
  rw [← polynomial.nat_degree_mul hr₁ hs₂, ← polynomial.nat_degree_mul hr₂ hs₁, h_eq],
end

lemma ratfunc.num_add_ne_zero {x y : ratfunc k} (hxy : x + y ≠ 0) :
  x.num * y.denom + x.denom * y.num ≠ 0 :=
begin
  intro h_zero,
  have h := ratfunc.num_denom_add x y,
  rw [h_zero, zero_mul] at h,
  exact (mul_ne_zero (ratfunc.num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h,
end

lemma infty_valuation_add_rw {x y : ratfunc k} (hxy : x + y ≠ 0) :
  ((x + y).num.nat_degree : ℤ) - ((x + y).denom.nat_degree)  = 
  ((x.num) * y.denom + (x.denom) * y.num).nat_degree - ((x.denom) * y.denom).nat_degree :=
infty_valuation_well_defined (ratfunc.num_ne_zero hxy) ((x + y).denom_ne_zero)
    (ratfunc.num_add_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (ratfunc.num_denom_add x y)

lemma infty_valuation_rw {x : ratfunc k} (hx : x ≠ 0) {s : polynomial k} (hs : s ≠ 0):
  (x.num.nat_degree : ℤ) - (x.denom.nat_degree)  = 
  ((x.num)*s).nat_degree - (s*(x.denom)).nat_degree :=
begin
  apply infty_valuation_well_defined (ratfunc.num_ne_zero hx) x.denom_ne_zero
    (mul_ne_zero (ratfunc.num_ne_zero hx) hs) (mul_ne_zero hs x.denom_ne_zero),
  rw mul_assoc,
end

variable (k)
lemma infty_valuation.map_add_le_max' (x y : ratfunc k) :
  infty_valuation_def k (x + y) ≤ max (infty_valuation_def k x) (infty_valuation_def k y) :=
begin
  by_cases hx : x = 0,
    { rw [hx, zero_add],
      conv_rhs {rw [infty_valuation_def, if_pos (eq.refl _)]},
      rw max_eq_right (with_zero.zero_le (infty_valuation_def k y)),
      exact le_refl _, },
    { by_cases hy : y = 0,
        { rw [hy, add_zero],
          conv_rhs {rw [max_comm, infty_valuation_def, if_pos (eq.refl _)]},
          rw max_eq_right (with_zero.zero_le (infty_valuation_def k x)), 
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

/-- The valuation at infinity on `k(t)`. -/
def infty_valuation  : valuation (ratfunc k) (with_zero (multiplicative ℤ)) :=
{ to_fun    := infty_valuation_def k, 
  map_zero' := infty_valuation.map_zero' k,
  map_one'  := infty_valuation.map_one' k,
  map_mul'  := infty_valuation.map_mul' k,
  map_add_le_max'  := infty_valuation.map_add_le_max' k }

/-- The valued field `k(t)` with the valuation at infinity. -/
def infty_valued_kt : valued (ratfunc k) (with_zero (multiplicative ℤ)) := 
⟨infty_valuation k⟩

lemma infty_valued_kt.def {x : ratfunc k} :
  @valued.v (ratfunc k) _ _ _ (infty_valued_kt k) (x) = infty_valuation_def k x := rfl

/-- The topology structure on `k(t)` induced by the valuation at infinity. -/
def tsq' : topological_space (ratfunc k) :=
@valued.topological_space (ratfunc k) _ _ _ (infty_valued_kt k)
lemma tdrq' : @topological_division_ring (ratfunc k) _ (tsq' k) := 
@valued.topological_division_ring (ratfunc k) _ _ _ (infty_valued_kt k)
lemma trq' : @topological_ring (ratfunc k) (tsq' k) _ := infer_instance
lemma tgq' : @topological_add_group (ratfunc k) (tsq' k) _ := infer_instance
/-- The uniform structure on `k(t)` induced by the valuation at infinity. -/
def usq' : uniform_space (ratfunc k) := 
@topological_add_group.to_uniform_space (ratfunc k) _ (tsq' k) (tgq' k)
lemma ugq' : @uniform_add_group (ratfunc k) (usq' k) _ := 
@topological_add_group_is_uniform (ratfunc k) _ (tsq' k) (tgq' k)
lemma cfq' : @completable_top_field (ratfunc k) _ (usq' k) :=
@valued.completable (ratfunc k) _ _ _ (infty_valued_kt k)
lemma ssq' : @separated_space (ratfunc k) (usq' k) :=
@valued_ring.separated (ratfunc k) _ _ _ (infty_valued_kt k)

/-- The completion `k((t⁻¹))`  of `k(t)` with respect to the valuation at infinity. -/
def kt_infty := @uniform_space.completion (ratfunc k) (usq' k)
instance : field (kt_infty k) :=
@field_completion (ratfunc k) _ (usq' k) (tdrq' k) _ (ugq' k)

/-- The valuation at infinity on `k(t)` extends to a valuation on `kt_infty`. -/
instance valued_kt_infty : valued (kt_infty k) (with_zero (multiplicative ℤ)):= 
⟨@valued.extension_valuation (ratfunc k) _ _ _ (infty_valued_kt k)⟩

lemma valued_kt_infty.def {x : kt_infty k} :
  valued.v (x) = @valued.extension (ratfunc k) _ _ _ (infty_valued_kt k) x := rfl

instance tsq : topological_space (kt_infty k) :=
@valued.topological_space (kt_infty k) _ _ _ (valued_kt_infty k)
instance tdrq : @topological_division_ring (kt_infty k) _ (tsq k) := 
@valued.topological_division_ring (kt_infty k) _ _ _(valued_kt_infty k)
instance trq : @topological_ring (kt_infty k) (tsq k) _ := (tdrq k).to_topological_ring
instance tgq : @topological_add_group (kt_infty k) (tsq k) _ := 
@topological_ring.to_topological_add_group (kt_infty k) _ (tsq k) (trq k)
instance usq : uniform_space (kt_infty k) := 
@topological_add_group.to_uniform_space (kt_infty k) _ (tsq k) (tgq k)
instance ugq : @uniform_add_group (kt_infty k) (usq k) _ := 
@topological_add_group_is_uniform (kt_infty k) _ (tsq k) (tgq k)
