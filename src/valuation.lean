/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import algebraic_geometry.prime_spectrum.basic
import ring_theory.dedekind_domain.adic_valuation

/-!
# Adic valuations on Dedekind domains
Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the 
`v`-adic valuation on `R` and its extension to the field of fractions `K` of `R`. 
We prove several properties of this valuation, including the existence of uniformizers.

## Main definitions
 - `height_one_spectrum.valuation v` is the `v`-adic valuation on `K`. 

## Main results
- `valuation_well_defined` : The valuation of `k ∈ K` is independent on how we express `k` 
  as a fraction.
- `valuation_of_mk'` : The `v`-adic valuation of `r/s ∈ K` is the valuation of `r` divided by 
  the valuation of `s`.
- `valuation_of_algebra_map` : The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`.
- `valuation_exists_uniformizer` : There exists `π ∈ K` with `v`-adic valuation 
  `multiplicative.of_add (-1)`.
  
## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1.

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

noncomputable theory
open_locale classical

open multiplicative is_dedekind_domain

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type*} [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

namespace is_dedekind_domain.height_one_spectrum
/-! ### Adic valuations on the Dedekind domain R -/


/- @[simp] lemma with_zero.le_max_iff {M : Type} [linear_ordered_comm_monoid M] {a b c : M} :
  (a : with_zero M) ≤ max b c ↔ a ≤ max b c :=
by simp only [with_zero.coe_le_coe, le_max_iff] -/

/-! ### Adic valuations on the field of fractions `K` -/
/-- The `v`-adic valuation of `x ∈ K` is the valuation of `r` divided by the valuation of `s`, 
where `r` and `s` are chosen so that `x = r/s`. -/
def valuation_def (x : K) : (with_zero (multiplicative ℤ)) :=
let s := classical.some (classical.some_spec (is_localization.mk'_surjective
  (non_zero_divisors R) x)) in (v.int_valuation_def (classical.some
    (is_localization.mk'_surjective (non_zero_divisors R) x)))/(v.int_valuation_def s)

variable (K)
/-- The valuation of `k ∈ K` is independent on how we express `k` as a fraction. -/
lemma valuation_well_defined {r r' : R} {s s' : non_zero_divisors R} 
  (h_mk : is_localization.mk' K r s = is_localization.mk' K r' s') :
  (v.int_valuation_def r)/(v.int_valuation_def s) =
  (v.int_valuation_def r')/(v.int_valuation_def s') := 
begin
  rw [div_eq_div_iff (int_valuation_ne_zero' v s) (int_valuation_ne_zero' v s'),
  ← int_valuation.map_mul', ← int_valuation.map_mul',
  is_fraction_ring.injective R K (is_localization.mk'_eq_iff_eq.mp h_mk)],
end

/-- The `v`-adic valuation of `r/s ∈ K` is the valuation of `r` divided by the valuation of `s`. -/
lemma valuation_of_mk' {r : R} {s : non_zero_divisors R} :
  v.valuation_def (is_localization.mk' K r s) =
   (v.int_valuation_def r)/(v.int_valuation_def s) :=
begin
  rw valuation_def,
  exact valuation_well_defined K v
    (classical.some_spec (classical.some_spec (is_localization.mk'_surjective (non_zero_divisors R) 
    (is_localization.mk' K r s)))),
end

variable {K}
/-- The `v`-adic valuation on `K` extends the `v`-adic valuation on `R`. -/
lemma valuation_of_algebra_map {r : R} :
  v.valuation_def (algebra_map R K r) = v.int_valuation_def r :=
by rw [← is_localization.mk'_one K r, valuation_of_mk', submonoid.coe_one, 
    int_valuation.map_one', div_one _]

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
lemma valuation_le_one (r : R) : v.valuation_def (algebra_map R K r) ≤ 1 :=
by { rw valuation_of_algebra_map, exact v.int_valuation_le_one r }

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
lemma valuation_lt_one_iff_dvd (r : R) : 
  v.valuation_def (algebra_map R K r) < 1 ↔ v.as_ideal ∣ ideal.span {r} :=
by { rw valuation_of_algebra_map, exact v.int_valuation_lt_one_iff_dvd r }

/-- The `v`-adic valuation of `0 : R` equals 0. -/
lemma valuation.map_zero' : v.valuation_def (0 : K) = 0 := 
begin
  rw [← (algebra_map R K).map_zero, valuation_of_algebra_map v],
  exact v.int_valuation.map_zero',
end

/-- The `v`-adic valuation of `1 : R` equals 1. -/
lemma valuation.map_one' : v.valuation_def (1 : K) = 1 := 
begin
  rw [← (algebra_map R K).map_one, valuation_of_algebra_map v],
  exact v.int_valuation.map_one',
end

/-- The `v`-adic valuation of a product is the product of the valuations. -/
lemma valuation.map_mul' (x y : K) :
  v.valuation_def (x * y) = v.valuation_def x * v.valuation_def y :=
begin
  rw [valuation_def, valuation_def, valuation_def, div_mul_div_comm₀, ← int_valuation.map_mul',
    ← int_valuation.map_mul', ← submonoid.coe_mul],
  apply valuation_well_defined K v,
  rw [(classical.some_spec (valuation_def._proof_2 (x * y))), is_fraction_ring.mk'_eq_div,
    (algebra_map R K).map_mul, submonoid.coe_mul, (algebra_map R K).map_mul, ← div_mul_div_comm₀,
    ← is_fraction_ring.mk'_eq_div, ← is_fraction_ring.mk'_eq_div,
    (classical.some_spec (valuation_def._proof_2 x)),
    (classical.some_spec (valuation_def._proof_2 y))],
end

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
lemma valuation.map_add_le_max' (x y : K) :
  v.valuation_def (x + y) ≤ max (v.valuation_def x) (v.valuation_def y) := 
begin
  obtain ⟨rx, sx, hx⟩ := is_localization.mk'_surjective (non_zero_divisors R) x,
  obtain ⟨rxy, sxy, hxy⟩ := is_localization.mk'_surjective (non_zero_divisors R) (x + y),
  obtain ⟨ry, sy, hy⟩ := is_localization.mk'_surjective (non_zero_divisors R) y,
  rw [← hxy, ← hx, ← hy, valuation_of_mk', valuation_of_mk', valuation_of_mk'],
  have h_frac_xy : is_localization.mk' K rxy sxy = 
    is_localization.mk' K (rx*(sy : R) + ry*(sx : R)) (sx*sy),
  { rw [is_localization.mk'_add, hx, hy, hxy], },
  have h_frac_x : is_localization.mk' K rx sx = is_localization.mk' K (rx*(sy : R)) (sx*sy),
  { rw [is_localization.mk'_eq_iff_eq, submonoid.coe_mul, mul_assoc, mul_comm (sy : R) _], },
  have h_frac_y : is_localization.mk' K ry sy = is_localization.mk' K (ry*(sx : R)) (sx*sy),
  { rw [is_localization.mk'_eq_iff_eq, submonoid.coe_mul, mul_assoc], },
  have h_denom : 0 < v.int_valuation_def ↑(sx * sy),
  { rw [int_valuation_def, if_neg _], 
    { exact with_zero.zero_lt_coe _ },
    { exact non_zero_divisors.ne_zero
        (submonoid.mul_mem (non_zero_divisors R) sx.property sy.property), }},
  rw [valuation_well_defined K v h_frac_x, valuation_well_defined K v h_frac_y,
    valuation_well_defined K v h_frac_xy, le_max_iff, div_le_div_right₀ (ne_of_gt h_denom), 
    div_le_div_right₀ (ne_of_gt h_denom), ← le_max_iff],
  exact v.int_valuation.map_add_le_max' _ _,
end

/-- The `v`-adic valuation on `K`. -/
def valuation  : valuation K (with_zero (multiplicative ℤ)) := { 
  to_fun    := v.valuation_def, 
  map_zero' := valuation.map_zero' v,
  map_one'  := valuation.map_one' v, 
  map_mul'  := valuation.map_mul' v, 
  map_add_le_max'  := valuation.map_add_le_max' v }

variable (K)
/-- There exists `π ∈ K` with `v`-adic valuation `multiplicative.of_add (-1)`. -/
lemma valuation_exists_uniformizer : 
  ∃ (π : K), v.valuation_def π = multiplicative.of_add (-1 : ℤ) := 
begin
  obtain ⟨r, hr⟩ := v.int_valuation_exists_uniformizer,
  use algebra_map R K r,
  rw valuation_of_algebra_map v,
  exact hr,
end

/-- Uniformizers are nonzero. -/
lemma valuation_uniformizer_ne_zero :
  (classical.some (v.valuation_exists_uniformizer K)) ≠ 0 :=
begin
  have hu := (classical.some_spec (v.valuation_exists_uniformizer K)),
  have h : v.valuation_def (classical.some _) = valuation v (classical.some _) := rfl,
  rw h at hu,
  exact (valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu with_zero.coe_ne_zero),
end

end is_dedekind_domain.height_one_spectrum