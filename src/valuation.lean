import algebraic_geometry.prime_spectrum.basic
import ring_theory.dedekind_domain
import topology.algebra.valued_field

noncomputable theory
open_locale classical

variables (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type*} [field K]
  [algebra R K] [is_fraction_ring R K] 

-- Note : not the maximal spectrum if R is a field
def maximal_spectrum := {v : prime_spectrum R // v.val ≠ 0 }
variable (v : maximal_spectrum R)

variable {R}
--Maximal spectrum lemmas
lemma ideal.prime_of_maximal (v : maximal_spectrum R) :
  prime v.val.val := 
begin
  apply ideal.prime_of_is_prime v.property v.val.property,
end

lemma ideal.irreducible_of_maximal (v : maximal_spectrum R) :
  irreducible v.val.val := 
begin
  rw [unique_factorization_monoid.irreducible_iff_prime],
  apply ideal.prime_of_maximal v,
end

lemma associates.irreducible_of_maximal (v : maximal_spectrum R) :
  irreducible (associates.mk v.val.val) := 
begin
  rw [associates.irreducible_mk _],
  apply ideal.irreducible_of_maximal v,
end

-- of_add lemmas
lemma of_add_le (α : Type*) [has_add α] [partial_order α] (x y : α) :
  multiplicative.of_add x ≤ multiplicative.of_add y ↔ x ≤ y := by refl

lemma of_add_lt (α : Type*) [has_add α] [partial_order α] (x y : α) :
  multiplicative.of_add x < multiplicative.of_add y ↔ x < y := by refl

lemma of_add_inj (α : Type*) [has_add α] (x y : α) 
  (hxy : multiplicative.of_add x = multiplicative.of_add y) : x = y := 
by rw [← to_add_of_add x, ← to_add_of_add y, hxy]

-- is_localization lemmas
lemma is_localization.mk'_zero {R : Type*} [comm_ring R] {M : submonoid R}
  {S : Type*} [comm_ring S] [algebra R S] [is_localization M S] {y : M} :  
  is_localization.mk' S 0 y = 0 := 
by rw [eq_comm, is_localization.eq_mk'_iff_mul_eq, zero_mul, map_zero]

lemma is_localization.mk'_num_ne_zero_of_ne_zero {R : Type*} [comm_ring R] {M : submonoid R}
  {S : Type*} [comm_ring S] [algebra R S] [is_localization M S] {z : S}  {x : R} {y : M}
  (hxyz : z = is_localization.mk' S x y) (hz : z ≠ 0) : x ≠ 0 := 
begin
  intro hx,
  rw [hx, is_localization.mk'_zero] at hxyz,
  exact hz hxyz,
end

variables {A : Type*} [comm_ring A] [is_domain A] {S : Type*} [field S] [algebra A S]
  [is_fraction_ring A S]

lemma is_localization.mk'_eq_zero {r : A} {s : non_zero_divisors A}
  (h : is_localization.mk' S r s = 0) : r = 0 := 
begin
  rw [is_fraction_ring.mk'_eq_div, div_eq_zero_iff] at h,
  apply is_fraction_ring.injective A S,
  rw (algebra_map A S).map_zero,
  exact or.resolve_right h (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors s.property)
end

variable (S)
lemma is_localization.mk'_eq_one {r : A} {s : non_zero_divisors A}
  (h : is_localization.mk' S r s = 1) : r = s :=
begin
  rw [is_fraction_ring.mk'_eq_div, div_eq_one_iff_eq] at h,
  { exact is_fraction_ring.injective A S h },
  { exact is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors s.property }
end 

-- Ideal associates lemmas
@[simp] lemma associates.mk_ne_zero' {x : R} : 
  (associates.mk (ideal.span{x} : ideal R)) ≠ 0 ↔ (x ≠ 0):=
by rw [associates.mk_ne_zero, ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot]

lemma associates.le_singleton_iff (x : R) (n : ℕ) (I : ideal R) :
  associates.mk I^n ≤ associates.mk (ideal.span {x}) ↔ x ∈ I^n :=
begin
  rw [← associates.dvd_eq_le, ← associates.mk_pow, associates.mk_dvd_mk, ideal.dvd_span_singleton],
end

-- Ideal lemmas
lemma ideal.mem_pow_count {x : R} (hx : x ≠ 0) {I : ideal R} (hI : irreducible I) :
  x ∈ I^((associates.mk I).count (associates.mk (ideal.span {x})).factors) :=
begin
  have hx' := associates.mk_ne_zero'.mpr hx,
  rw [← associates.le_singleton_iff, 
    associates.prime_pow_dvd_iff_le hx' ((associates.irreducible_mk I).mpr hI)],
end   

lemma ideal.mem_le_pow {x : R}  (hx : x ≠ 0) {I : ideal R} (hI : irreducible I)
  {n : ℕ} (hxI : x ∈ I^n) (m : ℕ) (hm : m ≤ n) : x ∈ I^m := ideal.pow_le_pow hm hxI

namespace maximal_spectrum
/-! Adic valuation on the Dedekind domain R -/
def int_valuation_def (r : R) : with_zero (multiplicative ℤ) :=
ite (r = 0) 0 (multiplicative.of_add  
  (-(associates.mk v.val.val).count (associates.mk (ideal.span{r} : ideal R)).factors : ℤ))

lemma int_valuation_def_if_pos {r : R} (hr : r = 0) :
  v.int_valuation_def r = 0 :=
if_pos hr

lemma int_valuation_def_if_neg {r : R} (hr : r ≠ 0) :
  v.int_valuation_def r = (multiplicative.of_add
  (-(associates.mk v.val.val).count (associates.mk (ideal.span{r} : ideal R)).factors : ℤ)) :=
if_neg hr

lemma int_valuation.map_zero' : v.int_valuation_def 0 = 0 := 
by { rw [int_valuation_def, if_pos], refl, }

lemma int_valuation.map_one' : v.int_valuation_def 1 = 1 := 
begin
  rw [int_valuation_def, if_neg (zero_ne_one.symm : (1 : R) ≠ 0)],
  simp [← ideal.one_eq_top, -subtype.val_eq_coe,
    associates.count_zero (associates.irreducible_of_maximal v)],
end

lemma int_valuation.map_mul' (x y : R) :
  v.int_valuation_def (x * y) = v.int_valuation_def x * v.int_valuation_def y :=
begin
  rw [int_valuation_def, int_valuation_def, int_valuation_def],
  by_cases hx : x = 0,
  { rw [hx, zero_mul, if_pos (eq.refl _), zero_mul] },
  { by_cases hy : y = 0,
    { rw [hy, mul_zero, if_pos (eq.refl _), mul_zero] },
    { rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← with_zero.coe_mul,
        with_zero.coe_inj, ← of_add_add],
      have hx' : associates.mk (ideal.span{x} : ideal R) ≠ 0 := associates.mk_ne_zero'.mpr hx,
      have hy' : associates.mk (ideal.span{y} : ideal R) ≠ 0 := associates.mk_ne_zero'.mpr hy,
      rw [← ideal.span_singleton_mul_span_singleton, ← associates.mk_mul_mk, ← neg_add,
        associates.count_mul hx' hy' _],
      { refl },
      { apply (associates.irreducible_of_maximal v), }}}
end

lemma int_valuation.map_add' (x y : R) : v.int_valuation_def (x + y) ≤
  max (v.int_valuation_def x) (v.int_valuation_def y) := 
begin
  by_cases hx : x = 0,
  { rw [hx, zero_add],
    conv_rhs {rw [int_valuation_def, if_pos (eq.refl _)]},
    rw max_eq_right (with_zero.zero_le (v.int_valuation_def y)),
    exact le_refl _, },
  { by_cases hy : y = 0,
    { rw [hy, add_zero],
      conv_rhs {rw [max_comm, int_valuation_def, if_pos (eq.refl _)]},
        rw max_eq_right (with_zero.zero_le (v.int_valuation_def x)), 
        exact le_refl _ },
    { by_cases hxy : x + y = 0,
      { rw [int_valuation_def, if_pos hxy], exact zero_le',},
      { rw [int_valuation_def, int_valuation_def, int_valuation_def,
          if_neg hxy, if_neg hx, if_neg hy],
      rw [le_max_iff, with_zero.coe_le_coe, of_add_le, with_zero.coe_le_coe, of_add_le,
        neg_le_neg_iff, neg_le_neg_iff, int.coe_nat_le, int.coe_nat_le, ← min_le_iff],
      set nmin := min 
        ((associates.mk v.val.val).count (associates.mk (ideal.span {x})).factors)
        ((associates.mk v.val.val).count (associates.mk (ideal.span {y})).factors),
      have hx' : (associates.mk (ideal.span {x} : ideal R)) ≠ 0 := associates.mk_ne_zero'.mpr hx,
      have hy' : (associates.mk (ideal.span {y} : ideal R)) ≠ 0 := associates.mk_ne_zero'.mpr hy,
      have hxy' : (associates.mk (ideal.span {x + y} : ideal R)) ≠ 0 := 
      associates.mk_ne_zero'.mpr hxy,
      have h_dvd_x : x ∈ v.val.val ^ (nmin),
      { rw [← associates.le_singleton_iff x nmin _],
       rw [associates.prime_pow_dvd_iff_le hx' _],
       exact min_le_left _ _,
        apply associates.irreducible_of_maximal v,
      },
      have h_dvd_y : y ∈ v.val.val ^ nmin,
      { rw [← associates.le_singleton_iff y nmin _, associates.prime_pow_dvd_iff_le hy' _],
        exact min_le_right _ _,
        apply associates.irreducible_of_maximal v,
      },
      have h_dvd_xy : associates.mk v.val.val^nmin ≤ associates.mk (ideal.span {x + y}),
      { rw associates.le_singleton_iff,
        exact ideal.add_mem (v.val.val^nmin) h_dvd_x h_dvd_y, },
      rw (associates.prime_pow_dvd_iff_le hxy' _) at h_dvd_xy,
      exact h_dvd_xy,
      apply associates.irreducible_of_maximal v, }}}
end

/-! Adic valuation on the ring of fractions -/

def int_valuation (v : maximal_spectrum R) : valuation R (with_zero (multiplicative ℤ)) :=
{ to_fun    := v.int_valuation_def, 
  map_zero' := int_valuation.map_zero' v,
  map_one'  := int_valuation.map_one' v,
  map_mul'  := int_valuation.map_mul' v,
  map_add'  := int_valuation.map_add' v }

lemma int_valuation_ne_zero' (x : R) (hx : x ≠ 0) : v.int_valuation_def x ≠ 0 :=
begin
  rw [int_valuation_def, if_neg hx],
  exact with_zero.coe_ne_zero,
end

lemma int_valuation_ne_zero (x : non_zero_divisors R) : v.int_valuation_def x ≠ 0 :=
int_valuation_ne_zero' v x (non_zero_divisors.coe_ne_zero x)


lemma int_valuation_zero_le (x : non_zero_divisors R) : 0 < v.int_valuation_def x :=
begin
  rw [int_valuation_def, if_neg (non_zero_divisors.coe_ne_zero x)],
  exact with_zero.zero_lt_coe _,
end

lemma int_valuation_le_one (x : R) : v.int_valuation_def x ≤ 1 :=
begin
  rw int_valuation_def,
  by_cases hx : x = 0,
  { rw if_pos hx, exact with_zero.zero_le 1,},
  { rw [if_neg hx, ← with_zero.coe_one, ← of_add_zero, with_zero.coe_le_coe, of_add_le,
      right.neg_nonpos_iff],
    exact int.coe_nat_nonneg _, }
end

lemma int_valuation_lt_one_iff_dvd (r : R) : 
  v.int_valuation_def r < 1 ↔ v.val.val ∣ ideal.span {r} :=
begin
  rw int_valuation_def,
  split_ifs with hr,
  { simpa [hr] using (with_zero.zero_lt_coe _) },
  { rw [← with_zero.coe_one, ← of_add_zero, with_zero.coe_lt_coe, of_add_lt, neg_lt_zero,
      ← int.coe_nat_zero, int.coe_nat_lt, zero_lt_iff],
    apply associates.count_ne_zero_iff_dvd,
    { rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact hr },
    { apply ideal.irreducible_of_maximal v }}
end

lemma ideal.is_nonunit_iff {I : ideal R} : ¬ is_unit I ↔ I ≠ ⊤ := not_congr ideal.is_unit_iff

lemma int_valuation_exists_uniformizer : 
  ∃ (π : R), v.int_valuation_def π = multiplicative.of_add (-1 : ℤ) := 
begin
  have hv : irreducible (associates.mk v.val.val) := associates.irreducible_of_maximal v,
  have hlt : v.val.val^2 < v.val.val,
  { rw ← ideal.dvd_not_unit_iff_lt,
    exact ⟨v.property, v.val.val,
     ideal.is_nonunit_iff.mpr (ideal.is_prime.ne_top v.val.property), sq v.val.val⟩ } ,
  obtain ⟨π, mem, nmem⟩ := set_like.exists_of_lt hlt,
  have hπ : associates.mk (ideal.span {π}) ≠ 0,
  { rw associates.mk_ne_zero',
    intro h,
    rw h at nmem,
    exact nmem (submodule.zero_mem (v.val.val^2)), },
  use π,
  rw [int_valuation_def, if_neg (associates.mk_ne_zero'.mp hπ), with_zero.coe_inj],
  apply congr_arg, 
  rw [neg_inj, ← int.coe_nat_one, int.coe_nat_inj'],
  rw [← ideal.dvd_span_singleton, ← associates.mk_le_mk_iff_dvd_iff] at mem nmem,
  rw [← pow_one ( associates.mk v.val.val), 
    associates.prime_pow_dvd_iff_le hπ hv]  at mem,
  rw [associates.mk_pow, associates.prime_pow_dvd_iff_le hπ hv, not_le] at nmem,
  exact nat.eq_of_le_of_lt_succ mem nmem,
end

def valuation_def (x : K) : (with_zero (multiplicative ℤ)) :=
let s := classical.some (classical.some_spec (is_localization.mk'_surjective
  (non_zero_divisors R) x)) in (v.int_valuation_def (classical.some
    (is_localization.mk'_surjective (non_zero_divisors R) x)))/(v.int_valuation_def s)

variable (K)
lemma valuation_well_defined {r r' : R} {s s' : non_zero_divisors R} 
  (h_mk : is_localization.mk' K r s = is_localization.mk' K r' s') :
  (v.int_valuation_def r)/(v.int_valuation_def s) =
  (v.int_valuation_def r')/(v.int_valuation_def s') := 
begin
  rw [div_eq_div_iff (int_valuation_ne_zero v s) (int_valuation_ne_zero v s'),
  ← int_valuation.map_mul', ← int_valuation.map_mul',
  is_fraction_ring.injective R K (is_localization.mk'_eq_iff_eq.mp h_mk)],
end

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
lemma valuation_of_algebra_map {r : R} :
  v.valuation_def (algebra_map R K r) = v.int_valuation_def r :=
by rw [← is_localization.mk'_one K r, valuation_of_mk', submonoid.coe_one, 
    int_valuation.map_one', div_one _]

lemma valuation_le_one (r : R) : v.valuation_def (algebra_map R K r) ≤ 1 :=
by { rw valuation_of_algebra_map, exact v.int_valuation_le_one r }

lemma valuation_lt_one_iff_dvd (r : R) : 
  v.valuation_def (algebra_map R K r) < 1 ↔ v.val.val ∣ ideal.span {r} :=
by { rw valuation_of_algebra_map, exact v.int_valuation_lt_one_iff_dvd r }

lemma valuation.map_zero' (v : maximal_spectrum R) :
  v.valuation_def (0 : K) = 0 := 
begin
  rw [← (algebra_map R K).map_zero, valuation_of_algebra_map v],
  exact v.int_valuation.map_zero',
end

lemma valuation.map_one' (v : maximal_spectrum R) :
  v.valuation_def (1 : K) = 1 := 
begin
  rw [← (algebra_map R K).map_one, valuation_of_algebra_map v],
  exact v.int_valuation.map_one',
end

lemma valuation.map_mul' (v : maximal_spectrum R) (x y : K) :
  v.valuation_def (x * y) = v.valuation_def x * v.valuation_def y :=
begin
  rw [valuation_def, valuation_def, valuation_def, div_mul_div _ _ _ _,
    ← int_valuation.map_mul', ← int_valuation.map_mul', ← submonoid.coe_mul],
  apply valuation_well_defined K v,
  rw [(classical.some_spec (valuation_def._proof_2 (x * y))), is_fraction_ring.mk'_eq_div,
    (algebra_map R K).map_mul, submonoid.coe_mul, (algebra_map R K).map_mul, ← div_mul_div,
    ← is_fraction_ring.mk'_eq_div, ← is_fraction_ring.mk'_eq_div,
    (classical.some_spec (valuation_def._proof_2 x)),
    (classical.some_spec (valuation_def._proof_2 y))],
end

lemma valuation.map_add' (v : maximal_spectrum R) (x y : K) :
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
  exact v.int_valuation.map_add' _ _,
end

def valuation (v : maximal_spectrum R) : valuation K (with_zero (multiplicative ℤ)) := { 
  to_fun    := v.valuation_def, 
  map_zero' := valuation.map_zero' v,
  map_one'  := valuation.map_one' v, 
  map_mul'  := valuation.map_mul' v, 
  map_add'  := valuation.map_add' v }

variable (K)
lemma valuation_exists_uniformizer : 
  ∃ (π : K), v.valuation_def π = multiplicative.of_add (-1 : ℤ) := 
begin
  obtain ⟨r, hr⟩ := v.int_valuation_exists_uniformizer,
  use algebra_map R K r,
  rw valuation_of_algebra_map v,
  exact hr,
end

lemma valuation_uniformizer_ne_zero :
  (classical.some (v.valuation_exists_uniformizer K)) ≠ 0 :=
begin
  have hu := (classical.some_spec (v.valuation_exists_uniformizer K)),
  have h : v.valuation_def (classical.some _) = valuation v (classical.some _) := rfl,
  rw h at hu,
  exact (valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu with_zero.coe_ne_zero),
end

end maximal_spectrum
