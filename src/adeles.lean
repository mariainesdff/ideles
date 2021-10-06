import data.int.basic
import data.nat.prime
import data.pnat.basic
import data.real.basic
import number_theory.padics
import topology.algebra.localization

noncomputable theory

/-! Finite adeles of ℚ -/
open nat 
instance (p : primes) : fact (nat.prime p) := ⟨p.2⟩

def pi_Z_p := (Π (p: primes), ℤ_[p])

instance : comm_ring pi_Z_p := pi.comm_ring
instance : ring pi_Z_p := infer_instance

def inj_pnat : ℤ  → (Π (p : primes), ℤ_[p]) := λ (z : ℤ), (λ p, z) 

def M : submonoid pi_Z_p := 
{ carrier  := inj_pnat '' set.compl {0},
  one_mem' := by {use [1, set.mem_compl_singleton_iff.mpr one_ne_zero], 
    rw inj_pnat, dsimp only, ext p, rw int.cast_one, refl},
  mul_mem' := 
  begin
    rintros a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩,
    use [za*zb, mul_ne_zero hza hzb],
    rw inj_pnat, ext, dsimp only,
    rw [pi.mul_apply, int.cast_mul],
  end }

def A_Q_f := localization M

--variables (α : Type*)
def f (x : Π p : primes, ℚ_[p]) (q : primes) : ℕ :=
{ p : primes | padic.valuation (x p) < 0 }.mul_indicator 
  (λ p : primes, p.val^int.nat_abs(padic.valuation (x p))) q 

open function set
--open_locale big_operators

lemma int_M (m : M) : ∃ d : ℤ, d ≠ 0 ∧ inj_pnat d = (m : pi_Z_p) :=
begin
  cases m with m hm,
  have hcarrier : M.carrier = inj_pnat '' ({0}ᶜ) := rfl,
  rw [← submonoid.mem_carrier, hcarrier] at hm,
  cases hm with d hd,
  use [d, hd.left, hd.right]
end

variables {α : Type*} [decidable_eq α] {N : Type*} [comm_monoid N]

lemma finprod_mem_div (f : α → N) (a : α) (hf : finite (mul_support f)) : (f a) ∣ (finprod f) :=
begin
  by_cases ha: a ∈ (mul_support f),
  { unfold_projs,
    rw ← @finprod_cond_eq_left α N _ f a,
    set h := λ (i : α), finprod (λ (H : i = a), f i) with hdef,
    have hna : ∀ x ≠ a, h x = 1 := by {intros x hx, 
    rw hdef, dsimp only, rwa [finprod_eq_if, if_neg],},
    have hs : finite (mul_support h),
    { have hss : mul_support h ⊆ {a},
      { intros x hx,
        exact not_not.mp (mt (hna x) hx)},
      exact finite.subset (finite_singleton a) hss},
    set g : α → N := λ b, if b = a then 1 else (f b) with gdef,
    use finprod g,
    have gs : finite (mul_support g),
    { have hfg: mul_support g ⊆ mul_support f,
      { intros x hgx,
        rw mem_mul_support at hgx ⊢,
        rw gdef at hgx, dsimp only at hgx, 
        by_cases h2 : x = a,
        { rw if_pos h2 at hgx, exfalso, apply hgx, refl,},
        { rw if_neg h2 at hgx, exact hgx}}, 
      exact finite.subset hf hfg},
    rw ← finprod_mul_distrib hs gs,
    apply finprod_congr,
    have H : ∀ x, f x = (h x) * (g x),
    { intro x,
      by_cases h2 : x = a,
        {rw [h2, gdef, hdef], 
        dsimp only, 
        rw [finprod_eq_if, if_pos, if_pos, mul_one], 
        refl, refl}, 
        {rw [hna x h2, one_mul, gdef], 
        dsimp only,
        rw if_neg, 
        exact h2}}, 
    exact H}, 
    rw [mem_mul_support, not_not] at ha,
    rw ha, exact one_dvd (finprod f),
end

lemma denom_pos (x : Π p : primes, ℚ_[p]) 
  (h : set.finite({ p : primes | padic.valuation (x p) < 0 })) : 1 ≤ finprod (f x) :=
begin
    have hp : ∀ p, 1 ≤ (f x) p,
    { intro p,
      rw [f, ← finprod_eq_mul_indicator_apply, finprod_eq_if],
      by_cases h : p ∈ {p : primes | (x p).valuation < 0},
      { rw if_pos h, exact nat.one_le_pow (int.nat_abs (x p).valuation) p (nat.prime.pos p.2)},
      { rw if_neg h }},
    exact one_le_finprod' hp,
end

lemma norm_d (x : Π p : primes, ℚ_[p]) (h : set.finite({ p : primes | padic.valuation (x p) < 0 })) 
  {p : primes} (hp : padic.valuation (x p) < 0) : 
  ∥(↑(↑(finprod (f x)) : ℤ) : ℚ_[p])∥ ≤ (↑(↑p : ℕ)^(x p).valuation : ℝ) := 
  begin
    set d := finprod ( f x) with hd,
    have : 0 ≤ -(x p).valuation,
    { rw [le_neg, neg_zero], exact le_of_lt hp },
    have hn : (x p).valuation = -int.nat_abs(padic.valuation (x p)),
    { cases int.nat_abs_eq (x p).valuation with habs hneg_abs,
    { have : 0 ≤  (x p).valuation, by {rw habs, rw ← int.abs_eq_nat_abs, exact abs_nonneg _},
    rw ← not_lt at this,
    exact absurd hp this },
    { exact hneg_abs }},
    rw [hn, padic_norm_e.norm_int_le_pow_iff_dvd (d : ℤ) (int.nat_abs(padic.valuation (x p)))],
    rw [int.coe_nat_dvd, hd],
    have h2 : f x p = ↑p^int.nat_abs(padic.valuation (x p)),
    { rw [f, mul_indicator_apply, if_pos], refl, rwa set.mem_set_of_eq },
    rw ← h2,
    apply finprod_mem_div (f x) p,
    have h3 : mul_support (f x) = { p : primes | padic.valuation (x p) < 0 },
    { ext q, 
      rw mul_support,
      simp_rw f,
      split,
      { intro hne_one, exact mem_of_mul_indicator_ne_one hne_one},
      { intro hval, rw mem_set_of_eq at hval ⊢, rw mul_indicator_apply, rw if_pos, 
      exact ne_of_gt (one_lt_pow (x q).valuation.nat_abs q
        (int.nat_abs_pos_of_ne_zero (int.ne_of_lt hval))
        (nat.prime.one_lt q.2)),
      exact hval }},
    rwa h3,
  end

lemma int_components (x : Π p : primes, ℚ_[p]) 
  (h : set.finite({ p : primes | padic.valuation (x p) < 0 })) (p : primes) : 
  ∥↑(finprod (f x))*(x p)∥ ≤ 1 := 
begin
  set d := finprod (f x) with hd,
  rw [padic_norm_e.mul],
  by_cases hp : p ∈ { p : primes | padic.valuation (x p) < 0 },
  { rw set.mem_set_of_eq at hp,
      have hd : ∥↑↑d∥ ≤ ↑(↑p : ℕ)^(x p).valuation := norm_d x h hp,
      have hxp : ∥x p∥ = ↑(↑p : ℕ)^-(x p).valuation,
      { apply padic.norm_eq_pow_val,
      intro hzero,
      rw [hzero, padic.valuation_zero] at hp,
      exact lt_irrefl 0 hp},
      have hpos : (0 : ℝ)  < ↑↑p := by { rw [← cast_zero, nat.cast_lt], exact nat.prime.pos p.2},
      calc ∥↑d∥ * ∥x p∥ ≤ ↑↑p^(x p).valuation * ∥x p∥          : mul_le_mul hd (le_refl ∥x p∥) 
        (norm_nonneg (x p)) (fpow_nonneg (le_of_lt hpos) (x p).valuation)
        ... = (↑↑p^(x p).valuation) * (↑↑p^-(x p).valuation)  : by rw hxp
        ... = (↑↑p^(x p).valuation) * (↑↑p^(x p).valuation)⁻¹ : by rw fpow_neg
        ... = 1                                               : mul_inv_cancel 
        (nat.fpow_ne_zero_of_pos (nat.prime.pos p.2) (x p).valuation)},
  { rw [set.nmem_set_of_eq, not_lt] at hp,
      have h1 : ∥x p∥ ≤ (1 : ℝ) ,
      { by_cases h2 : ((x p) = 0),
        { rw [h2, norm_zero], exact zero_le_one },
        { rw padic.norm_eq_pow_val h2, 
          lift (x p).valuation to ℕ using hp with xval,
          have h3 : (↑1 : ℝ) ≤ ↑(↑p ^ xval) := 
            nat.cast_le.mpr (nat.one_le_pow xval p (nat.prime.pos p.2)),
          rw [cast_pow, cast_one] at h3,
          rw [fpow_neg ↑↑p ↑xval, gpow_coe_nat],
          rw ← inv_le real.zero_lt_one (lt_of_lt_of_le zero_lt_one h3),
          rwa inv_one}},
        calc ∥↑d∥ * ∥x p∥ ≤ 1 * ∥x p∥       : mul_le_mul (padic_norm_e.norm_int_le_one d) 
          (le_refl ∥x p∥) (norm_nonneg (x p)) zero_le_one
        ... ≤ 1 * 1                        : mul_le_mul (le_refl 1) h1 (norm_nonneg (x p)) 
          zero_le_one
        ... = 1                            : by rw mul_one},
end

def map_from_Pi_Q_p (x : Π p : primes, ℚ_[p]) 
  (h : set.finite({ p : primes | padic.valuation (x p) < 0 })) : A_Q_f := 
let d := finprod (f x) in localization.mk 
  (λ p, ⟨d*(x p), int_components x h p⟩)
  ⟨inj_pnat d , by use [d, set.mem_compl_singleton_iff.mpr 
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (int.to_nat_le.mp (denom_pos x h))))]⟩

def group_hom_prod' (p : primes) : add_monoid_hom pi_Z_p ℚ_[p] := 
{ to_fun    := (λ a, ↑(a p)),
  map_zero' := rfl,
  map_add'  := (λ x y, padic_int.coe_add (x p) (y p)) }

def hom_prod' (p : primes) : ring_hom pi_Z_p ℚ_[p]   := 
{ to_fun   := (λ a, ↑(a p)),
  map_one' := rfl,
  map_mul' := (λ x y, padic_int.coe_mul (x p) (y p)),
  ..group_hom_prod' p }

/- def linear_prod' (p: primes) : linear_map ℤ pi_Z_p ℚ_[p] := 
{ to_fun    := (λ a, ↑(a p)),
  map_add'  := (λ x y, padic_int.coe_add (x p) (y p)),
  map_smul' :=  (λ m x, add_monoid_hom.map_int_module_smul (group_hom_prod' p) m x) } -/

def group_hom_prod : add_monoid_hom pi_Z_p (Π p : primes, ℚ_[p]) := 
{ to_fun    := (λ a p, ↑(a p)),
  map_zero' := rfl,
  map_add'  := assume x y, by {ext p, rw [pi.add_apply, padic_int.coe_add], refl}}

def hom_prod : ring_hom pi_Z_p (Π p : primes, ℚ_[p])   := 
{ to_fun   := (λ a p, ↑(a p)),
  map_one' := rfl,
  map_mul' := assume x y, by {ext p, rw [pi.mul_apply, padic_int.coe_mul], refl},
  ..group_hom_prod }

instance : comm_ring A_Q_f := localization.comm_ring
instance : algebra pi_Z_p A_Q_f := localization.algebra
instance : is_localization M A_Q_f := localization.is_localization

lemma m_ne_zero (m : M) (p : primes) : (↑m : pi_Z_p) p ≠ 0 := 
begin
  cases m with m hm,
  have hcarrier : M.carrier = inj_pnat '' ({0}ᶜ) := rfl,
  rw [← submonoid.mem_carrier, hcarrier, set.mem_image inj_pnat (compl {0}) m] at hm,
  rcases hm with ⟨z, hne_zero, hz⟩,
  rw set.mem_compl_singleton_iff at hne_zero,
  rw [set_like.coe_mk, ← hz, inj_pnat],
  exact int.cast_ne_zero.mpr hne_zero,
end

lemma padic_int.cast_eq_zero {p : primes} {z : ℤ_[p]} : (z : ℚ_[p]) = 0 ↔ z = 0 := 
⟨ λ h, by {ext, exact h}, λ h, by {rw h, refl}⟩

lemma padic_int.cast_ne_zero {p : primes} {z : ℤ_[p]} : (z : ℚ_[p]) ≠  0 ↔ z ≠ 0 := 
not_congr padic_int.cast_eq_zero

lemma padic_int.cast_inj {p : primes} {x y : ℤ_[p]} : (x : ℚ_[p]) = y ↔ x = y 
:= ⟨ λ h, by {ext, exact h}, λ h, by {rw h}⟩

lemma hom_prod_m_unit : ∀ m : M, is_unit (hom_prod m) :=
begin
  rintro ⟨m, hm⟩,
  rw is_unit_iff_exists_inv,
  use (λ p, (m p)⁻¹),
  rw [hom_prod, ring_hom.coe_mk, set_like.coe_mk, pi.mul_def],
  ext p,
  exact mul_inv_cancel (padic_int.cast_ne_zero.mpr (m_ne_zero ⟨m, hm⟩ p)),
end

def map_to_Pi_Q_p (a : A_Q_f) : Π p : primes, ℚ_[p] :=
is_localization.lift hom_prod_m_unit a

def map_to_Pi_Q_p' : ring_hom A_Q_f (Π p : primes, ℚ_[p]) :=
is_localization.lift hom_prod_m_unit

lemma padic.valuation_mul {p : primes} ( q r : ℚ_[p]) (hq : q ≠ 0) (hr : r ≠ 0) : 
  (q * r).valuation = q.valuation + r.valuation := 
begin
  have h : ∥q * r∥ = ∥q∥ * ∥r∥ := padic_norm_e.mul q r,
  rw [padic.norm_eq_pow_val hq, padic.norm_eq_pow_val hr] at h,
  rw padic.norm_eq_pow_val (mul_ne_zero hq hr) at h,
  have hp :  (0 : ℝ) < ↑(p : ℕ),
  {rw [← cast_zero, cast_lt], exact prime.pos p.property},
  have h0 : ↑(p : ℕ) ≠ (0 : ℝ) := ne_of_gt hp,
  have h1 : ↑(p : ℕ) ≠ (1 : ℝ),
  { rw ← cast_one,
    intro h2,
    exact (nat.prime.ne_one p.property) (nat.cast_inj.mp h2),
  },
  rw [← fpow_add h0 (-q.valuation) (-r.valuation), fpow_inj hp h1, ← neg_add _ _] at h,
  exact neg_inj.mp h,
end

/- def map_to_Pi_Q_p (a : A_Q_f) : Π p : primes, ℚ_[p] :=
map_to_Pi_Q_p' a -/

lemma finite_factors (d : ℤ) (hd : d ≠ 0) : finite {p : primes | ↑p.val ∣ d} := begin
  set factors := {p : primes | ↑p.val ∣ d},
  have h : factors = {p : primes | p.val ∈ (int.nat_abs d).factors.to_finset},
  { ext p,
    rw [set.mem_set_of_eq, set.mem_set_of_eq, list.mem_to_finset, 
      mem_factors_iff_dvd (nat.pos_of_ne_zero (int.nat_abs_ne_zero_of_ne_zero hd)) p.2, 
      ← int.coe_nat_dvd],
    exact iff.symm int.dvd_nat_abs,
  },
  rw h,
  exact finite.preimage_embedding (⟨(λ p : primes, (p : ℕ)), primes.coe_nat_inj⟩ ) 
    (finite_mem_finset ((int.nat_abs d).factors.to_finset)),
end

@[simp]
lemma padic_int.coe_valuation {p : ℕ} [fact p.prime] (x : ℤ_[p]) :
(x : ℚ_[p]).valuation = x.valuation := rfl

lemma padic.valuation_pos_iff_dvd {p : ℕ} [hp : fact (p.prime)] (d : ℤ) (hd : d ≠ 0) :
0 < (d : ℚ_[p]).valuation ↔ (p : ℤ) ∣ d := 
begin 
  rw [← padic_norm_e.norm_int_lt_one_iff_dvd, ← padic_int.coe_coe_int, 
    padic_int.padic_norm_e_of_padic_int (d : ℤ_[p]), padic_int.norm_eq_pow_val,
    ← gpow_zero (p : ℝ), fpow_lt_iff_lt, padic_int.coe_valuation, right.neg_neg_iff],
  { rw [← nat.cast_one, nat.cast_lt],
    exact prime.one_lt hp.1 },
  { exact int.cast_ne_zero.mpr hd },
end

--set_option pp.implicit true

lemma restricted_image (a : A_Q_f) : 
  set.finite({ p : primes | padic.valuation ((map_to_Pi_Q_p a) p) < 0 }) := 
begin
  set supp := {p : primes | padic.valuation ((map_to_Pi_Q_p a) p) < 0} with hsupp,
  have ha : ∃ r (d' : M), is_localization.mk' A_Q_f r d' = a := is_localization.mk'_surjective M a,
  rcases ha with ⟨r, d', ha⟩,
  rw [map_to_Pi_Q_p, ← ha, @is_localization.lift_mk' pi_Z_p _ M A_Q_f _ _ _ _ _ _ hom_prod_m_unit r d']
    at hsupp,
  have hd : ∃ d : ℤ, d ≠ 0 ∧ inj_pnat d = d'.val,
  { rw subtype.val_eq_coe,
    exact int_M d' },
  rcases hd with ⟨d, hd_ne_zero, hd_inj⟩,
  have hsubset : supp ⊆ {p : primes | ↑p.val ∣ d},
  { rw hsupp,
    intros p hp,
    have hd : (d' : pi_Z_p) p = (d : ℤ_[p]),
    { simp_rw [← subtype.val_eq_coe],
      rw [← hd_inj,inj_pnat]},
    rw mem_set_of_eq at hp ⊢,
    rw pi.mul_apply at hp,
    by_cases hr : (hom_prod r p) = 0,
    { rw [hr, zero_mul, padic.valuation_zero] at hp,
      exfalso,
      exact lt_irrefl 0 hp},
    { have h_inv : 
        (((is_unit.lift_right (hom_prod.to_monoid_hom.mrestrict M) hom_prod_m_unit) d').inv p) *
        ((hom_prod.to_monoid_hom.mrestrict M) d' p) = 1,
      { rw [units.inv_eq_coe_inv, ← pi.mul_apply, is_unit.lift_right_inv_mul 
          (hom_prod.to_monoid_hom.mrestrict M) hom_prod_m_unit d', pi.one_apply]},
      rw [← units.inv_eq_coe_inv , padic.valuation_mul _ _ hr (left_ne_zero_of_mul_eq_one h_inv),
        ← not_le] at hp,
      have hval : 0 < ((hom_prod.to_monoid_hom.mrestrict M) d' p).valuation,
      { have hinv_add : padic.valuation
        (((is_unit.lift_right (hom_prod.to_monoid_hom.mrestrict M) hom_prod_m_unit) d').inv p)
        + padic.valuation ((hom_prod.to_monoid_hom.mrestrict M) d' p) = 0,
        { rw [← padic.valuation_mul _ _ (left_ne_zero_of_mul_eq_one h_inv)
            (right_ne_zero_of_mul_eq_one h_inv), h_inv, padic.valuation_one]},
      have hp_nonneg: 0 ≤ (hom_prod r p).valuation,
      { rw [hom_prod, ring_hom.coe_mk, padic_int.coe_valuation],
        exact padic_int.valuation_nonneg (r p)},
        by_contradiction h1,
        rw [not_lt, ← (neg_eq_of_add_eq_zero hinv_add), ← neg_zero, neg_le_neg_iff] at h1,
        have h2 := le_add_of_nonneg_of_le hp_nonneg h1,
        exact hp h2},      
      rw [hom_prod, monoid_hom.mrestrict_apply, ring_hom.to_monoid_hom_eq_coe, 
        ring_hom.coe_monoid_hom_mk, monoid_hom.coe_mk, hd, padic_int.coe_coe_int] at hval,
      exact (padic.valuation_pos_iff_dvd d hd_ne_zero).mp hval}},
  exact finite.subset (finite_factors d hd_ne_zero) hsubset,
end

--set_option profiler true
-- ~7s
lemma left_inverse_map_to_Pi_Q_p (a : A_Q_f) : 
  map_from_Pi_Q_p (map_to_Pi_Q_p a) (restricted_image a) = a := 
begin
  have ha : ∃ r (d' : M), is_localization.mk' (localization M) r d' = a := 
    is_localization.mk'_surjective M a,
  rcases ha with ⟨r, ⟨d', hd'⟩, ha⟩,
  simp_rw map_to_Pi_Q_p,
  rw map_from_Pi_Q_p,
  dsimp only,
  rw [localization.mk_eq_mk'_apply, ← ha],
  apply is_localization.mk'_eq_iff_eq.mpr,
  rw [pi.mul_def, subtype.coe_mk, pi.mul_def, subtype.coe_mk],
  apply congr_arg,
  ext p,
  rw [inj_pnat, padic_int.coe_mul, padic_int.coe_mul, subtype.coe_mk],
  dsimp only,
  rw [int.cast_coe_nat, padic_int.coe_coe, mul_comm (r p : ℚ_[p]) _, mul_assoc,
    mul_eq_mul_left_iff],
  left,
  rw [@is_localization.lift_mk' pi_Z_p _ M (localization M) _ _ _ _ _ _ hom_prod_m_unit r ⟨d', hd' ⟩,
    pi.mul_apply],
  have h2 : (hom_prod.to_monoid_hom.mrestrict M) ⟨d', hd'⟩ p = ↑(d' p),
  { rw [monoid_hom.mrestrict_apply, ring_hom.to_monoid_hom_eq_coe, set_like.coe_mk, hom_prod,
    ring_hom.coe_monoid_hom_mk, monoid_hom.coe_mk],
  },
  rw [← h2, mul_assoc, ← pi.mul_apply _ ((hom_prod.to_monoid_hom.mrestrict M) ⟨d', hd'⟩),
    (is_unit.lift_right_inv_mul (hom_prod.to_monoid_hom.mrestrict M) hom_prod_m_unit ⟨d', hd'⟩),
    hom_prod, ring_hom.coe_mk, pi.one_apply, mul_one],
end

lemma right_inverse_map_to_Pi_Q_p (x : Π p : primes, ℚ_[p]) 
  (h : set.finite({ p : primes | padic.valuation (x p) < 0 })):
  (map_to_Pi_Q_p (map_from_Pi_Q_p x h)) = x := 
begin
  rw map_from_Pi_Q_p,
  dsimp only,
  rw [localization.mk_eq_mk'_apply, map_to_Pi_Q_p],
  apply (is_localization.lift_mk'_spec _ _ _ _).mpr,
  ext p,
  rw [hom_prod, ring_hom.coe_mk, subtype.coe_mk, subtype.coe_mk, pi.mul_apply,
    mul_eq_mul_right_iff],
  by_cases hp: (x p = 0),
  { right, exact hp},
  {left, rw inj_pnat, 
  dsimp only,
  rw [int.cast_coe_nat, padic_int.coe_coe]},
end

lemma map_mul (r s : ℚ) (p : primes) : 
((r * s).num : ℚ_[p]) * ((r.denom) * (s.denom)) =  (r.num) * (s.num) * ((r * s).denom) := 
begin
  rw [rat.mul_num, rat.mul_denom, ← nat.cast_mul, ← int.cast_coe_nat, ← int.cast_mul,
    ← int.cast_mul, ← int.mul_div_assoc' ↑(r.denom * s.denom), padic.cast_eq_of_rat_of_nat,
    ← int.cast_coe_nat _, ← padic.cast_eq_of_rat_of_int, ← int.cast_mul (r.num * s.num) _,
    int.coe_nat_div, ← int.mul_div_assoc (r.num * s.num)],
  exact int.gcd_dvd_right (r.num * s.num) (r.denom * s.denom),
  exact int.gcd_dvd_left (r.num * s.num) (r.denom * s.denom),
end

private lemma map_add (r s : ℚ) (p : primes) : 
((r + s).num : ℚ_[p]) * ((r.denom) * (s.denom)) = 
((r.num) * (s.denom) + (s.num) * (r.denom)) * ((r + s).denom) := 
begin
  rw [rat.add_num_denom r s, ← int.cast_coe_nat],
  repeat {rw ← int.cast_coe_nat},
  repeat {rw ← int.cast_mul},
  rw [← int.cast_add, ← int.cast_mul, int.cast_inj,← int.coe_nat_mul],
  have h : 0 < (r.denom * s.denom : ℕ) := 
    mul_pos (nat.pos_of_ne_zero r.denom_ne_zero) (nat.pos_of_ne_zero s.denom_ne_zero),
  rw [← rat.mk_pnat_eq _ (r.denom * s.denom : ℕ) h, rat.mk_pnat_num _ _, rat.mk_pnat_denom _ _,
  pnat.mk_coe, int.coe_nat_div, int.coe_nat_mul, mul_comm ↑(r.denom) s.num,
  ← int.mul_div_assoc' (↑(r.denom) * ↑(s.denom)),
  int.mul_div_assoc (r.num * ↑(s.denom) + s.num * ↑(r.denom))],
  exact int.gcd_dvd_right _ _,
  exact int.gcd_dvd_left (r.num * ↑(s.denom) + s.num * ↑(r.denom)) (r.denom * s.denom),
end


private lemma M_non_divisors: M ≤ non_zero_divisors pi_Z_p :=
begin
  intros x hxM,
  have hcarrier : M.carrier = inj_pnat '' ({0}ᶜ) := rfl,
  rw [non_zero_divisors, ← submonoid.mem_carrier, mem_set_of_eq],
  rw [← submonoid.mem_carrier, hcarrier, mem_image] at hxM,
  rcases hxM with ⟨d, hd, hd1⟩,
  rw [mem_compl_eq {(0 : ℤ)}, mem_singleton_iff] at hd,
  intros z hz,
  rw [← hd1, pi.mul_def, pi.zero_def, inj_pnat] at hz,
  ext p,
  have h : (z p)*↑d = 0, 
  { calc (z p)*↑d = (λ (i : primes), z i * ↑d) p : rfl
              ... = (λ (i : primes), (0 : ℤ_[p])) p : by rw hz
              ... = 0 : rfl},
  rw padic_int.cast_inj,
  have hd' : ↑d ≠ (0 : ℤ_[p]) := int.cast_ne_zero.mpr hd,
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero hd' h,
end

--set_option profiler true
noncomputable instance Q_algebra_A_Q_f: algebra ℚ A_Q_f := { smul := λ r a,
  (localization.mk (λ p, r.num) 
    ⟨(inj_pnat ↑r.denom), by {use [↑ r.denom, 
      set.mem_compl_singleton_iff.mpr (int.coe_nat_ne_zero.mpr (r.denom_ne_zero))]}⟩) * a,
  to_fun := λ r, localization.mk (λ p, r.num) 
    ⟨(inj_pnat ↑r.denom), by {use [↑ r.denom, 
      set.mem_compl_singleton_iff.mpr (int.coe_nat_ne_zero.mpr (r.denom_ne_zero))]}⟩,
  map_one' := begin
    rw [localization.mk_eq_mk', ← @is_localization.mk'_self' pi_Z_p _ M (localization M) _ _ _ 1],
    apply is_localization.mk'_eq_iff_eq.mpr,
    apply congr_arg,
    simp_rw inj_pnat,
    ext p,
    rw [set_like.coe_mk, submonoid.coe_one, mul_one, one_mul, rat.num_one, rat.denom_one,
    int.cast_coe_nat], refl,
  end,
  map_mul' :=  λ r s, begin
    simp_rw inj_pnat,
    rw [localization.mk_eq_mk', ← is_localization.mk'_mul (localization M) _ _ _ _],
    simp_rw int.cast_coe_nat,
    apply is_localization.mk'_eq_iff_eq.mpr,
    rw algebra_map,
    repeat {rw pi.mul_def},
    apply congr_arg,
    ext p,
    rw [submonoid.coe_mul, set_like.coe_mk, set_like.coe_mk, set_like.coe_mk, pi.mul_apply],
    dsimp only,
    repeat {rw padic_int.coe_mul},
    repeat {rw padic_int.coe_coe},
    repeat { rw padic_int.coe_coe_int},
    exact map_mul r s p,
  end,
  map_zero' := begin
    rw localization.mk_eq_mk',
    simp_rw [rat.num_zero, int.cast_zero, rat.denom_zero],
    rw [@is_localization.mk'_eq_iff_eq_mul pi_Z_p _ M (localization M) _ _ _ _ _ _, zero_mul,
      is_localization.to_map_eq_zero_iff (localization M) M_non_divisors],
    refl,
  end,
  map_add' :=  λ r s, begin
    simp_rw inj_pnat,
    rw [localization.mk_eq_mk', ← @is_localization.mk'_add pi_Z_p _ M (localization M) _ _ _ _ _ _ _,
      set_like.coe_mk, set_like.coe_mk], 
    simp_rw int.cast_coe_nat,
    apply is_localization.mk'_eq_iff_eq.mpr,
    apply congr_arg,
    repeat {rw pi.mul_def},
    rw pi.add_def,
    ext p,
    rw [submonoid.coe_mul, set_like.coe_mk, set_like.coe_mk, set_like.coe_mk, pi.mul_apply],
    dsimp only,
    repeat {rw padic_int.coe_mul},
    rw padic_int.coe_add,
    repeat {rw padic_int.coe_mul},
    repeat {rw padic_int.coe_coe},
    repeat { rw padic_int.coe_coe_int},
    exact map_add r s p,
  end,
  commutes' := λ r x, by {rw mul_comm},
  smul_def' := λ r x, rfl}

/-! Adeles of ℚ -/
def A_Q := A_Q_f × ℝ

def map_from_Pi_Q_p_pi_Z_p (x : (Π p : primes, ℚ_[p]) ×  ℝ) 
  (h : set.finite({ p : primes | padic.valuation (x.1 p) < 0 })) : A_Q := 
⟨ map_from_Pi_Q_p x.1 h, x.2⟩

def map_to_Pi_Q_p_pi_Z_p (a : A_Q) : (Π p : primes, ℚ_[p]) × ℝ :=
⟨map_to_Pi_Q_p a.1, a.2⟩

lemma left_inverse_map_to_Pi_Q_p_pi_Z_p (a : A_Q) : 
  map_from_Pi_Q_p_pi_Z_p (map_to_Pi_Q_p_pi_Z_p a) (restricted_image a.1) = a := 
begin
  simp_rw map_to_Pi_Q_p_pi_Z_p,
  rw [map_from_Pi_Q_p_pi_Z_p, prod.eq_iff_fst_eq_snd_eq],
  exact ⟨left_inverse_map_to_Pi_Q_p a.1, rfl⟩,
end

lemma right_inverse_map_to_Pi_Q_p_pi_Z_p (x : (Π p : primes, ℚ_[p]) ×  ℝ)
  (h : set.finite({ p : primes | padic.valuation (x.1 p) < 0 })) :
  (map_to_Pi_Q_p_pi_Z_p (map_from_Pi_Q_p_pi_Z_p x h)) = x :=
begin
  rw [map_from_Pi_Q_p_pi_Z_p, map_to_Pi_Q_p_pi_Z_p, prod.eq_iff_fst_eq_snd_eq], 
  exact ⟨ right_inverse_map_to_Pi_Q_p x.1 h, rfl⟩,
end

instance : semiring A_Q := prod.semiring
instance : comm_ring A_Q := prod.comm_ring
instance : algebra ℚ A_Q := algebra.prod.algebra ℚ A_Q_f ℝ

/-! Topological ring  -/
instance : topological_space pi_Z_p := Pi.topological_space
instance : topological_space A_Q_f := localization.topological_space
instance : topological_ring A_Q_f := localization.topological_ring

instance : topological_space A_Q := prod.topological_space
instance : topological_ring A_Q := prod.topological_ring