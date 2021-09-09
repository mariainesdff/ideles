import data.int.basic
import data.nat.prime
import data.pnat.basic
import data.real.basic
import number_theory.padics
import ring_theory.localization

noncomputable theory

open nat 
instance (p : primes) : fact (nat.prime p) := ⟨p.2⟩

def R := (Π (p: primes), ℤ_[p])

instance : comm_ring R := pi.comm_ring
instance : ring R := infer_instance

def inj_pnat : ℤ  → (Π (p : primes), ℤ_[p]) := λ (z : ℤ), (λ p, z) 

def M : submonoid R := 
{ carrier  := inj_pnat '' set.compl {0},
  one_mem' := by {use [1, set.mem_compl_singleton_iff.mpr one_ne_zero], 
    unfold inj_pnat, simp, refl},
  mul_mem' := 
  begin
    rintros a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩,
    use [za*zb, mul_ne_zero hza hzb],
    unfold inj_pnat, ext, simp,
  end }

def A_Q_f := localization M

--variables (α : Type*)
def f (x : Π p : primes, ℚ_[p]) (q : primes) : ℕ :=
{ p : primes | padic.valuation (x p) < 0 }.mul_indicator 
  (λ p : primes, p.val^int.nat_abs(padic.valuation (x p))) q 

open function set
--open_locale big_operators

variables {α : Type*} [decidable_eq α] {M : Type*} [comm_monoid M]

lemma finprod_mem_div (f : α → M) (a : α) (hf : finite (mul_support f)) : (f a) ∣ (finprod f) :=
begin
  by_cases ha: a ∈ (mul_support f),
  { unfold_projs,
    rw ← @finprod_cond_eq_left α M _ f a,
    set h := λ (i : α), finprod (λ (H : i = a), f i) with hdef,
    have hna : ∀ x ≠ a, h x = 1 := by {intros x hx, 
    rw hdef, dsimp only, rwa [finprod_eq_if, if_neg],},
    have hs : finite (mul_support h),
    { have hss : mul_support h ⊆ {a},
      { intros x hx,
        exact not_not.mp (mt (hna x) hx)},
      exact finite.subset (finite_singleton a) hss},
    set g : α → M := λ b, if b = a then 1 else (f b) with gdef,
    use finprod g,
    have gs : finite (mul_support g),
    { have hfg: mul_support g ⊆ mul_support f,
      { intros x hgx,
        rw mem_mul_support at hgx ⊢,
        rw gdef at hgx, dsimp only at hgx, 
        by_cases h2 : x = a,
        { rw if_pos h2 at hgx, exfalso, apply hgx, refl,},
        { rw if_neg h2 at hgx, exact hgx}}, 
        --simp at hgx ⊢,
        --exact hgx.right},
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
      unfold f, 
      rw [← finprod_eq_mul_indicator_apply, finprod_eq_if],
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
    exact absurd hp this},
    { exact hneg_abs }},
    rw [hn, padic_norm_e.norm_int_le_pow_iff_dvd (d : ℤ) (int.nat_abs(padic.valuation (x p)))],
    rw [int.coe_nat_dvd, hd],
    have h2 : f x p = ↑p^int.nat_abs(padic.valuation (x p)),
    { unfold f, 
      rw [mul_indicator_apply, if_pos], refl, rwa set.mem_set_of_eq },
    rw ← h2,
    apply finprod_mem_div (f x) p,
    have h3 : mul_support (f x) = { p : primes | padic.valuation (x p) < 0 },
    { ext q, 
      rw mul_support,
      unfold f,
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

def group_hom_prod (p : primes) : add_monoid_hom (Π (q: primes), ℤ_[q])  ℚ_[p] := 
{ to_fun    := (λ a, ↑(a p)),
  map_zero' := rfl,
  map_add'  := (λ x y, padic_int.coe_add (x p) (y p)) }

def hom_prod (p : primes) : ring_hom (Π (q: primes), ℤ_[q])  ℚ_[p]   := 
{ to_fun   := (λ a, ↑(a p)),
  map_one' := rfl,
  map_mul' := (λ x y, padic_int.coe_mul (x p) (y p)),
  ..group_hom_prod p }

def linear_prod (p: primes) : linear_map ℤ (Π (q: primes), ℤ_[q])  ℚ_[p] := 
{ to_fun    := (λ a, ↑(a p)),
  map_add'  := (λ x y, padic_int.coe_add (x p) (y p)),
  map_smul' :=  (λ m x, add_monoid_hom.map_int_module_smul (group_hom_prod p) m x) }

/- def map_to_Pi_Q_p (a : A_Q_f) : Π p : primes, ℚ_[p] :=
begin
  cases ((localization.monoid_of M).sec  a) with r d,
  exact λ p, (r p)/(d.val p),
end -/

/-  def proj_p (p: primes) : A_Q_f → ℚ_[p] := 
tensor_product.lift 
  (linear_map.mk₂ ℤ ((λ (p: primes) (r : ℚ) (a: Π (q: primes), ℤ_[q]), (r*(a p) : ℚ_[p])) p)
    (λ m₁ m₂ n, by {simp, ring})
    (λ c m n, by {simp, ring}) 
    (λ m n₁ n₂, by {simp, ring})
    (λ c m n, by {simp, ring})) -/