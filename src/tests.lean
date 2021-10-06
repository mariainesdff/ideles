import adeles
import topological_ring

noncomputable theory
open nat 

-- Ring filter basis for ℤ_[p] satisfying h

instance m_p {p : primes} : metric_space ℤ_[p] := infer_instance
instance t_p {p : primes} : topological_space ℤ_[p] := infer_instance

private lemma one_lt_real_prime (p : primes) : 1 < (p : ℝ) :=
by { rw [coe_coe, one_lt_cast], exact nat.prime.one_lt p.2}
private lemma real_prime_pos (p : primes) : 0 < (p : ℝ) :=
lt_trans zero_lt_one (one_lt_real_prime p)

-- overkill
def B_Z_p (p : primes) := { U : set ℤ_[p] | ∃ n : ℤ,  U = metric.ball (0 : ℤ_[p]) (p^-n)}

lemma padic_int.univ_open_ball {p : primes} (n : ℤ) (hn : 0 < n) : 
  set.univ = (metric.ball (0 : ℤ_[p]) ((p : ℝ)^n)) := 
begin
  ext z,
  split; intro hz,
  { rw mem_ball_zero_iff,
    have hz : ∥z∥ ≤ 1 := padic_int.norm_le_one z,
    have hp : 1 < (p : ℝ)^(n : ℤ) := 
    begin
      rw [← gpow_zero (p : ℝ), fpow_lt_iff_lt (one_lt_real_prime p)],
      exact hn,
    end,
    exact lt_of_le_of_lt hz hp, },
  { exact set.mem_univ z }
end

/- lemma padic.norm_le_pow_iff_norm_lt_pow_add_one {p : ℕ} [hp_prime : fact p.prime] (x : ℚ_[p]) 
  (n : ℤ) : ∥x∥ ≤ p ^ n ↔ ∥x∥ < p ^ (n + 1) :=
begin
  have aux : ∀ n : ℤ, 0 < (p ^ n : ℝ),
  { apply nat.fpow_pos_of_pos, exact hp_prime.1.pos },
  by_cases hx0 : x = 0, { simp [hx0, norm_zero, aux, le_of_lt (aux _)], },
  rw padic.norm_eq_pow_val hx0,
  have h1p : 1 < (p : ℝ), { exact_mod_cast hp_prime.1.one_lt },
  have H := fpow_strict_mono h1p,
  rw [H.le_iff_le, H.lt_iff_lt, int.lt_add_one_iff],
end

lemma padic.norm_lt_pow_iff_norm_le_pow_sub_one {p : ℕ} [ hp_prime : fact p.prime] (x : ℚ_[p])
  (n : ℤ) : ∥x∥ < p ^ n ↔ ∥x∥ ≤ p ^ (n - 1) :=
by rw [padic.norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel] -/

lemma padic_int.mul_open_ball {p : primes} {z : ℤ_[p]} (hz : z ≠ 0) (n : ℤ) :
  {z} * (metric.ball (0 : ℤ_[p]) ((p : ℝ)^n)) = 
  (metric.ball (0 : ℤ_[p]) ((p : ℝ)^((min 1 n) - (z : ℤ_[p]).valuation))) := 
begin
  ext x,
  rw [set.singleton_mul, set.mem_image, metric.mem_ball, dist_eq_norm, sub_zero],
  simp_rw [metric.mem_ball, dist_eq_norm, sub_zero],
  split; intro hx,
  { rcases hx with ⟨y, hy, hyx⟩,
    rw [ ← hyx, fpow_sub (ne_of_gt (real_prime_pos p)), padic_int.norm_mul, 
    padic_int.norm_eq_pow_val hz, ← coe_coe, lt_div_iff (fpow_pos_of_pos (real_prime_pos p)
    ((z : ℤ_[p]).valuation)), mul_comm, ← mul_assoc, ← fpow_add (ne_of_gt (real_prime_pos p)),
    add_right_neg, gpow_zero, one_mul],
    cases (min_choice 1 n) with hmin_1 hmin_n,
    { rw [hmin_1, coe_coe, padic_int.norm_lt_pow_iff_norm_le_pow_sub_one y 1, sub_self, gpow_zero], 
      exact padic_int.norm_le_one y, },
    { rw hmin_n,
      exact hy }},
  { have hz_pos : 0 < ∥(z : ℚ_[p])∥ := by { rw [norm_pos_iff, padic_int.cast_ne_zero], exact hz },
    have hdiv_p : ∥(x : ℚ_[p])/z∥ < (p : ℝ)^(min 1 n),
    { rw [normed_field.norm_div, div_lt_iff hz_pos, padic_int.padic_norm_e_of_padic_int (z : ℤ_[p]),
        padic_int.norm_eq_pow_val hz, ← coe_coe, ← fpow_add (ne_of_gt (real_prime_pos p)), 
        ← sub_eq_add_neg],
      exact hx },
    have hdiv : ∥(x : ℚ_[p])/z∥ ≤ 1,
    { rw [← gpow_zero ((p : ℕ) : ℝ), padic.norm_le_pow_iff_norm_lt_pow_add_one, zero_add],
      have hp : (p : ℝ)^(min 1 n) ≤ (p : ℝ)^(1 : ℤ),
      { rw fpow_le_iff_le (one_lt_real_prime p),
        exact min_le_left 1 n },
      exact lt_of_lt_of_le hdiv_p hp },
    use [(x : ℚ_[p])/z, hdiv],
    split,
    { rw padic_int.norm_eq_padic_norm,
      have hp : (p : ℝ)^(min 1 n) ≤ (p : ℝ)^n,
      { rw fpow_le_iff_le (one_lt_real_prime p),
        exact min_le_right 1 n },
      exact lt_of_lt_of_le hdiv_p hp },
    { rw [← padic_int.cast_inj, padic_int.coe_mul, subtype.coe_mk, ← mul_div_assoc, mul_comm, 
        mul_div_assoc, div_self, mul_one],
      rw padic_int.cast_ne_zero,
      exact hz }}
end

lemma open_mul_Z_p {p : primes} (U : set ℤ_[p]) (hU : U ∈ B_Z_p p) {z : ℤ_[p]} (hz : z ≠ 0) : 
(λ (x : ℤ_[p]), z*x) '' U ∈ B_Z_p p := 
begin
  cases hU with n hball,
  rw [← set.singleton_mul, hball],
  have hzU : {(z : ℤ_[p])} * (metric.ball (0 : ℤ_[p]) ((p : ℝ)^-n)) = metric.ball (0 : ℤ_[p])
    ((p : ℝ)^((min 1 (-n)) - (z : ℤ_[p]).valuation)) := padic_int.mul_open_ball hz (-n),
  use -((min 1 (-n)) - (z : ℤ_[p]).valuation),
  rw [hzU, neg_neg],
end

private lemma Z_p.mul_left (p : primes) (z : ℤ_[p]) {U : set ℤ_[p]} (hU : U ∈ (B_Z_p p)) : (∃ (V : set ℤ_[p]) (H : V ∈ (B_Z_p p)), V ⊆ (λ (x : ℤ_[p]), z * x) ⁻¹' U)
:= 
begin
    lift z.valuation to ℕ using z.valuation_nonneg with m hm,
    cases hU with nU hU,
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rw [set.mem_preimage, mem_ball_zero_iff, padic_int.norm_mul, ← one_mul ((p : ℝ)^-(nU : ℤ))],
    exact mul_lt_mul' z.norm_le_one (mem_ball_zero_iff.mp hx) (norm_nonneg x) zero_lt_one,
end

instance ring_filter_basis_Z_p (p : primes) : ring_filter_basis ℤ_[p] := { sets := B_Z_p p,
  nonempty := by {use [metric.ball (0 : ℤ_[p]) (p^(-(0 : ℤ))), 0]},
  inter_sets := λ U V ⟨nU, hU⟩ ⟨nV, hV⟩, begin
    let nmax := max nU nV,
    use [metric.ball (0 : ℤ_[p]) (p^(-(nmax : ℤ))), nmax],
    have hp : 1 < (p : ℝ) := one_lt_real_prime p,
    rw set.subset_inter_iff,
    split,
    { rw hU,
      apply metric.ball_subset_ball,
      rw [fpow_le_iff_le hp, neg_le_neg_iff],
      exact le_max_left _ _},
    { rw hV,
      apply metric.ball_subset_ball,
      rw [fpow_le_iff_le hp, neg_le_neg_iff],
      exact le_max_right _ _},
  end,
  zero' := λ U ⟨nU, hU⟩, begin
    rw hU,
    exact metric.mem_ball_self (nat.fpow_pos_of_pos (nat.prime.pos p.2) _),
  end,
  add' := λ U ⟨nU, hU⟩, begin
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rw set.mem_add at hx,
    rcases hx with ⟨y, z, hy, hz, hadd⟩,
    rw [mem_ball_zero_iff, ← hadd],
    exact lt_of_le_of_lt (padic_int.nonarchimedean _ _) (max_lt (mem_ball_zero_iff.mp hy) (mem_ball_zero_iff.mp hz)),
  end,
  neg' := λ U ⟨nU, hU⟩, begin
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rw [set.neg_preimage, set.mem_neg, mem_ball_zero_iff, norm_neg],
    exact mem_ball_zero_iff.mp hx,
  end,
  conj' := λ z U ⟨nU, hU⟩, begin
    use [U, nU, hU],
    simp_rw [← sub_eq_add_neg, add_sub_cancel', set.preimage_id'],
  end,
  mul' := λ U ⟨nU', hU'⟩, begin
    by_cases hn : 0 ≤ nU',
    { use [U, nU', hU'],
      lift nU' to ℕ using hn with nU hU,
      rw hU',
      intros x hx,
      rcases hx with ⟨y, z, hy, hz, hmul⟩,
      rw [mem_ball_zero_iff] at hy hz ⊢,
      rw [← hmul, padic_int.norm_mul _ _],
      have hp : 1 < (p : ℝ) := one_lt_real_prime p,
      have hp' : 0 < (p : ℝ) := real_prime_pos p,
      by_cases hz_zero : z = 0,
      { rw [hz_zero, norm_zero, mul_zero],
        exact fpow_pos_of_pos hp' _},
      have h := mul_lt_mul hy (le_of_lt hz) (norm_pos_iff.mpr hz_zero)
        (fpow_nonneg (le_of_lt hp') _),
      have h1 : (p : ℝ)^-(nU : ℤ) * (p : ℝ)^-(nU : ℤ) ≤ (p : ℝ)^-(nU : ℤ),
      { rw [← fpow_add (ne_of_gt hp'), fpow_le_iff_le hp,  add_neg_le_iff_le_add', add_right_neg,
          right.neg_nonpos_iff],
        exact int.coe_nat_nonneg nU },
      rw hU at h1,
      exact lt_of_lt_of_le h h1 },
    { use [metric.ball (0 : ℤ_[p]) ((p : ℝ)^-(0 : ℤ)), 0],
      rw hU',
      intros x hx,
      rcases hx with ⟨y, z, hy, hz, hmul⟩,
      rw [mem_ball_zero_iff, neg_zero, gpow_zero] at hy hz,
      have hp : 1 * 1 < (p : ℝ)^-nU',
      { rw [mul_one, ← gpow_zero (p : ℝ), fpow_lt_iff_lt (one_lt_real_prime p), right.neg_pos_iff],
        exact not_le.mp hn,},
      rw [mem_ball_zero_iff, ← hmul, padic_int.norm_mul],
      exact lt_trans (mul_lt_mul'' hy hz (norm_nonneg _) (norm_nonneg _)) hp },
  end,
  mul_left' := Z_p.mul_left p,
  mul_right' := by { simp_rw mul_comm, exact Z_p.mul_left p }}

instance ring_filter_basis_pi_Z_p : ring_filter_basis pi_Z_p := 
pi.ring_filter_basis (λ  p : primes, ring_filter_basis_Z_p p)

lemma open_mul_pi_Z_p (m ∈ M) (U : set pi_Z_p) : U ∈ ring_filter_basis_pi_Z_p.sets →
  {(m : pi_Z_p)}*U ∈ ring_filter_basis_pi_Z_p.sets :=
begin
  obtain ⟨ z, hz_ne_zero, hzm⟩ := int_M ⟨m, H⟩,
  rw set_like.coe_mk at hzm,
  set F_factors := set.finite.to_finset (finite_factors z hz_ne_zero)with hF_factors,
  rintro ⟨S, F, hrestr, hSF⟩,
  set T : Π p : primes, set (ℤ_[p]) := λ p, if p ∈ F then {m p}*(S p)
    else {m p}*(metric.ball (0 : ℤ_[p]) ((p : ℝ)^-(-1 : ℤ))) with hT,
  use [T, F ∪ F_factors],
  have hz : ∀ p : primes, (z : ℤ_[p]) ≠ 0 := by { intro p, exact int.cast_ne_zero.mpr hz_ne_zero },
  have hm_p :  ∀ p : primes, (m p : ℚ_[p]) ≠ 0,
  { intro p,
    rw [← hzm, inj_pnat],
    dsimp only,
    rw padic_int.cast_ne_zero,
    exact (hz p) },
  split,
  { intros p hpF_union,
    rw [hT, ← hzm, inj_pnat],
    by_cases hpF : p ∈ F,
    { dsimp only,
      rw if_pos hpF,   
      convert open_mul_Z_p (S p) (hrestr p hpF) (hz p),
      simp_rw [set.singleton_mul], },
    { dsimp only,
      use (z : ℤ_[p]).valuation - 1,
      rw [if_neg hpF, padic_int.mul_open_ball (hz p) _, neg_neg, min_eq_right (le_refl (1 : ℤ)),
        neg_sub] }},
  rw hSF, 
  ext x,
  rw [set.singleton_mul, set.mem_image, set.mem_pi],
  split,
  { intro hx,
    rcases hx with ⟨y, hy, hyx⟩,
    intros p hpF,
    rw [← hyx, hT, pi.mul_apply],
    dsimp only,
    by_cases hpF : p ∈ F,
    { rw if_pos hpF,
      use [m p, y p, set.mem_singleton (m p), hy p hpF] },
    { rw if_neg hpF,
      use [m p, y p, set.mem_singleton (m p)],
      split,
      { rw [neg_neg, ← padic_int.univ_open_ball 1 (zero_lt_one)],
      exact set.mem_univ (y p), },
      { refl }}},
  { intro hx,
    rw hT at hx,
    dsimp only at hx,
    have h_int_F : ∀ (p : primes), p ∈ F → ∃ (y_p : ℤ_[p]), y_p ∈ (S p) ∧ (x p : ℚ_[p])/(m p) = y_p,
    { intros p hpF,
      have hx_p := hx p (finset.mem_union_left F_factors hpF),
      rw if_pos (finset.mem_coe.mp hpF) at hx_p,
      choose mp y_p hy_p using hx_p,
      rcases hy_p with ⟨hmp, hyS, hzy⟩,
      rw set.mem_singleton_iff at hmp,
      rw hmp at hzy,
      use [y_p, hyS],
      rw [div_eq_iff (hm_p p), ← hzy, mul_comm, padic_int.coe_mul] },
    have h_int : ∀ (p : primes), ∥(x p : ℚ_[p])/(m p)∥ ≤ 1,
    { intro p,
      by_cases hpF_union : p ∈ F ∪ F_factors,
      { by_cases hpF : p ∈ F,
        { rcases (h_int_F p hpF) with ⟨yp, -, hyp⟩,
          rw hyp,
          exact padic_int.norm_le_one yp },
        { have hx_p := hx p hpF_union,
          rw [if_neg hpF, neg_neg, padic_int.mul_open_ball (padic_int.cast_ne_zero.mp (hm_p p)) 1,
            mem_ball_zero_iff, min_eq_right (refl (1 : ℤ))] at hx_p,
          rw [normed_field.norm_div, div_le_iff (norm_pos_iff.mpr (hm_p p)),
            padic.norm_eq_pow_val (hm_p p),  one_mul, padic.norm_le_pow_iff_norm_lt_pow_add_one _ _,
            padic_int.padic_norm_e_of_padic_int (x p), ← coe_coe, ← sub_eq_neg_add,
            padic_int.coe_valuation (m p)],
          exact hx_p }},
      { have hm_norm : ∥(m p : ℚ_[p])∥ = 1,
        { have hpF_factors: ¬ p ∈ F_factors,
          { intro hpF_factors,
            exact hpF_union (finset.mem_union_right F hpF_factors),
          },
          rw [hF_factors, set.finite.mem_to_finset, set.mem_set_of_eq, subtype.val_eq_coe,
            ← padic_int.norm_int_lt_one_iff_dvd] at hpF_factors,
          rw [← hzm, inj_pnat],
          dsimp only,
          rw padic_int.padic_norm_e_of_padic_int _,
          have h_norm_le_one := padic_int.norm_le_one (z : ℤ_[p]),
          rw le_iff_lt_or_eq at h_norm_le_one,
          cases h_norm_le_one with h_norm_lt h_norm_one,
          { exfalso, exact hpF_factors h_norm_lt },
          { exact h_norm_one }},
        rw [normed_field.norm_div, div_le_iff (norm_pos_iff.mpr (hm_p p)),  hm_norm,
          padic_int.padic_norm_e_of_padic_int (x p), mul_one],
        exact padic_int.norm_le_one (x p), }},
    set y : pi_Z_p := λ p, ⟨((x p : ℚ_[p])/(m p)), h_int p ⟩ with hy,
    use y,
    split, 
    { rw set.mem_pi,
      intros p hpF,
      rcases (h_int_F p hpF) with ⟨zp, hzS, hyz⟩,
      rw hy, dsimp only, simp_rw hyz, rw subtype.coe_eta,
      exact hzS,
      },
    { ext p,
      rw [pi.mul_apply, hy],
      dsimp only, 
      rw [padic_int.coe_mul, subtype.coe_mk,
      ← mul_div_assoc, mul_comm,  mul_div_assoc, div_self, mul_one],
      { rw [← hzm, inj_pnat], dsimp only, 
      rw [padic_int.coe_coe_int, int.cast_ne_zero],
      exact hz_ne_zero }}},
end

instance ring_filter_basis_A_Q_f : ring_filter_basis A_Q_f := 
localization.ring_filter_basis pi_Z_p M A_Q_f ring_filter_basis_pi_Z_p (open_mul_pi_Z_p)

