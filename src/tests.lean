import adeles
import topological_ring

noncomputable theory
open nat 

-- Ring filter basis for ℤ_[p] satisfying h

instance m_p {p : primes} : metric_space ℤ_[p] := infer_instance
instance t_p {p : primes} : topological_space ℤ_[p] := infer_instance

def B_Z_p (p : primes) := { U : set ℤ_[p] | ∃ n : ℕ,  U = metric.ball (0 : ℤ_[p]) (p^(-(n : ℤ)))}
  
lemma open_mul_Z_p {p : primes} (U : set ℤ_[p]) (hU : U ∈ B_Z_p p) (z : ℤ) (hne_zero : z ≠ 0) : 
(λ (x : ℤ_[p]), ↑z*x) '' U ∈ B_Z_p p := 
begin
  cases hU with n hball,
  lift (padic_int.valuation z) to ℕ using (padic_int.valuation_nonneg (z : ℤ_[p])) with m hm,
  have hp_ne_zero : (p : ℝ) ≠ 0,
  { rw [coe_coe, nat.cast_ne_zero],
    exact nat.prime.ne_zero p.2},
  have hne_zero' : (z : ℤ_[p]) ≠ 0 := int.cast_ne_zero.mpr (hne_zero),
  have hpos : 0 < (p : ℝ)^-(m : ℤ),
  { rw lt_iff_le_and_ne,
  split,
  { apply fpow_nonneg,  
    rw [coe_coe, ← cast_zero, nat.cast_le],
    exact le_of_lt (nat.prime.pos p.2)},
  { exact ne.symm (fpow_ne_zero _ hp_ne_zero)}},

  have hz_pos : 0 < ∥(z : ℚ_[p])∥,
  { rw [← padic_int.coe_coe_int, padic_int.padic_norm_e_of_padic_int,lt_iff_le_and_ne],
    split,
    { exact norm_nonneg (z : ℤ_[p])},
    { intro h,
      exact hne_zero' (norm_eq_zero_iff'.mp (eq.symm h))},
  },

  use (m + n),
  rw hball,
  ext x,
  split; rw set.mem_image,
  { rintro ⟨y, hyball, hxy⟩,
    rw [metric.mem_ball, dist_eq_norm, sub_zero] at hyball ⊢,
    rw [← hxy, padic_int.norm_mul, padic_int.norm_eq_pow_val hne_zero', ← hm, ← coe_coe, 
      int.coe_nat_add, neg_add (m : ℤ) n, fpow_add hp_ne_zero],
    exact mul_lt_mul'(le_of_eq (refl _)) hyball (norm_nonneg y) hpos },
    { intro hx,
      rw [metric.mem_ball, dist_eq_norm, sub_zero] at hx,
      set y := (x/z : ℚ_[p]) with hy,
      have hy_int : ∥y∥ ≤ 1,
      { rw [hy, normed_field.norm_div],
        by_cases hx_zero : (x : ℚ_[p]) = 0,
        { rw [hx_zero, norm_zero, zero_div], exact zero_le_one },
        
        rw [div_le_iff hz_pos, one_mul],
        apply le_trans (le_of_lt hx),
        rw [← padic_int.coe_coe_int, padic_int.padic_norm_e_of_padic_int, 
          padic_int.norm_eq_pow_val hne_zero', ← coe_coe, fpow_le_iff_le],
        { rw [← hm, int.coe_nat_add, neg_add, add_neg_le_iff_le_add', le_add_neg_iff_add_le, 
            add_left_neg],
          exact int.coe_nat_nonneg n },
        { rw [coe_coe, one_lt_cast], 
          exact prime.one_lt p.2 }},
      use ⟨y, hy_int⟩,
      split,
      { rw [metric.mem_ball, dist_eq_norm, sub_zero, padic_int.norm_eq_padic_norm, hy, 
          normed_field.norm_div, padic_int.padic_norm_e_of_padic_int, ← padic_int.coe_coe_int, 
          div_lt_iff,padic_int.padic_norm_e_of_padic_int],
        { rw [padic_int.norm_eq_pow_val hne_zero', ← hm, ← coe_coe, ← fpow_add hp_ne_zero, 
            ← neg_add, add_comm, ← int.coe_nat_add m n],
          exact hx },
        rw padic_int.coe_coe_int,
        exact hz_pos },
      have : (z : ℚ_[p]) ≠ 0 := int.cast_ne_zero.mpr (hne_zero),
      rw [← padic_int.cast_inj, padic_int.coe_mul,padic_int.coe_coe_int, subtype.coe_mk _ _,
      hy, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self this, mul_one] },
end

private lemma one_lt_real_prime (p : primes) : 1 < (p : ℝ) :=
by { rw [coe_coe, one_lt_cast], exact nat.prime.one_lt p.2}
private lemma real_prime_pos (p : primes) : 0 < (p : ℝ) :=
lt_trans zero_lt_one (one_lt_real_prime p)

instance ring_filter_basis_Z_p {p : primes} : ring_filter_basis ℤ_[p] := { sets := B_Z_p p,
  nonempty := by {use [metric.ball (0 : ℤ_[p]) (p^(-(0 : ℤ))), 0], refl},
  inter_sets := λ U V ⟨nU, hU⟩ ⟨nV, hV⟩, begin
    let nmax := max nU nV,
    use [metric.ball (0 : ℤ_[p]) (p^(-(nmax : ℤ))), nmax],
    have hp : 1 < (p : ℝ) := one_lt_real_prime p,
    rw set.subset_inter_iff,
    split,
    { rw hU,
      apply metric.ball_subset_ball,
      rw [fpow_le_iff_le hp, neg_le_neg_iff,int.coe_nat_le],
      exact le_max_left _ _},
    { rw hV,
      apply metric.ball_subset_ball,
      rw [fpow_le_iff_le hp, neg_le_neg_iff,int.coe_nat_le],
      exact le_max_right _ _},
  end,
  zero := λ U ⟨nU, hU⟩, begin
    rw hU,
    exact metric.mem_ball_self (nat.fpow_pos_of_pos (nat.prime.pos p.2) _),
  end,
  add := λ U ⟨nU, hU⟩, begin
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rw set.mem_add at hx,
    rcases hx with ⟨y, z, hy, hz, hadd⟩,
    rw [mem_ball_0_iff] at hy hz ⊢,
    rw ← hadd,
    exact lt_of_le_of_lt (padic_int.nonarchimedean _ _) (max_lt hy hz),
  end,
  neg := λ U ⟨nU, hU⟩, begin
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rw [set.neg_preimage, set.mem_neg, mem_ball_0_iff, norm_neg],
    exact mem_ball_0_iff.mp hx,
  end,
  conj := λ z U ⟨nU, hU⟩, begin
    use [U, nU, hU],
    simp_rw [add_sub_cancel', set.preimage_id'],
  end,
  mul := λ U ⟨nU, hU⟩, begin
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rcases hx with ⟨y, z, hy, hz, hmul⟩,
    rw [mem_ball_0_iff] at hy hz ⊢,
    rw [← hmul, padic_int.norm_mul _ _],
    have hp : 1 < (p : ℝ) := one_lt_real_prime p,
    have hp' : 0 < (p : ℝ) := real_prime_pos p,
    by_cases hz_zero : z = 0,
    { rw [hz_zero, norm_zero, mul_zero],
      exact fpow_pos_of_pos hp' _},
    have h := mul_lt_mul hy (le_of_lt hz) (norm_pos_iff.mpr hz_zero) (fpow_nonneg (le_of_lt hp') _),
    have h1 : (p : ℝ)^-(nU : ℤ) * (p : ℝ)^-(nU : ℤ) ≤ (p : ℝ)^-(nU : ℤ),
    { rw [← fpow_add (ne_of_gt hp'), fpow_le_iff_le hp,  add_neg_le_iff_le_add', add_right_neg, right.neg_nonpos_iff],
      exact int.coe_nat_nonneg nU,
    },
    exact lt_of_lt_of_le h h1,
  end,
  mul_left := λ z U ⟨nU, hU⟩, begin
    lift z.valuation to ℕ using z.valuation_nonneg with m hm,
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rw mem_ball_0_iff at hx,
    rw [set.mem_preimage, mem_ball_0_iff, padic_int.norm_mul, ← one_mul ((p : ℝ)^-(nU : ℤ))],
    exact mul_lt_mul' z.norm_le_one hx (norm_nonneg x) zero_lt_one,
  end,
  mul_right := λ z U ⟨nU, hU⟩, begin
    lift z.valuation to ℕ using z.valuation_nonneg with m hm,
    use [U, nU, hU],
    rw hU,
    intros x hx,
    rw mem_ball_0_iff at hx,
    rw [set.mem_preimage, mem_ball_0_iff, padic_int.norm_mul, mul_comm, ← one_mul ((p : ℝ)^-(nU : ℤ))],
    exact mul_lt_mul' z.norm_le_one hx (norm_nonneg x) zero_lt_one, -- TODO : rewrite using mul_left
  end,}

instance ring_filter_basis_pi_Z_p : ring_filter_basis pi_Z_p := pi.ring_filter_basis (λ p : primes, ring_filter_basis_Z_p)

/- lemma open_mul_pi_Z_p (m ∈ M) (U : set (Π p : primes, ℤ_[p])) : U ∈ ring_filter_basis_pi_Z_p.sets → {(m : pi_Z_p)}*U ∈ ring_filter_basis_pi_Z_p.sets := sorry

instance ring_filter_basis_A_Q_f : ring_filter_basis A_Q_f := localization.ring_filter_basis pi_Z_p M A_Q_f ring_filter_basis_pi_Z_p (open_mul_pi_Z_p) -/

