import data.nat.prime
import data.set.finite
import number_theory.padics

open nat

namespace fin_ad

instance (p : primes) : fact (nat.prime p) := ⟨p.2⟩

structure A_Q_f : Type :=
(el : Π p : primes, ℚ_[p])
(fin_supp : set.finite({ p : primes | padic_norm_e (el p) > 1}))

noncomputable instance inhabited_pre : inhabited A_Q_f :=
begin
  use λ p, (1: ℚ_[p]),
  have h : {p : primes | padic_norm_e (1 : ℚ_[p]) > 1} = ∅, {
    rw set.eq_empty_iff_forall_not_mem,
    rintros p ⟨-, hp⟩,
    exact hp (le_of_eq padic_norm_e.one'),
  },
  rw h,
  exact set.finite_empty,
end

noncomputable def add : A_Q_f →  A_Q_f →  A_Q_f := begin
  intros x y,
  exact {el := (λ p :primes, (x.el p + y.el p)),
   fin_supp := begin
     let supp_sum := {p : primes | padic_norm_e (x.el p + y.el p) > 1},
     let supp_x := {p : primes | padic_norm_e (x.el p) > 1},
     let supp_y := {p : primes | padic_norm_e (y.el p) > 1},
     have h_subset: supp_sum ⊆ (supp_x ∪ supp_y), 
     {intros p hp,
      rw set.mem_set_of_eq at hp,
      by_contradiction hnot,
      rw ← set.set_of_or at hnot,
      rw set.nmem_set_of_eq at hnot,
      push_neg at hnot,
      cases hnot with hx hy,
      have h_le_max, exact padic_norm_e.nonarchimedean' (x.el p) (y.el p),
      rw le_max_iff at h_le_max,
      cases h_le_max; 
      linarith,
     },
     exact set.finite.subset (set.finite.union x.fin_supp y.fin_supp) h_subset,
   end},
end

noncomputable instance : has_add A_Q_f := {add := fin_ad.add}

lemma add_apply (a b : A_Q_f) (p : primes) :
  (a + b).el p = a.el p + b.el p := rfl

theorem add_assoc: ∀ (a b c : A_Q_f), a + b + c = a + (b + c) := begin
  intros a b c,
  unfold_projs,
  rw add,
  simp,
  exact add_assoc _ _ _,
end

noncomputable def zero : A_Q_f :=
{ el :=  λ p, (0: ℚ_[p]),
  fin_supp := 
begin
  have h : {p : primes | padic_norm_e (0 : ℚ_[p]) > 1} = ∅, {
    rw set.eq_empty_iff_forall_not_mem,
    rintros p ⟨-, hp⟩,
    rw padic_norm_e.zero at hp,
    linarith,
  },
  rw h,
  exact set.finite_empty,
end}

noncomputable instance : has_zero A_Q_f := {zero := fin_ad.zero}

variable a: A_Q_f


lemma problem (a: A_Q_f): {A_Q_f . el := a.el, fin_supp := a.fin_supp} = a := begin
  sorry,
end

theorem zero_add: ∀ (a : A_Q_f), 0 + a = a := 
begin
  intro a,
  unfold_projs,
  rw zero,
  rw add,
  simp,
  --change {A_Q_f . el := a.el, fin_supp := a.fin_supp} = a,
  sorry,
end 

theorem add_zero: ∀ (a : A_Q_f), a + 0 = a := begin
  intro a,
  unfold_projs,
  rw zero,
  rw add,
  simp,
  sorry,
end
-- next challenge : topological ring!
-- my suggestion:
-- (1) add_comm_group
-- (2) comm_ring
-- (3) topological_space
-- (4) topological_ring

-- {! !}

noncomputable def neg : A_Q_f →  A_Q_f := begin
  intro x,
  exact {el := (λ p :primes, -(x.el p)),
   fin_supp := begin
     have h: ∀ p: primes, padic_norm_e (-(x.el p)) = padic_norm_e (x.el p), {
       intro p,
       exact padic_norm_e.neg (x.el p),
      },
     have h_eq: {p : primes | padic_norm_e (-(x.el p)) > 1} = {p : primes | padic_norm_e (x.el p) > 1}, 
     {ext p,
     repeat {rw set.mem_set_of_eq},
     rwa (h p),
     },
     rw h_eq,
     exact  x.fin_supp,
   end},
end

noncomputable instance : has_neg A_Q_f := {neg := fin_ad.neg}

theorem add_left_neg : ∀ (a : A_Q_f), -a + a = 0 := begin
  intro a,
  unfold_projs,
  rw add,
  rw zero,
  simp,
  exact add_left_neg _,
end

theorem add_comm : ∀ (a b : A_Q_f), a + b = b + a := 
begin
  intros a b,
  unfold_projs,
  rw add,
  simp,
  exact add_comm _ _,
end

noncomputable def mul : A_Q_f →  A_Q_f →  A_Q_f := begin
  intros x y,
  exact {el := (λ p :primes, (x.el p * y.el p)),
   fin_supp := begin
     let supp_sum := {p : primes | padic_norm_e (x.el p * y.el p) > 1},
     let supp_x := {p : primes | padic_norm_e (x.el p) > 1},
     let supp_y := {p : primes | padic_norm_e (y.el p) > 1},
     have h_subset: supp_sum ⊆ (supp_x ∪ supp_y), 
     {intros p hp,
      rw set.mem_set_of_eq at hp,
      rw padic_norm_e.mul' _ _  at hp,
      by_contradiction hnot,
      rw ← set.set_of_or at hnot,
      rw set.nmem_set_of_eq at hnot,
      push_neg at hnot,
      cases hnot with hx hy,
      have h_le: padic_norm_e (x.el p) * padic_norm_e (y.el p) ≤ 1 * 1 := mul_le_mul hx hy (padic_norm_e.nonneg (y.el p)) (by linarith),
      rw mul_one at h_le,
      linarith, 
     },
     exact set.finite.subset (set.finite.union x.fin_supp y.fin_supp) h_subset,
   end},
end

noncomputable instance : has_mul A_Q_f := {mul := fin_ad.mul}

theorem mul_assoc : ∀ (a b c : A_Q_f), a * b * c= a * (b * c):= begin
  intros a b c,
  unfold_projs,
  rw mul,
  simp,
  exact mul_assoc _ _ _,
end

noncomputable def one : A_Q_f :=
{ el := λ p, (1: ℚ_[p]),
  fin_supp := begin
      have h : {p : primes | padic_norm_e (1 : ℚ_[p]) > 1} = ∅, {
        rw set.eq_empty_iff_forall_not_mem,
        rintros p ⟨-, hp⟩,
        exact hp (le_of_eq padic_norm_e.one'),
      },
      rw h,
      exact set.finite_empty,
    end
}

noncomputable instance : has_one A_Q_f := {one := fin_ad.one}

theorem one_mul: ∀ (a : A_Q_f), 1 * a = a := begin
  intro a,
  unfold_projs,
  rw mul,
  rw one,
  simp,
  sorry,
end

theorem mul_one: ∀ (a : A_Q_f), a * 1 = a := begin
  intro a,
  unfold_projs,
  rw mul,
  rw one,
  simp,
  sorry,
end

theorem mul_comm : ∀ (a b : A_Q_f), a * b = b * a := begin
  intros a b,
  unfold_projs,
  rw mul,
  simp,
  exact mul_comm _ _,
end

theorem left_distrib: ∀ (a b c : A_Q_f), a * (b + c) = a * b + a * c := begin
  intros a b c,
  unfold_projs,
  rw mul,
  rw add,
  simp,
  exact left_distrib _ _ _,
end

theorem right_distrib: ∀ (a b c : A_Q_f), (a + b) * c = a * c + b * c := begin
  intros a b c,
  unfold_projs,
  rw mul,
  rw add,
  simp,
  exact right_distrib _ _ _,
end

end fin_ad


open fin_ad

noncomputable instance : add_comm_group A_Q_f :=
{ add := fin_ad.add,
  add_assoc := fin_ad.add_assoc,
  zero := fin_ad.zero,
  zero_add := fin_ad.zero_add,
  add_zero := fin_ad.add_zero,
  neg := fin_ad.neg,
  add_left_neg := fin_ad.add_left_neg,
  add_comm := fin_ad.add_comm
}

noncomputable instance : comm_ring A_Q_f  := 
{ 
  mul := fin_ad.mul,
  mul_assoc := fin_ad.mul_assoc,
  one := fin_ad.one,
  one_mul := fin_ad.one_mul,
  mul_one := fin_ad.mul_one,
  left_distrib := fin_ad.left_distrib,
  right_distrib := fin_ad.right_distrib,
  mul_comm := fin_ad.mul_comm,
  
  -- TODO: figure out how not to repeat this
  add := fin_ad.add,
  add_assoc := fin_ad.add_assoc,
  zero := fin_ad.zero,
  zero_add := fin_ad.zero_add,
  add_zero := fin_ad.add_zero,
  neg := fin_ad.neg,
  add_left_neg := fin_ad.add_left_neg,
  add_comm := fin_ad.add_comm,
}