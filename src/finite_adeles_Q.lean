import data.nat.prime
import data.set.finite
import number_theory.padics
import number_theory.divisors
import topology.metric_space.basic

noncomputable theory
open nat

namespace fin_adeles

instance (p : primes) : fact (nat.prime p) := ⟨p.2⟩

structure A_Q_f : Type :=
(el : Π p : primes, ℚ_[p])
(fin_supp : set.finite({ p : primes | padic_norm_e (el p) > 1}))

lemma eq_constr (a: A_Q_f): {A_Q_f . el := a.el, fin_supp := a.fin_supp} = a := by {cases a, refl}

instance inhabited_pre : inhabited A_Q_f :=
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

section add_comm_group

def add : A_Q_f →  A_Q_f →  A_Q_f := begin
  intros a b,
  exact {el := (λ p :primes, (a.el p + b.el p)),
   fin_supp := begin
     let supp_sum := {p : primes | padic_norm_e (a.el p + b.el p) > 1},
     let supp_a := {p : primes | padic_norm_e (a.el p) > 1},
     let supp_b := {p : primes | padic_norm_e (b.el p) > 1},
     have h_subset: supp_sum ⊆ (supp_a ∪ supp_b), 
     {intros p hp,
      rw set.mem_set_of_eq at hp,
      by_contradiction hnot,
      rw ← set.set_of_or at hnot,
      rw set.nmem_set_of_eq at hnot,
      push_neg at hnot,
      cases hnot with ha hb,
      have h_le_max, exact padic_norm_e.nonarchimedean' (a.el p) (b.el p),
      rw le_max_iff at h_le_max,
      cases h_le_max; 
      linarith,
     },
     exact set.finite.subset (set.finite.union a.fin_supp b.fin_supp) h_subset,
   end},
end

instance : has_add A_Q_f := {add := fin_adeles.add}

theorem add_assoc (a b c : A_Q_f): a + b + c = a + (b + c) := begin
  unfold_projs,
  rw add,
  simp,
  exact add_assoc _ _ _,
end

theorem add_comm (a b : A_Q_f): a + b = b + a := 
begin
  unfold_projs,
  rw add,
  simp,
  exact add_comm _ _,
end

def zero : A_Q_f :=
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

instance : has_zero A_Q_f := {zero := fin_adeles.zero}

theorem zero_add (a : A_Q_f) : 0 + a = a := 
begin
  unfold_projs,
  rw zero,
  rw add,
  simp,
  exact eq_constr a,
end 

theorem add_zero (a : A_Q_f): a + 0 = a := begin
  rw add_comm,
  exact zero_add a,
end

def neg : A_Q_f →  A_Q_f := begin
  intro a,
  exact {el := (λ p :primes, -(a.el p)),
   fin_supp := begin
     have h: ∀ p: primes, padic_norm_e (-(a.el p)) = padic_norm_e (a.el p), {
       intro p,
       exact padic_norm_e.neg (a.el p),
      },
     have h_eq: {p : primes | padic_norm_e (-(a.el p)) > 1} = {p : primes | padic_norm_e (a.el p) > 1}, 
     {ext p,
     repeat {rw set.mem_set_of_eq},
     rwa (h p),
     },
     rw h_eq,
     exact  a.fin_supp,
   end},
end

instance : has_neg A_Q_f := {neg := fin_adeles.neg}

theorem add_left_neg (a : A_Q_f) : -a + a = 0 := begin
  unfold_projs,
  rw add,
  rw zero,
  simp,
  exact add_left_neg _,
end

end add_comm_group

section comm_ring

def mul : A_Q_f →  A_Q_f →  A_Q_f := begin
  intros a b,
  exact {el := (λ p :primes, (a.el p * b.el p)),
   fin_supp := begin
     let supp_sum := {p : primes | padic_norm_e (a.el p * b.el p) > 1},
     let supp_a := {p : primes | padic_norm_e (a.el p) > 1},
     let supp_b := {p : primes | padic_norm_e (b.el p) > 1},
     have h_subset: supp_sum ⊆ (supp_a ∪ supp_b), 
     {intros p hp,
      rw set.mem_set_of_eq at hp,
      rw padic_norm_e.mul' _ _  at hp,
      by_contradiction hnot,
      rw ← set.set_of_or at hnot,
      rw set.nmem_set_of_eq at hnot,
      push_neg at hnot,
      cases hnot with ha hb,
      have h_le: padic_norm_e (a.el p) * padic_norm_e (b.el p) ≤ 1 * 1 := mul_le_mul ha hb (padic_norm_e.nonneg (b.el p)) (by linarith),
      rw mul_one at h_le,
      linarith, 
     },
     exact set.finite.subset (set.finite.union a.fin_supp b.fin_supp) h_subset,
   end},
end

instance : has_mul A_Q_f := {mul := fin_adeles.mul}

theorem mul_assoc (a b c : A_Q_f) : a * b * c = a * (b * c):= begin
  unfold_projs,
  rw mul,
  simp,
  exact mul_assoc _ _ _,
end

theorem mul_comm (a b : A_Q_f) : a * b = b * a := begin
  unfold_projs,
  rw mul,
  simp,
  exact mul_comm _ _,
end

def one : A_Q_f :=
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

instance : has_one A_Q_f := {one := fin_adeles.one}

theorem one_mul (a : A_Q_f): 1 * a = a := begin
  unfold_projs,
  rw mul,
  rw one,
  simp,
  exact eq_constr a,
end

theorem mul_one (a : A_Q_f): a * 1 = a := begin
  rw mul_comm,
  exact one_mul a,
end

theorem left_distrib (a b c : A_Q_f):  a * (b + c) = a * b + a * c := begin
  unfold_projs,
  rw mul,
  rw add,
  simp,
  exact left_distrib _ _ _,
end

theorem right_distrib (a b c : A_Q_f) : (a + b) * c = a * c + b * c := begin
  repeat {rw mul_comm _ c},
  exact left_distrib _ _ _,
end

end comm_ring

/-

variable p: primes
instance (p : primes) : topological_ring ℚ_[p] := by apply_instance 

instance (p : primes) : pseudo_metric_space ℚ_[p] := by apply_instance

def Z_p_ball (p : primes) : set ℚ_[p] := (metric.ball (0 : ℚ_[p]) (1 : ℝ))

#check Z_p_ball p

lemma open_padic_integers {p:primes}: is_open (Z_p_ball p) :=  metric.is_open_ball


section topological_spacevariable (p: primes)

instance (p : primes): topological_ring ℚ_[p] := by apply_instance

def is_open : set A_Q_f → Prop := sorry

theorem is_open_univ : is_open set.univ := sorry

theorem is_open_inter (S T : set A_Q_f) : is_open S → is_open T → is_open (S ∩ T) := sorry

theorem is_open_sUnion (S : set (set A_Q_f)) : (∀ (T : set A_Q_f), T ∈ S → is_open T) → is_open (⋃₀S) := sorry

instance : topological_space A_Q_f := { 
  is_open := fin_adeles.is_open,
  is_open_univ := fin_adeles.is_open_univ,
  is_open_inter := fin_adeles.is_open_inter,
  is_open_sUnion := fin_adeles.is_open_sUnion }

instance : topological_ring A_Q_f := { 
  continuous_add := sorry,
  continuous_mul := sorry,
  continuous_neg := sorry} 


end topological_space -/

instance : add_comm_group A_Q_f := 
{ add := fin_adeles.add,
  add_assoc := fin_adeles.add_assoc,
  zero := fin_adeles.zero,
  zero_add := fin_adeles.zero_add,
  add_zero := fin_adeles.add_zero,
  neg := fin_adeles.neg,
  add_left_neg := fin_adeles.add_left_neg,
  add_comm := fin_adeles.add_comm
} 

instance : comm_ring A_Q_f  := 
{ mul := fin_adeles.mul,
  mul_assoc := fin_adeles.mul_assoc,
  one := fin_adeles.one,
  one_mul := fin_adeles.one_mul,
  mul_one := fin_adeles.mul_one,
  left_distrib := fin_adeles.left_distrib,
  right_distrib := fin_adeles.right_distrib,
  mul_comm := fin_adeles.mul_comm,
  ..(show add_comm_group A_Q_f, by apply_instance),
}

section Q_algebra

def map_Q_fin_adeles : ℚ → A_Q_f := (λ r, {A_Q_f . el := (λ p, (r: ℚ_[p])), fin_supp := begin
  let supp := {p : primes | padic_norm_e ↑r > 1},
  let im_supp  := (λ p: primes, p.val) '' supp,

  have h1 : im_supp ⊆ divisors r.denom,
  { intros p hp,
    rw ← finset.set_of_mem,
    rw set.mem_set_of_eq,
    rcases hp with ⟨p, hp, rfl⟩,
    rw set.mem_set_of_eq at hp,
    rcases hp with ⟨-, hp⟩,
    rw nat.mem_divisors,
    split,
    {simp,
     by_contradiction hr,
     have h := padic_norm_e.norm_rat_le_one hr,
     rw ← padic_norm_e.is_norm at h,
     rw ← rat.cast_one at h,
     rw rat.cast_le at h,
     exact hp h,
    },
    exact rat.denom_ne_zero r,
  },
  exact set.finite_of_finite_image (set.inj_on_of_injective (primes.coe_nat_inj) supp) (set.finite.subset (set.finite_mem_finset (divisors r.denom)) h1),
end
})

theorem map_one' : map_Q_fin_adeles 1 = 1 := begin
  unfold map_Q_fin_adeles,
  rw ← eq_constr 1,
  simp,
  refl,
end

theorem map_mul' (r s : ℚ) : map_Q_fin_adeles (r * s) = map_Q_fin_adeles r * map_Q_fin_adeles s := begin
  unfold map_Q_fin_adeles,
  unfold_projs,
  unfold mul,
  simp,
  ext p,
  exact padic.coe_mul p,
end

theorem map_zero' : map_Q_fin_adeles 0 = 0 := begin
  unfold map_Q_fin_adeles,
  rw ← eq_constr 0,
  simp,
  refl,
end

theorem map_add' (r s : ℚ) : map_Q_fin_adeles (r + s) = map_Q_fin_adeles r + map_Q_fin_adeles s := begin
  unfold map_Q_fin_adeles,
  unfold_projs,
  unfold add,
  simp,
  ext p,
  exact padic.coe_add p,
end

def smul : ℚ → A_Q_f → A_Q_f := λ (r : ℚ) (a: A_Q_f), mul (map_Q_fin_adeles r) a

instance : has_scalar ℚ A_Q_f := {smul := fin_adeles.smul}

theorem smul_def' (r : ℚ) (a : A_Q_f) : r • a = map_Q_fin_adeles r * a := begin
  unfold_projs,
  unfold smul,
end

theorem fin_adeles.commutes' (r : ℚ) (a : A_Q_f):  map_Q_fin_adeles r * a = a * map_Q_fin_adeles r := mul_comm _ _

def hom_Q_fin_adeles : ring_hom ℚ A_Q_f := { to_fun := fin_adeles.map_Q_fin_adeles,
  map_one' := fin_adeles.map_one',
  map_mul' := fin_adeles.map_mul',
  map_zero' := fin_adeles.map_zero',
  map_add' := fin_adeles.map_add' }

instance : algebra ℚ A_Q_f := { smul := fin_adeles.smul,
  to_fun := fin_adeles.map_Q_fin_adeles,
  commutes' := fin_adeles.commutes',
  smul_def' := fin_adeles.smul_def',
  ..hom_Q_fin_adeles }

end Q_algebra

end fin_adeles

namespace adeles
open fin_adeles

def A_Q := A_Q_f × ℝ
instance : semiring A_Q := prod.semiring
instance : algebra ℚ A_Q := algebra.prod.algebra ℚ A_Q_f ℝ 

open algebra

def finite_adele_ring (K : Type)[field K][algebra ℚ K] := tensor_product ℚ K A_Q_f

def adele_ring (K : Type)[field K][algebra ℚ K] := tensor_product ℚ K A_Q

end adeles
