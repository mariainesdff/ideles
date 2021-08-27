import data.nat.prime
import linear_algebra.tensor_product
import number_theory.padics

noncomputable theory

open nat 
instance (p : primes) : fact (nat.prime p) := ⟨p.2⟩

variables (p:primes) 

def A_Q_f := tensor_product ℤ ℚ (Π (p: primes), ℤ_[p])

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

def f (p: primes) : ℚ → (Π (q: primes), ℤ_[q]) → ℚ_[p] := λ r a, r*(a p)

lemma l1 (m₁ m₂ : ℚ) (n : Π (q : primes), ℤ_[↑q]): f p (m₁ + m₂) n = f p m₁ n + f p m₂ n := 
by {unfold f, rw [padic.coe_add, add_mul]}

lemma l2 (c : ℤ) (m : ℚ) (n : Π (q : primes), ℤ_[↑q]) : f p(c • m) n = c • f p m n := 
by { unfold f, simp, ring}

lemma l3 (m : ℚ) (n₁ n₂ : Π (q : primes), ℤ_[↑q]): f p m (n₁ + n₂) = f p m n₁ + f p m n₂ := 
begin
  unfold f,
  change ↑m * ↑((n₁ p) + (n₂ p)) = ↑m * ↑(n₁ p) + ↑m * ↑(n₂ p),
  rw [padic_int.coe_add, mul_add],
end

def f_bilinear (p:primes) :=  
linear_map.mk₂ ℤ (f p)
  (λ m₁ m₂ n, by {unfold f, simp, ring})
  (λ c m n, by { unfold f, simp, ring}) 
  (λ m n₁ n₂, by { unfold f, simp, ring})
  (λ c m n, by { unfold f, simp, ring})

#check f_bilinear

 /-
def f_bilinear (p:primes) :=  
linear_map.mk₂ ℤ (f p) (λ m₁ m₂ n, by {unfold f, rw [padic.coe_add, add_mul]}) (H2 : ∀ (c : R) (m : M) (n : N), f (c • m) n = c • f m n) (λ m n₁ n₂, by {unfold f, change ↑m * ↑((n₁ p) + (n₂ p)) = ↑m * ↑(n₁ p) + ↑m * ↑(n₂ p), rw [padic_int.coe_add, mul_add]}) (H4 : ∀ (c : R) (m : M) (n : N), f m (c • n) = c • f m n)

def linear_map.mk₂ (R : Type u_1) [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [module R M] [module R N] [module R P] (f : M → N → P) (H1 : ∀ (m₁ m₂ : M) (n : N), f (m₁ + m₂) n = f m₁ n + f m₂ n) (H2 : ∀ (c : R) (m : M) (n : N), f (c • m) n = c • f m n) (H3 : ∀ (m : M) (n₁ n₂ : N), f m (n₁ + n₂) = f m n₁ + f m n₂) (H4 : ∀ (c : R) (m : M) (n : N), f m (c • n) = c • f m n) :
M →ₗ[R] N →ₗ[R] P-/


/-def map (p: primes) : A_Q_f → (tensor_product ℤ ℚ ℚ_[p]) := linear_map.ltensor ℚ (linear_prod p)
#check map p-/
