import data.nat.prime
import linear_algebra.tensor_product
import number_theory.padics

noncomputable theory

open nat 
instance (p : primes) : fact (nat.prime p) := ⟨p.2⟩

variables (p:primes) 

def R := (Π (p: primes), ℤ_[p])

instance : comm_ring R := pi.comm_ring
instance : ring R := infer_instance

--def A_Q_f := tensor_product ℤ ℚ (Π (p: primes), ℤ_[p])
def A_Q_f := tensor_product ℤ ℚ R 

variables a : A_Q_f

#check a

instance : non_assoc_semiring A_Q_f := 
{ mul := _,
  left_distrib := _,
  right_distrib := _,
  zero_mul := _,
  mul_zero := _,
  one := _,
  one_mul := _,
  mul_one := _,
  ..tensor_product.add_comm_group }

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

def proj_p (p: primes) : A_Q_f → ℚ_[p] := 
tensor_product.lift 
  (linear_map.mk₂ ℤ ((λ (p: primes) (r : ℚ) (a: Π (q: primes), ℤ_[q]), (r*(a p) : ℚ_[p])) p)
    (λ m₁ m₂ n, by {simp, ring})
    (λ c m n, by {simp, ring}) 
    (λ m n₁ n₂, by {simp, ring})
    (λ c m n, by {simp, ring}))

def ring_hom_proj_p (p : primes) : ring_hom A_Q_f ℚ_[p] := { to_fun := proj_p p,
  map_one' := _,
  map_mul' := _,
  map_zero' := _,
  map_add' := _ }



