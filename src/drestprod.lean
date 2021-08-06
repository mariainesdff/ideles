import algebra.big_operators.basic

universes u v

--open_locale big_operators

variables (ι : Type u)  (β : ι → Type v) (α : ι → Type v)

namespace drestprod

-- What I would really want is to say that each (α i) is nonempty and contained in (β i)
variables [Π i, has_one (α i)] [Π i, has_one (β i)]
variables [Π i, has_lift_t (α i) (β i)]  
structure pre : Type (max u v) :=
(to_fun : Π i, β i)
(to_sub_fun : Π i, α i)
(pre_support : multiset ι)
(restricted : ∀ (i : ι), i ∈ pre_support ∨ (to_fun i) = ↑(to_sub_fun i))

instance inhabited_pre : inhabited (pre ι β α) :=
begin
  use λ i, ↑(1:α i),
  use λ i, 1,
  use ∅,
  intro i,
  right, 
  refl,
end

instance : setoid (pre ι β α) :=
{ r := λ x y, ∀ i, (x.to_fun i = y.to_fun i),
iseqv := begin
  unfold equivalence,
  split,
  { --show reflexive
    intros x i, exact refl _
   },
   split,
   {--show symmetric
    intros x y hxy i,
    rwa hxy i,
   },
   {--show transitive
   intros x y z hxy hyz i,
   exact trans (hxy i) (hyz i),
   }
end
}
end drestprod

variable {ι}

@[reducible]
def drestprod [Π i, has_one (β i)] [Π i, has_one (α i)][Π i, has_lift_t (α i) (β i)]  : Type* :=
quotient (drestprod.pre.setoid ι β α)