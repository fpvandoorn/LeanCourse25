import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.ComputeDegree

import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

open Function Set Ideal Polynomial
noncomputable section

/- ## Last time: group theory

- monoids and groups,
- group homomorphisms and isomorphisms,
- subgroups and normal subgroups,
- quotient groups,

-/

-- Let's go over the last section in a bit more detail.
-- Recall the alternating group on some type `α`, consisting of all even permutations of `α`
#check alternatingGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

example [Nontrivial α] : (alternatingGroup α).index = 2 := alternatingGroup.index_eq_two

example : (alternatingGroup α).Normal := by exact alternatingGroup.normal

-- In fact, an index two subgroup is always normal.
example {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2) : H.Normal :=
  Subgroup.normal_of_index_eq_two hH

open Nat.factorial

-- The cardinality of the alternating group with `n` letters is n!/2 (assuming n ≥ 2).
example {n : ℕ} (hn : n ≥ 2) : Nat.card (alternatingGroup (Fin n)) = Nat.factorial n / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_fin n]

-- Note that `n!/2 * 2 = n!`: this is an instance of **Lagrange's theorem**:
-- for any finite group `G` and subgroup `H` of `G`, we have `|G| = |G/H| |H|`.
#check Subgroup.card_eq_card_quotient_mul_card_subgroup

-- For n ≥ 5, the alternating group in n letters is simple: it has no non-trivial normal subgroups.
#check IsSimpleGroup
#check Subgroup.isSimpleGroup_iff

example : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five


/- ## Practical comments

* the next homework assignment (due Thursday, November 27 at 10.00) again includes a project
  component: address any review feedback you got on your pull request to the formal conjectures
  repository

* avoid `import Mathlib`, i.e. loading all of mathlib: on computers with not *a lot* of memory,
  this can cause your computer to freeze (and loading to take a long time).
  (The next version of Lean already helps with this.)
  Instead, import just the files you need. Sorry for Tuesday's file being different.

* Project 2: work on your own formalisation project. See `Project2.md` in the `Projects` folder.

-/

/- ## Ring theory -/

/- # Rings -/

/- Lean uses `Ring` and `CommRing` for rings and commutative rings. -/
example : CommRing ℤ := by infer_instance

/- Also important are *semirings*, which are rings without postulating negation. -/
example : CommSemiring ℕ := by infer_instance

/- A field (German: Körper) is a nontrivial commutative ring with inverses. -/
example : Field ℚ := by infer_instance


/- Many classes only take a type as argument,
others are predicates that take another class as argument -/
#check Field
#check EuclideanDomain

#check IsDomain
#check IsField
#check UniqueFactorizationMonoid


/- In Mathlib, many lemmas about multiplication are stated in two ways:
* For Group-like structures
* For Ring-like structures (with an absorbing element 0).
-/

#check mul_div_cancel_right -- group-like
#check mul_div_cancel_right₀ -- ring-like


/- Use Loogle to find lemmas you want.

`MonoidWithZero` and `GroupWithZero` capture the
multiplicative structure of a ring or a field
-/

-- #loogle _ * _ < _ * _ ↔ _
#check mul_lt_mul_left
-- #loogle ?a * _ < ?a * _ ↔ _

#check MonoidWithZero
#check GroupWithZero





/- Note that the tactics for computation in a
`Ring` and `CommRing` is `noncomm_ring` resp. `ring`.-/
example {R : Type*} [CommRing R] (x y : R) :
    (x - y)^2 = x^2 - 2*x*y + y^2 := by ring

example {R : Type*} [Semiring R] (x y : R) :
    (x + y)^2 = x^2 + x*y + y*x + y^2 := by noncomm_ring

/- The binomial theorem.
The natural number `Nat.choose n m` is coerced to an element of `R`
using `Nat.cast`. -/
example {R : Type*} [CommRing R] (x y : R) (n : ℕ) : (x + y) ^ n =
    ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m := by
  exact add_pow x y n






/- We have a predicate `IsUnit` stating
whether an element of the ring is a unit. -/
example {R : Type*} [CommRing R] (x : R) :
    IsUnit x ↔ ∃ y, x * y = 1 := isUnit_iff_exists_inv


/- We can write `Rˣ` for the units of a ring
(i.e. the elements with a multiplicative inverse). -/
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {R : Type*} [Ring R] : Group Rˣ := by infer_instance




/- We write ring homomorphisms with `→+*`. -/
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y ∧ f (x * y) = f x * f y ∧
    f 1 = 1 ∧ f 0 = 0 :=
  ⟨f.map_add x y, f.map_mul x y, f.map_one, f.map_zero⟩

variable {R S : Type*} [Ring R] [Ring S] in
#check R →* S -- `Monoid` homomorphism

variable {R S : Type*} [Ring R] [Ring S] in
#check R →+ S -- `AddMonoid` homomorphism

variable {R S : Type*} [Ring R] [Ring S] in
#check R →+* S -- ring homomorphism, `RingHom`


/- A subring is a subset of `R`
that is an additive subgroup and multiplicative submonoid.

As subgroups, subrings are bundled as a set with closure properties.
They are only moderately useful, since we cannot quotient a ring by a subring. -/
example {R : Type*} [Ring R] (S : Subring R) : Ring S := by infer_instance



/- ## Ideals -/


section Ring
variable {R : Type*} [CommRing R] {I J : Ideal R}

/- Ideals are additive subgroups that are closed under arbitary multiplication. -/
example {x y : R} (hy : y ∈ I) : x * y ∈ I :=
  I.mul_mem_left x hy

example {x y : R} (hx : x ∈ I) : x * y ∈ I :=
  I.mul_mem_right y hx



/- There are various operations on ideals. -/
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ I ⊓ J := mul_le_inf

example : CompleteLattice (Ideal R) := by infer_instance
example : Semiring (Ideal R) := by infer_instance

#check (⊥ : Ideal R)
#check (⊤ : Ideal R)


/- We write `Ideal.span s` for the smallest ideal containing `s`.
In particular, `Ideal.span {a}` is the principal ideal generated by `a`. -/


/- Exercise: use Loogle to find relevant lemmas. -/
example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by
  rw [span_gcd, span_insert]
  -- or:
  --rw [← span_union {n} {m}, singleton_union, ← span_gcd n m]
  done
-- #loogle Ideal.span {_, _} fails, but searching on loogle online works

/- Exercise: use Loogle to find relevant lemmas. -/
example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by
  rw [Ideal.ext_iff]
  intro x
  rw [mem_inf]
  simp only [mem_span_singleton]
  exact lcm_dvd_iff.symm


example (n m : ℤ) : span {n} * span {m} = span {n * m} := by
  exact span_singleton_mul_span_singleton n m



/- We can quotient a ring by an ideal. -/

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

variable {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsPrime] in
#synth IsDomain (R ⧸ I)

example {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsMaximal] :
    Field (R ⧸ I) :=
  Quotient.field I



/- The Chinese remainder theorem can be stated
for ideals in a commutative ring. -/

example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (f : ι → Ideal R) (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) :
    (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i := by
  exact quotientInfRingEquivPiQuotient f hf

/- Note that we re-use the generic definition of `IsCoprime` here. -/
#print IsCoprime

/- From this we can easily get the traditional version for `ℤ/nℤ`. -/

example (n : ℕ) : Ring (ZMod n) := by infer_instance

example {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* ∀ i, ZMod (a i) :=
  by exact ZMod.prodEquivPi a ha



example {R : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] (I : Ideal R) :
    ∃ x : R, I = span {x} := by exact Submodule.IsPrincipal.principal I




/- # Algebras and polynomials -/

variable {A : Type*} [Semiring A] [Algebra R A]

/- An (associative unital) *algebra*  `A` over a ring `R`
is a semiring `A` equipped with a ring homomorphism `R →+* A`
whose image commutes with every element of `A`. -/
example : R →+* A := algebraMap R A

example (r : R) (a : A) :
    algebraMap R A r * a = a * algebraMap R A r :=
  Algebra.commutes r a

/- We can also denote `algebraMap R A r * a`
using scalar multiplication as `r • a`. -/
example (r : R) (a : A) : r • a = algebraMap R A r * a := Algebra.smul_def r a




/- An important algebra is the polynomial ring `R[X]` or `Polynomial R`.
We can write `X` or `Polynomial.X` for the polynoial variable. -/

example : Algebra R R[X] := by infer_instance

example {R : Type*} [CommRing R] : R[X] := X

-- R[X] is custom notation, and X a special element: this does not work (yet)
-- example {R : Type*} [CommRing R] : R[Y] := Y

example {R : Type*} [CommRing R] (r : R) : R[X] :=
  X - C r

/- `C` is registered as a ring homomorphism. -/
#check C

example {R : Type*} [CommRing R] (r : R) :
    (X + C r) * (X - C r) = X^2 - C (r ^ 2) := by
  ring_nf
  rw [C.map_pow]
  done



/- You can access coefficients using `Polynomial.coeff` -/

example {R : Type*} [CommRing R] (r : R) :
  (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X^2 + 2*X + C 3 : R[X]).coeff 1 = 2 := by simp

/- Defining the degree of a polynomial leads to a choice:
what is the degree of the `0` polynomial? -/
#check natDegree (R := R)
#check degree (R := R)
example : natDegree (R := R) 0 = 0 := rfl

/- `WithBot ℕ` can be seen as `ℕ ∪ {-∞}`, except that `-∞` is denoted `⊥`. -/
example : degree (R := R) 0 = ⊥ := rfl

example [IsDomain R] (p q : R[X]) :
    degree (p * q) = degree p + degree q := by
  exact degree_mul

example [IsDomain R] (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q := by
  exact natDegree_mul hp hq



/- `compute_degree!` and `monicity!` can automate some proofs. -/

example [Nontrivial R] (p : R) :
    degree (X ^ 3 + C p * X ^ 2 + 2 * X - 4) = 3 := by
  compute_degree!

example [IsDomain R] (p : R) :
    natDegree (X ^ 3 + C p * X ^ 2 + 2 * X - 4) = 3 := by
  compute_degree!

example [IsDomain R] (p : R) :
    Monic (X ^ 3 + C p * X ^ 2 + 2 * X - 4) := by
  monicity!




/- We can evaluate polynomials using `Polynomial.eval`. -/

#check eval (R := R)
example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := P.eval x

example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := eval x P

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

/- If `P : R[X]`, then we often want to evaluate `P` in algebras over `R`.
E.g. we want to say that `X ^ 2 - 2 : ℤ[X]` has a root in `ℝ` -/
#check aeval (R := R) (A := A)

example : ∃ (x : ℝ), aeval x (X ^ 2 - 2 : ℤ[X]) = 0 := by
  use √2
  simp [aeval]
  done



end Ring
