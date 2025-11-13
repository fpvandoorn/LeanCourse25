import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic

import Mathlib

open Real Function
noncomputable section
variable (a b c : ℝ)

/- # Last time

- Universes
- Coercions
- Subtypes
- Additive vs. multiplicative classes
- Equivalence relations
-/


/-- Let's define the equivalence relation for the even numbers:
two numbers are equivalent iff their difference is an even number. -/
-- Recall: Setoid is Lean's name for equivalence relation.
def evensEquivalenceRelation : Setoid ℤ where
  r k l := ∃ n : ℤ, k - l = 2 * n
  iseqv := {
    refl := by
      intro m
      use 0
      ring
    symm := by
      intro m k ⟨n, hn⟩
      use - n
      linarith
    trans := by
      intro m₁ m₂ m₃ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩
      use n₁ + n₂
      linarith
  }









/- # This time

* Project 1: contribute to Formal Conjectures. See `Project1.md` in the `Projects` folder

* How to use Git? See `Git.md` in the `Projects` folder.
-/










/-
## Axiom of Choice

If time left, we will discuss how to use the axiom of choice.
We will use it to define left/right inverses of a function.

Suppose we have a function `f : α → β`.
Can we find a inverse `g : β → α` of `f`?
Not without assuming that `f` is bijective...

But suppose we try, suppose that `∃ x, f x = y`, and we want to define `g y`.
It must be one of the `x` such that `f x = y`.
We can choose one such `x` using *the axiom of choice*.
-/

section Inverse

variable {α β : Type*} (f : α → β)

#check Classical.choose
#check Classical.choose_spec




/- This doesn't look like the axiom of choice,
since we're only choosing 1 element.
However, this is a *function* that takes a proof
of an existential and produces an element in `α` from it.
This is called *global choice* and it is a bit stronger
than the usual axiom of choice.
We can prove the usual axiom of choice from it.
-/

theorem normal_axiom_of_choice {ι α : Type*} {s : ι → Set α}
    (h : ∀ i, (s i).Nonempty) :
    Nonempty {f : ι → α | ∀ i, f i ∈ s i} := by
  let f i := Classical.choose (h i)
  use f
  intro i
  exact Classical.choose_spec (h i)
  done







/- When working with choice,
opening the namespace `Classical` is useful.
If Lean complains that is cannot synthesize `Decidable` or `DecidableEq`
then you should `open Classical`. -/
open Classical

def conditionalInverse (y : β) (h : ∃ x : α, f x = y) : α :=
  Classical.choose h

lemma invFun_spec (y : β) (h : ∃ x, f x = y) :
    f (conditionalInverse f y h) = y :=
  Classical.choose_spec h


/-
You can ask Lean whether a declaration depends on the axiom of choice.
The actual axiom of choice is stated a bit differently in Lean,
and `Classical.choose` is derived from that. -/

#print axioms conditionalInverse
#check Classical.choice
#print Nonempty

#check axiom_of_choice



/- We can now define the function by cases on whether it lies in the range of `f` or not. -/

variable [Inhabited α]
def inverse (f : α → β) (y : β) : α :=
  if h : ∃ x : α, f x = y then
    conditionalInverse f y h else
    default




/- We can now prove that `inverse f` is a right-inverse if `f` is surjective
and a left-inverse if `f` is injective.
We use the `ext` tactic to show that two functions are equal. -/




lemma rightInv_of_surjective (hf : Surjective f) : f ∘ inverse f = id := by
  ext y
  simp
  obtain ⟨x, rfl⟩ := hf y -- the `rfl` here performs `subst y`
  simp [inverse]
  rw [invFun_spec f]
  done




lemma leftInv_of_injective (hf : Injective f) : inverse f ∘ f = id := by
  ext x
  simp [inverse]
  apply hf
  rw [invFun_spec f]
  done




/- We can package this together in one statement. -/
lemma inv_of_bijective (hf : Bijective f) :
    ∃ g : β → α, f ∘ g = id ∧ g ∘ f = id := by
  use inverse f
  constructor
  · apply rightInv_of_surjective
    exact hf.2
  · apply leftInv_of_injective
    exact hf.1
  done




end Inverse
