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


/-- Let's define the equivalence relation for the even numbers: two numbers are equivalent
iff their difference is an even number. -/

def evensEquivalenceRelation : Setoid ℤ :=
{ r := fun a b => Even (a - b),
  iseqv :=
  ⟨
    -- Reflexive
    by
      intro a
      show Even (a - a)
      rw [sub_self]
      use 0
      simp,

    -- Symmetric
    by
      intro a b h
      -- h : Even (a - b)
      rcases h with ⟨k, hk⟩
      -- hk : a - b = 2 * k
      show Even (b - a)
      -- note: b - a = -(a - b)
      rw [← neg_sub]
      rw [hk]
      -- b - a = -(2 * k) = 2 * (-k)
      use -k
      ring,

    -- Transitive
    by
      intro a b c hab hbc
      rcases hab with ⟨k₁, hk₁⟩
      rcases hbc with ⟨k₂, hk₂⟩
      show Even (a - c)
      use k₁ + k₂
      calc
        a - c = (a - b) + (b - c) := by ring
        _     = k₁ + k₁ + (k₂ +k₂)  := by rw [hk₁, hk₂]
        _     = k₁ + k₂ + (k₁ + k₂)    := by ring
  ⟩ }





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

theorem normal_axiom_of_choice {ι α : Type*} {s : ι → Set α} (h : ∀ i, (s i).Nonempty) :
    Nonempty {f : ι → α | ∀ i, f i ∈ s i} := by
  sorry
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
  sorry
  done




lemma leftInv_of_surjective (hf : Injective f) : inverse f ∘ f = id := by
  sorry
  done




/- We can package this together in one statement. -/
lemma inv_of_bijective (hf : Bijective f) :
    ∃ g : β → α, f ∘ g = id ∧ g ∘ f = id := by
  sorry
  done




end Inverse
