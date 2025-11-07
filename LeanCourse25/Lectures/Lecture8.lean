import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic

import Mathlib

open Real
noncomputable section
variable (a b c : ℝ)

/- # Last time

- structures can bundle data and properties together
- several ways to define an instance of a structure:
    - `{ ... }` and specify all fields `def myPoint := { x := 1, y := 2, z := 3 : Point }`
    - `where` notation
    ```
    def myPoint : Point where
      x := 1
      y := 2
      z := 3
    ```
    - use an explicit constructor:
      `def myPoint : Point := ⟨1, 2, 3⟩` or `def myPoint := Point.mk 1 2 3`
- namespaces (`open Point` to shorten all names in the `Point` namespace)
- projection notation: `p.add q` for `Point.add p q`
- avoid duplication using `extends`

- important structures: `Equiv` (bijective functions together with its inverse), abelian groups
- `class`es allow creating a database of "instances of this class", so Lean can tell e.g. that
  `G × G'` is an abelian group if `G` and `G'` are

-/



/- # A note on universes

Lean has a hierarchy of universes. -/

#check ℝ
#check Type 0
#check Type 1
#check Type 2

/- You can also work in a variable universe. -/

universe u v
#check Type u
#check Type (v + 3)
-- #check Type (3 + max 1 2)
#check Type (max u v)
#check fun (α : Type u) (β : Type v) ↦ α → β
-- #check Type (u + v) -- the operations on universes are very limited.

/-
* `Type*` means `Type u` for a *variable* `u`
* `Type _` means an arbitary universe (variable or not)

In Mathlib, when introducing a new type `α`,
we generally write `(α : Type*)` to be as general as possible.
-/

#check Type*
#check Type _


example : Type (u + 3) = Type _ := by rfl
-- example : Type (u + 3) = Type* := by rfl -- error

/-
* `Prop` is a bottom universe below `Type`.
* `Sort` is used to write "`Prop` or `Type`"
-/

#check Prop
#check Sort 0
#check Sort 1
#check Sort 2
#check Sort (u + 1)
#check Sort*

example : Sort (u +1) = Type u := by rfl
example : Type = Type 0 := by rfl
example : Sort 0 = Prop := by rfl
example : Sort = Sort 0 := by rfl
-- example : Sort* = Sort* := by rfl -- error; two different universe levels


/- ## A note on coercions

You can specify *coercions* to say that an element of one type
can be silently coerced to an element of another type.
We've already seen the coercions
`ℕ → ℤ → ℚ → ℝ → ℂ`
for numbers.
-/

#check fun n : ℕ ↦ (n : ℚ)

abbrev PosReal : Type := {x : ℝ // x > 0}

instance : Coe PosReal Real := ⟨fun x ↦ x.val⟩

-- errors without the type ascription: no subtraction implemented on PosReal, but can coerce to ℝ
def diff (x y : PosReal) : ℝ := x - y

/- coercions can be composed. -/
#check fun (x : PosReal) ↦ (x : ℂ)




/-
* We use `CoeSort` to coerce to `Type _` (or `Sort _`)
* We use `CoeFun` to coerce to functions.
-/


structure PointedType where
  carrier : Type*
  pt : carrier

instance : CoeSort PointedType Type* := ⟨fun α ↦ α.carrier⟩

structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

variable {X Y : PointedType}

infix:50 " →.. " => PointedFunction

-- You can also define this instance, but this is not as useful:
instance {X Y : PointedType} : Coe (X →.. Y) (X → Y) := ⟨fun e ↦ e.toFun⟩
-- This example errors: to apply x to f, Lean would need to coerce f to a function:
--example (f : X →.. Y) (x : X) : Y := f x

instance {X Y : PointedType} : CoeFun (X →.. Y) (fun _ ↦ X → Y) := ⟨fun e ↦ e.toFun⟩
-- Whereas now it works.
example (f : X →.. Y) (x : X) : Y := f x

-- This tells the pretty printer to print the operation with `↑`.
attribute [coe] PointedFunction.toFun

namespace PointedFunction

variable {X Y Z : PointedType}

@[simp] lemma coe_pt (f : X →.. Y) : f X.pt = Y.pt := f.toFun_pt

def comp (g : Y →.. Z) (f : X →.. Y) : X →.. Z where
  toFun := g ∘ f
  toFun_pt := by simp

end PointedFunction

-- Playing with namespaces a bit
namespace PointedFunction

namespace Bar

def foo : ℕ := 1

end PointedFunction.Bar

namespace PointedFunction

def ar : ℕ := 37

end PointedFunction


/- ## A note on subtypes

As mentioned on Tuesday, you can define subtypes of a given type.
-/

#check {x : ℝ // 2 ≤ x }

/- You can also treat a set `s` as the subtype `{x // x ∈ s}`.
This operation is a coercion. -/
section
variable (s : Set ℝ)
#check (s : Type)

example (s : Set ℝ) (x : s) : (x : ℝ) ∈ s := x.2
end

/- However, subtypes are often not that convenient to work with,
and generally it's easier to reformulate a statement without using subtypes. -/

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by
  intro x y hxy
  simp
  gcongr
  · apply (f x).property
  · apply hf
    assumption
  done

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : Set.range f ⊆ {x | x > 0}) (h2f : Monotone f) :
    Monotone (log ∘ f) := by
  intro x y hxy
  simp
  gcongr
  · apply hf
    exact Set.mem_range_self x
  · apply h2f hxy
  done

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by
  intro x y hxy
  simp
  apply hf
  -- rw does not work nicely because of subtypes!
  refine Subtype.mk_le_mk.mpr ?_
  apply exp_le_exp_of_le hxy

  -- rw [exp_le_exp_of_le]
  --show_term gcongr
  done


/- Define a function on the whole type, but
only specify that a function is well-behaved
on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by
  intro x y hxy
  apply hf
  · refine Set.mem_setOf.mpr ?_
    positivity
  · rw [Set.mem_setOf]; positivity
  gcongr
  done

/- In Lean, many functions are defined using "junk values" outside their
domain. -/
#check Real.log

#eval 5 / 0
variable (x y : ℝ)
#check x / y



/- # Additive vs Multiplicative classes. -/

/- In Mathlib, there are two notions of abelian groups,
one written using `(*, 1, ⁻¹)` and one using `(+, 0, -)`. -/

#check CommGroup
#check AddCommGroup


/- To explain this distinction, consider monoids
(sets/types with a binary operation and a unit for the operation).
`(ℝ, +, 0)` and `(ℝ, *, 1)` are both monoids,
and we want to have a distinction in notation and
lemma names of these two structures. -/

#check Monoid
#check AddMonoid

example : CommMonoid ℝ := by infer_instance
example : AddCommMonoid ℝ := by infer_instance
example (x : ℝ) : x + 0 = x := add_zero x
example (x : ℝ) : x * 1 = x := mul_one x

/- In Mathlib there is a `@[to_additive]` command
that automatically translates a lemma written
multiplicatively to a lemma written additively. -/

-- Here's one example.

/-- Fancy documentation for my lemma -/
@[to_additive bar /-- Even fancier documentation, additive -/]
lemma Group.foo {G : Type*} [Group G] {g : G} : g * 1 = g := by
  exact mul_one g



/-! # Equivalence relations -/

#check Eq

/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the trivial equivalence relation on the integers. -/
def myEquivalenceRelation : Setoid ℤ where
  r k l := k = l
  iseqv := {
    refl k := by simp
    symm h := by symm; exact h --exact h.symm
    trans := by
      intro k l m hkl hlm
      --rw [hkl, hlm]
      linarith
    }


/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (k l : ℤ) :
  letI := myEquivalenceRelation; k ≈ l ↔ k = l := by rfl

/-
Let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/
def quotient_equiv_subtype :
    Quotient (myEquivalenceRelation) ≃ ℤ where
  toFun := by
    apply Quotient.lift (id (α := ℤ))
    intro k l h
    simp at h
    simp [h]
  invFun := fun k ↦ Quotient.mk _ k
  left_inv := by
    apply Quotient.ind
    intro k
    simp
  right_inv := by sorry

/- END OF LECTURE -/

/-- Let's define the equivalence relation for the even numbers: two numbers are equivalent
iff their difference is an even number. -/
def evensEquivalenceRelation : Setoid ℤ where
  r k l := ∃ n, k - l = 2 * n
  iseqv := sorry
