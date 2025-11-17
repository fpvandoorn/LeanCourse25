import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Function Finset
variable (a b c : ℝ)
set_option linter.unusedVariables false






/- ## Last time

- introduction of project 1
- git: the version management system used for Lean projects
- The axiom of choice in Lean
-/

#check Classical.choose
#check Classical.choose_spec





/-
One remark on the axiom of choice:
The `obtain` tactic doesn't use the axiom of choice.
The type theory of Lean itself (without the axiom of choice)
only allows you to destruct the proof of an existential quantifier
when you're proving a proposition, not when you're constructing data
(an element of type that is not a proposition).
-/
example {α : Sort*} {p : α → Prop} (h : ∃ x, p x) : α := by
  -- obtain ⟨x, hx⟩ := h -- this gives an error
  exact Classical.choose h


example {α : Sort*} {p : α → Prop} (h : ∃ x, p x) : 1 ≤ 2 := by
  obtain ⟨x, hx⟩ := h -- this works fine
  exact one_le_two







/-
## Comments on notation and namespaces
-/

/-
We saw that opening a namespaces shortens names in that namespace.
It also enables notation specific to that namespace.

Note: `open Real in` just means that
we're opening the `Real` namespace just for the following command.
-/

section
open Real
variable (x y : ℝ)

#check π

#check Real.pi

#check pi

#check x + y

end

variable (x : ℝ) in
#check x + x

#check x + y

#check π

/-
`protected` means that a name doesn't get shortened
even if you open the namespace.

`scoped` means that a notation is only available when you open
a namespace.

`section` limits the scope of commands like `open`, `variable` or
`local notation`
-/


/- You can declare your own notation with the `notation` keyword. -/

namespace Real

scoped notation "φ" => (1 + √5) / 2

end Real

open Real

lemma φ_sq : φ ^ 2 = φ + 1 := by
  simp [add_sq, div_pow]; ring





/- You can also define infix, prefix and postfix notation
the `:65` specifies the *precedence* of the notation.
Multiplication has higher precedence (70) than addition (65).
-/

section CustomNotation

#check 1 + 1

local infix:65 " +' " => Nat.add
#eval 3 +' (5 * 2)
#eval (3 +' 5) * 2
#eval 3 +' 5 * 2
#eval 3 +' 5 * 2 = 13 -- equality has a precedence of 50




/- You can declare notation with multiple meanings.
In this case the notation will be overloaded.
You can also override notation by setting a priority, e.g.
`(priority := high)`
It chooses which notation to use, depending on the type of
the given arguments.
-/
#check ℤ ⊕ ℕ

local infix:65 " ⊕ " => Nat.add
-- local infix:65 " ⊕ " => Nat.mul
#check 2 ⊕ 3 * 3
#check ℤ ⊕ ℕ

#check (-3 : ℤ)
#check 5 - 3


/- Most notation in Lean has only one meaning,
but that meaning can be type-dependent.

For example `+` stands (roughly) for `Add.add`, which is the
addition function for any type that has a specified addition on it. -/

#check Add.add
#check 2 + 3
#check HAdd.hAdd

#check Add
end CustomNotation


/-
If you want to define more complicated notations,
look at how a similar notation is already defined.
-/
variable {s : ℕ → Set ℝ}
variable {t : ℕ → ℕ → Set ℝ}
#check ⋃ j, s j
#check ⋃ i : ℕ, ⋃ j : ℕ, t i j

/- some notation takes more than 2 arguments. -/
#check _ →ₗ[_] _













/-
## Finiteness

We saw `Finset` briefly when discussing the `∑`-notation.

A `Finset` is a finite set where Lean can exactly
compute what elements it contains.
-/

#check ({1, 2, 3} : Finset ℕ)

#eval ∑ i ∈ {1, 2, 3}, i ^ 2

#check ({j ∈ {1, 2, 3, 4} | Even j} : Finset ℕ)
#eval ({j ∈ {1, 2, 3, 4} | Even j} : Finset ℕ)


-- #check ({j ∈ {1} | RiemannHypothesis } : Finset ℕ)



/-
The reason that `Even j` does work is because Lean knows that
`Even` is "decidable": there is an algorithm to decide
whether a number is even or not.
-/
#check Decidable

#synth DecidablePred (Even : ℕ → Prop)


-- #synth Decidable RiemannHypothesis


/-
If you open the `Classical` namespace, then you can treat
any finite set as a `Finset`.

With the `Classical` namespace open, Lean treats every
predicate as "decidable"
-/

open Classical in
noncomputable def riemannHypothesisSet : Finset ℕ :=
  {j ∈ {1} | RiemannHypothesis }

-- open Classical in
-- #eval ∑ i ∈ riemannHypothesisSet, i

open Classical in
#synth Decidable RiemannHypothesis






/- We have the usual operations on `Finset`, similar to `Set`. -/

section Nat

variable (s t : Finset ℕ)

#check s ∩ t
#check s ∪ t
#check s \ t
#check (∅ : Finset ℕ)

#eval ({1, 2, 3, 3} ∪ {2, 1 + 2, 4} : Finset ℕ)

example {a b c : Finset ℕ} : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x
  simp
  tauto
  done


end Nat

/-
If we work in an arbitrary type, to do operations on `Finset`,
we need to to be able to decide/compute whether two elements are equal.

For example, it's not easy to decide whether `riemannHypothesisSet` equals `{1}`
-/

section DecidableEq

variable {α : Type*} (s t : Finset α)
variable [DecidableEq α]
-- open Classical

#check s ∪ t

end DecidableEq





/-
`insert a s` means inserting one new element to a `Finset`
(that also works for `Set`).
`{0, 1, 2}` is just notation for using `insert` a few times.
-/

example (s : Finset ℕ) (a : ℕ) : insert a s = {a} ∪ s := by rfl


set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)

#check ({0, 1, 2} : Finset ℕ)




/- You can take the maximum of a Finset by using `Finset.max'`,
but we have to prove that the finite set is non-empty.

Alternatively, we can use `Finset.max`, but that returns an element of `WithBot α` -/

#check Finset.min'

example : Finset.min' {0, 5, 10} (by decide) = 0 := by decide
#eval Finset.min' {0, 5, 10} (by decide)

#check Finset.min

example : Finset.min (range 10) = 0 := by decide
example : Finset.min (∅ : Finset ℕ) = ⊤ := by decide




/-
We can prove something for all finite sets by using
the following induction principle.
-/

#check Finset.induction


example {α : Type*} [DecidableEq α] (f : α → ℕ)
    (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    simp [ha]
    constructor
    · apply h
      exact?
    · apply ih
      intros x hx
      apply h
      exact?
  done




/- We can write `#s` for the cardinality of a Finset. -/

#check Finset.card

example {α : Type*} (s : Finset α) : #s = ∑ i ∈ s, 1 := by
  simp




/-
We can also say that a type is finite, using `Fintype`.

The prototypical finite type with `n` elements is `Fin n`.

A `Fintype` has a finset `Finset.univ` that contains all its elements.

We can use `Infinite` to say that a type is infinite.
-/


example : Fintype.card (Fin 5) = 5 := by simp

example {α : Type*} [Fintype α] (x : α) : x ∈ Finset.univ := mem_univ x

example : Infinite ℕ := by exact?






/-
We write `s.image f` for the image of the Finset `s`
under the function `f`.
Let's do a simple computation with cardinalities.
-/

example (m n : ℕ) (h : n ≤ m) :
    #(range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  sorry
  done



/-
Let's do a computation using a double counting argument:
If `G` is a bipartite graph with independent sets `s` and `t`.
Suppose that the degree of all vertices in `s` is at least 3,
and the degree of all vertices in `t` at most 1.

Then `3 * #s ≤ #t`.
-/


open Classical in
example {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #s ≤ #t := by
  calc
    3 * #s = 3 * ∑ i ∈ s, 1 := by simp
    _ = ∑ i ∈ s, 3 := by exact mul_sum s (fun i ↦ 1) 3
    _ ≤ ∑ i ∈ s, #{j ∈ t | r i j} := by gcongr with i hi; exact h_left i hi
    _ = ∑ i ∈ s, ∑ j ∈ t, if r i j then 1 else 0 := by simp
    _ = ∑ j ∈ t, ∑ i ∈ s, if r i j then 1 else 0 := by exact sum_comm
    _ = ∑ j ∈ t, #{i ∈ s | r i j} := by simp
    _ ≤ ∑ j ∈ t, 1 := by gcongr with j hj; exact h_right j hj
    _ = #t := by simp


/- END OF LECTURE -/






/-
## Inductive types

Lean's rules allow us to define *inductive types*.
An inductive type is a type where you (recursively) specify all elements.

For example, the following is a declaration of (a copy of) the natural numbers.
every element is either `zero` or `succ` of an (already constructed) natural number.
-/

inductive NaturalNumber where
  | zero : NaturalNumber
  | succ (n : NaturalNumber) : NaturalNumber

#check NaturalNumber.zero

open NaturalNumber
#check succ (succ (succ zero))



/-
Similarly, a list of elements from `α` is inductively defined by saying that:
- the empty list is a list
- if you have a list `l` and an element `x` in `α`,
  then adding `x` in front of `l` gives a new list.
-/

inductive MyList (α : Type*) where
  | nil : MyList α
  | cons : α → MyList α → MyList α



/- We'll use the `List` that Lean already knows,
since it comes with nice notation. -/
#check ([] : List ℕ)
#check List.cons 5 (List.cons 3 List.nil)
#check 5 :: 3 :: []
#check [1, 2, 3, 4]




/- Inductive types allow you to define new operations on it
by *pattern matching*.

This defines a new function that is defined by the given equations. -/



@[simp]
def appendLists {α : Type*} : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: appendLists as bs

infix:60 " +' " => appendLists

example {α : Type*} (as : List α) : [] +' as = as := rfl

example {α : Type*} (a : α) (as bs : List α) :
    (a :: as) +' bs = a :: (as +' bs) := by rfl



def myAdd : NaturalNumber → NaturalNumber → NaturalNumber
  | zero,   m => m
  | succ n, m => succ (myAdd n m)



/- We can prove properties about inductive types using `induction`. -/

example {α : Type*} (as bs cs : List α) :
    (as +' bs) +' cs = as +' (bs +' cs) := by
  sorry
  done

example {α : Type*} (as : List α) :
    as +' [] = as := by
  sorry
  done
