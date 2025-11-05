import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic

/-
--- IGNORE THIS ---
(a small bug was introduced in Mathlib that prints rational numbers weirdly
when running `#eval`. We override the pretty printer here.)
-/
open Lean in
instance (priority := high) : ToExpr Rat where
  toTypeExpr := .const ``Rat []
  toExpr q :=
    let lit r := mkApp3 (.const ``OfNat.ofNat [levelZero]) (.const ``Rat [])
      (mkRawNatLit r) (.app (.const ``Rat.instOfNat []) (mkRawNatLit r))
    let numAbs := lit q.num.natAbs
    let num :=
      if q.num ≥ 0 then numAbs else
        mkApp3 (.const ``Neg.neg [levelZero]) (.const ``Rat []) (.const ``Rat.instNeg []) numAbs
    if q.den = 1 then num else
      let den := lit q.den
      mkApp6 (.const ``HDiv.hDiv [levelZero, levelZero, levelZero])
        (.const ``Rat []) (.const ``Rat []) (.const ``Rat [])
        (mkApp2 (.const ``instHDiv [levelZero]) (.const ``Rat []) (.const ``Rat.instDiv []))
        num den




noncomputable section


/- # Last time

Last time we saw:

* More on orders: `gcongr` and `grw`
* The tactic cheatsheet
* Sets:
  - `Set α` is the type of sets with elements from `α`
  - Common notation can be used: `x ∈ s`, `s ⊆ t`, `s ∪ t`, `∅`, ...
  - Prove two sets equal by using the `ext` tactic.
  - We can use the notation `{x : α | P x}` for the set of elements satisfying `P`.
  - Unions/intersections: `⋃ i : ι, C i`, `⋃ i ∈ s, C i` or `⋃₀ C`;
-/

/- Answering a question: "how to subtract `x` from both sides of an equation? -/
-- #loogle _ - _ = _ - _ ↔ _ -- do this on the website to find `sub_left_inj`
example (x y z : ℝ) : y = z := by
  rw [← sub_left_inj (a := x)]
  sorry
  done

/- # Today: Sets (continued), numbers -/

/- We can take images and preimages of sets.

`f ⁻¹' s` is the preimage of `s` under `f`.
`f '' s` is the image of `s` under `f`.

On paper, you would write `f(A)` or `f[A]` for the image
and `f⁻¹(B)` or `f⁻¹[B]` for the preimage.
This notation is hard to parse for Lean, since parentheses and ⁻¹
have so many different meanings in mathematics.
Therefore we use this funny notation.
-/

variable {α β ι : Type*} (x : α) (s t u : Set α) (a b c : ℝ)
open Set

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl

example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl


example {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  constructor
  · intro h x hx
    simp
    rw [subset_def] at h
    apply h
    exact mem_image_of_mem f hx
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst y
    rw [subset_def] at h
    simp at h
    exact h x hx
  done


/- We can do pointwise operations on sets (e.g. the Minkowski sum). -/

open Pointwise

example (s t : Set ℝ) :
    s + t = {x : ℝ | ∃ a ∈ s, ∃ b ∈ t, a + b = x } := by rfl

example (s : Set ℝ) : -s = {x : ℝ | -x ∈ s } := by rfl


/- We can write `{a, b, c, ...}` to write enumerated sets. -/

example : ({1, 3, 4} : Set ℝ) + {0, 3} = {1, 3, 4, 6, 7} := by
  ext x
  simp [mem_add]
  norm_num
  tauto

  done



/- ## Intervals -/

/-
Lean has the following names for intervals:
("c" = closed, "o" = open, "i" = infinity)
Icc a b = [a, b]
Ico a b = [a, b)
Ioc a b = (a, b]
Ioo a b = (a, b)
Ici a   = [a, ∞)
Ioi a   = (a, ∞)
Iic b   = (-∞, b]
Iio b   = (-∞, b)
-/

example : Icc a b = {x | a ≤ x ∧ x ≤ b} := by rfl
example : Ico a b = {x | a ≤ x ∧ x < b} := by rfl
example : Ioc a b = {x | a < x ∧ x ≤ b} := by rfl
example : Ioo a b = {x | a < x ∧ x < b} := by rfl
example : Ici a   = {x | a ≤ x}         := by rfl
example : Ioi a   = {x | a < x}         := by rfl
example : Iic b   = {x | x ≤ b}         := by rfl
example : Iio b   = {x | x < b}         := by rfl

example : Icc a b ∩ Ici c = Icc (max a c) b := by
  ext x
  simp
  tauto
  done



/- # Numbers -/

/-
Some useful tactics when dealing with numbers:
* `norm_num`: compute equalities and inequalities involving numerals
* `cutsat`: can do linear arithmetic on `ℕ` and `ℤ`.
* `positivity`: can show that something is positive/non-negative
  by using that its components are positive/non-negative.
* `field_simp` can simplify divisions.
-/

example : (2 : ℂ) ^ 3 + 17 = 300 / 12 := by norm_num

example (x : ℝ) : x + 5 + 3 = x + 8 := by
  rw [add_assoc]
  norm_num
  -- ring
  done

example (n m : ℤ) : 2 * n + 1 ≠ 2 * m := by cutsat

example (n m k : ℝ) (hn : 0 < n) (hm : 0 ≤ m) (hk : 0 < k) :
    0 < n * m + k  := by positivity

example (x y : ℝ) (hy : y ≠ 0) :
    2 * x / y + 1 + x * y = (2 * x + y) / y + y * x := by
  field_simp




/- **Warning**
Division and subtraction of natural numbers
again returns a natural number.
This is division rounded down and truncated subtraction.
-/

#eval 12 / 3
#eval 13 / 3
#eval 14 / 3
#eval 15 / 3
#eval (14 : ℚ) / 3
#eval (14 / 3 : ℚ)
#eval 7 - 6
#eval 7 - 7
#eval 7 - 8



/- ## Coercions
When using subtraction and division, it is better to
do the calculation in the rationals or reals.

We write the type ascription `(<expression> : ℚ)` to tell Lean
that the expression should be interpreted as a rational number.

If you give a natural number expression, and tell Lean that it
should be a rational number, Lean will automatically
insert *coercions*, or canonical inclusions, in the expression.
In the infoview (right half of your screen),
these coercions are denoted with `↑`.

Coercions are used widely, between many types.
-/

#eval (12 : ℚ) / 15
#eval (7 : ℤ) - 8

variable (n : ℕ) (x : ℝ)
#check (n : ℚ)
#check (n + 1 : ℚ)
#check ((n - 3) / 2 : ℝ)

#check x + n
#check x + (n : ℝ)
#check n + x


/- If you want precise control where the coercion is inserted,
you can use `↑` or a double type ascription.
However, just writing `↑` without any type information often doesn't
give Lean enough information to know what you mean. -/

#check (↑(n + 1) : ℚ)
#check ((n + 1 : ℕ) : ℚ)
#check ((n + 1 : ℤ) : ℚ)

#check ↑(n + 1)




/-
Some tactics that are useful when working with coercions:
* `norm_cast`: pull coercions out of an expression.
  E.g. turn `↑n * ↑m + ↑k` into `↑(n * m + k)`
* `push_cast`: push coercions into an expression.
  E.g. turn `↑(n * m + k)` into `↑n * ↑m + ↑k`

Note: Sometimes you need additional hypotheses to pull/push casts
out of/into `-` or `/`, since `↑n - ↑m = ↑(n - m)` and
`↑n / ↑m = ↑(n / m)` are not always true.
(assuming `n` and `m` are natural numbers, and you coerce to e.g. the rationals)
-/

example (n : ℕ) : ((n + 1 : ℤ) : ℚ) = n + 1 := by norm_cast

example (n m : ℕ) (h : m ∣ n) : (↑(n / m) : ℚ) = ↑n / ↑m := by norm_cast

example (n m : ℕ) (h : (n : ℚ) + 1 ≤ m) : (n : ℝ) + 1 ≤ m := by
  norm_cast
  norm_cast at h
  done

example (n m : ℕ) (h : n = m * m + 2) : (n : ℝ) - 3 = (m + 1) * (m - 1) := by
  rw [h]
  push_cast
  ring
  done


/- # Recursion and induction

Let's start by defining our own factorial function.
Note that there is no `:=` -/

def fac : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fac n



lemma fac_zero : fac 0 = 1 := by rfl

lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rfl
lemma fac_succ' (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by simp [fac]

example : fac 4 = 24 := by rfl

#eval fac 100




/- Lean checks that every function is *terminating*. If it isn't,
you have to mark it `partial` and cannot use it in proofs. -/
partial def wrong : ℕ → ℕ
  | n => 1 + wrong (n + 1)


/- ## Induction -/

/- Let's prove that the factorial function we just defined
is always positive. -/

lemma fac_pos (n : ℕ) : 0 < fac n := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    -- simp [fac, ih]
    unfold fac
    positivity
  done





/- Next we define the Fibonacci numbers.
We mark it with `@[simp]`: this is an *attribute* that tells
the `simp` tactic to simplify its definition whenever it can.
-/

@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by
  simp
  done



lemma fib_add (m n : ℕ) : fib (m + n + 1) =
    fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
  calc
    fib (m + (n + 1) + 1) = fib ((m + 1) + n + 1) := by congr 1; ring
    _ = fib (m + 1) * fib n + fib (m + 1 + 1) * fib (n + 1) := by rw [ih]
    _ = fib m * fib (n + 1) + fib (m + 1) * fib (n + 1 + 1) := by simp; ring
  done

/-
Note: in the above proof, if we use `induction n` then our
induction hypothesis is "for this specific `m`, we have
`fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)`".

If we use `induction n generalizing m` then our
induction hypothesis is "for all `m`, we have
`fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)`".
-/



open Finset

/- We can use `∑ i ∈ range n, f i` to take the sum `f 0 + f 1 + ⋯ + f (n - 1)`. -/

#eval ∑ i ∈ range 11, i ^ 2

example (f : ℕ → ℝ) : ∑ i ∈ range 0, f i = 0 :=
  sum_range_zero f

example (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range (n + 1), f i = (∑ i ∈ range n, f i) + f n :=
  sum_range_succ f n

/-
Here `range n` or `Finset.range n` is the set `{0, ..., n - 1}`.
Its type is `Finset ℕ`, which is a finite set of natural numbers
(We will talk more about finite sets in a later lecture.)
-/

#check Finset.range





/- We will prove the basic equality: `1 + ⋯ + n = n(n+1)/2`.

Note that we prove the following after coercing to rational numbers.
We could also prove it in `ℕ` (with natural number division),
but it is more annoying to work with natural number division. -/

example (n : ℕ) : ∑ i ∈ range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    field_simp
    norm_cast
  done




/- We can use other induction principles with
`induction ... using ... with`.
There are multiple other induction principles we can use.
-/

/- Prove something by induction with two base cases. -/
#check Nat.twoStepInduction

/- Prove something by strong induction: prove it for `n`
assuming it holds for all numbers below `n`. -/
#check Nat.strongRec

/- Induction with a different starting point:
prove something for all `n ≥ m` by proving it for `m`
and proving it for `k + 1` if it holds for `k`. -/
#check Nat.le_induction


lemma fac_dvd_fac (n m : ℕ) (h : n ≤ m) : fac n ∣ fac m := by
  induction m, h using Nat.le_induction with
  | base => sorry
  | succ m hmn ih => sorry
  done



/-
Here are two exercises for you to practice with induction.
-/

example (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hfs : ∀ n, f (n + 1) = 2 * f n + 1) :
    ∀ n, f n + 1 = 2 ^ n := by
  sorry
  done


/-
Let's prove an explicit formula for the Fibonacci sequence.
We will define the golden ratio, and prove 3 simple properties for you.
These lemmas are marked `@[simp]`, so that `simp` automatically uses them.
-/

open Real

def ϕ : ℝ := (1 + sqrt 5) / 2
def ψ : ℝ := (1 - sqrt 5) / 2

@[simp] lemma ϕ_sub_ψ_ne_zero : ϕ - ψ ≠ 0 := by
  simp [ϕ, ψ, sub_eq_zero, div_left_inj',
    sub_eq_add_neg (1 : ℝ), CharZero.eq_neg_self_iff]

@[simp] lemma ϕ_sq : ϕ ^ 2 = ϕ + 1 := by
  simp [ϕ, add_sq, div_pow]; ring

@[simp] lemma ψ_sq : ψ ^ 2 = ψ + 1 := by
  simp [ψ, sub_sq, div_pow]; ring


lemma coe_fib_eq (n : ℕ) : (fib n : ℝ) = (ϕ ^ n - ψ ^ n) / (ϕ - ψ) := by
  sorry
  done
