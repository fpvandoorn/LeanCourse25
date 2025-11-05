import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real
noncomputable section
variable (a b c : ℝ)




/-
# Practical remarks
* **New time/date for exercise classes**:
  - Tue 12-14 SR 0.006. Tutor: Hannah Scholz
  - Fri 8-10 SR 0.006. Tutor: Pablo Cageao Honduvilla
* First homework problems will be posted today on GitHub.
  No hand-in exercises this week.
* The lecture will be posted in advance of class,
  so you can open the file yourself during class.
* To get the latest version of this repository,
  follow the instructions in the README file.
-/







/- # Last Week -/

/- You type code on the left-hand side of the screen,
and Lean automatically compiles the file and
shows output in the *Lean Infoview* on the right.

If you ever close the Infoview, you can toggle it
under the `∀`-button at the top-right of your window. -/



/- Every expression in Lean has a type. -/

#check 1
#check (1 : ℝ)

#check fun x : ℝ ↦ x^2
#check fun n : ℤ ↦ n^2





/- We can write our own definitions. -/
def u : ℕ → ℚ := fun n ↦ 1 / (n + 1)




/-
The most basic protection against error is type checking:
mathematical objects must be combined according to their type.

`u` has type `ℕ → ℚ`, hence it expects natural numbers
as inputs, and produces real numbers as outputs.

Hence `u 1` is ok and has type `ℚ`.
-/

#check u 1 -- u(1), u_1
#check u (1 + 2)
#check (u 1) + 2
#check u 1 + 2
#check u (1)

#eval 1 + 2 * 3



#check (fun x : ℝ ↦ x^2) (π + 3)




/- You need a space between a function and its argument,
even when writing parentheses. -/
-- #check u(1)


/-
But `u π` is not ok, we say it doesn't type-check.
-/

-- #check u π
-- #check u u





/- The type `Prop` contains all statements

Unfortunate clash in terminology:
* In math: "Proposition" means
    useful proven statement (less important than a theorem)
* In logic: "Proposition" means
    any statement that can be either true or false.
-/


#check 2 + 2 = 4
#check 3 < π


#check 2 + 2 = 5









def Statement1 : Prop :=
  ∃ p, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement2 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement3 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2)




/- Nat.Prime is a predicate on natural numbers, so it has type `ℕ → Prop`. -/

#check (Nat.Prime)

def MyProposition : ℕ → Prop := fun n ↦ n > 10
def MyFunctionOnPropositions : Prop → Prop :=
  fun p ↦ ¬ p

open Nat
/- What is the type of the factorial function? -/
#check Nat.factorial
#check fun n ↦ n !



/- What is the type of the predicate
stating that a natural number is at least 2? -/
#check Nat.AtLeastTwo



/- What is the type of addition on the natural numbers? -/
#check fun (n : ℕ) (m : ℕ) ↦ n + m
#check fun n : ℕ ↦ (fun m : ℕ ↦ n + m)
-- this has type ℕ → (ℕ → ℕ), not ℕ × ℕ → ℕ



/- What is the type of `≤` on the integers? -/
#check fun n m : ℤ ↦ n ≤ m


#check True
#check trivial

#check False

-- #check propext

#check ℕ



/- If we have a statement `A : Prop`,
we can try to prove `A` using *tactics*.

The easiest tactic is **`rfl`**, which shows that an
equality holds where both sides are literally the same.

You can optionally append `done` at the end of a tactic script,
which only succeeds if you have finished the proof. -/


example (a b c : ℝ) : a * b + c = a * b + c := by
  rfl
  done


example : 2 + 2 = 4 := by rfl
example : (2 : ℝ) + (2 : ℝ) = (4 : ℝ) := by
  norm_num



/- A much more powerful tactic is the **`ring`** tactic,
which will prove anything that only requires the axioms of a ring.
So it can reason with `+`, `-`, `*`, and natural number exponents,
but not with other definitions. -/

lemma foo (a b : ℝ) : a * (a + b) = a^2 + a*b := by
  ring
  done

-- #print foo

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring
  done


example (a b c : ℝ) : (a * b) * c = a * (b * c) := by
  ring
  done



/- The **`rw`** tactic allows you to rewrite with equalities. -/

example (a b c d e : ℝ) (h : a = b + c) (h' : e = d - b) : a + e = d + c := by
  rw [h, h']
  ring
  done


/- You can use `rw ... at h` to do the rewrite steps in a hypothesis. -/

example (a b c d : ℝ) (h : a = b + c) (h' : b = 0) : a + d = d + c + b := by
  rw [h, h']
  ring
  done

example (a b c d : ℝ) (h : a = b + c) (h' : b = 0) : a + d = d + c + b := by
  rw [h'] at h ⊢
  rw [h]
  ring
  done

example (a b c d : ℝ) (h : a = b + c) (h' : b = 0) : a + d = d + c + b := by
  rw [h', add_zero (d + c), h, h', zero_add c,
    add_comm d c]
  done

example (a b c d : ℝ) (h : a = b + c) (h' : b = 0) : a + d = d + c + b := by
  rw [h', add_zero, h, h', zero_add, add_comm]
  done


/- Instead of `ring`, we can also rewrite with lemmas manually. -/

#check add_zero a
#check zero_add a
#check add_comm a b



/- ## Calculation layout using calc

If you write a sequence of rewrites, it is more natural and readable
to write your proofs as a calculation.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring



/-
Let's write a calc-proof from scratch.
-/

example (a b c : ℝ) (h : a = b + c) : a * a = a * b + a * c := by
  calc
    a * a = a * (b + c)   := by rw [h]
    _     = a * b + a * c := by ring







/-
**Exercise**: Now try to prove this with `calc`.
Also try it directly with `rw`.
-/

example (a b c : ℝ) (h : a = b - c) (h2 : b * b = 2 * c) :
    a * b = (2 - b) * c := by
  calc
      a * b = (b-c) * b := by rw [h]
      _     = b*b -c*b  := by ring
      _     = 2*c - c*b := by rw [h2]
      _     = (2 - b) * c := by ring

example (a b c : ℝ) (h : a = b - c) (h2 : b * b = 2 * c) :
  a * b = (2 - b) * c := by
  rw [h]        -- replace a with (b - c)
  rw [sub_mul]  -- simplify: (b - c) * b → b*b - c*b
  rw [h2]       -- replace b*b with 2*c
  ring_nf       -- simplify: 2*c - c*b → (2 - b)*c


/-
If you haven't installed Lean, click Navigate to
  https://live.lean-lang.org/
and copy the following lines into the editor: (without the backticks)
```
import Mathlib.Tactic

example (a b c : ℝ) (h : a = b - c) (h2 : b * b = 2 * c) :
    a * b = (2 - b) * c := by
  sorry
```
-/











/-
Now we will introduce the *logical connectives*
to do more interesting reasoning than just calculations.

We will start with **Implication**
-/

/-
**Forwards Reasoning** is reasoning forwards from the hypotheses that other facts must hold.
We can do this with the `have` tactic.
`intro` is used to introduce assumptions.
`exact` or `assumption` can be used to finish the proof.
-/

example (p q r : Prop) (hq : p → q) (hr : p → q → r) : p → r := by
  intro (h : p)
  have h2 : q := hq h
  have h3 : q → r := hr h
  have h4 : r := h3 h2
  exact h4
  done

/- We can also use `specialize` to apply a hypothesis to arguments. -/
example (p q : Prop) (a b c : ℝ) (hq : p → q) (hr : p → q → a = b) : p → a + c = b + c := by
  intro hp  
  specialize hq hp
  specialize hr hp hq
  rw [hr]
  done

example (p q : Prop) (a b c : ℝ) (hq : p → q) (hr : p → q → a = b) : p → a + c = b + c := by
  intro hp
  specialize hq hp
  -- specialize hr hp hq
  rw [hr hp hq]
  done




/-
**Backwards reasoning** is where we chain implications backwards,
deducing what we want to prove from a combination of other statements
(potentially even stronger ones).
We do this with the `apply` tactic.
-/

example (p q r s : Prop) (hq : p → s → q) (hr : q → r) : s → p → r := by
  intro hs hp
  apply hr
  apply hq
  · exact hp
  · assumption
  done





example (p q r s : Prop) (hq : (p → s) → q) (hr : q → r) : s → p → r := by
  intro hs hp
  apply hr
  apply hq
  intro h2p
  exact hs

/- We can also use `exact` or `refine` with more complicated proof terms. -/

example (p q r : Prop) (hq : p → p → q) (hr : q → r) : p → r := by
  intro hp
  refine hr ?_
  exact hq hp hp
  done



/-
# Difference between `rw` and `apply`
- `rw` can be used to rewrite a subexpression (almost) anywhere in the goal,
  `apply` has to match the outermost thing you are trying to prove.
- *generally* you use `rw` with an equality,
  and `apply` with implications and "for all" statements.
-/

/- END OF LECTURE HERE -/

/- Often we can `apply` lemmas from Mathlib. -/
variable (f g : ℝ → ℝ)
#check (Continuous.add : Continuous f → Continuous g → Continuous (fun x : ℝ ↦ f x + g x))
#check (Continuous.mul : Continuous f → Continuous g → Continuous (fun x : ℝ ↦ f x * g x))
#check (continuous_id : Continuous (fun x : ℝ ↦ x))
#check (continuous_sin : Continuous (fun x : ℝ ↦ sin x))

example : Continuous (fun x ↦ x + x * Real.sin x) := by
  apply Continuous.add       -- need both parts continuous
  ·apply continuous_id        -- part 1: x ↦ x
  apply Continuous.mul       -- part 2: x ↦ x * sin x
  ··apply continuous_id        -- factor 1: x ↦ x
  ··apply continuous_sin       -- factor 2: x ↦ sin x
  done





/- ## If and only if
* You can use `constructor` to prove an "if and only if" statement
* To use an "if and only if" statement `h`, you can use any of the following
  - `apply h.1`
  - `apply h.2`
  - `rw [h]`
  - `rw [← h]`
-/



#check exp_le_exp
#check (exp_le_exp.1 : exp a ≤ exp b → a ≤ b)
#check (exp_le_exp.2 : a ≤ b → exp a ≤ exp b)




example (h : a ≤ b) : exp a ≤ exp b := by
  apply exp_le_exp.2
  exact h 
  done



example (h : exp a ≤ exp b) : a ≤ b := by
  apply exp_le_exp.1
  assumption 
  done




example {p q : Prop} (h1 : p → q) (h2 : q → p) : p ↔ q := by
  constructor
  · apply h1
  · apply h2
  done




/- ## Universal quantification
The tactics for universal quantification and implication are the same.
* We can use `intro` to prove an universal quantification (or implication).
* We can use `apply` or `specialize` to use a hypothesis
  that is a universal quantification (or implication). -/


def Injective (f : ℝ → ℝ) : Prop := ∀ x y : ℝ, f x = f y → x = y


example (f g : ℝ → ℝ) (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := by
  intro x y h
  specialize hg (f x) (f y) h
  have h1 : f x = f y := hg
  exact hf x y h1  
  done




/- ## Conjunction

In Lean the conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`, read as "P and Q".

We can use a conjunction as follows:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.
Note that this is the same as for `↔`.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `obtain ⟨hP, hQ⟩ := h`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `obtain ⟨hPQ, hQP⟩ := h`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  sorry
  done
