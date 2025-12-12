import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BigOperators Function Set Real Topology Filter
open ENNReal MeasureTheory Interval intervalIntegral
set_option linter.unusedVariables false
noncomputable section







/- # Last time

Last time we discussed differential calculus:
* `∫ x in a..b, f x` is the notation used for definite integrals
* `ℝ≥0∞` is the type of extended nonnegative real numbers `[0, ∞]`
* `MeasurableSpace X` is used to equip `X` with a σ-algebra
* `μ : OuterMeasure X` resp. `μ : Measure X` states that
  `μ` is an (outer) measure on `X`.
* `∀ᵐ x ∂μ, P x` means that `P` holds for almost all `x` (relative to `μ`)


**Today**
* finish integration
* inductive types
-/

section MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} {f : X → Y}

example : ∀ᵐ x : ℝ, Irrational x := by
  sorry
  done



/- A map is (Borel-)measurable if preimages of measurable sets
under that map are measurable.
Note the similarity to the definition of continuity.
In particular, continuous functions are measurable. -/

example {f : X → Y} : Measurable f ↔
    (∀ s : Set Y, MeasurableSet s → MeasurableSet (f ⁻¹' s)) := by rfl
#check Continuous.measurable

/- We can write `MeasurePreserving f μ ν` to state that `f : X → Y`
maps the measure `μ : Measure X` to `ν : Measure Y`,
i.e. `ν s = μ (f ⁻¹' s)` for all (measurable) sets `s`.
This is important for Ergodic theory. -/
#check MeasurePreserving



/- A map `f` into a normed group is integrable when it is
measurable and the map `x ↦ ‖f x‖` has a finite integral.
You can write `Integrable f μ` to say that `f` is integrable
w.r.t. `μ`, and `Integrable f` for `μ = volume` -/
#check Integrable

example (f : ℝ → ℝ) (h1 : Continuous f) (h2 : HasCompactSupport f) :
    Integrable f :=
  Continuous.integrable_of_hasCompactSupport h1 h2



/- `Integrable` means that a function is integrable
on the whole domain.
You can use `IntegrableOn` to state that a function is
only integrable on some set. -/

#check IntegrableOn

example : ¬ Integrable (fun _ ↦ 1 : ℝ → ℝ) := by
  sorry
  done








/- We can take the integrals for functions intro a Banach space.
This version of the integral is called the *Bochner integral*.
The integral is denoted `∫ a, f x ∂μ` -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : X → E}

#check X →₁[μ] E

example {f g : X → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
  integral_add hf hg


/-
* We can write `∫ x in s, f x ∂μ` for the integral restricted to a set.
* We can abbreviate `∫ x, f x ∂volume` to `∫ x, f x`
* We write `∫ x in a..b, f x ∂μ` for the integral on an interval.
-/
example {s : Set X} (c : E) :
    ∫ x in s, c ∂μ = μ.real s • c :=
  setIntegral_const c

example {f : ℝ → E} {a b c : ℝ} :
    ∫ x in a..b, c • f x = c • ∫ x in a..b, f x :=
  intervalIntegral.integral_smul c f

example {f : ℝ → E} {a b : ℝ} (h : a ≤ b) :
    ∫ x in a..b, f x = ∫ x in Ioc a b, f x :=
  integral_of_le h

example {f : ℝ → E} {a b : ℝ} (h : b ≤ a) :
    ∫ x in a..b, f x = -∫ x in Ioc b a, f x :=
  integral_of_ge h


/- See the *Technical* section from last time if you want to see
more details on how the Bochner integral is defined. -/



/- If you have taken analysis III,
you will have seen some important theorems in measure theory.
General versions of these are also in Mathlib. -/

/- Here is a version of the dominated convergence theorem. -/
example {F : ℕ → X → E} {f : X → E} (bound : X → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim


/- Here is the statement of Fubini's theorem. -/
variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν] in
example (f : X × Y → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf

/-
There are various versions of the change of variables theorem.
Here is one for functions in only 1 variable.
-/
example {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → E) :
    ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) :=
  integral_image_eq_integral_abs_deriv_smul hs hf' hf g

/-
Note that this has weaker assumptions versions you often see:
- `s` is not required to be open;
- `f` is not required to be continuously differentiable;
- because the integral of non-integrable functions has junk value 0,
  `g` is not required to be integrable.
-/

/- Here is a version of the change of variables formula for interval integrals. -/
#check integral_comp_smul_deriv''

end MeasureTheory








/-
## Inductive types

Lean's rules allow us to define *inductive types*.
An inductive type is a type where you (recursively) specify all elements.

For example, the following is a declaration of (a copy of) the natural numbers.
every element is either `zero` or `succ` of an (already constructed) natural number.

`zero` and `succ` are called the *constructors* of this inductive type.
-/
inductive NaturalNumber where
  | zero : NaturalNumber
  | succ (n : NaturalNumber) : NaturalNumber

#check NaturalNumber
#check NaturalNumber.zero
#check NaturalNumber.succ

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
#check [5, 3]
#check 5 :: 3 :: []
#check List.cons 5 (List.cons 3 List.nil)




/- Inductive types allow you to define new operations on it
by *pattern matching*.

This defines a new function *recursively* by the given equations. -/



@[simp]
def appendLists {α : Type*} : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: appendLists as bs

infix:60 " +' " => appendLists

example {α : Type*} (as : List α) : [] +' as = as := rfl

example {α : Type*} (a : α) (as bs : List α) :
    (a :: as) +' bs = a :: (as +' bs) := by rfl

/-
The default recursion is *structural recursion*.

Structural recursion allows you to define e.g.
a function `f : List α → β` by defining
- `f [] := f_nil`
- `f (a :: as) := f_cons a as (f as)`
for some expressions `f_nil` and `f_cons`.
We write `f_cons a as (f as)` to signify that
this expression can depend on `a`, `as`` and `f as`
(but not `f` applied to other values.
-/


/- We can prove properties about inductive types using `induction`. -/

example {α : Type*} (as bs cs : List α) :
    (as +' bs) +' cs = as +' (bs +' cs) := by
  sorry
  done

example {α : Type*} (as : List α) :
    as +' [] = as := by
  sorry
  done


/- As another example, here are *two* ways to define addition
on the natural numbers I defined above. -/

@[simp]
def myAdd : NaturalNumber → NaturalNumber → NaturalNumber
  | zero,   m => m
  | succ n, m => succ (myAdd n m)


@[simp]
def myAdd' : NaturalNumber → NaturalNumber → NaturalNumber
  | n, zero  => n
  | n, succ m => succ (myAdd' n m)


/- They are not trivially equal! -/

example : myAdd = myAdd' := by
  sorry
  done

/- Under the hood, both (structural) recursion and induction
come from a *recursor*, that is automatically generated when
you write an `inductive` command. -/

#check Nat.rec

/-
Given
- `P : ℕ → Sort u` (think: `P : ℕ → Prop`)
- `c_0 : P 0`
- `c_succ : ∀ n, P n → P (n + 1)`

then the function `g = @Nat.rec P c_0 c_succ : ∀ n : ℕ, P n`
is the function defined by
- `g 0 := c_0`
- `g (n + 1) := c_succ n (g n)`

These equalities hold *by definition*.
In other words, `rfl` can prove these two equalities:
- `@Nat.rec P c_0 c_succ 0 = c_0`
- `@Nat.rec P c_0 c_succ (n + 1) = c_succ n (@Nat.rec P c_0 c_succ n)`
These are called the *computation rules* for `ℕ`.

Let's see some examples. -/


def myFac : ℕ → ℕ :=
  sorry

lemma myFac_succ (n : ℕ) : myFac (n + 1) = (n + 1) * myFac n := by
  sorry

lemma myFac_pos (n : ℕ) : 0 < myFac n := by
  sorry
  done

/-
In summary: defining a inductive type like
```
inductive NaturalNumber where
  | zero : NaturalNumber
  | succ (n : NaturalNumber) : NaturalNumber
```
gives 4 things:
* A new type `NaturalNumber : Type`
* *constructors* `NaturalNumber.zero` and `NaturalNumber.succ`
* A *recursor* `NaturalNumber.rec` that stated how to define functions
  recursively and prove things inductively.
* *computation rules* that state how to compute
  when the recursor is applied to a constructor.
-/




/-
### Well-founded recursion

Lean also support *non-structural* recursion.
This is implemented using *well-founded recursion*.
Lean tries to prove automatically that the arguments
in the recursive calls are smaller than the input argument.
-/

/- the Fibonacci sequence -/
def F : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

/- the number of factors 2 in a number -/
def twoVal : ℕ → ℕ∞
  | 0 => ⊤
  | n + 1 =>
    if (n + 1) % 2 = 0 then
      twoVal ((n + 1) / 2) + 1
    else
      0

/- The Ackermann function -/
def A : ℕ → ℕ → ℕ
| 0,     n     => n + 1
| m + 1, 0     => A m 1
| m + 1, n + 1 => A m (A (m + 1) n)


/- `(b, n) ↦ ⌊log_b(n)⌋`, i.e. the logarithm rounded down.
In this case, we need to help Lean -/
def myLog (b : ℕ) : ℕ → ℕ
  | n => if h : b ≤ n ∧ 1 < b then myLog b (n / b) + 1 else 0
decreasing_by
  exact Nat.div_lt_self (by cutsat) h.2




/-
*Well-founded recursion* uses a special inductive type
`Acc` (for *accessibility*).

Take a look at these definitions if you want to know the details.
-/
#check WellFounded
#check Acc



/-
### Other inductive types

Many types in Lean are inductive types.
Here are some examples. Each of these inductive types
-/

/- Cartesian product of types. -/
inductive CartesianProduct (A B : Type*) where
  | pair : A → B → CartesianProduct A B

/- Coproduct (disjoint union) of types. -/
inductive DisjointUnion (A B : Type*) where
  | left  : A → DisjointUnion A B
  | right : B → DisjointUnion A B

/- specific enumerated types. -/
inductive Booleans where
  | true : Booleans
  | false : Booleans

inductive SingletonType where
  | singlePoint : SingletonType

inductive EmptyType where
-- 0 constructors!



/- We can also define *inductive propositions*. -/

inductive Conjunction (A B : Prop) : Prop where
  | and_intro : A → B → Conjunction A B

inductive Disjunction (A B : Prop) : Prop where
  | left  : A → Disjunction A B
  | right : B → Disjunction A B

inductive Truth : Prop where
  | trivial : Truth

inductive Falsity : Prop where

inductive Existential (A : Type*) (P : A → Prop) : Prop where
  | intro : ∀ x, P x → Existential A P


/- Even equality is defined inductively.
This is a special: it is a inductive *family* of propositions.
We define for each type `A` we define `Equality A a b`
simultaneously for all `a b : A`. -/
inductive Equality (A : Type*) : A → A → Prop where
  | reflexivity : ∀ a : A, Equality A a a

/- We can define the proposition stating that a type is non-empty. -/
inductive IsNonempty (A : Type*) : Prop where
  | intro : A → IsNonempty A


/- Another example if inductive families comes from constructions
that construct the smallest collection of objects satisfying some property.

For example, if `g` is any collection of subsets of a type `X`,
the following gives the smallest topology where all sets in `g` are open.
Equivalently: the intersection of all topologies containing `g`. -/
inductive GenerateOpen {X : Type*} (g : Set (Set X)) : Set X → Prop
  | basic : ∀ s ∈ g, GenerateOpen g s
  | univ : GenerateOpen g univ
  | inter : ∀ s t, GenerateOpen g s → GenerateOpen g t → GenerateOpen g (s ∩ t)
  | sUnion : ∀ S : Set (Set X), (∀ s ∈ S, GenerateOpen g s) → GenerateOpen g (⋃₀ S)

def generateFrom {X : Type*} (g : Set (Set X)) : TopologicalSpace X where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion

/-
Something special happens with inductive propositions.
Some propositions (`∧`, `True`, `False`, `=`) can eliminate
to *any* sort (all types and `Prop`)
Other propositions (`∃`, `∨`, `Nonempty`) can only eliminate to `Prop`.

Look at type type of `motive` in the recursors below.

The difference is that the propositions `∃`, `∨` and `Nonempty` can be proven
with either different constructors or one constructor applied to different arguments.
If such a proposition could eliminate to any type, then (together with the computation rule)
you could derive a contradiction.
-/
#check Conjunction.rec
#check Disjunction.rec
#check Nonempty.rec
#check Equality.rec
