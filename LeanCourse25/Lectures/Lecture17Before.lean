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
* `DifferentiableAt`, `HasDerivAt` and `deriv` are used
  to talk about derivatives of single-variable functions.
* `HasFDerivAt` and `fderiv` are used to talk about the
  Fréchet derivative (total derivative) of a function
  whose domain is a normed space.
  Partial derivatives and directional derivatives can be
  obtained by applying `fderiv` to a (basis) vector.
* `Differentiable` (and variants like `DifferentiableOn`)
  are used to say that functions are differentiable
  (this is the same predicate for single-variable functions
  and functions on normed spaces).
* "`E` is a Banach space (over `ℝ`)" is written as
  `[NormedSpace ℝ E] [CompleteSpace E]`
* `ContDiff ℝ n f` states that `f` is `C^n`
  `ContDiff 𝕜 ω f` states that `f` is analytic
* Mathlib has standard theorems:
  - intermediate value theorem
  - mean value theorem

Today: integration and measure theory

Practical remark: during this class, I will discuss projects
-/













/-! ## Basic Integration -/

/- We start with some basic integration results in Mathlib.
The integral of a function `f` on the interval `[a, b)`
is written as `∫ x in a..b, f x`. -/

example (a b : ℝ) : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example : ∫ x in 0..1, x = 1/2 := by
  simp

example (a b : ℝ) : ∫ x in a..b, exp x = exp b - exp a :=
  integral_exp


/- We can use this to define an specific antiderivative
of a function. -/

example (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t in 0..x, f t

/- the notation `[[a, b]]` (in namespace `Interval`) means
`uIcc a b`, i.e. the interval from `min a b` to `max a b` -/
example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, 1 / x = log (b / a) :=
  integral_one_div h

/- In very simple cases `simp` can solve an abstract integral.
In this case, it uses translation invariance of integrals. -/
example (a b : ℝ) :
    ∫ x in a..b, exp (x + 3) = exp (b + 3) - exp (a + 3) := by
  simp

/- If we swap `a` and `b`, the sign flips. -/
example {f : ℝ → ℝ} {a b : ℝ} :
    ∫ x in b..a, f x = - ∫ x in a..b, f x :=
  intervalIntegral.integral_symm a b




/- We have the fundamental theorem of calculus in Lean. -/

/- FTC-1: the derivative of the integral is the original function. -/
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

/- FTC-2: the integral of a derivative can be computed by
evaluation at the endpoints. -/
example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ}
    (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt h h'

/- We can use this to compute integrals
if we know the antiderivative. -/
example (a b : ℝ) : ∫ x in a..b, exp (x / 2) =
    2 * exp (b / 2) - 2 * exp (a / 2) := by
  sorry
  done

/-
In the example above we computed the derivative using
`apply HasDerivAt.congr_deriv`, which will caused a *metavariable*
to appear in the goal.
Some tactics (like `apply?`) don't work well in such cases,
but sometimes it's convenient.
-/




/-
## Measure Theory

Integrals in Mathlib are defined using *Bochner integration*.
This is a general method to work with integrals, since it is
defined for functions that take values in a Banach space.

This requires us to develop some measure theory.

A brief explanation for the students that have not done Analysis 3:

We want to define functions that assign a measure to a set
(e.g. the volume of a set `A ⊆ ℝ³` or the length of a set `A ⊆ ℝ`).
Measures take values in the extended non-negative reals `[0, ∞]`.
We want a measure `μ` to satisfy the following conditions:
1. *Translation invariance*: `μ(A + x) = μ(A)`
2. *Countable additivity*: if `(Aᵢ)ᵢ` is a countable family of
  pairwise disjoint sets, then `μ(⋃ᵢ Aᵢ) = ∑ᵢ μ(Aᵢ)`
3. `μ([0, 1)) = 1`

Theorem: There is no function `μ` that assigns a measure to all
subsets of `ℝ` that satisfies the three conditions above.

**Outer measures** An outer measure is a function
`μ : 𝒫(X) → [0, ∞]` satisfying:
* `μ(∅) = 0`
* *Countable subadditivity*: if `(Aᵢ)ᵢ` is
  a countable family of sets, then
  `μ(⋃ᵢ Aᵢ) ≤ ∑ᵢ μ(Aᵢ)`
* *Monotonicity*: if `A ⊆ B` then `μ(A) ≤ μ(B)`.

**Measures** do satisfy 2, but have as domain only the
*measurable sets*.

The measurable sets must form a **σ-algebra**:
* `∅` is measurable
* If `A` is measurable, then `Aᶜ` is measurable
* If `Aᵢ` is countable measurable family, then `⋃ᵢ Aᵢ` is measurable.

Lemma. Given a measure `μ`, we can define an outer measure `m`
that extends `μ` as `m(A) = inf{B | A ⊆ B ∧ B is measurable}`.

Let's see how this looks in Lean.
-/

/- In Mathlib, we denote `[0, ∞]` by `ℝ≥0∞` or `ENNReal`. -/

#check ℝ≥0∞
example : ℝ≥0∞ = WithTop {x : ℝ // 0 ≤ x} := rfl
example : (∞ + 5) = ∞ := by simp
example : (∞ * 0) = 0 := by simp


/-
`OuterMeasure X` is the type of outer measures on `X`
-/
section OuterMeasure

variable {X : Type*} {μ : OuterMeasure X}

#check (μ : Set X → ℝ≥0∞)

example : μ ∅ = 0 :=
  measure_empty

example {s t : Set X} (h : s ⊆ t) : μ s ≤ μ t :=
  measure_mono h

example {s : ℕ → Set X} : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

end OuterMeasure

/- We write `MeasurableSpace X` to say that `X` has a notion
of measurable sets that form a σ-algebra. -/

variable {X : Type*} [MeasurableSpace X]

example : MeasurableSet (∅ : Set X) :=
  MeasurableSet.empty

example {s : Set X} (hs : MeasurableSet s) : MeasurableSet sᶜ :=
  hs.compl

example {f : ℕ → Set X} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

/-
A measure `μ` on `X` comes together with its associated outer measure.
This means that we can apply `μ` to any subset of `X`, but
many lemmas (e.g. additivity) require that the sets are measurable.
-/

variable {μ : Measure X}

example : μ ∅ = 0 :=
  measure_empty

example {s : ℕ → Set X} (hmeas : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (Disjoint on s)) :
    μ (⋃ i, s i) = ∑' i, μ (s i) :=
  measure_iUnion hdis hmeas

example (s : Set X) : μ s = ⨅ (t ⊇ s) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ℕ → Set X) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s




/- If you know that the measure of a set is finite, you can get
the measure as a real number with `μ.real`.

The function `ENNReal.toReal` sends `∞` to `0`. -/
example (s : Set X) : μ.real s = (μ s).toReal := rfl



/- The collection of measurable sets on `ℝ`
is the smallest σ-algebra containing the open sets.
These are called the *Borel-measurable* sets. -/
example (s : Set ℝ) : MeasurableSet s ↔
    MeasurableSpace.GenerateMeasurable { t : Set ℝ | IsOpen t } s := by rfl

example : BorelSpace ℝ := by infer_instance


/- The *Lebesgue-measurable* sets are the sets
that are Borel measurable up to a null set. -/
#check NullMeasurableSet
example {s : Set ℝ} (hs : volume s = 0) : NullMeasurableSet s := by
  exact?

/- Various spaces have a canonical measure associated to them,
called `volume`. This is given by the class `MeasureSpace`.

On the real numbers, this is the measure on the Borel measurable sets
that is translation invariant and has `μ([0, 1]) = 1` -/
example : MeasureSpace ℝ := by infer_instance
#check (volume : Measure ℝ)
#check (volume : Measure (Fin 3 → ℝ))


example (a b : ℝ) (h : a ≤ b) :
    volume.real (Icc a b) = b - a := by
  simp [h]

example (x : ℝ) (s : Set ℝ) :
    volume ((· + x) '' s) = volume s := by
  simp?





/- Filters are also useful in measure theory.

We say that a property `P` holds **almost everywhere**
if the set of elements where it doesn't hold has measure 0. -/
example {P : X → Prop} :
    (∀ᶠ x in ae μ, P x) ↔ μ {x | ¬ P x} = 0 := by
  rfl

/- This also has the specific notation `∀ᵐ (x : X) ∂μ, P x`.
We write `f =ᵐ[μ] g` to state that two functions are a.e. equal. -/
variable (P : X → Prop) in
#check ∀ᶠ x in ae μ, P x


example : ({0} : Set ℝ).indicator 1 =ᵐ[volume] (0 : ℝ → ℝ) := by
  simp [Filter.EventuallyEq, ae_iff]
  done

example : ∀ᵐ x : ℝ, Irrational x := by
  sorry
  done



/- A map is (Borel-)measurable if preimages of measurable sets
under that map are measurable.
Note the similarity to the definition of continuity.
In particular, continuous functions are measurable. -/
#print Measurable
#check Continuous.measurable






/- A map `f` into a normed group is integrable when it is measurable and the map
`x ↦ ‖f x‖` has a finite integral. -/
#print Integrable

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






section Technical

/- **Side note**: technical remarks
(that we will skip in class; for those that are interested in the details.) -/

/-
There are multiple notions of measurability in Mathlib.
* *simple functions* are functions with finite range and
  whose preimage of every set is measurable.
* A function is *strongly measurable* if it is
  the pointwise limit of a sequence of simple functions
  In most cases (i.e. if the codomain is second-countable and metrizable)
  that is equivalent to being measurable.
* A function is *a.e.-(strongly) measurable* if
  it is a (strongly) measurable function up to a null set.
  This corresponds to the Lebesgue measurable functions
-/
#print SimpleFunc
#print StronglyMeasurable
#print AEMeasurable
#print AEStronglyMeasurable

/-
For simple functions `g : X → ℝ≥0∞` we can define the integral easily:
for any `x` in the range of `g` just compute `x * μ (g ⁻¹' {x})`
and then sum over such `x`.

For any function `f : X → ℝ≥0∞`, we can define the *Lebesgue integral* of `f`
as the supremum of the integrals of all (pointwise) smaller simple functions.
This is denoted `∫⁻ x, f x ∂μ`.
-/

example (g : SimpleFunc X ℝ≥0∞) : g.lintegral μ =
    ∑ x ∈ g.range, x * μ (g ⁻¹' {x}) := by rfl

example (f : X → ℝ≥0∞) : ∫⁻ x, f x ∂μ =
    ⨆ (g : SimpleFunc X ℝ≥0∞) (_ : g ≤ f), g.lintegral μ := by
  simp [lintegral]

example {f g : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x + g x ∂μ = ∫⁻ x, f x ∂μ + ∫⁻ x, g x ∂μ :=
  lintegral_add_left hf g

/-
The *Bochner integral* is defined for functions
that take values in a Banach space.

The idea of the definition is the same:
a strongly measurable function can be approximated by simple functions,
and the integral is the limit of the integrals of such simple funcions.

The details are more technical:
We can use the Lebesgue integral to define integrability:
`f` is integrable if it is a.e.-strongly measurable and `∫⁻ x, ‖f x‖ₑ ∂μ` is finite.
(`‖y‖ₑ` is just the norm of `y` as an element of `ℝ≥0∞`.)

We define `X →₁[μ] E` (or `L¹(X, μ; E)`) as the space of L¹-functions
from `X` to `E`, i.e. the integrable functions module a.e.-equality.

This is a Banach space with the norm of `f` given by `∫⁻ x, ‖f x‖ₑ ∂μ`.
The simple integrable functions are dense in this space.
We can define the integral as a continuous linear map on this subspace,
and then uniquely extend it to all `L¹`-functions.
This defines the Bochner integral of an arbitrary integrable function.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : X → E}

/- You can jump to these definitions to see them in Mathlib. -/
#check X →₁[μ] E
#check L1.integral
#check integral

end Technical

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



/-
# Exercises

These exercises are only on basic integration on intervals.
-/

/- simp can deal with a translations and scaling inside integrals. -/
example (a b : ℝ) : ∫ x in a..b, 4 * cos (2 * x + 3) =
    2 * (sin (2 * b + 3) - sin (2 * a + 3)) := by
  sorry
  done

example : ∫ x in 0..2, exp x + x ^ 3 = exp 2 + 3 := by
  sorry
  done


/- Do this *without* using the fundamental theorem of calculus. -/
example (a b : ℝ) : ∫ x in a..b, sin x * cos x =
    (cos (2 * a) - cos (2 * b)) / 4 := by
  sorry
  done

/- Use the fundamental theorem of calculus. -/
example (a b : ℝ) (n : ℕ) : ∫ x in a..b, x ^ n * sin (x ^ (n + 1)) =
    (cos (a ^ (n + 1)) - cos (b ^ (n + 1))) / (n + 1) := by
  sorry
  done

/- This one is tricky. Find appropriate lemmas using `rw??` or loogle. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, 1 / x + 1 / x ^ 2 =
  log b + 1 / a - log a - 1 / b := by
  have : 0 ∉ [[a, b]] := by exact notMem_uIcc_of_lt ha hb
  sorry
  done
