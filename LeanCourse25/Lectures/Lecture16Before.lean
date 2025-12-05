import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.MetricSpace.Contracting

open BigOperators Function Set Real Topology Filter
open Interval ENNReal
noncomputable section

/- # Last time

Last time we discussed topology:
* `TopologicalSpace X` states that `X` is a topological space.
* continuity via `Filter.Tendsto` and via open sets
* homeomorphisms; compactness; connectedness
* various separation axioms
* the `fun_prop` tactics for proving goals of the form
  "the composition of continuous functions is continuous"
* `MetricSpace X` states that `X` is a metric space.


Today: differential calculus and differentiation
-/




/- # Differential Calculus -/

/- We write `deriv` to compute the derivative of a function.
`simp` can compute the derivatives of standard functions. -/

example (x : ℝ) : deriv Real.sin x = Real.cos x := by sorry

example (x : ℂ) :
    deriv (fun y ↦ Complex.sin (y + 3)) x = Complex.cos (x + 3) := by sorry

/- Not every function has a derivative.
As usual, in Mathlib we just define the derivative
of a non-differentiable function to be `0`. -/

variable (f : ℝ → ℝ) (x : ℝ) in
#check (deriv_zero_of_not_differentiableAt :
  ¬ DifferentiableAt ℝ f x → deriv f x = 0)

/- So proving that `deriv f x = y` doesn't
necessarily mean that `f` is differentiable.
Often it is nicer to use the predicate `HasDerivAt f y x`,
which states that `f` is differentiable and `f'(x) = y`. -/

example (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x :=
  sorry


/- We can also specify that a function has a derivative
without specifying its derivative. -/

example (x : ℝ) : DifferentiableAt ℝ sin x :=
  sorry


/- Mathlib contains lemmas stating that common operations satisfy
`HasDerivAt` and `DifferentiableAt` and to compute `deriv`. -/

#check HasDerivAt.add
#check deriv_add
#check DifferentiableAt.add


example (x : ℝ) :
    HasDerivAt (fun x ↦ Real.cos x + Real.sin x)
    (Real.cos x - Real.sin x) x := by
  -- rw [sub_eq_neg_add]
  sorry
  done


/- There are various variations of derivatives/being differentiable -/

/- A function is differentiable everywhere. -/
#check Differentiable

/- A function is differentiable on a subset. -/
#check DifferentiableOn

/- A function is differentiable at a point, considered only within the subset -/
#check DifferentiableWithinAt

/- We can also consider the derivative only within a subset. -/
#check HasDerivWithinAt
#check derivWithin




/-
Recall Lean's notation for intervals: `Icc a b = [a, b]` is a closed interval

The **intermediate value theorem** states that if `f` is continuous and
`f a ≤ y ≤ f b`, then there is an `x ∈ [a, b]` with `f(x) = y`.
-/

example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  sorry

/- The deeper mathematical reason is that intervals are connected (and vice versa).
Continuous functions preserve connectedness.
-/
#check isConnected_Icc
#check IsPreconnected.mem_intervals

#check IsConnected.image

#check IsConnected.Icc_subset

-- Let's put this together ourselves.
example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b := by
  sorry








/-
The mean value theorem states that if `f` is continous on `[a, b]`
and differentiable on `(a, b)` then there is a `c ∈ (a, b)` where `f'(c)` is the
average slope of `f` on `[a, b]`
-/
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  sorry


/- Rolle's theorem is the special case where `f a = f b`.
Why is there no differentiability requirement on `f` here? -/
example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  sorry



/- We can more generally talk about the derivative of functions between normed spaces.

A *normed group* is an abelian group with a norm satisfying the following rules.
-/

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

#check (fun x ↦ ‖x‖ : E → ℝ)

example (x : E) : 0 ≤ ‖x‖ :=
  sorry

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  sorry

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  sorry

/- This turns `E` into a metric space. -/
example (x y : E) : dist x y = ‖x - y‖ :=
  sorry

/- A *normed space* is a normed group that is a vector space
satisfying the following condition. -/

variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  sorry


/- A complete normed space is known as a *Banach space*.
Every finite-dimensional vector space is complete. -/

example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance

-- Products of Banach spaces are also Banach.
example [CompleteSpace E] : CompleteSpace (E × E) := by infer_instance

-- A quotient of a Banach space is also Banach.
example [CompleteSpace E] (s : Submodule ℝ E) : CompleteSpace (E ⧸ s) := by infer_instance

-- The Banach fixed point theorem
#check ContractingWith.exists_fixedPoint

/- In the above examples, we could also replace `ℝ` by `ℂ`
or another *normed field*. -/
#check NormedField

#check TopologicalSpace.SeparableSpace

-- The continuous dual space: all continuous linear maps `E →L[R] R`
#check StrongDual

#check Module.IsReflexive

-- Hahn-Banach theorem
#check exists_extension_norm_eq

-- Banach-Alaoglu theorem
#check WeakDual.isCompact_polar

-- Mathlib also has the closed graph theorem.

end NormedGroup



/- We can also take the derivative of functions that take values in a
normed vector space. -/

-- Proving differentiability is easy using `fun_prop`.
example {x : ℝ} : DifferentiableAt ℝ (fun x ↦ ((Real.cos x) ^ 2, (Real.sin x) ^ 2)) x := by
  fun_prop

-- Currently, derivatives still have to be computed by hand.
example (x : ℝ) : deriv (fun x ↦ ((Real.cos x) ^ 2, (Real.sin x) ^ 2)) x =
    (- 2 * Real.cos x * Real.sin x, 2 * Real.sin x * Real.cos x) := by
  sorry







  -- suffices HasDerivAt (fun x ↦ cos x ^ 2) (2 * (cos x) ^ 1 * (- sin x)) x by
  done



/- If the domain is a normed space we can define the
total derivative, which will be a continuous linear map. -/

/- Morphisms between normed spaces are continuous linear maps `E →L[𝕜] F`. -/
section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]


example : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F := f

example (f : E →L[𝕜] F) : Continuous f := f.cont

example (f : E →L[𝕜] F) : E →ₗ[𝕜] F := f

example (f : E →L[𝕜] F) (g : F →L[𝕜] G) : E →L[𝕜] G := g.comp f

/- Isomorphisms between normed spaces are continuous linear equivalences `E ≃L[𝕜] F` -/
example : E ≃L[𝕜] E := ContinuousLinearEquiv.refl 𝕜 E

-- We can invert and compose continuous linear equivalences: these operations are called
-- `symm` and `trans`, like for linear equivalences.
example (f : E ≃L[𝕜] F) : F ≃L[𝕜] E := f.symm

example (f : E ≃L[𝕜] F) (g : F ≃L[𝕜] G) : E ≃L[𝕜] G := f.trans g



/- Continuous linear maps have an operator norm. -/

example (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  sorry

example (f : E →L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  sorry


/- We define the *Fréchet derivative* of any function between normed spaces. -/

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔
    Tendsto (fun x ↦ ‖f x - f x₀ - f' (x - x₀)‖ / ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
  sorry -- let's find a good lemma using rw??

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) :
    fderiv 𝕜 f x₀ = f' :=
  sorry

-- Like for the derivative, we also have a Fréchet derivative within a set.
variable (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x₀ : E) in
#check fderivWithin 𝕜 f s x₀

#check HasFDerivWithinAt.fderivWithin


-- Careful: in higher dimensions, a function can have several derivatives within a set,
-- if that set is sufficiently "bad".
-- However, on "nice" sets, it is: this includes open sets and convex sets with non-empty interior.
#check UniqueDiffOn

example {s : Set E} (hs : IsOpen s) : UniqueDiffOn 𝕜 s := by sorry

#check Convex
#check uniqueDiffOn_convex





/- We can take the directional derivative or partial derivative
by applying the Fréchet derivative to an argument -/
example (x y : ℝ) :
    let f := fun ((x,y) : ℝ × ℝ) ↦ x^2 + x * y
    fderiv ℝ f (x, y) (1, 0) = 2 * x + y := by
  sorry -- exercise


/- We write `ContDiff 𝕜 n f` to say that `f` is `C^n`,
i.e. it is `n`-times continuously differentiable.
Here `n` lives in `WithTop ℕ∞`:
`ℕ∞` is `ℕ` with an extra top element `∞` added ("∞"),
and `WithTop ℕ∞` adds another element `⊤` ("ω").
-/
variable {f g : E → F} {m : ℕ∞} {r : 𝕜}

open scoped ContDiff -- for the notation "∞"

#check ContDiff 𝕜 42 f
#check ContDiff 𝕜 ∞ f -- f is smooth



example : ContDiff 𝕜 0 f ↔ Continuous f := contDiff_zero

example {n : ℕ} : ContDiff 𝕜 (n+1) f ↔
    Differentiable 𝕜 f ∧ ContDiff 𝕜 n (fderiv 𝕜 f) := by
  sorry


example : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f :=
  sorry



/- The element ω denotes analytic functions: those which have a Taylor series which converges
to the function -/
#check ContDiff 𝕜 ω f -- f is analytic

#check AnalyticAt

example [CompleteSpace F] : ContDiff 𝕜 ω f ↔ ∀ x, AnalyticAt 𝕜 f x := sorry

/- `fun_prop` can also prove that simple functions are `C^n`,
and knows about the relation between differentiability and `C^n` functions -/
variable {f g : E → F} {n : ℕ∞} {r : 𝕜}
example (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x ↦ (f x, r • f x + g x)) := by
  sorry

-- The implicit function theorem
#check ImplicitFunctionData.implicitFunction

-- The inverse function theorem
#check HasStrictFDerivAt.to_localInverse


/- If `f` is C¹, its `fderiv` is continuous -/
#check ContDiff.continuous_fderiv

-- There is also a converse: if `f` is differentiable and has continuous fderiv, it is C¹.
#check contDiff_one_iff_fderiv

-- This also holds for higher smoothness.
#check contDiff_succ_iff_fderiv


-- We can also take higher derivatives: these are denoted `iteratedFDeriv`
#check iteratedFDeriv

-- If `f : E → F`, then `fderiv 𝕜 f x : E →L[𝕜] F` is a continuous linear map.
#check fderiv 𝕜 f

-- The `fderiv` of that is a continuous bilinear map, and so on:
variable {x₀ : E}
#check iteratedFDeriv 𝕜 2 f x₀

#check ContinuousMultilinearMap

-- The 0-th iterated fderiv is the function itself.
#check iteratedFDeriv_zero_apply

-- The first iterated fderiv is the function itself.
-- Strictly speaking, their types are slightly different.
example (m : Fin 1 → E) : iteratedFDeriv 𝕜 1 f x₀ m = (fderiv 𝕜 f x₀) (m 0) := by
  sorry

-- The k+1-th iterated fderiv is the fderiv of the k-th one.
#check iteratedFDeriv_succ_apply_left

end NormedSpace
