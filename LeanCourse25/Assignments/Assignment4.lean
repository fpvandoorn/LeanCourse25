import Mathlib.Analysis.Complex.Exponential

import Mathlib
open Real Function Set

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 8 explains some of the design decisions for classes in Mathlib.

* Hand in the solutions to the exercises below. Deadline: **Thursday**, 14.11.2025 at 10.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/


-- Recall the definition of points from the lecture.
@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

instance : Add Point := ⟨add⟩

-- Prove that addition of points is associative.
lemma add_assoc {a b c : Point} : a + (b + c) = a + b + c := by
  sorry
  done

-- Define scalar multiplication of a point by a real number
-- in the way you know from Euclidean geometry.
def smul (r : ℝ) (a : Point) : Point := sorry

-- If you made the right definition, proving these lemmas should be easy.
@[simp] lemma smul_x (r : ℝ) (a : Point) : (Point.smul r a).x = r * a.x := by sorry
@[simp] lemma smul_y (r : ℝ) (a : Point) : (Point.smul r a).y = r * a.y := by sorry
@[simp] lemma smul_z (r : ℝ) (a : Point) : (Point.smul r a).z = r * a.z := by sorry

-- This registers the above operation as "scalar multiplication":
-- you can now write • for scalar multiplication.
instance : SMul ℝ Point := ⟨smul⟩

variable (x : ℝ) (a : Point)
#check x • a

end Point

-- This is the standard two-simplex in ℝ³. How does it look like, geometrically?
structure StandardTwoSimplex where
  coords : Point
  x_nonneg : 0 ≤ coords.x
  y_nonneg : 0 ≤ coords.y
  z_nonneg : 0 ≤ coords.z
  sum_eq : coords.x + coords.y + coords.z = 1

namespace StandardTwoSimplex

noncomputable section

-- Prove that a convex combination of two points in the standard simplex is again in the
-- standard simplex.
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
  (a b : StandardTwoSimplex) : StandardTwoSimplex
where
  coords := lambda • a.coords + (1 - lambda) • b.coords
  x_nonneg := by sorry
  y_nonneg := by sorry
  z_nonneg := by sorry
  sum_eq := by sorry

end

end StandardTwoSimplex


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by
  sorry
  done

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by
  sorry
  done

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by
  sorry
  done

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by
  sorry
  done


example : Setoid (ℕ × ℕ) where
  r := fun ⟨k, l⟩ ⟨m, n⟩ ↦ k + n = m + l
  iseqv := sorry


/-! # Exercises to hand-in. -/

section

-- Let's define a new operation on points in ℝ⁴.

@[ext]
structure Point4 where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ

def op (a b : Point4) : Point4 where
  x := a.x * b.x - a.y * b.y - a.z * b.z - a.w * b.w
  y := a.x * b.y + a.y * b.x + a.z * b.w - a.w * b.z
  z := a.x * b.z - a.y * b.w + a.z * b.x + a.w * b.y
  w := a.x * b.w + a.y * b.z - a.z * b.y + a.w * b.x

-- Prove that op is associative.
lemma op_assoc {a b c : Point4} : op (op a b) c = op a (op b c) := by
  sorry
  done

-- Investigate whether op is commutative: prove one of the following.
lemma op_comm : ∀ a b : Point4, op a b = op b a := by sorry

-- For the latter, you may the following helpful.
example : ⟨0, 1, 2, 3⟩ ≠ (⟨0, 3, 2, 3⟩ : Point4) := by
  sorry
  done

example {x y : ℝ} (h : x ≠ y) : ⟨0, 1, x, 3⟩ ≠ (⟨0, 1, y, 3⟩ : Point4) := by
  sorry
  done

-- If you want to use one of these lemmas, prove it also.
lemma ne_of_ne_x {a b : Point4} (h : a.x ≠ b.x) : a ≠ b := by sorry
lemma ne_of_ne_y {a b : Point4} (h : a.y ≠ b.y) : a ≠ b := by sorry
lemma ne_of_ne_z {a b : Point4} (h : a.z ≠ b.z) : a ≠ b := by sorry
lemma ne_of_ne_w {a b : Point4} (h : a.w ≠ b.w) : a ≠ b := by sorry


lemma not_op_comm : ¬(∀ a b : Point4, op a b = op b a) := by
  sorry

-- Let us now consider a special kind of points.
def SpecialPoint := { p : Point4 // p.x ^2 + p.y ^2 + p.z ^ 2 + p.w ^ 2 = 1 }

-- We define "the same" operation on special points: complete the proof.
def op' (a b : SpecialPoint) : SpecialPoint :=
  ⟨op a.val b.val, sorry⟩

-- Prove that `SpecialPoint` with the operation `op'` is a group.
-- (If commutativity holds, it's even an abelian group. You don't need to prove this.)
-- Here is a definition of group to use.
structure Group' (G : Type*) where
  gop (x : G) (y : G) : G
  assoc (x y z : G) : gop (gop x y) z = gop x (gop y z)
  neutral : G
  gop_neutral : ∀ x : G, gop x neutral = x
  inv (x : G) : G
  gop_inv : ∀ x : G, gop x (inv x) = neutral

-- Note that you are working with subtypes again: you may need to use loogle to
-- find the right lemma to get "out of subtype world".
noncomputable example : Group' SpecialPoint := sorry


-- Bonus: Do you recognise this operation from your mathematics classes?
-- Can you even give it a geometric interpretation?

end



section Bipointed

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here

-- state and prove the lemma here


end Bipointed

section Subtypes

/-- Let's prove that the positive rationals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosRat : Type := {x : ℚ // 0 < x}

def groupPosRat : Group PosRat := sorry

end Subtypes

section EquivalenceRelation

-- Prove that the following defines an equivalence relation.
def integerEquivalenceRelation : Setoid (ℤ × ℤ) where
  r := fun ⟨k, l⟩ ⟨m, n⟩ ↦ k + n = l + m
  iseqv := sorry

/- This simp-lemma will simplify `x ≈ y` in the lemma below. -/
@[simp] lemma integerEquivalenceRelation'_iff (a b : ℤ × ℤ) :
  letI := integerEquivalenceRelation; a ≈ b ↔ a.1 + b.2 = a.2 + b.1 := by rfl

example : Quotient integerEquivalenceRelation ≃ ℤ := sorry

end EquivalenceRelation
