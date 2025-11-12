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

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

-- Prove that addition of points is associative.
lemma add_assoc {a b c : Point} : a + (b + c) = a + b + c := by
  ext <;> (simp; rw [@AddSemigroup.add_assoc])
  done

-- Define scalar multiplication of a point by a real number
-- in the way you know from Euclidean geometry.
def smul (r : ℝ) (a : Point) : Point :=
  { x:= r*a.x
    y:= r*a.y
    z:= r*a.z
  }

-- If you made the right definition, proving these lemmas should be easy.
@[simp] lemma smul_x (r : ℝ) (a : Point) : (Point.smul r a).x = r * a.x := by rfl
@[simp] lemma smul_y (r : ℝ) (a : Point) : (Point.smul r a).y = r * a.y := by rfl
@[simp] lemma smul_z (r : ℝ) (a : Point) : (Point.smul r a).z = r * a.z := by rfl

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
  x_nonneg := by
    have hx₁ : 0 ≤ lambda • a.coords.x  :=   mul_nonneg lambda_nonneg  a.x_nonneg
    have h01 : 0 ≤ 1 - lambda := sub_nonneg.mpr lambda_le
    have hx₂ : 0 ≤ (1 - lambda) • b.coords.x :=  mul_nonneg h01 b.x_nonneg
    have hx := add_nonneg hx₁ hx₂
    change 0 ≤ lambda * a.coords.x + (1 - lambda) * b.coords.x
    exact hx


  y_nonneg := by
    have hy₁ : 0 ≤ lambda • a.coords.y  :=   mul_nonneg lambda_nonneg  a.y_nonneg
    have h01 : 0 ≤ 1 - lambda := sub_nonneg.mpr lambda_le
    have hy₂ : 0 ≤ (1 - lambda) • b.coords.y :=  mul_nonneg h01 b.y_nonneg
    have hy := add_nonneg hy₁ hy₂
    change 0 ≤ lambda * a.coords.y + (1 - lambda) * b.coords.y
    exact hy

  z_nonneg := by
    have hz₁ : 0 ≤ lambda • a.coords.z  :=   mul_nonneg lambda_nonneg  a.z_nonneg
    have h01 : 0 ≤ 1 - lambda := sub_nonneg.mpr lambda_le
    have hz₂ : 0 ≤ (1 - lambda) • b.coords.z :=  mul_nonneg h01 b.z_nonneg
    have hz := add_nonneg hz₁ hz₂
    change 0 ≤ lambda * a.coords.z + (1 - lambda) * b.coords.z
    exact hz

  sum_eq := by
    have ha := a.sum_eq
    have hb := b.sum_eq
    calc
      (lambda • a.coords + (1 - lambda) • b.coords).x
        + (lambda • a.coords + (1 - lambda) • b.coords).y
        + (lambda • a.coords + (1 - lambda) • b.coords).z
      = lambda • a.coords.x + (1 - lambda) • b.coords.x
        + (lambda • a.coords.y + (1 - lambda) • b.coords.y)
        + (lambda • a.coords.z + (1 - lambda) • b.coords.z) := by rfl
    _ = lambda * (a.coords.x + a.coords.y + a.coords.z)
          + (1 - lambda) * (b.coords.x + b.coords.y + b.coords.z) := by
          simp [mul_add, add_assoc, add_comm, add_left_comm]
    _ = 1 := by simp [ha, hb]
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

-- I added @simp because I dont know what to do otherwise
@[simp] def op (a b : Point4) : Point4 where
  x := a.x * b.x - a.y * b.y - a.z * b.z - a.w * b.w
  y := a.x * b.y + a.y * b.x + a.z * b.w - a.w * b.z
  z := a.x * b.z - a.y * b.w + a.z * b.x + a.w * b.y
  w := a.x * b.w + a.y * b.z - a.z * b.y + a.w * b.x



-- Prove that op is associative.
lemma op_assoc {a b c : Point4} : op (op a b) c = op a (op b c) := by
  ext <;> (simp;ring)
  done

-- Investigate whether op is commutative: prove one of the following.
lemma op_comm : ∀ a b : Point4, op a b = op b a := by sorry
-- This statement is not true, I am proving the one below

-- I don't need the lemmas below, but I am proving them anyway

-- For the latter, you may the following helpful.
example : ⟨0, 1, 2, 3⟩ ≠ (⟨0, 3, 2, 3⟩ : Point4) := by
  simp
  done

example {x y : ℝ} (h : x ≠ y) : ⟨0, 1, x, 3⟩ ≠ (⟨0, 1, y, 3⟩ : Point4) := by
  simp
  assumption
  done

-- If you want to use one of these lemmas, prove it also.
lemma ne_of_ne_x {a b : Point4} (h : a.x ≠ b.x) : a ≠ b := by
  by_contra h1
  have h2 : a.x = b.x := by simp [h1]
  contradiction
  done
lemma ne_of_ne_y {a b : Point4} (h : a.y ≠ b.y) : a ≠ b := by
  by_contra h1
  have h2 : a.y = b.y := by simp [h1]
  contradiction
  done
lemma ne_of_ne_z {a b : Point4} (h : a.z ≠ b.z) : a ≠ b := by
  by_contra h1
  have h2 : a.z = b.z := by simp [h1]
  contradiction
  done
lemma ne_of_ne_w {a b : Point4} (h : a.w ≠ b.w) : a ≠ b := by
  by_contra h1
  have h2 : a.w = b.w := by simp [h1]
  contradiction
  done



lemma not_op_comm : ¬(∀ a b : Point4, op a b = op b a) := by
  push_neg
  use (⟨0, 1, 2, 0⟩ : Point4)
  use (⟨0, 3, 4, 0⟩ : Point4)
  simp
  norm_num
  done


-- Let us now consider a special kind of points.
def SpecialPoint := { p : Point4 // p.x ^2 + p.y ^2 + p.z ^ 2 + p.w ^ 2 = 1 }

-- We define "the same" operation on special points: complete the proof.
def op' (a b : SpecialPoint) : SpecialPoint := by
  refine ⟨op a.val b.val, ?_⟩
  have hmul :
      (op a.val b.val).x^2 + (op a.val b.val).y^2
    + (op a.val b.val).z^2 + (op a.val b.val).w^2
      =
      (a.val.x^2 + a.val.y^2 + a.val.z^2 + a.val.w^2) *
      (b.val.x^2 + b.val.y^2 + b.val.z^2 + b.val.w^2) := by
    simp [op] ; ring

  rw [a.property, b.property,one_mul] at hmul
  exact hmul


-- Prove that `SpecialPoint` with the operation `op'` is a group.
-- (If commutativity holds, it's even an abelian group. You don't need to prove this.)
-- Here is a definition of
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
noncomputable example : Group' SpecialPoint :=  {
  gop := op'
  assoc := by
    intro x y z
    unfold op'
    simp
    ring_nf
    done
  neutral := ⟨(⟨1, 0, 0, 0⟩ : Point4), by norm_num⟩
  gop_neutral := by
    intro x
    unfold op'
    simp
    rfl
    done
  inv a := (⟨(⟨a.val.x, -a.val.y, -a.val.z, -a.val.w⟩ : Point4), by
    simp; exact a.property ⟩ : SpecialPoint)
  gop_inv := by
    intro a
    unfold op'
    simp
    ring_nf
    simp [a.property]
}


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
structure StrictBipointed where
  α  : Type
  x₀ : α
  x₁ : α
  neq : x₀ ≠ x₁
-- state and prove the lemma here
lemma ne_left_or_ne_right  (x : StrictBipointed) :
  ∀z : x.α  , z ≠ x.x₀ ∨ z ≠ x.x₁ := by
  intro z
  by_cases hz0 : z = x.x₀
  right
  intro hz
  have h01 : x.x₀ = x.x₁ := by rw [← hz0, hz]
  exact x.neq h01
  left
  exact hz0

end Bipointed

section Subtypes

/-- Let's prove that the positive rationals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosRat : Type := {x : ℚ // 0 < x}

namespace PosRat

def gop (a b : PosRat) : PosRat :=
  ⟨a.1 * b.1, by exact mul_pos a.2 b.2⟩

def neutral : PosRat :=
  ⟨1, by exact rfl⟩

def inv (a : PosRat) : PosRat :=
  ⟨a.1⁻¹, by exact inv_pos.mpr a.2⟩

end PosRat

def groupPosRat : Group' PosRat :=
{ gop := PosRat.gop,
  assoc := by
    intro x y z
    apply Subtype.ext
    simp [PosRat.gop, mul_assoc],

  neutral := PosRat.neutral,

  gop_neutral := by
    intro x
    apply Subtype.ext
    simp [PosRat.gop, PosRat.neutral],

  inv := PosRat.inv,

  gop_inv := by
    intro x
    apply Subtype.ext
    have hx0 : (x.1) ≠ 0 := ne_of_gt x.2
    simp [PosRat.gop, PosRat.neutral, PosRat.inv, hx0] }
end Subtypes

section EquivalenceRelation

-- Prove that the following defines an equivalence relation.
def integerEquivalenceRelation : Setoid (ℤ × ℤ) where
  r := fun ⟨k, l⟩ ⟨m, n⟩ ↦ k + n = l + m
  iseqv :=
  by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro a; rcases a with ⟨k,l⟩
      simp [add_comm]
    · intro a b h; rcases a with ⟨k,l⟩; rcases b with ⟨m,n⟩

      simpa [add_comm] using h.symm
    · intro a b c h₁ h₂
      rcases a with ⟨k,l⟩; rcases b with ⟨m,n⟩; rcases c with ⟨p,q⟩

      have h₁' : k - l = m - n := by
        have := congrArg (fun t : ℤ => t + (-l) + (-n)) h₁
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have h₂' : m - n = p - q := by
        have := congrArg (fun t : ℤ => t + (-n) + (-q)) h₂
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have h := h₁'.trans h₂'
      have := congrArg (fun t : ℤ => t + l + q) h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using this

@[simp] lemma integerEquivalenceRelation'_iff (a b : ℤ × ℤ) :
  letI := integerEquivalenceRelation; a ≈ b ↔ a.1 + b.2 = a.2 + b.1 := by rfl

example : Quotient integerEquivalenceRelation ≃ ℤ :=
{ toFun :=
    Quot.lift (fun a : ℤ × ℤ => a.1 - a.2)
      (by
        intro a b h
        have := congrArg (fun t : ℤ => t + (-a.2) + (-b.2)) h
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this),
  invFun := fun z => Quot.mk _ ⟨z, 0⟩,
  left_inv := by
    refine Quot.ind ?_
    intro a
    apply Quot.sound
    change (a.1 - a.2) + a.2 = 0 + a.1
    simp [sub_eq_add_neg, add_comm, add_left_comm],
  right_inv := by
    intro z
    simp [sub_eq_add_neg]}


end EquivalenceRelation
