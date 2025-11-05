import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real
noncomputable section
variable (a b c : ℝ)

/-
# Practical remarks

* Assignment 3 was uploaded to ecampus yesterday: it is due next Monday (November 10).
* Assignment 4 will be upload on Thursday, as usual.
* The ecampus submission has been separated by tutorials: please submit your solutions
  in your corresponding tutorial.
* today's tutorial has been moved to Friday due to illness

-/


/- # Last time

* Sets
  - preimages `f ⁻¹' s` and images `f '' t` of sets
  - point-wise operations (e.g. the Minkowski sum)
  - writing enumerated sets `{1, 2, 3} : Set ℝ
* intervals: `Icc` and friends
  - "c" = closed, "o" = open, "i" = infinite
  - e.g., `Set.Ici a b = [a, ∞)` for `a b : ℝ`
  - e.g., `Set.Iio b   = (-∞, b)`

* useful tactics for dealing with numbers:
  - `norm_num`: compute equalities and inequalities involving numerals
  - `cutsat` can do linear arithmetic on `ℕ` and `ℤ`
  - `positivity`: can show that something is positive/non-negative
    by using that its components are positive/non-negative.
  - `field_simp` can simplify divisions.
* warning: subtraction and division of natural numbers returns a natural number!
* coercions (e.g., `(12 : ℚ) / 15` interprets 12 as a rational number),
  shown as `↑` in the infoview
* `norm_cast` pulls coercions out of an expression (e.g., turn `↑n * ↑m` into `↑(n * m)`),
  `push_cast` pushes them inside (e.g., turn `↑(n + m)` into `↑n + ↑m`)

* recursive functions (must be terminating)
* proofs by induction: `induction` tactic
  - `induction n generalizing m` generalises the inductive hypothesis,
  - `induction ... using ... with` allows using other induction principles
    (e.g., strong induction or two-step induction)

**Attention**: divisibility is written using `\|`, **not** the vertical bar on your keyboard.

-/

/- # Today: structures and classes -/


/-
# Structures and classes

Structures are used to build data and properties together.
For example in the structure below `Point` bundles three coordinates together.
-/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point




section

/- Given a point, we get access to its coordinates / projections. -/
variable (a : Point)
#check a.x
#check a.y
#check a.z
#check Point.x a

example : a.x = Point.x a := rfl

end





/- We can prove that two points are equal using the `ext` tactic. -/

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  sorry
  done

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  sorry
  done

#check Point.ext
#check Point.ext_iff

/- There are multiple ways to define a point (or more generally an instance of a structure).

Tip: if you write `_` for a Point, a lightbulb 💡 will appear.
Clicking it will give you the skeleton to write all fields. -/

def myPoint1 : Point where
  x := 1
  y := 2
  z := 3

def myPoint2 : Point := sorry

def myPoint3 : Point :=
 id {
   x := 1
   y := 2
   z := 3
 }

def myPoint4 : Point := ⟨1, 2, 3⟩

def myPoint5 := Point.mk 1 2 3



namespace Point

/- We can define operations on points, like addition. -/

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

def add' : Point → Point → Point :=
  fun ⟨ux, uy, uz⟩ ⟨vx, vy, vz⟩ ↦ ⟨ux + vx, uy + vy, uz + vz⟩

def add'' : Point → Point → Point
  | ⟨ux, uy, uz⟩, ⟨vx, vy, vz⟩ => ⟨ux + vx, uy + vy, uz + vz⟩

/- We define these operations in `namespace Point`.
This means that if this namespace is open we can write `add p q`.
If the namespace isn't open, we have to write `Point.add p q`.

In either case, we can use the *projection notation*,
`p.add q` where `p q : Point`.
Lean knows that we mean the function `Point.add`,
by looking at the type of `p`, which is `Point`. -/

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

/- You can *open* a namespace to shorten the names in it. -/
open Point

#check add myPoint1 myPoint2











namespace Point

/- We can prove properties about points. `protected` in the line below means that
even in the namespace `Point` we still have to write `Point.add_comm`
(the name is not shortened) -/

protected lemma add_comm (a b : Point) : add a b = add b a := by
  sorry

#check Point.add_comm

/- We can also state that we want to use the `+` notation here.
In that case, we have to write lemmas stating how `+` computes. -/

instance : Add Point := ⟨add⟩

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

example (a b : Point) : a + b = b + a := by
  sorry
  done

end Point





/- We can bundle properties in structures -/

structure PosPoint where
  x : ℝ
  y : ℝ
  z : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

def PointPoint.add (a b : PosPoint) : PosPoint :=
{ x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z
  x_pos := by sorry
  y_pos := by sorry
  z_pos := by sorry }

/- Going from `Point` to `PosPoint` has code duplication.
We don't want this when defining monoids, groups, rings, fields. -/

structure PosPoint' extends Point where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

#check PosPoint'.toPoint

def PointPoint'.add (a b : PosPoint') : PosPoint' where
  toPoint := a.toPoint + b.toPoint
  x_pos := by sorry
  y_pos := by sorry
  z_pos := by sorry

/- We could also define a type like this using a subtype. It's notation is very similar to sets,
but written as `{x : α // p x}` instead of `{x : α | p x}`.
We will learn about subtypes in more detail on Thursday. -/

def PosReal : Type :=
  { x : ℝ // x > 0 }

def set_of_positive_reals : Set ℝ :=
  { x : ℝ | x > 0 }

/- However, that doesn't give you nice projections names (automatically).
And it gets ugly when you have more than 2 projections. -/

example (x : PosReal) : x.1 > 0 := x.2

def PosPoint'' : Type :=
  { x : ℝ × (ℝ × ℝ) // x.1 > 0 ∧ x.2.1 > 0 ∧ x.2.2 > 0 }





/- Structures can have parameters -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

#check Triple.mk 1 2 3

#check Triple.mk cos sin tan










/- # Equiv

An important structure is equivalences between two types,
i.e. a bijection (with a chosen inverse).
This exists in the library as `Equiv α β` or `α ≃ β`.  -/

#check Equiv

example {α β : Type*} (e : α ≃ β) (x : α) : β := e.toFun x
example {α β : Type*} (e : α ≃ β) (x : α) : β := e x

example {α β : Type*} (e : α ≃ β) : β ≃ α := e.symm
example {α β : Type*} (e : α ≃ β) (y : β) : α := e.symm y





/- # Abelian groups
Let's define abelians group in Lean. -/

structure AbelianGroup where
  G : Type*
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg (x : G) : G
  add_neg : ∀ x : G, add x (neg x) = zero

def IntGroup : AbelianGroup where
  G := ℤ
  add a b := a + b
  comm := by sorry
  assoc := by sorry
  zero := 0
  add_zero := by sorry
  neg a := -a
  add_neg := by sorry

lemma AbelianGroup.zero_add (g : AbelianGroup) (x : g.G) :
    g.add g.zero x = x := by
  sorry




/-
Issues with this approach:
* we want a notation for `AbelianGroup.add` and `AbelianGroup.neg`.
* we want this to be automatically attached to certain concrete type such as `ℕ`, `ℝ`...
* we want that Lean knows that `G × G'` is an abelian group if `G` and `G'` are.

Using `class` instead of `structure` tells Lean to
create a database of "instances of this class".
The `instance` command allows to add entries to this database.
-/


class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

instance : AbelianGroup' ℤ where
  add := fun a b ↦ a + b
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg := fun a ↦ -a
  add_neg := by exact?

#eval AbelianGroup'.add (2 : ℤ) 5

infixl:70 " +' " => AbelianGroup'.add

#eval (-2) +' 5

notation " 𝟘 " => AbelianGroup'.zero

prefix:max "-'" => AbelianGroup'.neg

/- When you assume you have an object in a certain class, you put them in square brackets
(and giving a name to them is optional).
Such arguments are called instance-implicit arguments,
Lean will provide them automatically by searching the corresponding database.
-/

#check AbelianGroup'.add

instance AbelianGroup'.prod (G G' : Type*) [AbelianGroup' G] [AbelianGroup' G'] :
    AbelianGroup' (G × G') where
  add a b := (a.1 +' b.1, a.2 +' b.2)
  comm a b := by sorry
  assoc a b c := by sorry
  zero := (𝟘, 𝟘)
  add_zero a := by sorry
  neg a := sorry
  add_neg a := by sorry

/- Now Lean will figure out itself that `AbelianGroup' (ℤ × ℤ)`. -/
set_option trace.Meta.synthInstance true in
#check ((2, 3) : ℤ × ℤ) +' (4, 5)
