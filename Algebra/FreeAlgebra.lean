/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.FreeMonoid.UniqueProds
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Free Algebras

Given a commutative semiring `R`, and a type `X`, we construct the free unital, associative
`R`-algebra on `X`.

## Notation

1. `FreeAlgebra R X` is the free algebra itself. It is endowed with an `R`-algebra structure.
2. `FreeAlgebra.ι R` is the function `X → FreeAlgebra R X`.
3. Given a function `f : X → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
   `R`-algebra morphism `FreeAlgebra R X → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : FreeAlgebra R X → A` is
   given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
   of the composition of an algebra morphism with `ι` is the algebra morphism itself.
5. `equivMonoidAlgebraFreeMonoid : FreeAlgebra R X ≃ₐ[R] R[FreeMonoid X]`
6. An inductive principle `induction`.

## Implementation details

We construct the free algebra on `X` as a quotient of an inductive type `FreeAlgebra.Pre` by an
inductively defined relation `FreeAlgebra.Rel`. Explicitly, the construction involves three steps:
1. We construct an inductive type `FreeAlgebra.Pre R X`, the terms of which should be thought
   of as representatives for the elements of `FreeAlgebra R X`.
   It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
2. We construct an inductive relation `FreeAlgebra.Rel R X` on `FreeAlgebra.Pre R X`.
   This is the smallest relation for which the quotient is an `R`-algebra where addition resp.
   multiplication are induced by `add` resp. `mul` from 1., and for which the map from `R` is the
   structure map for the algebra.
3. The free algebra `FreeAlgebra R X` is the quotient of `FreeAlgebra.Pre R X` by
   the relation `FreeAlgebra.Rel R X`.
-/

@[expose] public section

open scoped MonoidAlgebra

variable (R X : Type*) [CommSemiring R]

namespace FreeAlgebra

/-- This inductive type is used to express representatives of the free algebra.
-/
/-
**FreeAlgebra.Pre** 是 Mathlib 中的一个归纳类型，位于命名空间 `FreeAlgebra`。
形式化陈述：Type u_1 → Type u_2 → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This inductive type is used to express representatives of the free algebra.
-/
inductive Pre
  | of : X → Pre
  | ofScalar : R → Pre
  | add : Pre → Pre → Pre
  | mul : Pre → Pre → Pre

namespace Pre

/-
**FreeAlgebra.Pre.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra.Pre`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Pre R X) := ⟨ofScalar 0⟩

-- Note: These instances are only used to simplify the notation.
/-- Coercion from `X` to `Pre R X`. Note: Used for notation only. -/
@[instance_reducible]
/-
**FreeAlgebra.Pre.hasCoeGenerator** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra.Pre`。
形式化陈述：hasCoeGenerator : Coe X (Pre R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `X` to `Pre R X`. Note: Used for notation only.
-/
def hasCoeGenerator : Coe X (Pre R X) := ⟨of⟩

/-- Coercion from `R` to `Pre R X`. Note: Used for notation only. -/
@[instance_reducible]
/-
**FreeAlgebra.Pre.hasCoeSemiring** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra.Pre`。
形式化陈述：hasCoeSemiring : Coe R (Pre R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `R` to `Pre R X`. Note: Used for notation only.
-/
def hasCoeSemiring : Coe R (Pre R X) := ⟨ofScalar⟩

/-- Multiplication in `Pre R X` defined as `Pre.mul`. Note: Used for notation only. -/
@[instance_reducible]
/-
**FreeAlgebra.Pre.hasMul** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra.Pre`。
形式化陈述：hasMul : Mul (Pre R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication in `Pre R X` defined as `Pre.mul`. Note: Used for notation only.
-/
def hasMul : Mul (Pre R X) := ⟨mul⟩

/-- Addition in `Pre R X` defined as `Pre.add`. Note: Used for notation only. -/
@[instance_reducible]
/-
**FreeAlgebra.Pre.hasAdd** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra.Pre`。
形式化陈述：hasAdd : Add (Pre R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition in `Pre R X` defined as `Pre.add`. Note: Used for notation only.
-/
def hasAdd : Add (Pre R X) := ⟨add⟩

/-- Zero in `Pre R X` defined as the image of `0` from `R`. Note: Used for notation only. -/
@[instance_reducible]
/-
**FreeAlgebra.Pre.hasZero** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra.Pre`。
形式化陈述：hasZero : Zero (Pre R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Zero in `Pre R X` defined as the image of `0` from `R`. Note: Used for notation 
only.
-/
def hasZero : Zero (Pre R X) := ⟨ofScalar 0⟩

/-- One in `Pre R X` defined as the image of `1` from `R`. Note: Used for notation only. -/
@[instance_reducible]
/-
**FreeAlgebra.Pre.hasOne** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra.Pre`。
形式化陈述：hasOne : One (Pre R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One in `Pre R X` defined as the image of `1` from `R`. Note: Used for notation o
nly.
-/
def hasOne : One (Pre R X) := ⟨ofScalar 1⟩

/-- Scalar multiplication defined as multiplication by the image of elements from `R`.
Note: Used for notation only.
-/
@[instance_reducible]
/-
**FreeAlgebra.Pre.hasSMul** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra.Pre`。
形式化陈述：hasSMul : SMul R (Pre R X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication defined as multiplication by the image of elements from `R
`.
Note: Used for notation only.
-/
def hasSMul : SMul R (Pre R X) := ⟨fun r m ↦ mul (ofScalar r) m⟩

end Pre

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSMul

/-- Given a function from `X` to an `R`-algebra `A`, `lift_fun` provides a lift of `f` to a function
from `Pre R X` to `A`. This is mainly used in the construction of `FreeAlgebra.lift`. -/
/-
**FreeAlgebra.liftFun** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra`。
形式化陈述：(R : Type u_1) →   (X : Type u_2) →     [inst : CommSemiring R] → {A : Typ
e u_3} → [inst_1 : Semiring A] → [Algebra R A] → (X → A) → FreeAlgebra.Pre R X →
 A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function from `X` to an `R`-algebra `A`, `lift_fun` provides a lift of `
f` to a function
from `Pre R X` to `A`. This is mainly used in the construction of `FreeAlgebra.l
ift`.
-/
def liftFun {A : Type*} [Semiring A] [Algebra R A] (f : X → A) :
    Pre R X → A
  | .of t => f t
  | .add a b => liftFun f a + liftFun f b
  | .mul a b => liftFun f a * liftFun f b
  | .ofScalar c => algebraMap _ _ c

/-- An inductively defined relation on `Pre R X` used to force the initial algebra structure on
the associated quotient.
-/
/-
**FreeAlgebra.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `FreeAlgebra`。
形式化陈述：(R : Type u_1) → (X : Type u_2) → [CommSemiring R] → FreeAlgebra.Pre R X →
 FreeAlgebra.Pre R X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inductively defined relation on `Pre R X` used to force the initial algebra s
tructure on
the associated quotient.
-/
inductive Rel : Pre R X → Pre R X → Prop
  -- force `ofScalar` to be a central semiring morphism
  | add_scalar {r s : R} : Rel (↑(r + s)) (↑r + ↑s)
  | mul_scalar {r s : R} : Rel (↑(r * s)) (↑r * ↑s)
  | central_scalar {r : R} {a : Pre R X} : Rel (r * a) (a * r)
  -- commutative additive semigroup
  | add_assoc {a b c : Pre R X} : Rel (a + b + c) (a + (b + c))
  | add_comm {a b : Pre R X} : Rel (a + b) (b + a)
  | zero_add {a : Pre R X} : Rel (0 + a) a
  -- multiplicative monoid
  | mul_assoc {a b c : Pre R X} : Rel (a * b * c) (a * (b * c))
  | one_mul {a : Pre R X} : Rel (1 * a) a
  | mul_one {a : Pre R X} : Rel (a * 1) a
  -- distributivity
  | left_distrib {a b c : Pre R X} : Rel (a * (b + c)) (a * b + a * c)
  | right_distrib {a b c : Pre R X} :
      Rel ((a + b) * c) (a * c + b * c)
  -- other relations needed for semiring
  | zero_mul {a : Pre R X} : Rel (0 * a) 0
  | mul_zero {a : Pre R X} : Rel (a * 0) 0
  -- compatibility
  | add_compat_left {a b c : Pre R X} : Rel a b → Rel (a + c) (b + c)
  | add_compat_right {a b c : Pre R X} : Rel a b → Rel (c + a) (c + b)
  | mul_compat_left {a b c : Pre R X} : Rel a b → Rel (a * c) (b * c)
  | mul_compat_right {a b c : Pre R X} : Rel a b → Rel (c * a) (c * b)

end FreeAlgebra

/--
If `α` is a type, and `R` is a commutative semiring, then `FreeAlgebra R α` is the
free (unital, associative) `R`-algebra generated by `α`.
This is an `R`-algebra equipped with a function `FreeAlgebra.ι R : α → FreeAlgebra R α` which has
the following universal property: if `A` is any `R`-algebra, and `f : α → A` is any function,
then this function is the composite of `FreeAlgebra.ι R` and a unique `R`-algebra homomorphism
`FreeAlgebra.lift R f : FreeAlgebra R α →ₐ[R] A`.

A typical element of `FreeAlgebra R α` is an `R`-linear
combination of formal products of elements of `α`.
For example if `x` and `y` are terms of type `α` and `a`, `b` are terms of type `R` then
`(3 * a * a) • (x * y * x) + (2 * b + 1) • (y * x) + (a * b * b + 3)` is a
"typical" element of `FreeAlgebra R α`. In particular if `α` is empty
then `FreeAlgebra R α` is isomorphic to `R`, and if `α` has one term `t`
then `FreeAlgebra R α` is isomorphic to the polynomial ring `R[t]`.
If `α` has two or more terms then `FreeAlgebra R α` is not commutative.
One can think of `FreeAlgebra R α` as the free non-commutative polynomial ring
with coefficients in `R` and variables indexed by `α`.
-/
/-
**FreeAlgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeAlgebra
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a type, and `R` is a commutative semiring, then `FreeAlgebra R α` is t
he
free (unital, associative) `R`-algebra generated by `α`.
This is an `R`-algebra equipped with a function `FreeAlgebra.ι R : α → FreeAlgeb
ra R α` which has
the following universal property: if `A` is any `R`-algebra, and `f : α → A` is 
any function,
then this function is the composite of `FreeAlgebra.ι R` and a unique `R`-algebr
a homomorphism
`FreeAlgebra.lift R f : FreeAlgebra R α →ₐ[R] A`.

A typical element of `FreeAlgebra R α` is an `R`-linear
combination of formal products of elements of `α`.
For example if `x` and `y` are terms of type `α` and `a`, `b` are terms of type 
`R` then
`(3 * a * a) • (x * y * x) + (2 * b + 1) • (y * x) + (a * b * b + 3)` is a
"typical" element of `FreeAlgebra R α`. In particular if `α` is empty
then `FreeAlgebra R α` is isomorphic to `R`, and if `α` has one term `t`
then `FreeAlgebra R α` is isomorphic to the polynomial ring `R[t]`.
If `α` has two or more terms then `FreeAlgebra R α` is not commutative.
One can think of `FreeAlgebra R α` as the free non-commutative polynomial ring
with coefficients in `R` and variables indexed by `α`.
-/
def FreeAlgebra :=
  Quot (FreeAlgebra.Rel R X)

namespace FreeAlgebra

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSMul

/-! Define the basic operations -/

/-
**FreeAlgebra.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instSMul {A} [CommSemiring A] [Algebra R A] : SMul R (FreeAlgebra A X) whe
re smul r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the basic operations
-/
instance instSMul {A} [CommSemiring A] [Algebra R A] : SMul R (FreeAlgebra A X) where
  smul r := Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ ↦ Rel.mul_compat_right
/-
**FreeAlgebra.instZero** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instZero : Zero (FreeAlgebra R X) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (FreeAlgebra R X) where zero := Quot.mk _ 0
/-
**FreeAlgebra.instOne** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instOne : One (FreeAlgebra R X) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (FreeAlgebra R X) where one := Quot.mk _ 1
/-
**FreeAlgebra.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instAdd : Add (FreeAlgebra R X) where add
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (FreeAlgebra R X) where
  add := Quot.map₂ HAdd.hAdd (fun _ _ _ ↦ Rel.add_compat_right) fun _ _ _ ↦ Rel.add_compat_left
/-
**FreeAlgebra.instMul** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instMul : Mul (FreeAlgebra R X) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (FreeAlgebra R X) where
  mul := Quot.map₂ HMul.hMul (fun _ _ _ ↦ Rel.mul_compat_right) fun _ _ _ ↦ Rel.mul_compat_left

-- `Quot.mk` is an implementation detail of `FreeAlgebra`, so this lemma is private
/-
**FreeAlgebra.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mk_mul (x y : Pre R X) :
    Quot.mk (Rel R X) (x * y) = (HMul.hMul (self := instHMul (α := FreeAlgebra R X))
    (Quot.mk (Rel R X) x) (Quot.mk (Rel R X) y)) :=
  rfl

/-! Build the semiring structure. We do this one piece at a time as this is convenient for proving
the `nsmul` fields. -/

/-
**FreeAlgebra.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instMonoidWithZero : MonoidWithZero (FreeAlgebra R X) where mul_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build the semiring structure. We do this one piece at a time as this is convenie
nt for proving
the `nsmul` fields.
-/
instance instMonoidWithZero : MonoidWithZero (FreeAlgebra R X) where
  mul_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.mul_assoc
  one_mul := by
    rintro ⟨⟩
    exact Quot.sound Rel.one_mul
  mul_one := by
    rintro ⟨⟩
    exact Quot.sound Rel.mul_one
  zero_mul := by
    rintro ⟨⟩
    exact Quot.sound Rel.zero_mul
  mul_zero := by
    rintro ⟨⟩
    exact Quot.sound Rel.mul_zero
/-
**FreeAlgebra.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instDistrib : Distrib (FreeAlgebra R X) where left_distrib
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistrib : Distrib (FreeAlgebra R X) where
  left_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.left_distrib
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.right_distrib

set_option backward.isDefEq.respectTransparency false in
/-
**FreeAlgebra.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instAddCommMonoid : AddCommMonoid (FreeAlgebra R X) where add_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (FreeAlgebra R X) where
  add_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.add_assoc
  zero_add := by
    rintro ⟨⟩
    exact Quot.sound Rel.zero_add
  add_zero := by
    rintro ⟨⟩
    change Quot.mk _ _ = _
    rw [Quot.sound Rel.add_comm, Quot.sound Rel.zero_add]
  add_comm := by
    rintro ⟨⟩ ⟨⟩
    exact Quot.sound Rel.add_comm
  nsmul_zero := by
    rintro ⟨⟩
    change Quot.mk _ (_ * _) = _
    rw [map_zero]
    exact Quot.sound Rel.zero_mul
  nsmul_succ n := by
    rintro ⟨a⟩
    dsimp only [HSMul.hSMul, SMul.smul, NSMul.nsmul, Quot.map]
    rw [map_add, map_one, mk_mul, mk_mul, ← add_one_mul (_ : FreeAlgebra R X)]
    congr 1
    exact Quot.sound Rel.add_scalar
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring (FreeAlgebra R X) where
  __ := instMonoidWithZero R X
  __ := instAddCommMonoid R X
  __ := instDistrib R X
  natCast n := Quot.mk _ (n : R)
  natCast_zero := by simp; rfl
  natCast_succ n := by simpa using! Quot.sound Rel.add_scalar
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FreeAlgebra R X) :=
  ⟨0⟩
/-
**FreeAlgebra.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instAlgebra {A} [CommSemiring A] [Algebra R A] : Algebra R (FreeAlgebra A 
X) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra {A} [CommSemiring A] [Algebra R A] : Algebra R (FreeAlgebra A X) where
  algebraMap := ({
      toFun := fun r => Quot.mk _ r
      map_one' := rfl
      map_mul' := fun _ _ => Quot.sound Rel.mul_scalar
      map_zero' := rfl
      map_add' := fun _ _ => Quot.sound Rel.add_scalar } : A →+* FreeAlgebra A X).comp
      (algebraMap R A)
  commutes' _ := by
    rintro ⟨⟩
    exact Quot.sound Rel.central_scalar
  smul_def' _ _ := rfl

-- verify there is no diamond at `default` transparency but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
variable (S : Type) [CommSemiring S] in
/-
**FreeAlgebra.** 是 Mathlib 中的一个示例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Semiring.toNatAlgebra : Algebra ℕ (FreeAlgebra S X)) = instAlgebra _ _ := rfl
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [SMul R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S (FreeAlgebra A X) where
  smul_assoc r s x := by
    change algebraMap S A (r • s) • x = algebraMap R A _ • (algebraMap S A _ • x)
    rw [← smul_assoc]
    congr
    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
    rw [smul_assoc, ← smul_one_mul]
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A] [Algebra R A] [Algebra S A] :
    SMulCommClass R S (FreeAlgebra A X) where
  smul_comm r s x := smul_comm (algebraMap R A r) (algebraMap S A s) x
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommRing S] : Ring (FreeAlgebra S X) :=
  Algebra.semiringToRing S

-- verify there is no diamond but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
variable (S : Type) [CommRing S] in
/-
**FreeAlgebra.** 是 Mathlib 中的一个示例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Ring.toIntAlgebra _ : Algebra ℤ (FreeAlgebra S X)) = instAlgebra _ _ := rfl

variable {X}

/-- The canonical function `X → FreeAlgebra R X`.
-/
irreducible_def ι : X → FreeAlgebra R X := fun m ↦ Quot.mk _ m

@[simp]
/-
**FreeAlgebra.quot_mk_eq_** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_ι (m : X) : Quot.mk (FreeAlgebra.Rel R X) m = ι R m := by rw [ι_def]

variable {A : Type*} [Semiring A] [Algebra R A]

set_option backward.privateInPublic true in
/-- Internal definition used to define `lift` -/
/-
**FreeAlgebra.liftAux** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Internal definition used to define `lift`
-/
private def liftAux (f : X → A) : FreeAlgebra R X →ₐ[R] A where
  toFun a :=
    Quot.liftOn a (liftFun _ _ f) fun a b h ↦ by
      induction h
      · exact (algebraMap R A).map_add _ _
      · exact (algebraMap R A).map_mul _ _
      · apply Algebra.commutes
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assoc]
      · change _ + _ = _ + _
        rw [add_comm]
      · change algebraMap _ _ _ + liftFun R X f _ = liftFun R X f _
        simp
      · change _ * _ * _ = _ * (_ * _)
        rw [mul_assoc]
      · change algebraMap _ _ _ * liftFun R X f _ = liftFun R X f _
        simp
      · change liftFun R X f _ * algebraMap _ _ _ = liftFun R X f _
        simp
      · change _ * (_ + _) = _ * _ + _ * _
        rw [left_distrib]
      · change (_ + _) * _ = _ * _ + _ * _
        rw [right_distrib]
      · change algebraMap _ _ _ * _ = algebraMap _ _ _
        simp
      · change _ * algebraMap _ _ _ = algebraMap _ _ _
        simp
      repeat
        change liftFun R X f _ + liftFun R X f _ = _
        simp only [*]
        rfl
      repeat
        change liftFun R X f _ * liftFun R X f _ = _
        simp only [*]
        rfl
  map_one' := by
    change algebraMap _ _ _ = _
    simp
  map_mul' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  map_zero' := by
    change algebraMap _ _ _ = _
    simp
  map_add' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  commutes' := by tauto

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `FreeAlgebra R X → A`. -/
@[irreducible]
/-
**FreeAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra`。
形式化陈述：lift : (X -> A) ≃ (FreeAlgebra R X ->ₐ[R] A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the uniq
ue lift
of `f` to a morphism of `R`-algebras `FreeAlgebra R X → A`.
-/
def lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A) :=
  { toFun := liftAux R
    invFun := fun F ↦ F ∘ ι R
    left_inv := fun f ↦ by
      ext
      simp only [Function.comp_apply, ι_def]
      rfl
    right_inv := fun F ↦ by
      ext t
      rcases t with ⟨x⟩
      induction x with
      | of =>
        change ((F : FreeAlgebra R X → A) ∘ ι R) _ = _
        simp only [Function.comp_apply, ι_def]
      | ofScalar x =>
        change algebraMap _ _ x = F (algebraMap _ _ x)
        rw [AlgHom.commutes F _]
      | add a b ha hb =>
        -- Porting note: it is necessary to declare fa and fb explicitly otherwise Lean refuses
        -- to consider `Quot.mk (Rel R X) ·` as element of FreeAlgebra R X
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa + fb) = F (fa + fb)
        grind
      | mul a b ha hb =>
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa * fb) = F (fa * fb)
        grind }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**FreeAlgebra.liftAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：liftAux_eq (f : X -> A) : liftAux R f = lift R f
参数：f : X -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAlgebra.lift.eq_1`：∀ (R : Type u_1) {X : Type u_2} [inst : CommSemir
ing R] {A : Type u_3} [inst_1 : Semiring A] [inst_2 : Algebra R A],   FreeAlgebr
a.lift R = …
-/
theorem liftAux_eq (f : X → A) : liftAux R f = lift R f := by
  rw [lift]
  rfl

@[simp]
/-
**FreeAlgebra.lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：lift_symm_apply (F : FreeAlgebra R X ->ₐ[R] A) : (lift R).symm F = F ∘ ι R
参数：F : FreeAlgebra R X ->ₐ[R] A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAlgebra.lift.eq_1`：∀ (R : Type u_1) {X : Type u_2} [inst : CommSemir
ing R] {A : Type u_3} [inst_1 : Semiring A] [inst_2 : Algebra R A],   FreeAlgebr
a.lift R = …
-/
theorem lift_symm_apply (F : FreeAlgebra R X →ₐ[R] A) : (lift R).symm F = F ∘ ι R := by
  rw [lift]
  rfl

variable {R}

@[simp]
/-
**FreeAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_lift (f : X → A) : (lift R f : FreeAlgebra R X → A) ∘ ι R = f := by
  ext
  rw [Function.comp_apply, ι_def, lift]
  rfl

@[simp]
/-
**FreeAlgebra.lift_** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_ι_apply (f : X → A) (x) : lift R f (ι R x) = f x := by
  rw [ι_def, lift]
  rfl

@[simp]
/-
**FreeAlgebra.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：lift_unique (f : X -> A) (g : FreeAlgebra R X ->ₐ[R] A) : (g : FreeAlgebra
 R X -> A) ∘ ι R = f ↔ g = lift R f
参数：f : X -> A；g : FreeAlgebra R X ->ₐ[R] A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `FreeAlgebra.lift.eq_1`：∀ (R : Type u_1) {X : Type u_2} [inst : CommSemir
ing R] {A : Type u_3} [inst_1 : Semiring A] [inst_2 : Algebra R A],   FreeAlgebr
a.lift R = …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_unique (f : X → A) (g : FreeAlgebra R X →ₐ[R] A) :
    (g : FreeAlgebra R X → A) ∘ ι R = f ↔ g = lift R f := by
  rw [← (lift R).symm_apply_eq, lift]
  rfl

/-!
Since we have set the basic definitions as `@[Irreducible]`, from this point onwards one
should only use the universal properties of the free algebra, and consider the actual implementation
as a quotient of an inductive type as completely hidden. -/


-- Marking `FreeAlgebra` irreducible makes `Ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.
@[simp]
/-
**FreeAlgebra.lift_comp_** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_ι (g : FreeAlgebra R X →ₐ[R] A) :
    lift R ((g : FreeAlgebra R X → A) ∘ ι R) = g := by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**FreeAlgebra.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：hom_ext {f g : FreeAlgebra R X ->ₐ[R] A} (w : (f : FreeAlgebra R X -> A) ∘
 ι R = (g : FreeAlgebra R X -> A) ∘ ι R) : f = g
参数：w : (f : FreeAlgebra R X -> A) ∘ ι R = (g : FreeAlgebra R X -> A) ∘ ι R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeAlgebra.lift_symm_apply`：lift_symm_apply (F : FreeAlgebra R X ->ₐ[R]
 A) : (lift R).symm F = F ∘ ι R

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem hom_ext {f g : FreeAlgebra R X →ₐ[R] A}
    (w : (f : FreeAlgebra R X → A) ∘ ι R = (g : FreeAlgebra R X → A) ∘ ι R) : f = g := by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  exact (lift R).symm.injective w

/-- The free algebra on `X` is "just" the monoid algebra on the free monoid on `X`.

This would be useful when constructing linear maps out of a free algebra,
for example.
-/
/-
**FreeAlgebra.equivMonoidAlgebraFreeMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebr
a`。
形式化陈述：equivMonoidAlgebraFreeMonoid : FreeAlgebra R X ≃ₐ[R] R[FreeMonoid X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free algebra on `X` is "just" the monoid algebra on the free monoid on `X`.

This would be useful when constructing linear maps out of a free algebra,
for example.
-/
noncomputable def equivMonoidAlgebraFreeMonoid : FreeAlgebra R X ≃ₐ[R] R[FreeMonoid X] :=
  .ofAlgHom (lift R fun x ↦ .of R (FreeMonoid X) (.of x))
    (MonoidAlgebra.lift R (FreeAlgebra R X) (FreeMonoid X) (FreeMonoid.lift (ι R)))
    (MonoidAlgebra.algHom_ext' (by ext; simp) (by ext)) (by ext; simp)

/-- `FreeAlgebra R X` is nontrivial when `R` is. -/
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FreeAlgebra R X` is nontrivial when `R` is.
-/
instance [Nontrivial R] : Nontrivial (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.surjective.nontrivial

/-- `FreeAlgebra R X` has no zero-divisors when `R` has no zero-divisors. -/
/-
**FreeAlgebra.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instNoZeroDivisors [NoZeroDivisors R] : NoZeroDivisors (FreeAlgebra R X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.noZeroDivisors`：∀ {A : Type u_7} (B : Type u_8) [inst : MulZero
Class A] [inst_1 : MulZeroClass B] [NoZeroDivisors B] (e : A ≃* B),   NoZeroDivi
sors A
· 使用定理 `MonoidAlgebra.instNoZeroDivisorsOfUniqueProds`：∀ {R : Type u_1} {A : Typ
e u_2} [inst : Semiring R] [NoZeroDivisors R] [inst_2 : Mul A] [UniqueProds A], 
  NoZeroDivisors (MonoidAlgebra R A…
· 使用定理 `TwoUniqueProds.toUniqueProds`：∀ (G : Type u_1) [inst : Mul G] [TwoUnique
Prods G], UniqueProds G

--- 原说明 ---
`FreeAlgebra R X` has no zero-divisors when `R` has no zero-divisors.
-/
instance instNoZeroDivisors [NoZeroDivisors R] : NoZeroDivisors (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.toMulEquiv.noZeroDivisors

/-- `FreeAlgebra R X` is a domain when `R` is an integral domain. -/
/-
**FreeAlgebra.instIsDomain** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
形式化陈述：instIsDomain {R X} [CommRing R] [IsDomain R] : IsDomain (FreeAlgebra R X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `FreeAlgebra.instNontrivial`：∀ {R : Type u_1} {X : Type u_2} [inst : Comm
Semiring R] [Nontrivial R], Nontrivial (FreeAlgebra R X)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
`FreeAlgebra R X` is a domain when `R` is an integral domain.
-/
instance instIsDomain {R X} [CommRing R] [IsDomain R] : IsDomain (FreeAlgebra R X) :=
  NoZeroDivisors.to_isDomain _

section

/-- The left-inverse of `algebraMap`. -/
/-
**FreeAlgebra.algebraMapInv** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra`。
形式化陈述：algebraMapInv : FreeAlgebra R X ->ₐ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left-inverse of `algebraMap`.
-/
def algebraMapInv : FreeAlgebra R X →ₐ[R] R :=
  lift R (0 : X → R)
/-
**FreeAlgebra.algebraMap_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：algebraMap_leftInverse : Function.LeftInverse algebraMapInv (algebraMap R 
<| FreeAlgebra R X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X) := fun x ↦ by
  simp

@[simp]
/-
**FreeAlgebra.algebraMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：algebraMap_inj (x y : R) : algebraMap R (FreeAlgebra R X) x = algebraMap R
 (FreeAlgebra R X) y ↔ x = y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `FreeAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Function.Le
ftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X)
-/
theorem algebraMap_inj (x y : R) :
    algebraMap R (FreeAlgebra R X) x = algebraMap R (FreeAlgebra R X) y ↔ x = y :=
  algebraMap_leftInverse.injective.eq_iff

@[simp]
/-
**FreeAlgebra.algebraMap_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：algebraMap_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x 
= 0
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `FreeAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Function.Le
ftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X)
-/
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) algebraMap_leftInverse.injective

@[simp]
/-
**FreeAlgebra.algebraMap_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：algebraMap_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x =
 1
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `FreeAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Function.Le
ftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X)
-/
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) algebraMap_leftInverse.injective

-- this proof is copied from the approach in `FreeAbelianGroup.of_injective`
/-
**FreeAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_injective [Nontrivial R] : Function.Injective (ι R : X → FreeAlgebra R X) :=
  fun x y hoxy ↦
  by_contradiction <| by
    classical exact fun hxy : x ≠ y ↦
        let f : FreeAlgebra R X →ₐ[R] R := lift R fun z ↦ if x = z then (1 : R) else 0
        have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans <| if_pos rfl
        have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
        have hfy0 : f (ι R y) = 0 := (lift_ι_apply _ _).trans <| if_neg hxy
        one_ne_zero <| hfy1.symm.trans hfy0

@[simp]
/-
**FreeAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_inj [Nontrivial R] (x y : X) : ι R x = ι R y ↔ x = y :=
  ι_injective.eq_iff

@[simp]
/-
**FreeAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_ne_algebraMap [Nontrivial R] (x : X) (r : R) : ι R x ≠ algebraMap R _ r := fun h ↦ by
  let f0 : FreeAlgebra R X →ₐ[R] R := lift R 0
  let f1 : FreeAlgebra R X →ₐ[R] R := lift R 1
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  rw [h, f0.commutes, Algebra.algebraMap_self_apply] at hf0
  rw [h, f1.commutes, Algebra.algebraMap_self_apply] at hf1
  exact zero_ne_one (hf0.symm.trans hf1)

@[simp]
/-
**FreeAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_ne_zero [Nontrivial R] (x : X) : ι R x ≠ 0 :=
  ι_ne_algebraMap x 0

@[simp]
/-
**FreeAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_ne_one [Nontrivial R] (x : X) : ι R x ≠ 1 :=
  ι_ne_algebraMap x 1

end

end FreeAlgebra

/- There is something weird in the above namespace that breaks the typeclass resolution of
`CoeSort` below. Closing it and reopening it fixes it... -/
namespace FreeAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- An induction principle for the free algebra.

If `C` holds for the `algebraMap` of `r : R` into `FreeAlgebra R X`, the `ι` of `x : X`, and is
preserved under addition and multiplication, then it holds for all of `FreeAlgebra R X`.
-/
@[elab_as_elim, induction_eliminator]
/-
**FreeAlgebra.induction** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：induction {motive : FreeAlgebra R X -> Prop} (grade0 : forall r, motive (a
lgebraMap R (FreeAlgebra R X) r)) (grade1 : forall x, motive (ι R x)) (mul : for
all a b, motive a -> motive b -> motive (a * b)) (add : forall a b, motive a -> 
motive b -> motive (a + b)) (a : FreeAlgebra R X) : motive a
参数：grade0 : forall r, motive (algebraMap R (FreeAlgebra R X) r)；grade1 : forall 
x, motive (ι R x)；mul : forall a b, motive a -> motive b -> motive (a * b)；add :
 forall a b, motive a -> motive b -> motive (a + b)；a : FreeAlgebra R X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `FreeAlgebra.hom_ext`：hom_ext {f g : FreeAlgebra R X ->ₐ[R] A} (w : (f : 
FreeAlgebra R X -> A) ∘ ι R = (g : FreeAlgebra R X -> A) ∘ ι R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAlgebra.lift_ι_apply`：lift_ι_apply (f : X -> A) (x) : lift R f (ι R 
x) = f x
· 使用定理 `Subtype.coind_coe`：∀ {α : Sort u_4} {β : Sort u_5} (f : α → β) {p : β → 
Prop} (h : ∀ (a : α), p (f a)) (a : α),   ↑(Subtype.coind f h a) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
An induction principle for the free algebra.

If `C` holds for the `algebraMap` of `r : R` into `FreeAlgebra R X`, the `ι` of 
`x : X`, and is
preserved under addition and multiplication, then it holds for all of `FreeAlgeb
ra R X`.
-/
theorem induction {motive : FreeAlgebra R X → Prop}
    (grade0 : ∀ r, motive (algebraMap R (FreeAlgebra R X) r)) (grade1 : ∀ x, motive (ι R x))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (a : FreeAlgebra R X) : motive a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := {x | motive x}
      mul_mem' := mul _ _
      add_mem' := add _ _
      algebraMap_mem' := grade0 }
  let of : X → s := Subtype.coind (ι R) grade1
  -- the mapping through the subalgebra is the identity
  have of_id : AlgHom.id R (FreeAlgebra R X) = s.val.comp (lift R of) := by
    ext
    simp [of]
  -- finding a proof is finding an element of the subalgebra
  suffices a = lift R of a by
    rw [this]
    exact Subtype.prop (lift R of a)
  simp only [AlgHom.ext_iff, AlgHom.coe_id, id_eq, AlgHom.coe_comp, Subalgebra.coe_val,
    Function.comp_apply] at of_id
  exact of_id a

@[simp]
/-
**FreeAlgebra.adjoin_range_** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R : X → FreeAlgebra R X)) = ⊤ := by
  set S := Algebra.adjoin R (Set.range (ι R : X → FreeAlgebra R X))
  refine top_unique fun x hx => ?_; clear hx
  induction x with
  | grade0 => exact S.algebraMap_mem _
  | add x y hx hy => exact S.add_mem hx hy
  | mul x y hx hy => exact S.mul_mem hx hy
  | grade1 x => exact Algebra.subset_adjoin (Set.mem_range_self _)

variable {A : Type*} [Semiring A] [Algebra R A]

/-- Noncommutative version of `Algebra.adjoin_range_eq_range_aeval`. -/
/-
**FreeAlgebra._root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift** 是 Mathlib 
中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncommutative version of `Algebra.adjoin_range_eq_range_aeval`.
-/
theorem _root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift (f : X → A) :
    Algebra.adjoin R (Set.range f) = (FreeAlgebra.lift R f).range := by
  simp only [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

/-- Noncommutative version of `Algebra.adjoin_range_eq_range`. -/
/-
**FreeAlgebra._root_.Algebra.adjoin_eq_range_freeAlgebra_lift** 是 Mathlib 中的一个定理
，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncommutative version of `Algebra.adjoin_range_eq_range`.
-/
theorem _root_.Algebra.adjoin_eq_range_freeAlgebra_lift (s : Set A) :
    Algebra.adjoin R s = (FreeAlgebra.lift R ((↑) : s → A)).range := by
  rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift, Subtype.range_coe]

end FreeAlgebra

