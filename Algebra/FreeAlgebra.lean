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

/--
Inductive type `Pre` / 归纳类型 `Pre`

English:
inductive Pre
  constructors (4):
    - of: X -> Pre
    - ofScalar: R -> Pre
    - add: Pre -> Pre -> Pre
    - mul: Pre -> Pre -> Pre

中文:
归纳类型 Pre
  构造子 (4 个):
    - of: X -> Pre
    - ofScalar: R -> Pre
    - add: Pre -> Pre -> Pre
    - mul: Pre -> Pre -> Pre
-/
inductive Pre
  | of : X -> Pre
  | ofScalar : R -> Pre
  | add : Pre -> Pre -> Pre
  | mul : Pre -> Pre -> Pre

namespace Pre

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Pre R X)
  body: ⟨ofScalar 0⟩

中文:
实例 :
  签名: 可居 (Pre R X)
  定义体: ⟨ofScalar 0⟩

Depends on / 依赖: ofScalar
-/
instance : Inhabited (Pre R X) := ⟨ofScalar 0⟩

-- Note: These instances are only used to simplify the notation.
/-- Coercion from `X` to `Pre R X`. Note: Used for notation only. -/
@[instance_reducible]
/--
Definition of `hasCoeGenerator` / `hasCoeGenerator` 的定义

English:
definition hasCoeGenerator
  signature: : Coe X (Pre R X)
  body: ⟨of⟩

中文:
定义 hasCoeGenerator
  签名: : Coe X (Pre R X)
  定义体: ⟨of⟩
-/
def hasCoeGenerator : Coe X (Pre R X) := ⟨of⟩

/-- Coercion from `R` to `Pre R X`. Note: Used for notation only. -/
@[instance_reducible]
/--
Definition of `hasCoeSemiring` / `hasCoeSemiring` 的定义

English:
definition hasCoeSemiring
  signature: : Coe R (Pre R X)
  body: ⟨ofScalar⟩

中文:
定义 hasCoeSemiring
  签名: : Coe R (Pre R X)
  定义体: ⟨ofScalar⟩

Depends on / 依赖: ofScalar
-/
def hasCoeSemiring : Coe R (Pre R X) := ⟨ofScalar⟩

/-- Multiplication in `Pre R X` defined as `Pre.mul`. Note: Used for notation only. -/
@[instance_reducible]
/--
Definition of `hasMul` / `hasMul` 的定义

English:
definition hasMul
  signature: : Mul (Pre R X)
  body: ⟨mul⟩

中文:
定义 hasMul
  签名: : 乘法 (Pre R X)
  定义体: ⟨mul⟩
-/
def hasMul : Mul (Pre R X) := ⟨mul⟩

/-- Addition in `Pre R X` defined as `Pre.add`. Note: Used for notation only. -/
@[instance_reducible]
/--
Definition of `hasAdd` / `hasAdd` 的定义

English:
definition hasAdd
  signature: : Add (Pre R X)
  body: ⟨add⟩

中文:
定义 hasAdd
  签名: : 加法 (Pre R X)
  定义体: ⟨add⟩
-/
def hasAdd : Add (Pre R X) := ⟨add⟩

/-- Zero in `Pre R X` defined as the image of `0` from `R`. Note: Used for notation only. -/
@[instance_reducible]
/--
Definition of `hasZero` / `hasZero` 的定义

English:
definition hasZero
  signature: : Zero (Pre R X)
  body: ⟨ofScalar 0⟩

中文:
定义 hasZero
  签名: : 零 (Pre R X)
  定义体: ⟨ofScalar 0⟩

Depends on / 依赖: ofScalar
-/
def hasZero : Zero (Pre R X) := ⟨ofScalar 0⟩

/-- One in `Pre R X` defined as the image of `1` from `R`. Note: Used for notation only. -/
@[instance_reducible]
/--
Definition of `hasOne` / `hasOne` 的定义

English:
definition hasOne
  signature: : One (Pre R X)
  body: ⟨ofScalar 1⟩

中文:
定义 hasOne
  签名: : 幺 (Pre R X)
  定义体: ⟨ofScalar 1⟩

Depends on / 依赖: ofScalar
-/
def hasOne : One (Pre R X) := ⟨ofScalar 1⟩

/-- Scalar multiplication defined as multiplication by the image of elements from `R`.
Note: Used for notation only.
-/
@[instance_reducible]
/--
Definition of `hasSMul` / `hasSMul` 的定义

English:
definition hasSMul
  signature: : SMul R (Pre R X)
  body: ⟨fun r m => mul (ofScalar r) m⟩

中文:
定义 hasSMul
  签名: : 标量乘法 R (Pre R X)
  定义体: ⟨fun r m => mul (ofScalar r) m⟩

Depends on / 依赖: ofScalar
-/
def hasSMul : SMul R (Pre R X) := ⟨fun r m => mul (ofScalar r) m⟩

end Pre

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSMul

/--
Definition of `liftFun` / `liftFun` 的定义

English:
definition liftFun
  signature: {A : Type*} [Semiring A] [Algebra R A] (f : X -> A)

中文:
定义 liftFun
  签名: {A : 类型} [半环 A] [代数 R A] (f : X -> A)
-/
def liftFun {A : Type*} [Semiring A] [Algebra R A] (f : X -> A) :
    Pre R X -> A
  | .of t => f t
  | .add a b => liftFun f a + liftFun f b
  | .mul a b => liftFun f a * liftFun f b
  | .ofScalar c => algebraMap _ _ c

/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: : Pre R X -> Pre R X -> Prop
  constructors (17):
    - add_scalar: {r s : R} : Rel (↑(r + s)) (↑r + ↑s)
    - mul_scalar: {r s : R} : Rel (↑(r * s)) (↑r * ↑s)
    - central_scalar: {r : R} {a : Pre R X} : Rel (r * a) (a * r)
    - add_assoc: {a b c : Pre R X} : Rel (a + b + c) (a + (b + c))
    - add_comm: {a b : Pre R X} : Rel (a + b) (b + a)
    - zero_add: {a : Pre R X} : Rel (0 + a) a
    - mul_assoc: {a b c : Pre R X} : Rel (a * b * c) (a * (b * c))
    - one_mul: {a : Pre R X} : Rel (1 * a) a
    - mul_one: {a : Pre R X} : Rel (a * 1) a
    - left_distrib: {a b c : Pre R X} : Rel (a * (b + c)) (a * b + a * c)
    - right_distrib: {a b c : Pre R X} : Rel ((a + b) * c) (a * c + b * c)
    - zero_mul: {a : Pre R X} : Rel (0 * a) 0
    - mul_zero: {a : Pre R X} : Rel (a * 0) 0
    - add_compat_left: {a b c : Pre R X} : Rel a b -> Rel (a + c) (b + c)
    - add_compat_right: {a b c : Pre R X} : Rel a b -> Rel (c + a) (c + b)
    - mul_compat_left: {a b c : Pre R X} : Rel a b -> Rel (a * c) (b * c)
    - mul_compat_right: {a b c : Pre R X} : Rel a b -> Rel (c * a) (c * b)

中文:
归纳类型 关系
  参数: : Pre R X -> Pre R X -> 命题
  构造子 (17 个):
    - add_scalar: {r s : R} : 关系 (↑(r + s)) (↑r + ↑s)
    - mul_scalar: {r s : R} : 关系 (↑(r * s)) (↑r * ↑s)
    - central_scalar: {r : R} {a : Pre R X} : 关系 (r * a) (a * r)
    - add_assoc: {a b c : Pre R X} : 关系 (a + b + c) (a + (b + c))
    - add_comm: {a b : Pre R X} : 关系 (a + b) (b + a)
    - zero_add: {a : Pre R X} : 关系 (0 + a) a
    - mul_assoc: {a b c : Pre R X} : 关系 (a * b * c) (a * (b * c))
    - one_mul: {a : Pre R X} : 关系 (1 * a) a
    - mul_one: {a : Pre R X} : 关系 (a * 1) a
    - left_distrib: {a b c : Pre R X} : 关系 (a * (b + c)) (a * b + a * c)
    - right_distrib: {a b c : Pre R X} : 关系 ((a + b) * c) (a * c + b * c)
    - zero_mul: {a : Pre R X} : 关系 (0 * a) 0
    - mul_zero: {a : Pre R X} : 关系 (a * 0) 0
    - add_compat_left: {a b c : Pre R X} : 关系 a b -> 关系 (a + c) (b + c)
    - add_compat_right: {a b c : Pre R X} : 关系 a b -> 关系 (c + a) (c + b)
    - mul_compat_left: {a b c : Pre R X} : 关系 a b -> 关系 (a * c) (b * c)
    - mul_compat_right: {a b c : Pre R X} : 关系 a b -> 关系 (c * a) (c * b)
-/
inductive Rel : Pre R X -> Pre R X -> Prop
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
  | add_compat_left {a b c : Pre R X} : Rel a b -> Rel (a + c) (b + c)
  | add_compat_right {a b c : Pre R X} : Rel a b -> Rel (c + a) (c + b)
  | mul_compat_left {a b c : Pre R X} : Rel a b -> Rel (a * c) (b * c)
  | mul_compat_right {a b c : Pre R X} : Rel a b -> Rel (c * a) (c * b)

end FreeAlgebra

/--
Definition of `FreeAlgebra` / `FreeAlgebra` 的定义

English:
definition FreeAlgebra
  body: Quot (FreeAlgebra.Rel R X)

中文:
定义 FreeAlgebra
  定义体: Quot (FreeAlgebra.Rel R X)

Depends on / 依赖: FreeAlgebra, FreeAlgebra.Rel
-/
def FreeAlgebra :=
  Quot (FreeAlgebra.Rel R X)

namespace FreeAlgebra

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSMul


/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {A} [CommSemiring A] [Algebra R A]
  body: Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ => Rel.mul_compat_right

中文:
实例 instSMul
  签名: {A} [交换半环 A] [代数 R A]
  定义体: Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ => Rel.mul_compat_right

Depends on / 依赖: HMul.hMul, Quot.map, Rel.mul_compat_right, algebraMap, mul_compat_right
-/
instance instSMul {A} [CommSemiring A] [Algebra R A] : SMul R (FreeAlgebra A X) where
  smul r := Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ => Rel.mul_compat_right

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (FreeAlgebra R X) where zero
  body: Quot.mk _ 0

中文:
实例 instZero
  签名: : 零 (FreeAlgebra R X) where zero
  定义体: Quot.mk _ 0

Depends on / 依赖: Quot.mk
-/
instance instZero : Zero (FreeAlgebra R X) where zero := Quot.mk _ 0

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (FreeAlgebra R X) where one
  body: Quot.mk _ 1

中文:
实例 instOne
  签名: : 幺 (FreeAlgebra R X) where one
  定义体: Quot.mk _ 1

Depends on / 依赖: Quot.mk
-/
instance instOne : One (FreeAlgebra R X) where one := Quot.mk _ 1

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (FreeAlgebra R X) where
  body: Quot.map₂ HAdd.hAdd (fun _ _ _ => Rel.add_compat_right) fun _ _ _ => Rel.add_compat_left

中文:
实例 instAdd
  签名: : 加法 (FreeAlgebra R X) where
  定义体: Quot.map₂ HAdd.hAdd (fun _ _ _ => Rel.add_compat_right) fun _ _ _ => Rel.add_compat_left

Depends on / 依赖: HAdd.hAdd, Quot.map, Rel.add_compat_left, Rel.add_compat_right, add_compat_left, add_compat_right
-/
instance instAdd : Add (FreeAlgebra R X) where
  add := Quot.map₂ HAdd.hAdd (fun _ _ _ => Rel.add_compat_right) fun _ _ _ => Rel.add_compat_left

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (FreeAlgebra R X) where
  body: Quot.map₂ HMul.hMul (fun _ _ _ => Rel.mul_compat_right) fun _ _ _ => Rel.mul_compat_left

中文:
实例 instMul
  签名: : 乘法 (FreeAlgebra R X) where
  定义体: Quot.map₂ HMul.hMul (fun _ _ _ => Rel.mul_compat_right) fun _ _ _ => Rel.mul_compat_left

Depends on / 依赖: HMul.hMul, Quot.map, Rel.mul_compat_left, Rel.mul_compat_right, mul_compat_left, mul_compat_right
-/
instance instMul : Mul (FreeAlgebra R X) where
  mul := Quot.map₂ HMul.hMul (fun _ _ _ => Rel.mul_compat_right) fun _ _ _ => Rel.mul_compat_left

-- `Quot.mk` is an implementation detail of `FreeAlgebra`, so this lemma is private
/--
theorem `mk_mul` / 定理 `mk_mul`

English:
theorem mk_mul
  given: (x y : Pre R X)
  proof: rfl

中文:
定理 mk_mul
  条件: (x y : Pre R X)
  证明: rfl
-/
private theorem mk_mul (x y : Pre R X) :
    Quot.mk (Rel R X) (x * y) = (HMul.hMul (self := instHMul (α := FreeAlgebra R X))
    (Quot.mk (Rel R X) x) (Quot.mk (Rel R X) y)) :=
  rfl


/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: : MonoidWithZero (FreeAlgebra R X) where
  body: by
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
    exact Quot.sound

中文:
实例 instMonoidWithZero
  签名: : 带零幺半群 (FreeAlgebra R X) where
  定义体: by
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
    exact Quot.sound

Depends on / 依赖: Quot.sound, Rel.mul_assoc, Rel.mul_one, Rel.mul_zero, Rel.one_mul, Rel.zero_mul, mul_assoc, mul_one, mul_zero, one_mul, zero_mul
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

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: : Distrib (FreeAlgebra R X) where
  body: by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.left_distrib
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.right_distrib

中文:
实例 instDistrib
  签名: : Distrib (FreeAlgebra R X) where
  定义体: by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.left_distrib
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.right_distrib

Depends on / 依赖: Quot.sound, Rel.left_distrib, Rel.right_distrib, left_distrib, right_distrib
-/
instance instDistrib : Distrib (FreeAlgebra R X) where
  left_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.left_distrib
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.right_distrib

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (FreeAlgebra R X) where
  body: by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.add_assoc
  zero_add := by
    rintro ⟨⟩
    exact Quot.sound Rel.zero_add
  add_zero := by
    rintro ⟨⟩
    change Quot.mk _ _ = _
    rw [Quot.sound Rel.add_comm]; rw [Quot.sound Rel.zero_add]
  add_comm := by
    rintro ⟨⟩ ⟨⟩
    exact Quot.sound R

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (FreeAlgebra R X) where
  定义体: by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound Rel.add_assoc
  zero_add := by
    rintro ⟨⟩
    exact Quot.sound Rel.zero_add
  add_zero := by
    rintro ⟨⟩
    change Quot.mk _ _ = _
    rw [Quot.sound Rel.add_comm]; rw [Quot.sound Rel.zero_add]
  add_comm := by
    rintro ⟨⟩ ⟨⟩
    exact Quot.sound R

Depends on / 依赖: HSMul.hSMul, NSMul.nsmul, Quot.map, Quot.mk, Quot.sound, Rel.add_assoc, Rel.add_comm, Rel.zero_add, Rel.zero_mul, SMul.smul, add_assoc, add_comm, add_zero, map_add, map_one, map_zero, mk_mul, nsmul_succ, nsmul_zero, zero_add
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
    rw [Quot.sound Rel.add_comm]; rw [Quot.sound Rel.zero_add]
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
    rw [map_add]; rw [map_one]; rw [mk_mul]; rw [mk_mul]; rw [← add_one_mul (_ : FreeAlgebra R X)]
    congr 1
    exact Quot.sound Rel.add_scalar

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring (FreeAlgebra R X)
  body: instMonoidWithZero R X
  __ := instAddCommMonoid R X
  __ := instDistrib R X
  natCast n := Quot.mk _ (n : R)
  natCast_zero := by simp; rfl
  natCast_succ n := by simpa using! Quot.sound Rel.add_scalar

中文:
实例 :
  签名: 半环 (FreeAlgebra R X)
  定义体: instMonoidWithZero R X
  __ := instAddCommMonoid R X
  __ := instDistrib R X
  natCast n := Quot.mk _ (n : R)
  natCast_zero := by simp; rfl
  natCast_succ n := by simpa using! Quot.sound Rel.add_scalar

Depends on / 依赖: instMonoidWithZero
-/
instance : Semiring (FreeAlgebra R X) where
  __ := instMonoidWithZero R X
  __ := instAddCommMonoid R X
  __ := instDistrib R X
  natCast n := Quot.mk _ (n : R)
  natCast_zero := by simp; rfl
  natCast_succ n := by simpa using! Quot.sound Rel.add_scalar

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FreeAlgebra R X)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (FreeAlgebra R X)
  定义体: ⟨0⟩
-/
instance : Inhabited (FreeAlgebra R X) :=
  ⟨0⟩

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: {A} [CommSemiring A] [Algebra R A]
  body: ({
      toFun := fun r => Quot.mk _ r
      map_one' := rfl
      map_mul' := fun _ _ => Quot.sound Rel.mul_scalar
      map_zero' := rfl
      map_add' := fun _ _ => Quot.sound Rel.add_scalar } : A ->+* FreeAlgebra A X).comp
      (algebraMap R A)
  commutes' _ := by
    rintro ⟨⟩
    exact Quot.s

中文:
实例 instAlgebra
  签名: {A} [交换半环 A] [代数 R A]
  定义体: ({
      toFun := fun r => Quot.mk _ r
      map_one' := rfl
      map_mul' := fun _ _ => Quot.sound Rel.mul_scalar
      map_zero' := rfl
      map_add' := fun _ _ => Quot.sound Rel.add_scalar } : A ->+* FreeAlgebra A X).comp
      (algebraMap R A)
  commutes' _ := by
    rintro ⟨⟩
    exact Quot.s
-/
instance instAlgebra {A} [CommSemiring A] [Algebra R A] : Algebra R (FreeAlgebra A X) where
  algebraMap := ({
      toFun := fun r => Quot.mk _ r
      map_one' := rfl
      map_mul' := fun _ _ => Quot.sound Rel.mul_scalar
      map_zero' := rfl
      map_add' := fun _ _ => Quot.sound Rel.add_scalar } : A ->+* FreeAlgebra A X).comp
      (algebraMap R A)
  commutes' _ := by
    rintro ⟨⟩
    exact Quot.sound Rel.central_scalar
  smul_def' _ _ := rfl

-- verify there is no diamond at `default` transparency but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
variable (S : Type) [CommSemiring S] in
example : (Semiring.toNatAlgebra : Algebra Nat (FreeAlgebra S X)) = instAlgebra _ _ := rfl

instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [SMul R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S (FreeAlgebra A X) where
  smul_assoc r s x := by
    change algebraMap S A (r • s) • x = algebraMap R A _ • (algebraMap S A _ • x)
    rw [← smul_assoc]
    congr
    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
    rw [smul_assoc]; rw [← smul_one_mul]

instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A] [Algebra R A] [Algebra S A] :
    SMulCommClass R S (FreeAlgebra A X) where
  smul_comm r s x := smul_comm (algebraMap R A r) (algebraMap S A s) x

instance {S : Type*} [CommRing S] : Ring (FreeAlgebra S X) :=
  Algebra.semiringToRing S

-- verify there is no diamond but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
variable (S : Type) [CommRing S] in
example : (Ring.toIntAlgebra _ : Algebra Int (FreeAlgebra S X)) = instAlgebra _ _ := rfl

variable {X}

/-- The canonical function `X → FreeAlgebra R X`.
-/
irreducible_def ι : X -> FreeAlgebra R X := fun m => Quot.mk _ m

@[simp]
/--
theorem `quot_mk_eq_ι` / 定理 `quot_mk_eq_ι`

English:
theorem quot_mk_eq_ι
  given: (m : X)
  statement: Quot.mk (FreeAlgebra.Rel R X) m = ι R m
  proof: by rw [ι_def]

中文:
定理 quot_mk_eq_ι
  条件: (m : X)
  结论: 商.mk (FreeAlgebra.关系 R X) m = ι R m
  证明: by rw [ι_def]
-/
theorem quot_mk_eq_ι (m : X) : Quot.mk (FreeAlgebra.Rel R X) m = ι R m := by rw [ι_def]

variable {A : Type*} [Semiring A] [Algebra R A]

set_option backward.privateInPublic true in
/--
Definition of `liftAux` / `liftAux` 的定义

English:
definition liftAux
  signature: (f : X -> A)
  body: Quot.liftOn a (liftFun _ _ f) fun a b h => by
      induction h
      · exact (algebraMap R A).map_add _ _
      · exact (algebraMap R A).map_mul _ _
      · apply Algebra.commutes
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assoc]
      · change _ + _ = _ + _
        rw [add_comm]
      

中文:
定义 liftAux
  签名: (f : X -> A)
  定义体: Quot.liftOn a (liftFun _ _ f) fun a b h => by
      induction h
      · exact (algebraMap R A).map_add _ _
      · exact (algebraMap R A).map_mul _ _
      · apply Algebra.commutes
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assoc]
      · change _ + _ = _ + _
        rw [add_comm]
      
-/
private def liftAux (f : X -> A) : FreeAlgebra R X ->ₐ[R] A where
  toFun a :=
    Quot.liftOn a (liftFun _ _ f) fun a b h => by
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
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (X -> A) ≃ (FreeAlgebra R X ->ₐ[R] A)
  body: { toFun := liftAux R
    invFun := fun F => F ∘ ι R
    left_inv := fun f => by
      ext
      simp only [Function.comp_apply, ι_def]
      rfl
    right_inv := fun F => by
      ext t
      rcases t with ⟨x⟩
      induction x with
      | of =>
        change ((F : FreeAlgebra R X -> A) ∘ ι R) _ =

中文:
定义 lift
  签名: : (X -> A) ≃ (FreeAlgebra R X ->ₐ[R] A)
  定义体: { toFun := liftAux R
    invFun := fun F => F ∘ ι R
    left_inv := fun f => by
      ext
      simp only [Function.comp_apply, ι_def]
      rfl
    right_inv := fun F => by
      ext t
      rcases t with ⟨x⟩
      induction x with
      | of =>
        change ((F : FreeAlgebra R X -> A) ∘ ι R) _ =

Depends on / 依赖: AlgHom, AlgHom.commutes, FreeAlgebra, Function, Function.comp_apply, algebraMap, commutes, comp_apply, invFun, left_inv, liftAux, ofScalar, right_inv
-/
def lift : (X -> A) ≃ (FreeAlgebra R X ->ₐ[R] A) :=
  { toFun := liftAux R
    invFun := fun F => F ∘ ι R
    left_inv := fun f => by
      ext
      simp only [Function.comp_apply, ι_def]
      rfl
    right_inv := fun F => by
      ext t
      rcases t with ⟨x⟩
      induction x with
      | of =>
        change ((F : FreeAlgebra R X -> A) ∘ ι R) _ = _
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
/--
theorem `liftAux_eq` / 定理 `liftAux_eq`

English:
theorem liftAux_eq
  given: (f : X -> A)
  statement: liftAux R f = lift R f
  proof: by
  rw [lift]
  rfl

@[simp]

中文:
定理 liftAux_eq
  条件: (f : X -> A)
  结论: liftAux R f = lift R f
  证明: by
  rw [lift]
  rfl

@[simp]
-/
theorem liftAux_eq (f : X -> A) : liftAux R f = lift R f := by
  rw [lift]
  rfl

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (F : FreeAlgebra R X ->ₐ[R] A)
  statement: (lift R).symm F = F ∘ ι R
  proof: by
  rw [lift]
  rfl

中文:
定理 lift_symm_apply
  条件: (F : FreeAlgebra R X ->ₐ[R] A)
  结论: (lift R).symm F = F ∘ ι R
  证明: by
  rw [lift]
  rfl
-/
theorem lift_symm_apply (F : FreeAlgebra R X ->ₐ[R] A) : (lift R).symm F = F ∘ ι R := by
  rw [lift]
  rfl

variable {R}

@[simp]
/--
theorem `ι_comp_lift` / 定理 `ι_comp_lift`

English:
theorem ι_comp_lift
  given: (f : X -> A)
  statement: (lift R f : FreeAlgebra R X -> A) ∘ ι R = f
  proof: by
  ext
  rw [Function.comp_apply]; rw [ι_def]; rw [lift]
  rfl

@[simp]

中文:
定理 ι_comp_lift
  条件: (f : X -> A)
  结论: (lift R f : FreeAlgebra R X -> A) ∘ ι R = f
  证明: by
  ext
  rw [Function.comp_apply]; rw [ι_def]; rw [lift]
  rfl

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply
-/
theorem ι_comp_lift (f : X -> A) : (lift R f : FreeAlgebra R X -> A) ∘ ι R = f := by
  ext
  rw [Function.comp_apply]; rw [ι_def]; rw [lift]
  rfl

@[simp]
/--
theorem `lift_ι_apply` / 定理 `lift_ι_apply`

English:
theorem lift_ι_apply
  given: (f : X -> A) (x)
  statement: lift R f (ι R x) = f x
  proof: by
  rw [ι_def]; rw [lift]
  rfl

@[simp]

中文:
定理 lift_ι_apply
  条件: (f : X -> A) (x)
  结论: lift R f (ι R x) = f x
  证明: by
  rw [ι_def]; rw [lift]
  rfl

@[simp]
-/
theorem lift_ι_apply (f : X -> A) (x) : lift R f (ι R x) = f x := by
  rw [ι_def]; rw [lift]
  rfl

@[simp]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (f : X -> A) (g : FreeAlgebra R X ->ₐ[R] A)
  proof: by
  rw [← (lift R).symm_apply_eq]; rw [lift]
  rfl

中文:
定理 lift_unique
  条件: (f : X -> A) (g : FreeAlgebra R X ->ₐ[R] A)
  证明: by
  rw [← (lift R).symm_apply_eq]; rw [lift]
  rfl

Depends on / 依赖: symm_apply_eq
-/
theorem lift_unique (f : X -> A) (g : FreeAlgebra R X ->ₐ[R] A) :
    (g : FreeAlgebra R X -> A) ∘ ι R = f ↔ g = lift R f := by
  rw [← (lift R).symm_apply_eq]; rw [lift]
  rfl

/-!
Since we have set the basic definitions as `@[Irreducible]`, from this point onwards one
should only use the universal properties of the free algebra, and consider the actual implementation
as a quotient of an inductive type as completely hidden. -/


-- Marking `FreeAlgebra` irreducible makes `Ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.
@[simp]
/--
theorem `lift_comp_ι` / 定理 `lift_comp_ι`

English:
theorem lift_comp_ι
  given: (g : FreeAlgebra R X ->ₐ[R] A)
  proof: by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g

中文:
定理 lift_comp_ι
  条件: (g : FreeAlgebra R X ->ₐ[R] A)
  证明: by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g

Depends on / 依赖: apply_symm_apply, lift_symm_apply
-/
theorem lift_comp_ι (g : FreeAlgebra R X ->ₐ[R] A) :
    lift R ((g : FreeAlgebra R X -> A) ∘ ι R) = g := by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {f g : FreeAlgebra R X ->ₐ[R] A}
  proof: by
  rw [← lift_symm_apply]; rw [← lift_symm_apply] at w
  exact (lift R).symm.injective w

中文:
定理 hom_ext
  结论: {f g : FreeAlgebra R X ->ₐ[R] A}
  证明: by
  rw [← lift_symm_apply]; rw [← lift_symm_apply] at w
  exact (lift R).symm.injective w

Depends on / 依赖: injective, lift_symm_apply, symm.injective
-/
theorem hom_ext {f g : FreeAlgebra R X ->ₐ[R] A}
    (w : (f : FreeAlgebra R X -> A) ∘ ι R = (g : FreeAlgebra R X -> A) ∘ ι R) : f = g := by
  rw [← lift_symm_apply]; rw [← lift_symm_apply] at w
  exact (lift R).symm.injective w

/--
Definition of `equivMonoidAlgebraFreeMonoid` / `equivMonoidAlgebraFreeMonoid` 的定义

English:
definition equivMonoidAlgebraFreeMonoid
  signature: : FreeAlgebra R X ≃ₐ[R] R[FreeMonoid X]
  body: .ofAlgHom (lift R fun x => .of R (FreeMonoid X) (.of x))
    (MonoidAlgebra.lift R (FreeAlgebra R X) (FreeMonoid X) (FreeMonoid.lift (ι R)))
    (MonoidAlgebra.algHom_ext' (by ext; simp) (by ext)) (by ext; simp)

中文:
定义 equivMonoidAlgebraFreeMonoid
  签名: : FreeAlgebra R X ≃ₐ[R] R[自由幺半群 X]
  定义体: .ofAlgHom (lift R fun x => .of R (FreeMonoid X) (.of x))
    (MonoidAlgebra.lift R (FreeAlgebra R X) (FreeMonoid X) (FreeMonoid.lift (ι R)))
    (MonoidAlgebra.algHom_ext' (by ext; simp) (by ext)) (by ext; simp)

Depends on / 依赖: FreeAlgebra, FreeMonoid, FreeMonoid.lift, MonoidAlgebra, MonoidAlgebra.algHom_ext, MonoidAlgebra.lift, algHom_ext, ofAlgHom
-/
noncomputable def equivMonoidAlgebraFreeMonoid : FreeAlgebra R X ≃ₐ[R] R[FreeMonoid X] :=
  .ofAlgHom (lift R fun x => .of R (FreeMonoid X) (.of x))
    (MonoidAlgebra.lift R (FreeAlgebra R X) (FreeMonoid X) (FreeMonoid.lift (ι R)))
    (MonoidAlgebra.algHom_ext' (by ext; simp) (by ext)) (by ext; simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (FreeAlgebra R X)
  body: equivMonoidAlgebraFreeMonoid.surjective.nontrivial

中文:
实例 [非平凡
  签名: R] : 非平凡 (FreeAlgebra R X)
  定义体: equivMonoidAlgebraFreeMonoid.surjective.nontrivial

Depends on / 依赖: equivMonoidAlgebraFreeMonoid, equivMonoidAlgebraFreeMonoid.surjective.nontrivial, nontrivial, surjective
-/
instance [Nontrivial R] : Nontrivial (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.surjective.nontrivial

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: [NoZeroDivisors R]
  body: equivMonoidAlgebraFreeMonoid.toMulEquiv.noZeroDivisors

中文:
实例 instNoZeroDivisors
  签名: [无零因子 R]
  定义体: equivMonoidAlgebraFreeMonoid.toMulEquiv.noZeroDivisors

Depends on / 依赖: equivMonoidAlgebraFreeMonoid, equivMonoidAlgebraFreeMonoid.toMulEquiv.noZeroDivisors, noZeroDivisors, toMulEquiv
-/
instance instNoZeroDivisors [NoZeroDivisors R] : NoZeroDivisors (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.toMulEquiv.noZeroDivisors

/--
Instance `instIsDomain` / 实例 `instIsDomain`

English:
instance instIsDomain
  signature: {R X} [CommRing R] [IsDomain R]
  body: NoZeroDivisors.to_isDomain _

中文:
实例 instIsDomain
  签名: {R X} [交换环 R] [是整环 R]
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance instIsDomain {R X} [CommRing R] [IsDomain R] : IsDomain (FreeAlgebra R X) :=
  NoZeroDivisors.to_isDomain _

section

/--
Definition of `algebraMapInv` / `algebraMapInv` 的定义

English:
definition algebraMapInv
  signature: : FreeAlgebra R X ->ₐ[R] R
  body: lift R (0 : X -> R)

中文:
定义 algebraMapInv
  签名: : FreeAlgebra R X ->ₐ[R] R
  定义体: lift R (0 : X -> R)
-/
def algebraMapInv : FreeAlgebra R X ->ₐ[R] R :=
  lift R (0 : X -> R)

/--
theorem `algebraMap_leftInverse` / 定理 `algebraMap_leftInverse`

English:
theorem algebraMap_leftInverse
  proof: fun x => by
  simp

@[simp]

中文:
定理 algebraMap_leftInverse
  证明: fun x => by
  simp

@[simp]
-/
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X) := fun x => by
  simp

@[simp]
/--
theorem `algebraMap_inj` / 定理 `algebraMap_inj`

English:
theorem algebraMap_inj
  given: (x y : R)
  proof: algebraMap_leftInverse.injective.eq_iff

@[simp]

中文:
定理 algebraMap_inj
  条件: (x y : R)
  证明: algebraMap_leftInverse.injective.eq_iff

@[simp]

Depends on / 依赖: algebraMap_leftInverse, algebraMap_leftInverse.injective.eq_iff, eq_iff, injective
-/
theorem algebraMap_inj (x y : R) :
    algebraMap R (FreeAlgebra R X) x = algebraMap R (FreeAlgebra R X) y ↔ x = y :=
  algebraMap_leftInverse.injective.eq_iff

@[simp]
/--
theorem `algebraMap_eq_zero_iff` / 定理 `algebraMap_eq_zero_iff`

English:
theorem algebraMap_eq_zero_iff
  given: (x : R)
  statement: algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0
  proof: map_eq_zero_iff (algebraMap _ _) algebraMap_leftInverse.injective

@[simp]

中文:
定理 algebraMap_eq_zero_iff
  条件: (x : R)
  结论: algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0
  证明: map_eq_zero_iff (algebraMap _ _) algebraMap_leftInverse.injective

@[simp]

Depends on / 依赖: algebraMap, algebraMap_leftInverse, algebraMap_leftInverse.injective, injective, map_eq_zero_iff
-/
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) algebraMap_leftInverse.injective

@[simp]
/--
theorem `algebraMap_eq_one_iff` / 定理 `algebraMap_eq_one_iff`

English:
theorem algebraMap_eq_one_iff
  given: (x : R)
  statement: algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1
  proof: map_eq_one_iff (algebraMap _ _) algebraMap_leftInverse.injective

中文:
定理 algebraMap_eq_one_iff
  条件: (x : R)
  结论: algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1
  证明: map_eq_one_iff (algebraMap _ _) algebraMap_leftInverse.injective

Depends on / 依赖: algebraMap, algebraMap_leftInverse, algebraMap_leftInverse.injective, injective, map_eq_one_iff
-/
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) algebraMap_leftInverse.injective

-- this proof is copied from the approach in `FreeAbelianGroup.of_injective`
/--
theorem `ι_injective` / 定理 `ι_injective`

English:
theorem ι_injective
  given: [Nontrivial R]
  statement: Function.Injective (ι R : X -> FreeAlgebra R X)
  proof: fun x y hoxy =>
by_contradiction by
    classical exact fun hxy : x != y =>
        let f : FreeAlgebra R X ->ₐ[R] R := lift R fun z => if x = z then (1 : R) else 0
have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans if_pos rfl
        have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
have hfy0 : f (ι R y)

中文:
定理 ι_injective
  条件: [非平凡 R]
  结论: 函数.单射 (ι R : X -> FreeAlgebra R X)
  证明: fun x y hoxy =>
by_contradiction by
    classical exact fun hxy : x != y =>
        let f : FreeAlgebra R X ->ₐ[R] R := lift R fun z => if x = z then (1 : R) else 0
have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans if_pos rfl
        have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
have hfy0 : f (ι R y)

Depends on / 依赖: FreeAlgebra, by_contradiction, classical, hfy1.symm.trans, if_neg, if_pos, one_ne_zero
-/
theorem ι_injective [Nontrivial R] : Function.Injective (ι R : X -> FreeAlgebra R X) :=
  fun x y hoxy =>
by_contradiction by
    classical exact fun hxy : x != y =>
        let f : FreeAlgebra R X ->ₐ[R] R := lift R fun z => if x = z then (1 : R) else 0
have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans if_pos rfl
        have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
have hfy0 : f (ι R y) = 0 := (lift_ι_apply _ _).trans if_neg hxy
one_ne_zero hfy1.symm.trans hfy0

@[simp]
/--
theorem `ι_inj` / 定理 `ι_inj`

English:
theorem ι_inj
  given: [Nontrivial R] (x y : X)
  statement: ι R x = ι R y ↔ x = y
  proof: ι_injective.eq_iff

@[simp]

中文:
定理 ι_inj
  条件: [非平凡 R] (x y : X)
  结论: ι R x = ι R y ↔ x = y
  证明: ι_injective.eq_iff

@[simp]

Depends on / 依赖: _injective.eq_iff, eq_iff
-/
theorem ι_inj [Nontrivial R] (x y : X) : ι R x = ι R y ↔ x = y :=
  ι_injective.eq_iff

@[simp]
/--
theorem `ι_ne_algebraMap` / 定理 `ι_ne_algebraMap`

English:
theorem ι_ne_algebraMap
  given: [Nontrivial R] (x : X) (r : R)
  statement: ι R x != algebraMap R _ r
  proof: fun h => by
  let f0 : FreeAlgebra R X ->ₐ[R] R := lift R 0
  let f1 : FreeAlgebra R X ->ₐ[R] R := lift R 1
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  rw [h]; rw [f0.commutes]; rw [Algebra.algebraMap_self_apply] at hf0
  rw [h]; rw [f1.commutes]

中文:
定理 ι_ne_algebraMap
  条件: [非平凡 R] (x : X) (r : R)
  结论: ι R x != algebraMap R _ r
  证明: fun h => by
  let f0 : FreeAlgebra R X ->ₐ[R] R := lift R 0
  let f1 : FreeAlgebra R X ->ₐ[R] R := lift R 1
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  rw [h]; rw [f0.commutes]; rw [Algebra.algebraMap_self_apply] at hf0
  rw [h]; rw [f1.commutes]

Depends on / 依赖: Algebra, Algebra.algebraMap_self_apply, FreeAlgebra, algebraMap_self_apply, commutes, f0.commutes, f1.commutes, hf0.symm.trans, zero_ne_one
-/
theorem ι_ne_algebraMap [Nontrivial R] (x : X) (r : R) : ι R x != algebraMap R _ r := fun h => by
  let f0 : FreeAlgebra R X ->ₐ[R] R := lift R 0
  let f1 : FreeAlgebra R X ->ₐ[R] R := lift R 1
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  rw [h]; rw [f0.commutes]; rw [Algebra.algebraMap_self_apply] at hf0
  rw [h]; rw [f1.commutes]; rw [Algebra.algebraMap_self_apply] at hf1
  exact zero_ne_one (hf0.symm.trans hf1)

@[simp]
/--
theorem `ι_ne_zero` / 定理 `ι_ne_zero`

English:
theorem ι_ne_zero
  given: [Nontrivial R] (x : X)
  statement: ι R x != 0
  proof: ι_ne_algebraMap x 0

@[simp]

中文:
定理 ι_ne_zero
  条件: [非平凡 R] (x : X)
  结论: ι R x != 0
  证明: ι_ne_algebraMap x 0

@[simp]
-/
theorem ι_ne_zero [Nontrivial R] (x : X) : ι R x != 0 :=
  ι_ne_algebraMap x 0

@[simp]
/--
theorem `ι_ne_one` / 定理 `ι_ne_one`

English:
theorem ι_ne_one
  given: [Nontrivial R] (x : X)
  statement: ι R x != 1
  proof: ι_ne_algebraMap x 1

中文:
定理 ι_ne_one
  条件: [非平凡 R] (x : X)
  结论: ι R x != 1
  证明: ι_ne_algebraMap x 1
-/
theorem ι_ne_one [Nontrivial R] (x : X) : ι R x != 1 :=
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
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {motive : FreeAlgebra R X -> Prop}
  proof: by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := {x | motive x}
      mul_mem' := mul _ _
      add_mem' := add _ _
      algebraMap_mem' := grade0 }
  let of : X -> s := Subtype.coind (ι R) grade1
 

中文:
定理 induction
  结论: {motive : FreeAlgebra R X -> 命题}
  证明: by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := {x | motive x}
      mul_mem' := mul _ _
      add_mem' := add _ _
      algebraMap_mem' := grade0 }
  let of : X -> s := Subtype.coind (ι R) grade1
 
-/
theorem induction {motive : FreeAlgebra R X -> Prop}
    (grade0 : forall r, motive (algebraMap R (FreeAlgebra R X) r)) (grade1 : forall x, motive (ι R x))
    (mul : forall a b, motive a -> motive b -> motive (a * b))
    (add : forall a b, motive a -> motive b -> motive (a + b))
    (a : FreeAlgebra R X) : motive a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := {x | motive x}
      mul_mem' := mul _ _
      add_mem' := add _ _
      algebraMap_mem' := grade0 }
  let of : X -> s := Subtype.coind (ι R) grade1
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
/--
theorem `adjoin_range_ι` / 定理 `adjoin_range_ι`

English:
theorem adjoin_range_ι
  statement: Algebra.adjoin R (Set.range (ι R : X -> FreeAlgebra R X)) = ⊤
  proof: by
  set S := Algebra.adjoin R (Set.range (ι R : X -> FreeAlgebra R X))
  refine top_unique fun x hx => ?_; clear hx
  induction x with
  | grade0 => exact S.algebraMap_mem _
  | add x y hx hy => exact S.add_mem hx hy
  | mul x y hx hy => exact S.mul_mem hx hy
  | grade1 x => exact Algebra.subset_ad

中文:
定理 adjoin_range_ι
  结论: 代数.adjoin R (集合.range (ι R : X -> FreeAlgebra R X)) = ⊤
  证明: by
  set S := Algebra.adjoin R (Set.range (ι R : X -> FreeAlgebra R X))
  refine top_unique fun x hx => ?_; clear hx
  induction x with
  | grade0 => exact S.algebraMap_mem _
  | add x y hx hy => exact S.add_mem hx hy
  | mul x y hx hy => exact S.mul_mem hx hy
  | grade1 x => exact Algebra.subset_ad

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, FreeAlgebra, S.add_mem, S.algebraMap_mem, S.mul_mem, Set.mem_range_self, Set.range, add_mem, adjoin, algebraMap_mem, grade0, grade1, mem_range_self, mul_mem, subset_adjoin, top_unique
-/
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R : X -> FreeAlgebra R X)) = ⊤ := by
  set S := Algebra.adjoin R (Set.range (ι R : X -> FreeAlgebra R X))
  refine top_unique fun x hx => ?_; clear hx
  induction x with
  | grade0 => exact S.algebraMap_mem _
  | add x y hx hy => exact S.add_mem hx hy
  | mul x y hx hy => exact S.mul_mem hx hy
  | grade1 x => exact Algebra.subset_adjoin (Set.mem_range_self _)

variable {A : Type*} [Semiring A] [Algebra R A]

/--
theorem `_root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift` / 定理 `_root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift`

English:
theorem _root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift
  given: (f : X -> A)
  proof: by
  simp only [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

中文:
定理 _root_.代数.adjoin_range_eq_range_freeAlgebra_lift
  条件: (f : X -> A)
  证明: by
  simp only [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.map_top, Function, Function.comp_def, Set.range_comp, comp_def, map_adjoin, map_top, range_comp
-/
theorem _root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift (f : X -> A) :
    Algebra.adjoin R (Set.range f) = (FreeAlgebra.lift R f).range := by
  simp only [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

/--
theorem `_root_.Algebra.adjoin_eq_range_freeAlgebra_lift` / 定理 `_root_.Algebra.adjoin_eq_range_freeAlgebra_lift`

English:
theorem _root_.Algebra.adjoin_eq_range_freeAlgebra_lift
  given: (s : Set A)
  proof: by
  rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift]; rw [Subtype.range_coe]

中文:
定理 _root_.代数.adjoin_eq_range_freeAlgebra_lift
  条件: (s : 集合 A)
  证明: by
  rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift]; rw [Subtype.range_coe]

Depends on / 依赖: Algebra, Algebra.adjoin_range_eq_range_freeAlgebra_lift, Subtype, Subtype.range_coe, adjoin_range_eq_range_freeAlgebra_lift, range_coe
-/
theorem _root_.Algebra.adjoin_eq_range_freeAlgebra_lift (s : Set A) :
    Algebra.adjoin R s = (FreeAlgebra.lift R ((↑) : s -> A)).range := by
  rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift]; rw [Subtype.range_coe]

end FreeAlgebra
