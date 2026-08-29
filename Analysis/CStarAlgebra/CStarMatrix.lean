/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.UniformSpace.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Matrices with entries in a C⋆-algebra

This file creates a type copy of `Matrix m n A` called `CStarMatrix m n A` meant for matrices with
entries in a C⋆-algebra `A`. Its action on `C⋆ᵐᵒᵈ (n → A)` (via `Matrix.mulVec`) gives
it the operator norm, and this norm makes `CStarMatrix n n A` a C⋆-algebra.

## Main declarations

+ `CStarMatrix m n A`: the type copy
+ `CStarMatrix.instNonUnitalCStarAlgebra`: square matrices with entries in a non-unital C⋆-algebra
    form a non-unital C⋆-algebra
+ `CStarMatrix.instCStarAlgebra`: square matrices with entries in a unital C⋆-algebra form a
    unital C⋆-algebra

## Implementation notes

The norm on this type induces the product uniformity and bornology, but these are not defeq to
`Pi.uniformSpace` and `Pi.instBornology`. Hence, we prove the equality to the Pi instances and
replace the uniformity and bornology by the Pi ones when registering the
`NormedAddCommGroup (CStarMatrix m n A)` instance. See the docstring of the `TopologyAux` section
below for more details.
-/

@[expose] public section

open scoped ComplexOrder Topology Uniformity Bornology Matrix NNReal InnerProductSpace
  WithCStarModule

/--
Definition of `CStarMatrix` / `CStarMatrix` 的定义

English:
definition CStarMatrix
  signature: (m : Type*) (n : Type*) (A : Type*)
  body: Matrix m n A

中文:
定义 CStarMatrix
  签名: (m : 类型) (n : 类型) (A : 类型)
  定义体: Matrix m n A

Depends on / 依赖: Matrix
-/
def CStarMatrix (m : Type*) (n : Type*) (A : Type*) := Matrix m n A

namespace CStarMatrix

variable {m n R S A B : Type*}

section basic

variable (m n A) in
/--
Definition of `ofMatrix` / `ofMatrix` 的定义

English:
definition ofMatrix
  signature: {m n A : Type*}
  body: Equiv.refl _

@[simp]

中文:
定义 ofMatrix
  签名: {m n A : 类型}
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def ofMatrix {m n A : Type*} : Matrix m n A ≃ CStarMatrix m n A := Equiv.refl _

@[simp]
/--
lemma `ofMatrix_apply` / 引理 `ofMatrix_apply`

English:
lemma ofMatrix_apply
  given: {M : Matrix m n A} {i : m}
  statement: (ofMatrix M) i = M i
  proof: rfl

@[simp]

中文:
引理 ofMatrix_apply
  条件: {M : 矩阵 m n A} {i : m}
  结论: (ofMatrix M) i = M i
  证明: rfl

@[simp]
-/
lemma ofMatrix_apply {M : Matrix m n A} {i : m} : (ofMatrix M) i = M i := rfl

@[simp]
/--
lemma `ofMatrix_symm_apply` / 引理 `ofMatrix_symm_apply`

English:
lemma ofMatrix_symm_apply
  given: {M : CStarMatrix m n A} {i : m}
  statement: (ofMatrix.symm M) i = M i
  proof: rfl

中文:
引理 ofMatrix_symm_apply
  条件: {M : CStarMatrix m n A} {i : m}
  结论: (ofMatrix.symm M) i = M i
  证明: rfl
-/
lemma ofMatrix_symm_apply {M : CStarMatrix m n A} {i : m} : (ofMatrix.symm M) i = M i := rfl

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {M N : CStarMatrix m n A}
  statement: (forall i j, M i j = N i j) ↔ M = N
  proof: ⟨fun h => funext fun i => funext h i, fun h => by simp [h]⟩

@[ext]

中文:
定理 ext_iff
  条件: {M N : CStarMatrix m n A}
  结论: (对任意 i j, M i j = N i j) ↔ M = N
  证明: ⟨fun h => funext fun i => funext h i, fun h => by simp [h]⟩

@[ext]
-/
theorem ext_iff {M N : CStarMatrix m n A} : (forall i j, M i j = N i j) ↔ M = N :=
⟨fun h => funext fun i => funext h i, fun h => by simp [h]⟩

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {M₁ M₂ : CStarMatrix m n A} (h : forall i j, M₁ i j = M₂ i j)
  statement: M₁ = M₂
  proof: ext_iff.mp h

中文:
引理 ext
  条件: {M₁ M₂ : CStarMatrix m n A} (h : 对任意 i j, M₁ i j = M₂ i j)
  结论: M₁ = M₂
  证明: ext_iff.mp h

Depends on / 依赖: ext_iff, ext_iff.mp
-/
lemma ext {M₁ M₂ : CStarMatrix m n A} (h : forall i j, M₁ i j = M₂ i j) : M₁ = M₂ := ext_iff.mp h

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (M : CStarMatrix m n A) (f : A -> B)
  body: ofMatrix fun i j => f (M i j)

@[simp]

中文:
定义 map
  签名: (M : CStarMatrix m n A) (f : A -> B)
  定义体: ofMatrix fun i j => f (M i j)

@[simp]

Depends on / 依赖: ofMatrix
-/
def map (M : CStarMatrix m n A) (f : A -> B) : CStarMatrix m n B :=
  ofMatrix fun i j => f (M i j)

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {M : CStarMatrix m n A} {f : A -> B} {i : m} {j : n}
  statement: M.map f i j = f (M i j)
  proof: rfl

@[simp]

中文:
定理 map_apply
  条件: {M : CStarMatrix m n A} {f : A -> B} {i : m} {j : n}
  结论: M.map f i j = f (M i j)
  证明: rfl

@[simp]
-/
theorem map_apply {M : CStarMatrix m n A} {f : A -> B} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (M : CStarMatrix m n A)
  statement: M.map id = M
  proof: by
  ext
  rfl

@[simp]

中文:
定理 map_id
  条件: (M : CStarMatrix m n A)
  结论: M.map id = M
  证明: by
  ext
  rfl

@[simp]
-/
theorem map_id (M : CStarMatrix m n A) : M.map id = M := by
  ext
  rfl

@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  given: (M : CStarMatrix m n A)
  statement: M.map (·) = M
  proof: map_id M

中文:
定理 map_id'
  条件: (M : CStarMatrix m n A)
  结论: M.map (·) = M
  证明: map_id M

Depends on / 依赖: map_id
-/
theorem map_id' (M : CStarMatrix m n A) : M.map (·) = M := map_id M

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {C : Type*} {M : Matrix m n A} {f : A -> B} {g : B -> C}
  proof: by ext; rfl

中文:
定理 map_map
  条件: {C : 类型} {M : 矩阵 m n A} {f : A -> B} {g : B -> C}
  证明: by ext; rfl
-/
theorem map_map {C : Type*} {M : Matrix m n A} {f : A -> B} {g : B -> C} :
    (M.map f).map g = M.map (g ∘ f) := by ext; rfl

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : A -> B} (hf : Function.Injective f)
  proof: fun _ _ h =>
ext fun i j => hf ext_iff.mpr h i j

中文:
定理 map_injective
  条件: {f : A -> B} (hf : 函数.单射 f)
  证明: fun _ _ h =>
ext fun i j => hf ext_iff.mpr h i j
-/
theorem map_injective {f : A -> B} (hf : Function.Injective f) :
    Function.Injective fun M : CStarMatrix m n A => M.map f := fun _ _ h =>
ext fun i j => hf ext_iff.mpr h i j

/--
Definition of `transpose` / `transpose` 的定义

English:
definition transpose
  signature: (M : CStarMatrix m n A)
  body: ofMatrix fun x y => M y x

@[simp]

中文:
定义 transpose
  签名: (M : CStarMatrix m n A)
  定义体: ofMatrix fun x y => M y x

@[simp]

Depends on / 依赖: ofMatrix
-/
def transpose (M : CStarMatrix m n A) : CStarMatrix n m A :=
  ofMatrix fun x y => M y x

@[simp]
/--
theorem `transpose_apply` / 定理 `transpose_apply`

English:
theorem transpose_apply
  given: (M : CStarMatrix m n A) (i j)
  statement: transpose M i j = M j i
  proof: rfl

中文:
定理 transpose_apply
  条件: (M : CStarMatrix m n A) (i j)
  结论: transpose M i j = M j i
  证明: rfl
-/
theorem transpose_apply (M : CStarMatrix m n A) (i j) : transpose M i j = M j i :=
  rfl

/--
Definition of `conjTranspose` / `conjTranspose` 的定义

English:
definition conjTranspose
  signature: [Star A] (M : CStarMatrix m n A)
  body: M.transpose.map star

@[simp]

中文:
定义 conjTranspose
  签名: [对合 A] (M : CStarMatrix m n A)
  定义体: M.transpose.map star

@[simp]

Depends on / 依赖: M.transpose.map, transpose
-/
def conjTranspose [Star A] (M : CStarMatrix m n A) : CStarMatrix n m A :=
  M.transpose.map star

@[simp]
/--
theorem `conjTranspose_apply` / 定理 `conjTranspose_apply`

English:
theorem conjTranspose_apply
  given: [Star A] (M : CStarMatrix m n A) (i j)
  proof: rfl

中文:
定理 conjTranspose_apply
  条件: [对合 A] (M : CStarMatrix m n A) (i j)
  证明: rfl
-/
theorem conjTranspose_apply [Star A] (M : CStarMatrix m n A) (i j) :
    conjTranspose M i j = star (M j i) := rfl

/--
Instance `instStar` / 实例 `instStar`

English:
instance instStar
  signature: [Star A]
  body: M.conjTranspose

中文:
实例 instStar
  签名: [对合 A]
  定义体: M.conjTranspose

Depends on / 依赖: M.conjTranspose, conjTranspose
-/
instance instStar [Star A] : Star (CStarMatrix n n A) where
  star M := M.conjTranspose

/--
lemma `star_eq_conjTranspose` / 引理 `star_eq_conjTranspose`

English:
lemma star_eq_conjTranspose
  given: [Star A] {M : CStarMatrix n n A}
  statement: star M = M.conjTranspose
  proof: rfl

中文:
引理 star_eq_conjTranspose
  条件: [对合 A] {M : CStarMatrix n n A}
  结论: star M = M.conjTranspose
  证明: rfl
-/
lemma star_eq_conjTranspose [Star A] {M : CStarMatrix n n A} : star M = M.conjTranspose := rfl

/--
Instance `instInvolutiveStar` / 实例 `instInvolutiveStar`

English:
instance instInvolutiveStar
  signature: [InvolutiveStar A]
  body: star_involutive (R := Matrix n n A)

中文:
实例 instInvolutiveStar
  签名: [InvolutiveStar A]
  定义体: star_involutive (R := Matrix n n A)

Depends on / 依赖: Matrix, star_involutive
-/
instance instInvolutiveStar [InvolutiveStar A] : InvolutiveStar (CStarMatrix n n A) where
  star_involutive := star_involutive (R := Matrix n n A)

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Inhabited A]
  body: inferInstanceAs Inhabited (Matrix m n A)

中文:
实例 instInhabited
  签名: [可居 A]
  定义体: inferInstanceAs Inhabited (Matrix m n A)

Depends on / 依赖: Inhabited, Matrix
-/
instance instInhabited [Inhabited A] : Inhabited (CStarMatrix m n A) :=
inferInstanceAs Inhabited (Matrix m n A)

/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq A] [Fintype m] [Fintype n]
  body: inferInstanceAs DecidableEq (Matrix m n A)

中文:
实例 instDecidableEq
  签名: [DecidableEq A] [有限类型 m] [有限类型 n]
  定义体: inferInstanceAs DecidableEq (Matrix m n A)

Depends on / 依赖: DecidableEq, Matrix
-/
instance instDecidableEq [DecidableEq A] [Fintype m] [Fintype n] :
    DecidableEq (CStarMatrix m n A) :=
inferInstanceAs DecidableEq (Matrix m n A)

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (CStarMatrix m n α) :=
inferInstanceAs Fintype (Matrix m n α)

instance {n m} [Finite m] [Finite n] (α) [Finite α] : Finite (CStarMatrix m n α) :=
inferInstanceAs Finite (Matrix m n α)

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: [Add A]
  body: inferInstanceAs Add (Matrix m n A)

中文:
实例 instAdd
  签名: [加法 A]
  定义体: inferInstanceAs Add (Matrix m n A)

Depends on / 依赖: Matrix
-/
instance instAdd [Add A] : Add (CStarMatrix m n A) :=
inferInstanceAs Add (Matrix m n A)

/--
Instance `instAddSemigroup` / 实例 `instAddSemigroup`

English:
instance instAddSemigroup
  signature: [AddSemigroup A]
  body: inferInstanceAs AddSemigroup (Matrix m n A)

中文:
实例 instAddSemigroup
  签名: [加法半群 A]
  定义体: inferInstanceAs AddSemigroup (Matrix m n A)

Depends on / 依赖: AddSemigroup, Matrix
-/
instance instAddSemigroup [AddSemigroup A] : AddSemigroup (CStarMatrix m n A) :=
inferInstanceAs AddSemigroup (Matrix m n A)

/--
Instance `instAddCommSemigroup` / 实例 `instAddCommSemigroup`

English:
instance instAddCommSemigroup
  signature: [AddCommSemigroup A]
  body: inferInstanceAs AddCommSemigroup (Matrix m n A)

中文:
实例 instAddCommSemigroup
  签名: [加法交换半群 A]
  定义体: inferInstanceAs AddCommSemigroup (Matrix m n A)

Depends on / 依赖: AddCommSemigroup, Matrix
-/
instance instAddCommSemigroup [AddCommSemigroup A] : AddCommSemigroup (CStarMatrix m n A) :=
inferInstanceAs AddCommSemigroup (Matrix m n A)

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: [Zero A]
  body: inferInstanceAs Zero (Matrix m n A)

中文:
实例 instZero
  签名: [零 A]
  定义体: inferInstanceAs Zero (Matrix m n A)

Depends on / 依赖: Matrix
-/
instance instZero [Zero A] : Zero (CStarMatrix m n A) :=
inferInstanceAs Zero (Matrix m n A)

/--
Instance `instAddZeroClass` / 实例 `instAddZeroClass`

English:
instance instAddZeroClass
  signature: [AddZeroClass A]
  body: inferInstanceAs AddZeroClass (Matrix m n A)

中文:
实例 instAddZeroClass
  签名: [加法零类 A]
  定义体: inferInstanceAs AddZeroClass (Matrix m n A)

Depends on / 依赖: AddZeroClass, Matrix
-/
instance instAddZeroClass [AddZeroClass A] : AddZeroClass (CStarMatrix m n A) :=
inferInstanceAs AddZeroClass (Matrix m n A)

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul R A]
  body: inferInstanceAs SMul R (Matrix m n A)

中文:
实例 instSMul
  签名: [标量乘法 R A]
  定义体: inferInstanceAs SMul R (Matrix m n A)

Depends on / 依赖: Matrix
-/
instance instSMul [SMul R A] : SMul R (CStarMatrix m n A) :=
inferInstanceAs SMul R (Matrix m n A)

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: [AddMonoid A]
  body: letI := instSMul (R := Nat) (A := A) (m := m) (n := n); (· • · )
__ : AddMonoid (CStarMatrix m n A) := inferInstanceAs AddMonoid (Matrix m n A)

中文:
实例 instAddMonoid
  签名: [加法幺半群 A]
  定义体: letI := instSMul (R := Nat) (A := A) (m := m) (n := n); (· • · )
__ : AddMonoid (CStarMatrix m n A) := inferInstanceAs AddMonoid (Matrix m n A)

Depends on / 依赖: instSMul
-/
instance instAddMonoid [AddMonoid A] : AddMonoid (CStarMatrix m n A) where
  nsmul := letI := instSMul (R := Nat) (A := A) (m := m) (n := n); (· • · )
__ : AddMonoid (CStarMatrix m n A) := inferInstanceAs AddMonoid (Matrix m n A)

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid A]
  body: inferInstanceAs AddCommMonoid (Matrix m n A)

中文:
实例 instAddCommMonoid
  签名: [加法交换幺半群 A]
  定义体: inferInstanceAs AddCommMonoid (Matrix m n A)

Depends on / 依赖: AddCommMonoid, Matrix
-/
instance instAddCommMonoid [AddCommMonoid A] : AddCommMonoid (CStarMatrix m n A) :=
inferInstanceAs AddCommMonoid (Matrix m n A)

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: [Neg A]
  body: inferInstanceAs Neg (Matrix m n A)

中文:
实例 instNeg
  签名: [取负 A]
  定义体: inferInstanceAs Neg (Matrix m n A)

Depends on / 依赖: Matrix
-/
instance instNeg [Neg A] : Neg (CStarMatrix m n A) :=
inferInstanceAs Neg (Matrix m n A)

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: [Sub A]
  body: inferInstanceAs Sub (Matrix m n A)

中文:
实例 instSub
  签名: [减法 A]
  定义体: inferInstanceAs Sub (Matrix m n A)

Depends on / 依赖: Matrix
-/
instance instSub [Sub A] : Sub (CStarMatrix m n A) :=
inferInstanceAs Sub (Matrix m n A)

/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: [AddGroup A]
  body: letI := instSMul (R := Int) (A := A) (m := m) (n := n); (· • · )
__ : AddGroup (CStarMatrix m n A) := inferInstanceAs AddGroup (Matrix m n A)

中文:
实例 instAddGroup
  签名: [加法群 A]
  定义体: letI := instSMul (R := Int) (A := A) (m := m) (n := n); (· • · )
__ : AddGroup (CStarMatrix m n A) := inferInstanceAs AddGroup (Matrix m n A)

Depends on / 依赖: instSMul
-/
instance instAddGroup [AddGroup A] : AddGroup (CStarMatrix m n A) where
  zsmul := letI := instSMul (R := Int) (A := A) (m := m) (n := n); (· • · )
__ : AddGroup (CStarMatrix m n A) := inferInstanceAs AddGroup (Matrix m n A)

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup A]
  body: inferInstanceAs AddCommGroup (Matrix m n A)

中文:
实例 instAddCommGroup
  签名: [加法交换群 A]
  定义体: inferInstanceAs AddCommGroup (Matrix m n A)

Depends on / 依赖: AddCommGroup, Matrix
-/
instance instAddCommGroup [AddCommGroup A] : AddCommGroup (CStarMatrix m n A) :=
inferInstanceAs AddCommGroup (Matrix m n A)

/--
Instance `instUnique` / 实例 `instUnique`

English:
instance instUnique
  signature: [Unique A]
  body: inferInstanceAs Unique (Matrix m n A)

中文:
实例 instUnique
  签名: [唯一 A]
  定义体: inferInstanceAs Unique (Matrix m n A)

Depends on / 依赖: Matrix, Unique
-/
instance instUnique [Unique A] : Unique (CStarMatrix m n A) :=
inferInstanceAs Unique (Matrix m n A)

/--
Instance `instSubsingleton` / 实例 `instSubsingleton`

English:
instance instSubsingleton
  signature: [Subsingleton A]
  body: inferInstanceAs Subsingleton (Matrix m n A)

中文:
实例 instSubsingleton
  签名: [子单例 A]
  定义体: inferInstanceAs Subsingleton (Matrix m n A)

Depends on / 依赖: Matrix, Subsingleton
-/
instance instSubsingleton [Subsingleton A] : Subsingleton (CStarMatrix m n A) :=
inferInstanceAs Subsingleton (Matrix m n A)

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nonempty m] [Nonempty n] [Nontrivial A]
  body: inferInstanceAs Nontrivial (Matrix m n A)

中文:
实例 instNontrivial
  签名: [非空 m] [非空 n] [非平凡 A]
  定义体: inferInstanceAs Nontrivial (Matrix m n A)

Depends on / 依赖: Matrix, Nontrivial
-/
instance instNontrivial [Nonempty m] [Nonempty n] [Nontrivial A] : Nontrivial (CStarMatrix m n A) :=
inferInstanceAs Nontrivial (Matrix m n A)

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul R A] [SMul S A] [SMulCommClass R S A]
  body: inferInstanceAs SMulCommClass R S (Matrix m n A)

中文:
实例 instSMulCommClass
  签名: [标量乘法 R A] [标量乘法 S A] [标量交换类 R S A]
  定义体: inferInstanceAs SMulCommClass R S (Matrix m n A)

Depends on / 依赖: Matrix, SMulCommClass
-/
instance instSMulCommClass [SMul R A] [SMul S A] [SMulCommClass R S A] :
    SMulCommClass R S (CStarMatrix m n A) :=
inferInstanceAs SMulCommClass R S (Matrix m n A)

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul R S] [SMul R A] [SMul S A] [IsScalarTower R S A]
  body: inferInstanceAs IsScalarTower R S (Matrix m n A)

中文:
实例 instIsScalarTower
  签名: [标量乘法 R S] [标量乘法 R A] [标量乘法 S A] [标量塔 R S A]
  定义体: inferInstanceAs IsScalarTower R S (Matrix m n A)

Depends on / 依赖: IsScalarTower, Matrix
-/
instance instIsScalarTower [SMul R S] [SMul R A] [SMul S A] [IsScalarTower R S A] :
    IsScalarTower R S (CStarMatrix m n A) :=
inferInstanceAs IsScalarTower R S (Matrix m n A)

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul R A] [SMul Rᵐᵒᵖ A] [IsCentralScalar R A]
  body: inferInstanceAs IsCentralScalar R (Matrix m n A)

中文:
实例 instIsCentralScalar
  签名: [标量乘法 R A] [标量乘法 Rᵐᵒᵖ A] [中心标量 R A]
  定义体: inferInstanceAs IsCentralScalar R (Matrix m n A)

Depends on / 依赖: IsCentralScalar, Matrix
-/
instance instIsCentralScalar [SMul R A] [SMul Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (CStarMatrix m n A) :=
inferInstanceAs IsCentralScalar R (Matrix m n A)

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid R] [MulAction R A]
  body: inferInstanceAs MulAction R (Matrix m n A)

中文:
实例 instMulAction
  签名: [幺半群 R] [乘法作用 R A]
  定义体: inferInstanceAs MulAction R (Matrix m n A)

Depends on / 依赖: Matrix, MulAction
-/
instance instMulAction [Monoid R] [MulAction R A] : MulAction R (CStarMatrix m n A) :=
inferInstanceAs MulAction R (Matrix m n A)

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid R] [AddMonoid A] [DistribMulAction R A]
  body: inferInstanceAs DistribMulAction R (Matrix m n A)

中文:
实例 instDistribMulAction
  签名: [幺半群 R] [加法幺半群 A] [分配乘法作用 R A]
  定义体: inferInstanceAs DistribMulAction R (Matrix m n A)

Depends on / 依赖: DistribMulAction, Matrix
-/
instance instDistribMulAction [Monoid R] [AddMonoid A] [DistribMulAction R A] :
    DistribMulAction R (CStarMatrix m n A) :=
inferInstanceAs DistribMulAction R (Matrix m n A)

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [AddCommMonoid A] [Module R A]
  body: inferInstanceAs Module R (Matrix m n A)

@[simp]

中文:
实例 instModule
  签名: [半环 R] [加法交换幺半群 A] [模 R A]
  定义体: inferInstanceAs Module R (Matrix m n A)

@[simp]

Depends on / 依赖: Matrix, Module
-/
instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (CStarMatrix m n A) :=
inferInstanceAs Module R (Matrix m n A)

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: [Zero A] (i : m) (j : n)
  statement: (0 : CStarMatrix m n A) i j = 0
  proof: rfl

中文:
定理 zero_apply
  条件: [零 A] (i : m) (j : n)
  结论: (0 : CStarMatrix m n A) i j = 0
  证明: rfl
-/
theorem zero_apply [Zero A] (i : m) (j : n) : (0 : CStarMatrix m n A) i j = 0 := rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: [Add A] (M N : CStarMatrix m n A) (i : m) (j : n)
  proof: rfl

中文:
定理 add_apply
  条件: [加法 A] (M N : CStarMatrix m n A) (i : m) (j : n)
  证明: rfl
-/
@[simp] theorem add_apply [Add A] (M N : CStarMatrix m n A) (i : m) (j : n) :
    (M + N) i j = (M i j) + (N i j) := rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [SMul B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n)
  proof: rfl

中文:
定理 smul_apply
  条件: [标量乘法 B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n)
  证明: rfl
-/
@[simp] theorem smul_apply [SMul B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n) :
    (r • M) i j = r • (M i j) := rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: [Sub A] (M N : CStarMatrix m n A) (i : m) (j : n)
  proof: rfl

中文:
定理 sub_apply
  条件: [减法 A] (M N : CStarMatrix m n A) (i : m) (j : n)
  证明: rfl
-/
@[simp] theorem sub_apply [Sub A] (M N : CStarMatrix m n A) (i : m) (j : n) :
    (M - N) i j = (M i j) - (N i j) := rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: [Neg A] (M : CStarMatrix m n A) (i : m) (j : n)
  proof: rfl

@[simp]

中文:
定理 neg_apply
  条件: [取负 A] (M : CStarMatrix m n A) (i : m) (j : n)
  证明: rfl

@[simp]
-/
@[simp] theorem neg_apply [Neg A] (M : CStarMatrix m n A) (i : m) (j : n) :
    (-M) i j = -(M i j) := rfl

@[simp]
/--
theorem `conjTranspose_zero` / 定理 `conjTranspose_zero`

English:
theorem conjTranspose_zero
  given: [AddMonoid A] [StarAddMonoid A]
  proof: by ext; simp

中文:
定理 conjTranspose_zero
  条件: [加法幺半群 A] [StarAdd幺半群 A]
  证明: by ext; simp
-/
theorem conjTranspose_zero [AddMonoid A] [StarAddMonoid A] :
    conjTranspose (0 : CStarMatrix m n A) = 0 := by ext; simp


/--
theorem `of_zero` / 定理 `of_zero`

English:
theorem of_zero
  given: [Zero A]
  statement: ofMatrix (0 : Matrix m n A) = 0
  proof: rfl

中文:
定理 of_zero
  条件: [零 A]
  结论: ofMatrix (0 : 矩阵 m n A) = 0
  证明: rfl
-/
@[simp] theorem of_zero [Zero A] : ofMatrix (0 : Matrix m n A) = 0 := rfl

/--
theorem `of_add_of` / 定理 `of_add_of`

English:
theorem of_add_of
  given: [Add A] (f g : Matrix m n A)
  proof: rfl

@[simp]

中文:
定理 of_add_of
  条件: [加法 A] (f g : 矩阵 m n A)
  证明: rfl

@[simp]
-/
@[simp] theorem of_add_of [Add A] (f g : Matrix m n A) :
    ofMatrix f + ofMatrix g = ofMatrix (f + g) := rfl

@[simp]
/--
theorem `of_sub_of` / 定理 `of_sub_of`

English:
theorem of_sub_of
  given: [Sub A] (f g : Matrix m n A)
  statement: ofMatrix f - ofMatrix g = ofMatrix (f - g)
  proof: rfl

中文:
定理 of_sub_of
  条件: [减法 A] (f g : 矩阵 m n A)
  结论: ofMatrix f - ofMatrix g = ofMatrix (f - g)
  证明: rfl
-/
theorem of_sub_of [Sub A] (f g : Matrix m n A) : ofMatrix f - ofMatrix g = ofMatrix (f - g) :=
  rfl

/--
theorem `neg_of` / 定理 `neg_of`

English:
theorem neg_of
  given: [Neg A] (f : Matrix m n A)
  statement: -ofMatrix f = ofMatrix (-f)
  proof: rfl

中文:
定理 neg_of
  条件: [取负 A] (f : 矩阵 m n A)
  结论: -ofMatrix f = ofMatrix (-f)
  证明: rfl
-/
@[simp] theorem neg_of [Neg A] (f : Matrix m n A) : -ofMatrix f = ofMatrix (-f) := rfl

/--
theorem `smul_of` / 定理 `smul_of`

English:
theorem smul_of
  given: [SMul R A] (r : R) (f : Matrix m n A)
  proof: rfl

中文:
定理 smul_of
  条件: [标量乘法 R A] (r : R) (f : 矩阵 m n A)
  证明: rfl
-/
@[simp] theorem smul_of [SMul R A] (r : R) (f : Matrix m n A) :
    r • ofMatrix f = ofMatrix (r • f) := rfl

/--
theorem `star_apply` / 定理 `star_apply`

English:
theorem star_apply
  given: [Star A] {f : CStarMatrix n n A} {i j : n}
  proof: by
  rw [star_eq_conjTranspose]; rw [conjTranspose_apply]

中文:
定理 star_apply
  条件: [对合 A] {f : CStarMatrix n n A} {i j : n}
  证明: by
  rw [star_eq_conjTranspose]; rw [conjTranspose_apply]

Depends on / 依赖: conjTranspose_apply, star_eq_conjTranspose
-/
theorem star_apply [Star A] {f : CStarMatrix n n A} {i j : n} :
    (star f) i j = star (f j i) := by
  rw [star_eq_conjTranspose]; rw [conjTranspose_apply]

/--
theorem `star_apply_of_isSelfAdjoint` / 定理 `star_apply_of_isSelfAdjoint`

English:
theorem star_apply_of_isSelfAdjoint
  statement: [Star A] {f : CStarMatrix n n A} (hf : IsSelfAdjoint f)
  proof: by
  rw [← star_apply]; rw [IsSelfAdjoint.star_eq hf]

中文:
定理 star_apply_of_isSelfAdjoint
  结论: [对合 A] {f : CStarMatrix n n A} (hf : IsSelfAdjoint f)
  证明: by
  rw [← star_apply]; rw [IsSelfAdjoint.star_eq hf]

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.star_eq, star_apply, star_eq
-/
theorem star_apply_of_isSelfAdjoint [Star A] {f : CStarMatrix n n A} (hf : IsSelfAdjoint f)
    {i j : n} : star (f i j) = f j i := by
  rw [← star_apply]; rw [IsSelfAdjoint.star_eq hf]

/--
Instance `instStarAddMonoid` / 实例 `instStarAddMonoid`

English:
instance instStarAddMonoid
  signature: [AddMonoid A] [StarAddMonoid A]
  body: star_add (R := Matrix n n A)

中文:
实例 instStarAddMonoid
  签名: [加法幺半群 A] [StarAdd幺半群 A]
  定义体: star_add (R := Matrix n n A)

Depends on / 依赖: Matrix, star_add
-/
instance instStarAddMonoid [AddMonoid A] [StarAddMonoid A] : StarAddMonoid (CStarMatrix n n A) where
  star_add := star_add (R := Matrix n n A)

/--
Instance `instStarModule` / 实例 `instStarModule`

English:
instance instStarModule
  signature: [Star R] [Star A] [SMul R A] [StarModule R A]
  body: star_smul r (ofMatrix.symm a)

中文:
实例 instStarModule
  签名: [对合 R] [对合 A] [标量乘法 R A] [对合模 R A]
  定义体: star_smul r (ofMatrix.symm a)

Depends on / 依赖: ofMatrix, ofMatrix.symm, star_smul
-/
instance instStarModule [Star R] [Star A] [SMul R A] [StarModule R A] :
    StarModule R (CStarMatrix n n A) where
  star_smul r a := star_smul r (ofMatrix.symm a)

/--
Definition of `ofMatrixₗ` / `ofMatrixₗ` 的定义

English:
definition ofMatrixₗ
  signature: [AddCommMonoid A] [Semiring R] [Module R A]
  body: LinearEquiv.refl _ _

中文:
定义 ofMatrixₗ
  签名: [加法交换幺半群 A] [半环 R] [模 R A]
  定义体: LinearEquiv.refl _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def ofMatrixₗ [AddCommMonoid A] [Semiring R] [Module R A] :
    (Matrix m n A) ≃ₗ[R] CStarMatrix m n A := LinearEquiv.refl _ _

/-- The semilinear map constructed by applying a semilinear map to all the entries of the matrix. -/
@[simps]
/--
Definition of `mapₗ` / `mapₗ` 的定义

English:
definition mapₗ
  signature: [Semiring R] [Semiring S] {σ : R ->+* S} [AddCommMonoid A] [AddCommMonoid B]
  body: fun M => M.map f
  map_add' M N := by ext; simp
  map_smul' r M := by ext; simp

中文:
定义 mapₗ
  签名: [半环 R] [半环 S] {σ : R ->+* S} [加法交换幺半群 A] [加法交换幺半群 B]
  定义体: fun M => M.map f
  map_add' M N := by ext; simp
  map_smul' r M := by ext; simp

Depends on / 依赖: M.map
-/
def mapₗ [Semiring R] [Semiring S] {σ : R ->+* S} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module S B] (f : A ->ₛₗ[σ] B) : CStarMatrix m n A ->ₛₗ[σ] CStarMatrix m n B where
  toFun := fun M => M.map f
  map_add' M N := by ext; simp
  map_smul' r M := by ext; simp

section decidable

variable [DecidableEq n]

section zero_one

variable [Zero A] [One A]

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (CStarMatrix n n A)
  body: inferInstanceAs One (Matrix n n A)

中文:
实例 instOne
  签名: : 幺 (CStarMatrix n n A)
  定义体: inferInstanceAs One (Matrix n n A)

Depends on / 依赖: Matrix
-/
instance instOne : One (CStarMatrix n n A) := inferInstanceAs One (Matrix n n A)

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: {i j}
  statement: (1 : CStarMatrix n n A) i j = if i = j then 1 else 0
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: {i j}
  结论: (1 : CStarMatrix n n A) i j = if i = j then 1 else 0
  证明: rfl

@[simp]
-/
theorem one_apply {i j} : (1 : CStarMatrix n n A) i j = if i = j then 1 else 0 := rfl

@[simp]
/--
theorem `one_apply_eq` / 定理 `one_apply_eq`

English:
theorem one_apply_eq
  given: (i)
  statement: (1 : CStarMatrix n n A) i i = 1
  proof: Matrix.one_apply_eq _

中文:
定理 one_apply_eq
  条件: (i)
  结论: (1 : CStarMatrix n n A) i i = 1
  证明: Matrix.one_apply_eq _

Depends on / 依赖: Matrix, Matrix.one_apply_eq, one_apply_eq
-/
theorem one_apply_eq (i) : (1 : CStarMatrix n n A) i i = 1 := Matrix.one_apply_eq _

/--
theorem `one_apply_ne` / 定理 `one_apply_ne`

English:
theorem one_apply_ne
  given: {i j}
  statement: i != j -> (1 : CStarMatrix n n A) i j = 0
  proof: Matrix.one_apply_ne

中文:
定理 one_apply_ne
  条件: {i j}
  结论: i != j -> (1 : CStarMatrix n n A) i j = 0
  证明: Matrix.one_apply_ne
-/
@[simp] theorem one_apply_ne {i j} : i != j -> (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne

/--
theorem `one_apply_ne'` / 定理 `one_apply_ne'`

English:
theorem one_apply_ne'
  given: {i j}
  statement: j != i -> (1 : CStarMatrix n n A) i j = 0
  proof: Matrix.one_apply_ne'

中文:
定理 one_apply_ne'
  条件: {i j}
  结论: j != i -> (1 : CStarMatrix n n A) i j = 0
  证明: Matrix.one_apply_ne'

Depends on / 依赖: Matrix, Matrix.one_apply_ne, one_apply_ne
-/
theorem one_apply_ne' {i j} : j != i -> (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne'

end zero_one

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: [AddMonoidWithOne A]
  body: inferInstanceAs AddMonoidWithOne (Matrix n n A)

中文:
实例 instAddMonoidWithOne
  签名: [加法带幺幺半群 A]
  定义体: inferInstanceAs AddMonoidWithOne (Matrix n n A)

Depends on / 依赖: AddMonoidWithOne, Matrix
-/
instance instAddMonoidWithOne [AddMonoidWithOne A] : AddMonoidWithOne (CStarMatrix n n A) :=
inferInstanceAs AddMonoidWithOne (Matrix n n A)

/--
Instance `instAddGroupWithOne` / 实例 `instAddGroupWithOne`

English:
instance instAddGroupWithOne
  signature: [AddGroupWithOne A]
  body: inferInstanceAs AddGroupWithOne (Matrix n n A)

中文:
实例 instAddGroupWithOne
  签名: [加法带幺群 A]
  定义体: inferInstanceAs AddGroupWithOne (Matrix n n A)

Depends on / 依赖: AddGroupWithOne, Matrix
-/
instance instAddGroupWithOne [AddGroupWithOne A] : AddGroupWithOne (CStarMatrix n n A) :=
inferInstanceAs AddGroupWithOne (Matrix n n A)

/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: [AddCommMonoidWithOne A]
  body: inferInstanceAs AddCommMonoidWithOne (Matrix n n A)

中文:
实例 instAddCommMonoidWithOne
  签名: [加法交换带幺幺半群 A]
  定义体: inferInstanceAs AddCommMonoidWithOne (Matrix n n A)

Depends on / 依赖: AddCommMonoidWithOne, Matrix
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne A] :
    AddCommMonoidWithOne (CStarMatrix n n A) :=
inferInstanceAs AddCommMonoidWithOne (Matrix n n A)

/--
Instance `instAddCommGroupWithOne` / 实例 `instAddCommGroupWithOne`

English:
instance instAddCommGroupWithOne
  signature: [AddCommGroupWithOne A]
  body: inferInstanceAs AddCommGroupWithOne (Matrix n n A)

中文:
实例 instAddCommGroupWithOne
  签名: [加法交换带幺群 A]
  定义体: inferInstanceAs AddCommGroupWithOne (Matrix n n A)

Depends on / 依赖: AddCommGroupWithOne, Matrix
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne A] :
    AddCommGroupWithOne (CStarMatrix n n A) :=
inferInstanceAs AddCommGroupWithOne (Matrix n n A)

-- We want to be lower priority than `instHMul`, but without this we can't have operands with
-- implicit dimensions.
@[default_instance 100]
instance {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] :
    HMul (CStarMatrix l m A) (CStarMatrix m n A) (CStarMatrix l n A) where
  hMul M N := ofMatrix (ofMatrix.symm M * ofMatrix.symm N)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: n] [Mul A] [AddCommMonoid A] : Mul (CStarMatrix n n A) where mul M N
  body: M * N

中文:
实例 [有限类型
  签名: n] [乘法 A] [加法交换幺半群 A] : 乘法 (CStarMatrix n n A) where mul M N
  定义体: M * N
-/
instance [Fintype n] [Mul A] [AddCommMonoid A] : Mul (CStarMatrix n n A) where mul M N := M * N

end decidable

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  statement: {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
  proof: rfl

中文:
定理 mul_apply
  结论: {l : 类型} [有限类型 m] [乘法 A] [加法交换幺半群 A] {M : CStarMatrix l m A}
  证明: rfl
-/
theorem mul_apply {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = ∑ j, M i j * N j k := rfl

/--
theorem `mul_apply'` / 定理 `mul_apply'`

English:
theorem mul_apply'
  statement: {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
  proof: rfl

@[simp]

中文:
定理 mul_apply'
  结论: {l : 类型} [有限类型 m] [乘法 A] [加法交换幺半群 A] {M : CStarMatrix l m A}
  证明: rfl

@[simp]
-/
theorem mul_apply' {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k := rfl

@[simp]
/--
theorem `smul_mul` / 定理 `smul_mul`

English:
theorem smul_mul
  statement: {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
  proof: Matrix.smul_mul a M N

中文:
定理 smul_mul
  结论: {l : 类型} [有限类型 n] [幺半群 R] [加法交换幺半群 A] [乘法 A] [分配乘法作用 R A]
  证明: Matrix.smul_mul a M N

Depends on / 依赖: Matrix, Matrix.smul_mul, smul_mul
-/
theorem smul_mul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [IsScalarTower R A A] (a : R) (M : CStarMatrix m n A) (N : CStarMatrix n l A) :
    (a • M) * N = a • (M * N) := Matrix.smul_mul a M N

/--
theorem `mul_smul` / 定理 `mul_smul`

English:
theorem mul_smul
  statement: {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
  proof: Matrix.mul_smul M a N

@[simp]

中文:
定理 mul_smul
  结论: {l : 类型} [有限类型 n] [幺半群 R] [加法交换幺半群 A] [乘法 A] [分配乘法作用 R A]
  证明: Matrix.mul_smul M a N

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_smul, mul_smul
-/
theorem mul_smul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [SMulCommClass R A A] (M : CStarMatrix m n A) (a : R) (N : CStarMatrix n l A) :
    M * (a • N) = a • (M * N) := Matrix.mul_smul M a N

@[simp]
/--
theorem `mul_zero` / 定理 `mul_zero`

English:
theorem mul_zero
  statement: {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
  proof: Matrix.mul_zero _

@[simp]

中文:
定理 mul_zero
  结论: {o : 类型} [有限类型 n] [非幺非结合半环 A]
  证明: Matrix.mul_zero _

@[simp]
-/
protected theorem mul_zero {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (0 : CStarMatrix n o A) = 0 := Matrix.mul_zero _

@[simp]
/--
theorem `zero_mul` / 定理 `zero_mul`

English:
theorem zero_mul
  statement: {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
  proof: Matrix.zero_mul _

中文:
定理 zero_mul
  结论: {l : 类型} [有限类型 m] [非幺非结合半环 A]
  证明: Matrix.zero_mul _
-/
protected theorem zero_mul {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix m n A) : (0 : CStarMatrix l m A) * M = 0 := Matrix.zero_mul _

/--
theorem `mul_add` / 定理 `mul_add`

English:
theorem mul_add
  statement: {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
  proof: Matrix.mul_add _ _ _

中文:
定理 mul_add
  结论: {o : 类型} [有限类型 n] [非幺非结合半环 A]
  证明: Matrix.mul_add _ _ _
-/
protected theorem mul_add {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
    (L : CStarMatrix m n A) (M N : CStarMatrix n o A) :
    L * (M + N) = L * M + L * N := Matrix.mul_add _ _ _

/--
theorem `add_mul` / 定理 `add_mul`

English:
theorem add_mul
  statement: {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
  proof: Matrix.add_mul _ _ _

中文:
定理 add_mul
  结论: {l : 类型} [有限类型 m] [非幺非结合半环 A]
  证明: Matrix.add_mul _ _ _
-/
protected theorem add_mul {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L + M) * N = L * N + M * N := Matrix.add_mul _ _ _

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [Fintype n] [NonUnitalNonAssocSemiring A]
  body: inferInstanceAs NonUnitalNonAssocSemiring (Matrix n n A)

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [有限类型 n] [非幺非结合半环 A]
  定义体: inferInstanceAs NonUnitalNonAssocSemiring (Matrix n n A)

Depends on / 依赖: Matrix, NonUnitalNonAssocSemiring
-/
instance instNonUnitalNonAssocSemiring [Fintype n] [NonUnitalNonAssocSemiring A] :
    NonUnitalNonAssocSemiring (CStarMatrix n n A) :=
inferInstanceAs NonUnitalNonAssocSemiring (Matrix n n A)

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [Fintype n] [NonUnitalNonAssocRing A]
  body: inferInstanceAs NonUnitalNonAssocRing (Matrix n n A)

中文:
实例 instNonUnitalNonAssocRing
  签名: [有限类型 n] [非幺非结合环 A]
  定义体: inferInstanceAs NonUnitalNonAssocRing (Matrix n n A)

Depends on / 依赖: Matrix, NonUnitalNonAssocRing
-/
instance instNonUnitalNonAssocRing [Fintype n] [NonUnitalNonAssocRing A] :
    NonUnitalNonAssocRing (CStarMatrix n n A) :=
inferInstanceAs NonUnitalNonAssocRing (Matrix n n A)

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [Fintype n] [NonUnitalSemiring A]
  body: inferInstanceAs NonUnitalSemiring (Matrix n n A)

中文:
实例 instNonUnitalSemiring
  签名: [有限类型 n] [非幺半环 A]
  定义体: inferInstanceAs NonUnitalSemiring (Matrix n n A)

Depends on / 依赖: Matrix, NonUnitalSemiring
-/
instance instNonUnitalSemiring [Fintype n] [NonUnitalSemiring A] :
    NonUnitalSemiring (CStarMatrix n n A) :=
inferInstanceAs NonUnitalSemiring (Matrix n n A)

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [Fintype n] [DecidableEq n] [NonAssocSemiring A]
  body: inferInstanceAs NonAssocSemiring (Matrix n n A)

中文:
实例 instNonAssocSemiring
  签名: [有限类型 n] [DecidableEq n] [非结合半环 A]
  定义体: inferInstanceAs NonAssocSemiring (Matrix n n A)

Depends on / 依赖: Matrix, NonAssocSemiring
-/
instance instNonAssocSemiring [Fintype n] [DecidableEq n] [NonAssocSemiring A] :
    NonAssocSemiring (CStarMatrix n n A) :=
inferInstanceAs NonAssocSemiring (Matrix n n A)

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [Fintype n] [NonUnitalRing A]
  body: inferInstanceAs NonUnitalRing (Matrix n n A)

中文:
实例 instNonUnitalRing
  签名: [有限类型 n] [非幺环 A]
  定义体: inferInstanceAs NonUnitalRing (Matrix n n A)

Depends on / 依赖: Matrix, NonUnitalRing
-/
instance instNonUnitalRing [Fintype n] [NonUnitalRing A] :
    NonUnitalRing (CStarMatrix n n A) :=
inferInstanceAs NonUnitalRing (Matrix n n A)

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [Fintype n] [DecidableEq n] [NonAssocRing A]
  body: inferInstanceAs NonAssocRing (Matrix n n A)

中文:
实例 instNonAssocRing
  签名: [有限类型 n] [DecidableEq n] [非结合环 A]
  定义体: inferInstanceAs NonAssocRing (Matrix n n A)

Depends on / 依赖: Matrix, NonAssocRing
-/
instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing A] :
    NonAssocRing (CStarMatrix n n A) :=
inferInstanceAs NonAssocRing (Matrix n n A)

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Fintype n] [DecidableEq n] [Semiring A]
  body: inferInstanceAs Semiring (Matrix n n A)

中文:
实例 instSemiring
  签名: [有限类型 n] [DecidableEq n] [半环 A]
  定义体: inferInstanceAs Semiring (Matrix n n A)

Depends on / 依赖: Matrix, Semiring
-/
instance instSemiring [Fintype n] [DecidableEq n] [Semiring A] :
    Semiring (CStarMatrix n n A) :=
inferInstanceAs Semiring (Matrix n n A)

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Fintype n] [DecidableEq n] [Ring A]
  body: inferInstanceAs Ring (Matrix n n A)

中文:
实例 instRing
  签名: [有限类型 n] [DecidableEq n] [环 A]
  定义体: inferInstanceAs Ring (Matrix n n A)

Depends on / 依赖: Matrix
-/
instance instRing [Fintype n] [DecidableEq n] [Ring A] : Ring (CStarMatrix n n A) :=
inferInstanceAs Ring (Matrix n n A)

/--
Definition of `ofMatrixRingEquiv` / `ofMatrixRingEquiv` 的定义

English:
definition ofMatrixRingEquiv
  signature: [Fintype n] [Semiring A]
  body: { ofMatrix with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 ofMatrixRingEquiv
  签名: [有限类型 n] [半环 A]
  定义体: { ofMatrix with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: map_add, map_mul, ofMatrix
-/
def ofMatrixRingEquiv [Fintype n] [Semiring A] :
    Matrix n n A ≃+* CStarMatrix n n A :=
  { ofMatrix with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: [Fintype n] [NonUnitalSemiring A] [StarRing A]
  body: inferInstanceAs StarRing (Matrix n n A)

中文:
实例 instStarRing
  签名: [有限类型 n] [非幺半环 A] [对合环 A]
  定义体: inferInstanceAs StarRing (Matrix n n A)

Depends on / 依赖: Matrix, StarRing
-/
instance instStarRing [Fintype n] [NonUnitalSemiring A] [StarRing A] :
StarRing (CStarMatrix n n A) := inferInstanceAs StarRing (Matrix n n A)

/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A]
  body: inferInstanceAs Algebra R (Matrix n n A)

中文:
实例 instAlgebra
  签名: [有限类型 n] [DecidableEq n] [交换半环 R] [半环 A] [代数 R A]
  定义体: inferInstanceAs Algebra R (Matrix n n A)

Depends on / 依赖: Algebra, Matrix
-/
instance instAlgebra [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] :
Algebra R (CStarMatrix n n A) := inferInstanceAs Algebra R (Matrix n n A)

/--
Definition of `ofMatrixStarAlgEquiv` / `ofMatrixStarAlgEquiv` 的定义

English:
definition ofMatrixStarAlgEquiv
  signature: [Fintype n] [SMul Complex A] [Semiring A] [StarRing A]
  body: { ofMatrixRingEquiv with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }

中文:
定义 ofMatrixStarAlgEquiv
  签名: [有限类型 n] [标量乘法 复形 A] [半环 A] [对合环 A]
  定义体: { ofMatrixRingEquiv with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: map_smul, map_star, ofMatrixRingEquiv
-/
def ofMatrixStarAlgEquiv [Fintype n] [SMul Complex A] [Semiring A] [StarRing A] :
    Matrix n n A ≃⋆ₐ[Complex] CStarMatrix n n A :=
  { ofMatrixRingEquiv with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }

/--
lemma `ofMatrix_eq_ofMatrixStarAlgEquiv` / 引理 `ofMatrix_eq_ofMatrixStarAlgEquiv`

English:
lemma ofMatrix_eq_ofMatrixStarAlgEquiv
  given: [Fintype n] [SMul Complex A] [Semiring A] [StarRing A]
  proof: rfl

中文:
引理 ofMatrix_eq_ofMatrixStarAlgEquiv
  条件: [有限类型 n] [标量乘法 复形 A] [半环 A] [对合环 A]
  证明: rfl
-/
lemma ofMatrix_eq_ofMatrixStarAlgEquiv [Fintype n] [SMul Complex A] [Semiring A] [StarRing A] :
    (ofMatrix : Matrix n n A -> CStarMatrix n n A)
      = (ofMatrixStarAlgEquiv : Matrix n n A -> CStarMatrix n n A) := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (R) (A) in
/--
Definition of `reindexₗ` / `reindexₗ` 的定义

English:
definition reindexₗ
  signature: {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  body: { Matrix.reindex eₘ eₙ with
    map_add' M N := by ext; simp
    map_smul' r M := by ext; simp }

@[simp]

中文:
定义 reindexₗ
  签名: {l o : 类型} [半环 R] [加法交换幺半群 A] [模 R A]
  定义体: { Matrix.reindex eₘ eₙ with
    map_add' M N := by ext; simp
    map_smul' r M := by ext; simp }

@[simp]

Depends on / 依赖: Matrix, Matrix.reindex, map_add, map_smul, reindex
-/
def reindexₗ {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) : CStarMatrix m n A ≃ₗ[R] CStarMatrix l o A :=
  { Matrix.reindex eₘ eₙ with
    map_add' M N := by ext; simp
    map_smul' r M := by ext; simp }

@[simp]
/--
lemma `reindexₗ_apply` / 引理 `reindexₗ_apply`

English:
lemma reindexₗ_apply
  statement: {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  proof: rfl

中文:
引理 reindexₗ_apply
  结论: {l o : 类型} [半环 R] [加法交换幺半群 A] [模 R A]
  证明: rfl
-/
lemma reindexₗ_apply {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    {eₘ : m ≃ l} {eₙ : n ≃ o} {M : CStarMatrix m n A} {i : l} {j : o} :
    reindexₗ R A eₘ eₙ M i j = Matrix.reindex eₘ eₙ M i j := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `reindexₐ` / `reindexₐ` 的定义

English:
definition reindexₐ
  signature: (R) (A) [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
  body: { reindexₗ R A e e with
    map_mul' M N := by
      ext i j
      simp only [mul_apply]
      refine Fintype.sum_equiv e _ _ ?_
      intro k
      simp
    map_star' M := by
      ext
      unfold reindexₗ
      dsimp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Matrix.reindex_symm, AddHom.toFun

中文:
定义 reindexₐ
  签名: (R) (A) [有限类型 m] [有限类型 n] [半环 R] [加法交换幺半群 A] [乘法 A] [模 R A]
  定义体: { reindexₗ R A e e with
    map_mul' M N := by
      ext i j
      simp only [mul_apply]
      refine Fintype.sum_equiv e _ _ ?_
      intro k
      simp
    map_star' M := by
      ext
      unfold reindexₗ
      dsimp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Matrix.reindex_symm, AddHom.toFun

Depends on / 依赖: AddHom, AddHom.coe_mk, AddHom.toFun_eq_coe, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Fintype, Fintype.sum_equiv, Matrix, Matrix.reindex_apply, Matrix.reindex_symm, Matrix.submatrix_apply, coe_mk, invFun_as_coe, map_mul, map_star, mul_apply, reindex_apply, reindex_symm, star_apply, submatrix_apply
-/
def reindexₐ (R) (A) [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] (e : m ≃ n) : CStarMatrix m m A ≃⋆ₐ[R] CStarMatrix n n A :=
  { reindexₗ R A e e with
    map_mul' M N := by
      ext i j
      simp only [mul_apply]
      refine Fintype.sum_equiv e _ _ ?_
      intro k
      simp
    map_star' M := by
      ext
      unfold reindexₗ
      dsimp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Matrix.reindex_symm, AddHom.toFun_eq_coe,
        AddHom.coe_mk, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [star_apply]; rw [star_apply]
      simp [Matrix.submatrix_apply] }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `reindexₐ_apply` / 引理 `reindexₐ_apply`

English:
lemma reindexₐ_apply
  statement: [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A]
  proof: rfl

中文:
引理 reindexₐ_apply
  结论: [有限类型 m] [有限类型 n] [半环 R] [加法交换幺半群 A] [乘法 A] [对合 A]
  证明: rfl
-/
lemma reindexₐ_apply [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A]
    [Module R A] {e : m ≃ n} {M : CStarMatrix m m A}
    {i : n} {j : n} : reindexₐ R A e M i j = Matrix.reindex e e M i j := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mapₗ_reindexₐ` / 引理 `mapₗ_reindexₐ`

English:
lemma mapₗ_reindexₐ
  statement: [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
  proof: rfl

中文:
引理 mapₗ_reindexₐ
  结论: [有限类型 m] [有限类型 n] [半环 R] [加法交换幺半群 A] [乘法 A] [模 R A]
  证明: rfl
-/
lemma mapₗ_reindexₐ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] [AddCommMonoid B] [Mul B] [Module R B] [Star B] {e : m ≃ n} {M : CStarMatrix m m A}
    (φ : A ->ₗ[R] B) : reindexₐ R B e (M.mapₗ φ) = ((reindexₐ R A e M).mapₗ φ) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `reindexₐ_symm` / 引理 `reindexₐ_symm`

English:
lemma reindexₐ_symm
  statement: [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
  proof: by
  simp [reindexₐ, reindexₗ]

中文:
引理 reindexₐ_symm
  结论: [有限类型 m] [有限类型 n] [半环 R] [加法交换幺半群 A] [乘法 A] [模 R A]
  证明: by
  simp [reindexₐ, reindexₗ]
-/
lemma reindexₐ_symm [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] {e : m ≃ n} : reindexₐ R A e.symm = (reindexₐ R A e).symm := by
  simp [reindexₐ, reindexₗ]

set_option backward.isDefEq.respectTransparency.types false in
/-- Applying a non-unital ⋆-algebra homomorphism to every entry of a matrix is itself a
⋆-algebra homomorphism on matrices. -/
@[simps]
/--
Definition of `mapₙₐ` / `mapₙₐ` 的定义

English:
definition mapₙₐ
  signature: [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  body: fun M => M.mapₗ (f : A ->ₗ[R] B)
  map_smul' := by simp
  map_zero' := by simp [map_zero]
  map_add' := by simp [map_add]
  map_mul' M N := by
    ext
    -- Un-squeezing this `simp` seems to add about half a second elaboration time.
    simp only [mapₗ_apply, map, LinearMap.coe_coe, ofMatrix_apply,

中文:
定义 mapₙₐ
  签名: [有限类型 n] [半环 R] [非幺非结合半环 A] [模 R A]
  定义体: fun M => M.mapₗ (f : A ->ₗ[R] B)
  map_smul' := by simp
  map_zero' := by simp [map_zero]
  map_add' := by simp [map_add]
  map_mul' M N := by
    ext
    -- Un-squeezing this `simp` seems to add about half a second elaboration time.
    simp only [mapₗ_apply, map, LinearMap.coe_coe, ofMatrix_apply,

Depends on / 依赖: M.map
-/
def mapₙₐ [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A ->⋆ₙₐ[R] B) :
    CStarMatrix n n A ->⋆ₙₐ[R] CStarMatrix n n B where
  toFun := fun M => M.mapₗ (f : A ->ₗ[R] B)
  map_smul' := by simp
  map_zero' := by simp [map_zero]
  map_add' := by simp [map_add]
  map_mul' M N := by
    ext
    -- Un-squeezing this `simp` seems to add about half a second elaboration time.
    simp only [mapₗ_apply, map, LinearMap.coe_coe, ofMatrix_apply, mul_apply, map_sum, map_mul,
      ofMatrix_apply]
  map_star' M := by ext; simp [map, star_apply, map_star]

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  statement: [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
  proof: rfl

中文:
定理 algebraMap_apply
  结论: [有限类型 n] [DecidableEq n] [交换半环 R] [半环 A]
  证明: rfl
-/
theorem algebraMap_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Algebra R A] {r : R} {i j : n} :
    (algebraMap R (CStarMatrix n n A) r) i j = if i = j then algebraMap R A r else 0 := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (n) (R) (A) in
/--
Definition of `toOneByOne` / `toOneByOne` 的定义

English:
definition toOneByOne
  signature: [Unique n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A] [Module R A]
  body: fun x y => a
  invFun M := M default default
  left_inv := by intro; simp
  right_inv := by
    intro
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  map_mul' _ _ := by ext; simp [mul_apply]
  map_add' _ _ := by ext; simp
  map_star' _ := by ext; simp [star_eq_conjT

中文:
定义 toOneByOne
  签名: [唯一 n] [半环 R] [加法交换幺半群 A] [乘法 A] [对合 A] [模 R A]
  定义体: fun x y => a
  invFun M := M default default
  left_inv := by intro; simp
  right_inv := by
    intro
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  map_mul' _ _ := by ext; simp [mul_apply]
  map_add' _ _ := by ext; simp
  map_star' _ := by ext; simp [star_eq_conjT
-/
def toOneByOne [Unique n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A] [Module R A] :
    A ≃⋆ₐ[R] CStarMatrix n n A where
  toFun a := fun x y => a
  invFun M := M default default
  left_inv := by intro; simp
  right_inv := by
    intro
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  map_mul' _ _ := by ext; simp [mul_apply]
  map_add' _ _ := by ext; simp
  map_star' _ := by ext; simp [star_eq_conjTranspose]
  map_smul' _ _ := by ext; simp

end basic

variable [Fintype m] [NonUnitalCStarAlgebra A]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toCLM` / `toCLM` 的定义

English:
definition toCLM
  signature: : CStarMatrix m n A ->ₗ[Complex] C⋆ᵐᵒᵈ(A, m -> A) ->L[Complex] C⋆ᵐᵒᵈ(A, n -> A) where
  body: { toFun := (WithCStarModule.equivL Complex).symm ∘ M.vecMul ∘ WithCStarModule.equivL Complex
               map_add' := M.add_vecMul
               map_smul' := M.smul_vecMul }
  map_add' M₁ M₂ := by
    ext
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_a

中文:
定义 toCLM
  签名: : CStarMatrix m n A ->ₗ[复形] C⋆ᵐᵒᵈ(A, m -> A) ->L[复形] C⋆ᵐᵒᵈ(A, n -> A) where
  定义体: { toFun := (WithCStarModule.equivL Complex).symm ∘ M.vecMul ∘ WithCStarModule.equivL Complex
               map_add' := M.add_vecMul
               map_smul' := M.smul_vecMul }
  map_add' M₁ M₂ := by
    ext
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_a

Depends on / 依赖: M.vecMul, WithCStarModule, WithCStarModule.equivL, equivL, vecMul
-/
noncomputable def toCLM : CStarMatrix m n A ->ₗ[Complex] C⋆ᵐᵒᵈ(A, m -> A) ->L[Complex] C⋆ᵐᵒᵈ(A, n -> A) where
  toFun M := { toFun := (WithCStarModule.equivL Complex).symm ∘ M.vecMul ∘ WithCStarModule.equivL Complex
               map_add' := M.add_vecMul
               map_smul' := M.smul_vecMul }
  map_add' M₁ M₂ := by
    ext
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, _root_.add_apply, WithCStarModule.add_apply]
    rw [Matrix.vecMul_add]; rw [Pi.add_apply]
  map_smul' c M := by
    ext x i
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, _root_.smul_apply,
      WithCStarModule.smul_apply, RingHom.id_apply]
    rw [Matrix.vecMul_smul]; rw [Pi.smul_apply]

/--
lemma `toCLM_apply` / 引理 `toCLM_apply`

English:
lemma toCLM_apply
  given: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)}
  proof: rfl

中文:
引理 toCLM_apply
  条件: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)}
  证明: rfl
-/
lemma toCLM_apply {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)} :
    toCLM M v = (WithCStarModule.equiv _ _).symm (M.vecMul v) := rfl

/--
lemma `toCLM_apply_eq_sum` / 引理 `toCLM_apply_eq_sum`

English:
lemma toCLM_apply_eq_sum
  given: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)}
  proof: by
  ext i
  simp [toCLM_apply, Matrix.vecMul, dotProduct]

中文:
引理 toCLM_apply_eq_sum
  条件: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)}
  证明: by
  ext i
  simp [toCLM_apply, Matrix.vecMul, dotProduct]

Depends on / 依赖: Matrix, Matrix.vecMul, dotProduct, toCLM_apply, vecMul
-/
lemma toCLM_apply_eq_sum {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)} :
    toCLM M v = (WithCStarModule.equiv _ _).symm (fun j => ∑ i, v i * M i j) := by
  ext i
  simp [toCLM_apply, Matrix.vecMul, dotProduct]



set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toCLMNonUnitalAlgHom` / `toCLMNonUnitalAlgHom` 的定义

English:
definition toCLMNonUnitalAlgHom
  signature: [Fintype n]
  body: { (MulOpposite.opLinearEquiv Complex).toLinearMap ∘ₗ (toCLM (n := n) (m := n)) with
    map_zero' := by simp
    map_mul' := by
      intros
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv, Function.comp_app

中文:
定义 toCLMNonUnitalAlgHom
  签名: [有限类型 n]
  定义体: { (MulOpposite.opLinearEquiv Complex).toLinearMap ∘ₗ (toCLM (n := n) (m := n)) with
    map_zero' := by simp
    map_mul' := by
      intros
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv, Function.comp_app

Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.coe_toAddHom, MulOpposite, MulOpposite.coe_opLinearEquiv, MulOpposite.opLinearEquiv, MulOpposite.op_inj, MulOpposite.op_mul, coe_coe, coe_comp, coe_opLinearEquiv, coe_toAddHom, comp_apply, intros
-/
noncomputable def toCLMNonUnitalAlgHom [Fintype n] :
    CStarMatrix n n A ->ₙₐ[Complex] (C⋆ᵐᵒᵈ(A, n -> A) ->L[Complex] C⋆ᵐᵒᵈ(A, n -> A))ᵐᵒᵖ :=
  { (MulOpposite.opLinearEquiv Complex).toLinearMap ∘ₗ (toCLM (n := n) (m := n)) with
    map_zero' := by simp
    map_mul' := by
      intros
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv, Function.comp_apply,
        ← MulOpposite.op_mul, MulOpposite.op_inj]
      ext
      simp [toCLM] }

/--
lemma `toCLMNonUnitalAlgHom_eq_toCLM` / 引理 `toCLMNonUnitalAlgHom_eq_toCLM`

English:
lemma toCLMNonUnitalAlgHom_eq_toCLM
  given: [Fintype n] {M : CStarMatrix n n A}
  proof: rfl

中文:
引理 toCLMNonUnitalAlgHom_eq_toCLM
  条件: [有限类型 n] {M : CStarMatrix n n A}
  证明: rfl

Depends on / 依赖: MulOpposite, MulOpposite.op
-/
lemma toCLMNonUnitalAlgHom_eq_toCLM [Fintype n] {M : CStarMatrix n n A} :
    toCLMNonUnitalAlgHom (A := A) M = MulOpposite.op (toCLM M) := rfl

set_option backward.isDefEq.respectTransparency false in
open WithCStarModule in
@[simp high]
/--
lemma `toCLM_apply_single` / 引理 `toCLM_apply_single`

English:
lemma toCLM_apply_single
  given: [DecidableEq m] {M : CStarMatrix m n A} {i : m} (a : A)
  proof: by
  ext
  simp [toCLM_apply, equiv, Equiv.refl]

中文:
引理 toCLM_apply_single
  条件: [DecidableEq m] {M : CStarMatrix m n A} {i : m} (a : A)
  证明: by
  ext
  simp [toCLM_apply, equiv, Equiv.refl]

Depends on / 依赖: Equiv.refl, toCLM_apply
-/
lemma toCLM_apply_single [DecidableEq m] {M : CStarMatrix m n A} {i : m} (a : A) :
    (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) = (equiv _ _).symm (fun j => a * M i j) := by
  ext
  simp [toCLM_apply, equiv, Equiv.refl]

open WithCStarModule in
/--
lemma `toCLM_apply_single_apply` / 引理 `toCLM_apply_single_apply`

English:
lemma toCLM_apply_single_apply
  given: [DecidableEq m] {M : CStarMatrix m n A} {i : m} {j : n} (a : A)
  proof: by simp

中文:
引理 toCLM_apply_single_apply
  条件: [DecidableEq m] {M : CStarMatrix m n A} {i : m} {j : n} (a : A)
  证明: by simp
-/
lemma toCLM_apply_single_apply [DecidableEq m] {M : CStarMatrix m n A} {i : m} {j : n} (a : A) :
    (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) j = a * M i j := by simp

/--
lemma `toCLM_injective` / 引理 `toCLM_injective`

English:
lemma toCLM_injective
  statement: Function.Injective (toCLM (A := A) (m := m) (n := n))
  proof: by
  classical
  rw [injective_iff_map_eq_zero]
  intro M h
  ext i j
  rw [zero_apply]; rw [← norm_eq_zero]; rw [← sq_eq_zero_iff]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [← toCLM_apply_single_apply]
  simp [h]

中文:
引理 toCLM_injective
  结论: 函数.单射 (toCLM (A := A) (m := m) (n := n))
  证明: by
  classical
  rw [injective_iff_map_eq_zero]
  intro M h
  ext i j
  rw [zero_apply]; rw [← norm_eq_zero]; rw [← sq_eq_zero_iff]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [← toCLM_apply_single_apply]
  simp [h]

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, classical, injective_iff_map_eq_zero, norm_eq_zero, norm_star_mul_self, sq_eq_zero_iff, toCLM_apply_single_apply, zero_apply
-/
lemma toCLM_injective : Function.Injective (toCLM (A := A) (m := m) (n := n)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro M h
  ext i j
  rw [zero_apply]; rw [← norm_eq_zero]; rw [← sq_eq_zero_iff]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [← toCLM_apply_single_apply]
  simp [h]

variable [PartialOrder A] [StarOrderedRing A]

open WithCStarModule in
/--
lemma `mul_entry_mul_eq_inner_toCLM` / 引理 `mul_entry_mul_eq_inner_toCLM`

English:
lemma mul_entry_mul_eq_inner_toCLM
  statement: [Fintype n] [DecidableEq m] [DecidableEq n]
  proof: by = ⟪equiv _ _
  simp [mul_assoc, inner_def]

中文:
引理 mul_entry_mul_eq_inner_toCLM
  结论: [有限类型 n] [DecidableEq m] [DecidableEq n]
  证明: by = ⟪equiv _ _
  simp [mul_assoc, inner_def]

Depends on / 依赖: inner_def, mul_assoc
-/
lemma mul_entry_mul_eq_inner_toCLM [Fintype n] [DecidableEq m] [DecidableEq n]
    {M : CStarMatrix m n A} {i : m} {j : n} (a b : A) :
    a * M i j * star b
.symm (Pi.single j b), toCLM M (equiv _ _ |>.symm <| Pi.single i a)⟫_A := by = ⟪equiv _ _
  simp [mul_assoc, inner_def]

variable [Fintype n]

set_option backward.isDefEq.respectTransparency.types false in
open WithCStarModule in
/--
lemma `inner_toCLM_conjTranspose_left` / 引理 `inner_toCLM_conjTranspose_left`

English:
lemma inner_toCLM_conjTranspose_left
  statement: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, n -> A)}
  proof: by
  simp only [toCLM_apply_eq_sum, pi_inner, equiv_symm_pi_apply, inner_def, Finset.mul_sum,
    Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

中文:
引理 inner_toCLM_conjTranspose_left
  结论: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, n -> A)}
  证明: by
  simp only [toCLM_apply_eq_sum, pi_inner, equiv_symm_pi_apply, inner_def, Finset.mul_sum,
    Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_comm, Finset.sum_mul, Matrix, Matrix.conjTranspose_apply, conjTranspose_apply, equiv_symm_pi_apply, inner_def, mul_assoc, mul_sum, pi_inner, simp_rw, star_mul, star_star, star_sum, sum_comm, sum_mul, toCLM_apply_eq_sum
-/
lemma inner_toCLM_conjTranspose_left {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, n -> A)}
    {w : C⋆ᵐᵒᵈ(A, m -> A)} : ⟪toCLM Mᴴ v, w⟫_A = ⟪v, toCLM M w⟫_A := by
  simp only [toCLM_apply_eq_sum, pi_inner, equiv_symm_pi_apply, inner_def, Finset.mul_sum,
    Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `inner_toCLM_conjTranspose_right` / 引理 `inner_toCLM_conjTranspose_right`

English:
lemma inner_toCLM_conjTranspose_right
  statement: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)}
  proof: by
  apply Eq.symm
  simpa using inner_toCLM_conjTranspose_left (M := Mᴴ) (v := v) (w := w)

中文:
引理 inner_toCLM_conjTranspose_right
  结论: {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)}
  证明: by
  apply Eq.symm
  simpa using inner_toCLM_conjTranspose_left (M := Mᴴ) (v := v) (w := w)

Depends on / 依赖: Eq.symm, inner_toCLM_conjTranspose_left
-/
lemma inner_toCLM_conjTranspose_right {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)}
    {w : C⋆ᵐᵒᵈ(A, n -> A)} : ⟪v, toCLM Mᴴ w⟫_A = ⟪toCLM M v, w⟫_A := by
  apply Eq.symm
  simpa using inner_toCLM_conjTranspose_left (M := Mᴴ) (v := v) (w := w)

/--
Instance `instNorm` / 实例 `instNorm`

English:
instance instNorm
  signature: : Norm (CStarMatrix m n A) where
  body: ‖toCLM M‖

中文:
实例 instNorm
  签名: : 范数 (CStarMatrix m n A) where
  定义体: ‖toCLM M‖
-/
noncomputable instance instNorm : Norm (CStarMatrix m n A) where
  norm M := ‖toCLM M‖

/--
lemma `norm_def` / 引理 `norm_def`

English:
lemma norm_def
  given: {M : CStarMatrix m n A}
  statement: ‖M‖ = ‖toCLM M‖
  proof: rfl

中文:
引理 norm_def
  条件: {M : CStarMatrix m n A}
  结论: ‖M‖ = ‖toCLM M‖
  证明: rfl

Depends on / 依赖: AlgHomClass, FunLike
-/
lemma norm_def {M : CStarMatrix m n A} : ‖M‖ = ‖toCLM M‖ := rfl

/--
lemma `norm_def'` / 引理 `norm_def'`

English:
lemma norm_def'
  given: {M : CStarMatrix n n A}
  statement: ‖M‖ = ‖toCLMNonUnitalAlgHom (A := A) M‖
  proof: rfl

中文:
引理 norm_def'
  条件: {M : CStarMatrix n n A}
  结论: ‖M‖ = ‖toCLMNonUnitalAlgHom (A := A) M‖
  证明: rfl
-/
lemma norm_def' {M : CStarMatrix n n A} : ‖M‖ = ‖toCLMNonUnitalAlgHom (A := A) M‖ := rfl

/--
lemma `normedSpaceCore` / 引理 `normedSpaceCore`

English:
lemma normedSpaceCore
  statement: NormedSpace.Core Complex (CStarMatrix m n A) where
  proof: (toCLM M).opNorm_nonneg
  norm_smul c M := by rw [norm_def, norm_def, map_smul, norm_smul _ (toCLM M)]
  norm_triangle M₁ M₂ := by simpa [← map_add] using! norm_add_le (toCLM M₁) (toCLM M₂)
  norm_eq_zero_iff := by
    simpa only [norm_def, norm_eq_zero, ← injective_iff_map_eq_zero'] using! toCLM_in

中文:
引理 normedSpaceCore
  结论: 赋范空间.核 复形 (CStarMatrix m n A) where
  证明: (toCLM M).opNorm_nonneg
  norm_smul c M := by rw [norm_def, norm_def, map_smul, norm_smul _ (toCLM M)]
  norm_triangle M₁ M₂ := by simpa [← map_add] using! norm_add_le (toCLM M₁) (toCLM M₂)
  norm_eq_zero_iff := by
    simpa only [norm_def, norm_eq_zero, ← injective_iff_map_eq_zero'] using! toCLM_in

Depends on / 依赖: opNorm_nonneg
-/
lemma normedSpaceCore : NormedSpace.Core Complex (CStarMatrix m n A) where
  norm_nonneg M := (toCLM M).opNorm_nonneg
  norm_smul c M := by rw [norm_def, norm_def, map_smul, norm_smul _ (toCLM M)]
  norm_triangle M₁ M₂ := by simpa [← map_add] using! norm_add_le (toCLM M₁) (toCLM M₂)
  norm_eq_zero_iff := by
    simpa only [norm_def, norm_eq_zero, ← injective_iff_map_eq_zero'] using! toCLM_injective

open WithCStarModule in
/--
lemma `norm_entry_le_norm` / 引理 `norm_entry_le_norm`

English:
lemma norm_entry_le_norm
  given: {M : CStarMatrix m n A} {i : m} {j : n}
  proof: by
  classical
  suffices ‖M i j‖ * ‖M i j‖ <= ‖M‖ * ‖M i j‖ by
    obtain (h | h) := eq_zero_or_norm_pos (M i j)
    · simp [h, norm_def]
    · exact le_of_mul_le_mul_right this h
  rw [← CStarRing.norm_star_mul_self]; rw [← toCLM_apply_single_apply]
.trans apply norm_apply_le_norm _ _
.trans apply

中文:
引理 norm_entry_le_norm
  条件: {M : CStarMatrix m n A} {i : m} {j : n}
  证明: by
  classical
  suffices ‖M i j‖ * ‖M i j‖ <= ‖M‖ * ‖M i j‖ by
    obtain (h | h) := eq_zero_or_norm_pos (M i j)
    · simp [h, norm_def]
    · exact le_of_mul_le_mul_right this h
  rw [← CStarRing.norm_star_mul_self]; rw [← toCLM_apply_single_apply]
.trans apply norm_apply_le_norm _ _
.trans apply

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, classical, eq_zero_or_norm_pos, le_of_mul_le_mul_right, le_opNorm, norm_apply_le_norm, norm_def, norm_star_mul_self, toCLM_apply_single_apply
-/
lemma norm_entry_le_norm {M : CStarMatrix m n A} {i : m} {j : n} :
    ‖M i j‖ <= ‖M‖ := by
  classical
  suffices ‖M i j‖ * ‖M i j‖ <= ‖M‖ * ‖M i j‖ by
    obtain (h | h) := eq_zero_or_norm_pos (M i j)
    · simp [h, norm_def]
    · exact le_of_mul_le_mul_right this h
  rw [← CStarRing.norm_star_mul_self]; rw [← toCLM_apply_single_apply]
.trans apply norm_apply_le_norm _ _
.trans apply (toCLM M).le_opNorm _
  simp [norm_def]

open CStarModule in
/--
lemma `norm_le_of_forall_inner_le` / 引理 `norm_le_of_forall_inner_le`

English:
lemma norm_le_of_forall_inner_le
  statement: {M : CStarMatrix m n A} {C : Real>=0}
  proof: by
  refine (toCLM M).opNorm_le_bound (by simp) fun v => ?_
  obtain (h₀ | h₀) := (norm_nonneg (toCLM M v)).eq_or_lt
  · rw [← h₀]
    positivity
  · refine le_of_mul_le_mul_right ?_ h₀
    simpa [← sq, norm_sq_eq A] using h ..

中文:
引理 norm_le_of_对任意_inner_le
  结论: {M : CStarMatrix m n A} {C : 实数>=0}
  证明: by
  refine (toCLM M).opNorm_le_bound (by simp) fun v => ?_
  obtain (h₀ | h₀) := (norm_nonneg (toCLM M v)).eq_or_lt
  · rw [← h₀]
    positivity
  · refine le_of_mul_le_mul_right ?_ h₀
    simpa [← sq, norm_sq_eq A] using h ..

Depends on / 依赖: eq_or_lt, le_of_mul_le_mul_right, norm_nonneg, norm_sq_eq, opNorm_le_bound
-/
lemma norm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : Real>=0}
    (h : forall v w, ‖⟪w, toCLM M v⟫_A‖ <= C * ‖v‖ * ‖w‖) : ‖M‖ <= C := by
  refine (toCLM M).opNorm_le_bound (by simp) fun v => ?_
  obtain (h₀ | h₀) := (norm_nonneg (toCLM M v)).eq_or_lt
  · rw [← h₀]
    positivity
  · refine le_of_mul_le_mul_right ?_ h₀
    simpa [← sq, norm_sq_eq A] using h ..

end CStarMatrix

section TopologyAux
/-
## Replacing the uniformity and bornology

Note that while the norm that we have defined on `CStarMatrix m n A` induces the product uniformity,
it is not defeq to `Pi.uniformSpace`. In this section, we show that the norm indeed does induce
the product topology and use this fact to properly set up the
`NormedAddCommGroup (CStarMatrix m n A)` instance such that the uniformity is still
`Pi.uniformSpace` and the bornology is `Pi.instBornology`.

To do this, we locally register a `NormedAddCommGroup` instance on `CStarMatrix` which registers
the "bad" topology, and we also locally use the matrix norm `Matrix.normedAddCommGroup`
(which takes the norm of the biggest entry as the norm of the matrix)
in order to show that the map `ofMatrix` is bilipschitz. We then finally register the
`NormedAddCommGroup (C⋆ᵐᵒᵈ (n → A))` instance via `NormedAddCommGroup.ofCoreReplaceAll`.
-/

namespace CStarMatrix

variable {m n A : Type*} [Fintype m] [Fintype n]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private noncomputable local instance normedAddCommGroupAux :
    NormedAddCommGroup (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def normedSpaceAux
  body: .ofCore CStarMatrix.normedSpaceCore

中文:
定义 noncomputable
  签名: def normedSpaceAux
  定义体: .ofCore CStarMatrix.normedSpaceCore
-/
private noncomputable def normedSpaceAux : NormedSpace Complex (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

/- In this `Aux` section, we locally activate the following instances: a norm on `CStarMatrix`
which induces a topology that is not defeq with the matrix one, and the elementwise norm on
matrices, in order to show that the two topologies are in fact equal -/
open scoped Matrix.Norms.Elementwise

/--
lemma `nnnorm_le_of_forall_inner_le` / 引理 `nnnorm_le_of_forall_inner_le`

English:
lemma nnnorm_le_of_forall_inner_le
  statement: {M : CStarMatrix m n A} {C : Real>=0}
  proof: CStarMatrix.norm_le_of_forall_inner_le fun v w => h v w

中文:
引理 nnnorm_le_of_对任意_inner_le
  结论: {M : CStarMatrix m n A} {C : 实数>=0}
  证明: CStarMatrix.norm_le_of_forall_inner_le fun v w => h v w
-/
private lemma nnnorm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : Real>=0}
    (h : forall v w, ‖⟪w, CStarMatrix.toCLM M v⟫_A‖₊ <= C * ‖v‖₊ * ‖w‖₊) : ‖M‖₊ <= C :=
  CStarMatrix.norm_le_of_forall_inner_le fun v w => h v w

open Finset in
/--
lemma `lipschitzWith_toMatrixAux` / 引理 `lipschitzWith_toMatrixAux`

English:
lemma lipschitzWith_toMatrixAux
  proof: by
  refine AddMonoidHomClass.lipschitz_of_bound_nnnorm _ _ fun M => ?_
  rw [one_mul]; rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [coe_nnnorm]; rw [Matrix.norm_le_iff (norm_nonneg _)]
  exact fun _ _ => CStarMatrix.norm_entry_le_norm

中文:
引理 lipschitzWith_toMatrixAux
  证明: by
  refine AddMonoidHomClass.lipschitz_of_bound_nnnorm _ _ fun M => ?_
  rw [one_mul]; rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [coe_nnnorm]; rw [Matrix.norm_le_iff (norm_nonneg _)]
  exact fun _ _ => CStarMatrix.norm_entry_le_norm
-/
private lemma lipschitzWith_toMatrixAux :
    LipschitzWith 1 (ofMatrixₗ.symm (R := Complex) : CStarMatrix m n A -> Matrix m n A) := by
  refine AddMonoidHomClass.lipschitz_of_bound_nnnorm _ _ fun M => ?_
  rw [one_mul]; rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]; rw [coe_nnnorm]; rw [Matrix.norm_le_iff (norm_nonneg _)]
  exact fun _ _ => CStarMatrix.norm_entry_le_norm

open CStarMatrix WithCStarModule in
/--
lemma `antilipschitzWith_toMatrixAux` / 引理 `antilipschitzWith_toMatrixAux`

English:
lemma antilipschitzWith_toMatrixAux
  proof: by
  refine AddMonoidHomClass.antilipschitz_of_bound _ fun M => ?_
  calc
    ‖M‖ <= ∑ j, ∑ i, ‖M i j‖ := by
      rw [norm_def]
      refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
      simp only [toCLM_apply_eq_sum, Finset.sum_mul]
.trans apply pi_norm_le_sum_norm _
      gcongr wit

中文:
引理 antilipschitzWith_toMatrixAux
  证明: by
  refine AddMonoidHomClass.antilipschitz_of_bound _ fun M => ?_
  calc
    ‖M‖ <= ∑ j, ∑ i, ‖M i j‖ := by
      rw [norm_def]
      refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
      simp only [toCLM_apply_eq_sum, Finset.sum_mul]
.trans apply pi_norm_le_sum_norm _
      gcongr wit
-/
private lemma antilipschitzWith_toMatrixAux :
    AntilipschitzWith (Fintype.card n * Fintype.card m)
      (ofMatrixₗ.symm (R := Complex) : CStarMatrix m n A -> Matrix m n A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound _ fun M => ?_
  calc
    ‖M‖ <= ∑ j, ∑ i, ‖M i j‖ := by
      rw [norm_def]
      refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
      simp only [toCLM_apply_eq_sum, Finset.sum_mul]
.trans apply pi_norm_le_sum_norm _
      gcongr with i _
.trans apply norm_sum_le _ _
      gcongr with j _
.trans apply norm_mul_le _ _
      rw [mul_comm]
      gcongr
      exact norm_apply_le_norm v j
    _ <= ∑ _ : n, ∑ _ : m, ‖ofMatrixₗ.symm (R := Complex) M‖ := by
      gcongr with j _ i _
.norm_entry_le_entrywise_sup_norm exact ofMatrixₗ.symm (R := Complex) M
    _ = _ := by simp [mul_assoc]

/--
lemma `uniformInducing_toMatrixAux` / 引理 `uniformInducing_toMatrixAux`

English:
lemma uniformInducing_toMatrixAux
  proof: AntilipschitzWith.isUniformInducing antilipschitzWith_toMatrixAux
    lipschitzWith_toMatrixAux.uniformContinuous

中文:
引理 uniformInducing_toMatrixAux
  证明: AntilipschitzWith.isUniformInducing antilipschitzWith_toMatrixAux
    lipschitzWith_toMatrixAux.uniformContinuous
-/
private lemma uniformInducing_toMatrixAux :
    IsUniformInducing (ofMatrix.symm : CStarMatrix m n A -> Matrix m n A) :=
  AntilipschitzWith.isUniformInducing antilipschitzWith_toMatrixAux
    lipschitzWith_toMatrixAux.uniformContinuous

set_option backward.isDefEq.respectTransparency false in
/--
lemma `uniformity_eq_aux` / 引理 `uniformity_eq_aux`

English:
lemma uniformity_eq_aux
  proof: by
  have :
    (fun x : CStarMatrix m n A × CStarMatrix m n A => ⟨ofMatrix.symm x.1, ofMatrix.symm x.2⟩)
      = id := by
    ext i <;> rfl
  rw [← uniformInducing_toMatrixAux.comap_uniformity]; rw [this]; rw [Filter.comap_id]
  rfl

中文:
引理 uniformity_eq_aux
  证明: by
  have :
    (fun x : CStarMatrix m n A × CStarMatrix m n A => ⟨ofMatrix.symm x.1, ofMatrix.symm x.2⟩)
      = id := by
    ext i <;> rfl
  rw [← uniformInducing_toMatrixAux.comap_uniformity]; rw [this]; rw [Filter.comap_id]
  rfl
-/
private lemma uniformity_eq_aux :
    𝓤 (CStarMatrix m n A) = (𝓤[Pi.uniformSpace _] :
      Filter (CStarMatrix m n A × CStarMatrix m n A)) := by
  have :
    (fun x : CStarMatrix m n A × CStarMatrix m n A => ⟨ofMatrix.symm x.1, ofMatrix.symm x.2⟩)
      = id := by
    ext i <;> rfl
  rw [← uniformInducing_toMatrixAux.comap_uniformity]; rw [this]; rw [Filter.comap_id]
  rfl

open Bornology in
/--
lemma `cobounded_eq_aux` / 引理 `cobounded_eq_aux`

English:
lemma cobounded_eq_aux
  proof: by
  have : cobounded (CStarMatrix m n A) = Filter.comap ofMatrix.symm (cobounded _) := by
    refine le_antisymm ?_ ?_
    · exact antilipschitzWith_toMatrixAux.tendsto_cobounded.le_comap
    · exact lipschitzWith_toMatrixAux.comap_cobounded_le
  exact this.trans Filter.comap_id

中文:
引理 cobounded_eq_aux
  证明: by
  have : cobounded (CStarMatrix m n A) = Filter.comap ofMatrix.symm (cobounded _) := by
    refine le_antisymm ?_ ?_
    · exact antilipschitzWith_toMatrixAux.tendsto_cobounded.le_comap
    · exact lipschitzWith_toMatrixAux.comap_cobounded_le
  exact this.trans Filter.comap_id
-/
private lemma cobounded_eq_aux :
    cobounded (CStarMatrix m n A) = @cobounded _ Pi.instBornology := by
  have : cobounded (CStarMatrix m n A) = Filter.comap ofMatrix.symm (cobounded _) := by
    refine le_antisymm ?_ ?_
    · exact antilipschitzWith_toMatrixAux.tendsto_cobounded.le_comap
    · exact lipschitzWith_toMatrixAux.comap_cobounded_le
  exact this.trans Filter.comap_id

end CStarMatrix

end TopologyAux

namespace CStarMatrix

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n : Type*} [Fintype m] [Fintype n]

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (CStarMatrix m n A)
  body: inferInstanceAs TopologicalSpace (Matrix m n A)

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 (CStarMatrix m n A)
  定义体: inferInstanceAs TopologicalSpace (Matrix m n A)

Depends on / 依赖: Matrix, TopologicalSpace
-/
instance instTopologicalSpace : TopologicalSpace (CStarMatrix m n A) :=
inferInstanceAs TopologicalSpace (Matrix m n A)

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (CStarMatrix m n A)
  body: inferInstanceAs UniformSpace (Matrix m n A)

中文:
实例 instUniformSpace
  签名: : 一致空间 (CStarMatrix m n A)
  定义体: inferInstanceAs UniformSpace (Matrix m n A)

Depends on / 依赖: Matrix, UniformSpace
-/
instance instUniformSpace : UniformSpace (CStarMatrix m n A) :=
inferInstanceAs UniformSpace (Matrix m n A)

-- TODO: we are missing `Bornology (Matrix m n A)`
/--
Instance `instBornology` / 实例 `instBornology`

English:
instance instBornology
  signature: : Bornology (CStarMatrix m n A)
  body: inferInstanceAs Bornology (m -> n -> A)

中文:
实例 instBornology
  签名: : 有界结构 (CStarMatrix m n A)
  定义体: inferInstanceAs Bornology (m -> n -> A)

Depends on / 依赖: Bornology
-/
instance instBornology : Bornology (CStarMatrix m n A) :=
inferInstanceAs Bornology (m -> n -> A)

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: : CompleteSpace (CStarMatrix m n A)
  body: inferInstanceAs CompleteSpace (Matrix m n A)

中文:
实例 instCompleteSpace
  签名: : 完备空间 (CStarMatrix m n A)
  定义体: inferInstanceAs CompleteSpace (Matrix m n A)

Depends on / 依赖: CompleteSpace, Matrix
-/
instance instCompleteSpace : CompleteSpace (CStarMatrix m n A) :=
inferInstanceAs CompleteSpace (Matrix m n A)

/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: : T2Space (CStarMatrix m n A)
  body: inferInstanceAs T2Space (Matrix m n A)

中文:
实例 instT2Space
  签名: : T2空间 (CStarMatrix m n A)
  定义体: inferInstanceAs T2Space (Matrix m n A)

Depends on / 依赖: Matrix, T2Space
-/
instance instT2Space : T2Space (CStarMatrix m n A) := inferInstanceAs T2Space (Matrix m n A)
/--
Instance `instT3Space` / 实例 `instT3Space`

English:
instance instT3Space
  signature: : T3Space (CStarMatrix m n A)
  body: inferInstanceAs T3Space (Matrix m n A)

中文:
实例 instT3Space
  签名: : T3空间 (CStarMatrix m n A)
  定义体: inferInstanceAs T3Space (Matrix m n A)

Depends on / 依赖: Matrix, T3Space
-/
instance instT3Space : T3Space (CStarMatrix m n A) := inferInstanceAs T3Space (Matrix m n A)


/--
Instance `instIsTopologicalAddGroup` / 实例 `instIsTopologicalAddGroup`

English:
instance instIsTopologicalAddGroup
  signature: : IsTopologicalAddGroup (CStarMatrix m n A)
  body: inferInstanceAs IsTopologicalAddGroup (Matrix m n A)

中文:
实例 instIsTopologicalAddGroup
  签名: : 是拓扑加群 (CStarMatrix m n A)
  定义体: inferInstanceAs IsTopologicalAddGroup (Matrix m n A)

Depends on / 依赖: IsTopologicalAddGroup, Matrix
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (CStarMatrix m n A) :=
inferInstanceAs IsTopologicalAddGroup (Matrix m n A)

/--
Instance `instIsUniformAddGroup` / 实例 `instIsUniformAddGroup`

English:
instance instIsUniformAddGroup
  signature: : IsUniformAddGroup (CStarMatrix m n A)
  body: inferInstanceAs IsUniformAddGroup (Matrix m n A)

中文:
实例 instIsUniformAddGroup
  签名: : 是UniformAdd群 (CStarMatrix m n A)
  定义体: inferInstanceAs IsUniformAddGroup (Matrix m n A)

Depends on / 依赖: IsUniformAddGroup, Matrix
-/
instance instIsUniformAddGroup : IsUniformAddGroup (CStarMatrix m n A) :=
inferInstanceAs IsUniformAddGroup (Matrix m n A)

/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: {R : Type*} [SMul R A] [TopologicalSpace R] [ContinuousSMul R A]
  body: inferInstanceAs ContinuousSMul R (Matrix m n A)

中文:
实例 instContinuousSMul
  签名: {R : 类型} [标量乘法 R A] [拓扑空间 R] [连续标量乘法 R A]
  定义体: inferInstanceAs ContinuousSMul R (Matrix m n A)

Depends on / 依赖: ContinuousSMul, Matrix
-/
instance instContinuousSMul {R : Type*} [SMul R A] [TopologicalSpace R] [ContinuousSMul R A] :
    ContinuousSMul R (CStarMatrix m n A) :=
inferInstanceAs ContinuousSMul R (Matrix m n A)

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: :
  body: fast_instance% .ofCoreReplaceAll CStarMatrix.normedSpaceCore ?_ (fun _ => ?_)

中文:
实例 instNormedAddCommGroup
  签名: :
  定义体: fast_instance% .ofCoreReplaceAll CStarMatrix.normedSpaceCore ?_ (fun _ => ?_)

Depends on / 依赖: CStarMatrix, CStarMatrix.normedSpaceCore, fast_instance, normedSpaceCore, ofCoreReplaceAll
-/
noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (CStarMatrix m n A) :=
  fast_instance% .ofCoreReplaceAll CStarMatrix.normedSpaceCore ?_ (fun _ => ?_)
where finally
  exacts [CStarMatrix.uniformity_eq_aux.symm, Filter.ext_iff.1 CStarMatrix.cobounded_eq_aux.symm _]

/--
Instance `instNormedSpace` / 实例 `instNormedSpace`

English:
instance instNormedSpace
  signature: : NormedSpace Complex (CStarMatrix m n A)
  body: .ofCore CStarMatrix.normedSpaceCore

中文:
实例 instNormedSpace
  签名: : 赋范空间 复形 (CStarMatrix m n A)
  定义体: .ofCore CStarMatrix.normedSpaceCore

Depends on / 依赖: CStarMatrix, CStarMatrix.normedSpaceCore, normedSpaceCore, ofCore
-/
noncomputable instance instNormedSpace : NormedSpace Complex (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

/--
Instance `instNonUnitalNormedRing` / 实例 `instNonUnitalNormedRing`

English:
instance instNonUnitalNormedRing
  signature: :
  body: inferInstance
  __ : NormedAddCommGroup (CStarMatrix n n A) := inferInstance
  norm_mul_le _ _ := by simpa only [norm_def', map_mul] using norm_mul_le _ _

中文:
实例 instNonUnitalNormedRing
  签名: :
  定义体: inferInstance
  __ : NormedAddCommGroup (CStarMatrix n n A) := inferInstance
  norm_mul_le _ _ := by simpa only [norm_def', map_mul] using norm_mul_le _ _
-/
noncomputable instance instNonUnitalNormedRing :
    NonUnitalNormedRing (CStarMatrix n n A) where
  __ : NonUnitalRing (CStarMatrix n n A) := inferInstance
  __ : NormedAddCommGroup (CStarMatrix n n A) := inferInstance
  norm_mul_le _ _ := by simpa only [norm_def', map_mul] using norm_mul_le _ _

open ContinuousLinearMap CStarModule in
/--
Instance `instCStarRing` / 实例 `instCStarRing`

English:
instance instCStarRing
  signature: : CStarRing (CStarMatrix n n A)
  body: .of_le_norm_mul_star_self fun M => by
    have hmain : ‖M‖ <= √‖M * star M‖ := by
      change ‖toCLM M‖ <= √‖M * star M‖
      rw [opNorm_le_iff (by positivity)]
      intro v
      rw [norm_eq_sqrt_norm_inner_self (A := A)]; rw [← inner_toCLM_conjTranspose_right]
      have h₁ : ‖⟪v, (toCLM Mᴴ) ((

中文:
实例 instCStarRing
  签名: : CStar环 (CStarMatrix n n A)
  定义体: .of_le_norm_mul_star_self fun M => by
    have hmain : ‖M‖ <= √‖M * star M‖ := by
      change ‖toCLM M‖ <= √‖M * star M‖
      rw [opNorm_le_iff (by positivity)]
      intro v
      rw [norm_eq_sqrt_norm_inner_self (A := A)]; rw [← inner_toCLM_conjTranspose_right]
      have h₁ : ‖⟪v, (toCLM Mᴴ) ((

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, comp_apply, inner_toCLM_conjTranspose_right, mul_assoc, norm_eq_sqrt_norm_inner_self, norm_inner_le, of_le_norm_mul_star_self, opNorm_le_iff
-/
instance instCStarRing : CStarRing (CStarMatrix n n A) :=
  .of_le_norm_mul_star_self fun M => by
    have hmain : ‖M‖ <= √‖M * star M‖ := by
      change ‖toCLM M‖ <= √‖M * star M‖
      rw [opNorm_le_iff (by positivity)]
      intro v
      rw [norm_eq_sqrt_norm_inner_self (A := A)]; rw [← inner_toCLM_conjTranspose_right]
      have h₁ : ‖⟪v, (toCLM Mᴴ) ((toCLM M) v)⟫_A‖ <= ‖M * star M‖ * ‖v‖ ^ 2 := calc
          _ <= ‖v‖ * ‖(toCLM Mᴴ) (toCLM M v)‖ := norm_inner_le (C⋆ᵐᵒᵈ(A, n -> A))
          _ <= ‖v‖ * ‖(toCLM Mᴴ).comp (toCLM M)‖ * ‖v‖ := by
                    rw [mul_assoc]
                    gcongr
                    rw [← ContinuousLinearMap.comp_apply]
                    exact le_opNorm ((toCLM Mᴴ).comp (toCLM M)) v
          _ = ‖(toCLM Mᴴ).comp (toCLM M)‖ * ‖v‖ ^ 2 := by ring
          _ = ‖M * star M‖ * ‖v‖ ^ 2 := by
                    congr
                    apply MulOpposite.op_injective
                    simp only [← toCLMNonUnitalAlgHom_eq_toCLM, map_mul]
                    rfl
      have h₂ : ‖v‖ = √(‖v‖ ^ 2) := by simp
      rw [h₂]; rw [← Real.sqrt_mul]
      · gcongr
      positivity
    rw [← Real.sqrt_le_sqrt_iff (by positivity)]
    simp [hmain]

/--
Instance `instNonUnitalCStarAlgebra` / 实例 `instNonUnitalCStarAlgebra`

English:
instance instNonUnitalCStarAlgebra
  signature: :
  body: by simp
  smul_comm m a b := (Matrix.mul_smul _ _ _).symm

中文:
实例 instNonUnitalCStarAlgebra
  签名: :
  定义体: by simp
  smul_comm m a b := (Matrix.mul_smul _ _ _).symm

Depends on / 依赖: Matrix, Matrix.mul_smul, mul_smul, smul_comm
-/
noncomputable instance instNonUnitalCStarAlgebra :
    NonUnitalCStarAlgebra (CStarMatrix n n A) where
  smul_assoc x y z := by simp
  smul_comm m a b := (Matrix.mul_smul _ _ _).symm

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: :
  body: CStarAlgebra.spectralOrder _

中文:
实例 instPartialOrder
  签名: :
  定义体: CStarAlgebra.spectralOrder _

Depends on / 依赖: CStarAlgebra, CStarAlgebra.spectralOrder, spectralOrder
-/
noncomputable instance instPartialOrder :
    PartialOrder (CStarMatrix n n A) := CStarAlgebra.spectralOrder _
/--
Instance `instStarOrderedRing` / 实例 `instStarOrderedRing`

English:
instance instStarOrderedRing
  signature: :
  body: CStarAlgebra.spectralOrderedRing _

中文:
实例 instStarOrderedRing
  签名: :
  定义体: CStarAlgebra.spectralOrderedRing _

Depends on / 依赖: CStarAlgebra, CStarAlgebra.spectralOrderedRing, spectralOrderedRing
-/
instance instStarOrderedRing :
    StarOrderedRing (CStarMatrix n n A) := CStarAlgebra.spectralOrderedRing _

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Instance `instNormedRing` / 实例 `instNormedRing`

English:
instance instNormedRing
  signature: : NormedRing (CStarMatrix n n A) where
  body: rfl
  norm_mul_le := norm_mul_le

中文:
实例 instNormedRing
  签名: : 赋范环 (CStarMatrix n n A) where
  定义体: rfl
  norm_mul_le := norm_mul_le
-/
noncomputable instance instNormedRing : NormedRing (CStarMatrix n n A) where
  dist_eq _ _ := rfl
  norm_mul_le := norm_mul_le

/--
Instance `instNormedAlgebra` / 实例 `instNormedAlgebra`

English:
instance instNormedAlgebra
  signature: : NormedAlgebra Complex (CStarMatrix n n A) where
  body: by simpa only [norm_def, map_smul] using (toCLM M).opNorm_smul_le r

中文:
实例 instNormedAlgebra
  签名: : 赋范代数 复形 (CStarMatrix n n A) where
  定义体: by simpa only [norm_def, map_smul] using (toCLM M).opNorm_smul_le r

Depends on / 依赖: map_smul, norm_def, opNorm_smul_le
-/
noncomputable instance instNormedAlgebra : NormedAlgebra Complex (CStarMatrix n n A) where
  norm_smul_le r M := by simpa only [norm_def, map_smul] using (toCLM M).opNorm_smul_le r

/--
Instance `instCStarAlgebra` / 实例 `instCStarAlgebra`

English:
instance instCStarAlgebra
  signature: : CStarAlgebra (CStarMatrix n n A) where

中文:
实例 instCStarAlgebra
  签名: : CStar代数 (CStarMatrix n n A) where
-/
noncomputable instance instCStarAlgebra : CStarAlgebra (CStarMatrix n n A) where

end Unital

section

variable {m n A : Type*} [NonUnitalCStarAlgebra A]

/--
lemma `uniformEmbedding_ofMatrix` / 引理 `uniformEmbedding_ofMatrix`

English:
lemma uniformEmbedding_ofMatrix
  proof: Filter.comap_id'
  injective := fun ⦃_ _⦄ a => a

中文:
引理 uniformEmbedding_ofMatrix
  证明: Filter.comap_id'
  injective := fun ⦃_ _⦄ a => a

Depends on / 依赖: Filter, Filter.comap_id, comap_id
-/
lemma uniformEmbedding_ofMatrix :
    IsUniformEmbedding (ofMatrix : Matrix m n A -> CStarMatrix m n A) where
  comap_uniformity := Filter.comap_id'
  injective := fun ⦃_ _⦄ a => a

/--
Definition of `ofMatrixL` / `ofMatrixL` 的定义

English:
definition ofMatrixL
  signature: : Matrix m n A ≃L[Complex] CStarMatrix m n A
  body: { ofMatrixₗ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

中文:
定义 ofMatrixL
  签名: : 矩阵 m n A ≃L[复形] CStarMatrix m n A
  定义体: { ofMatrixₗ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

Depends on / 依赖: continuous_id, continuous_invFun, continuous_toFun
-/
def ofMatrixL : Matrix m n A ≃L[Complex] CStarMatrix m n A :=
  { ofMatrixₗ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

/--
lemma `ofMatrix_eq_ofMatrixL` / 引理 `ofMatrix_eq_ofMatrixL`

English:
lemma ofMatrix_eq_ofMatrixL
  proof: rfl

中文:
引理 ofMatrix_eq_ofMatrixL
  证明: rfl
-/
lemma ofMatrix_eq_ofMatrixL :
    (ofMatrix : Matrix m n A -> CStarMatrix m n A)
      = (ofMatrixL : Matrix m n A -> CStarMatrix m n A) := rfl

end

end CStarMatrix
