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

/-- Type copy `Matrix m n A` meant for matrices with entries in a C⋆-algebra. This is
a C⋆-algebra when `m = n`. -/
/-
**CStarMatrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CStarMatrix (m : Type*) (n : Type*) (A : Type*)
参数：m : Type*；n : Type*；A : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type copy `Matrix m n A` meant for matrices with entries in a C⋆-algebra. This i
s
a C⋆-algebra when `m = n`.
-/
def CStarMatrix (m : Type*) (n : Type*) (A : Type*) := Matrix m n A

namespace CStarMatrix

variable {m n R S A B : Type*}

section basic

variable (m n A) in
/-- The equivalence between `Matrix m n A` and `CStarMatrix m n A`. -/
/-
**CStarMatrix.ofMatrix** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrix {m n A : Type*} : Matrix m n A ≃ CStarMatrix m n A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The equivalence between `Matrix m n A` and `CStarMatrix m n A`.
-/
def ofMatrix {m n A : Type*} : Matrix m n A ≃ CStarMatrix m n A := Equiv.refl _

@[simp]
/-
**CStarMatrix.ofMatrix_apply** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrix_apply {M : Matrix m n A} {i : m} : (ofMatrix M) i = M i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofMatrix_apply {M : Matrix m n A} {i : m} : (ofMatrix M) i = M i := rfl

@[simp]
/-
**CStarMatrix.ofMatrix_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrix_symm_apply {M : CStarMatrix m n A} {i : m} : (ofMatrix.symm M) i 
= M i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofMatrix_symm_apply {M : CStarMatrix m n A} {i : m} : (ofMatrix.symm M) i = M i := rfl
/-
**CStarMatrix.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：ext_iff {M N : CStarMatrix m n A} : (forall i j, M i j = N i j) ↔ M = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ext_iff {M N : CStarMatrix m n A} : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩

@[ext]
/-
**CStarMatrix.ext** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：ext {M₁ M₂ : CStarMatrix m n A} (h : forall i j, M₁ i j = M₂ i j) : M₁ = M
₂
参数：h : forall i j, M₁ i j = M₂ i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CStarMatrix.ext_iff`：ext_iff {M N : CStarMatrix m n A} : (forall i j, M 
i j = N i j) ↔ M = N
-/
lemma ext {M₁ M₂ : CStarMatrix m n A} (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ := ext_iff.mp h

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`. -/
/-
**CStarMatrix.map** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：map (M : CStarMatrix m n A) (f : A -> B) : CStarMatrix m n B
参数：M : CStarMatrix m n A；f : A -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`
.
-/
def map (M : CStarMatrix m n A) (f : A → B) : CStarMatrix m n B :=
  ofMatrix fun i j => f (M i j)

@[simp]
/-
**CStarMatrix.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：map_apply {M : CStarMatrix m n A} {f : A -> B} {i : m} {j : n} : M.map f i
 j = f (M i j)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply {M : CStarMatrix m n A} {f : A → B} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

@[simp]
/-
**CStarMatrix.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：map_id (M : CStarMatrix m n A) : M.map id = M
参数：M : CStarMatrix m n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarMatrix.ext`：ext {M₁ M₂ : CStarMatrix m n A} (h : forall i j, M₁ i j
 = M₂ i j) : M₁ = M₂
-/
theorem map_id (M : CStarMatrix m n A) : M.map id = M := by
  ext
  rfl

@[simp]
/-
**CStarMatrix.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：map_id' (M : CStarMatrix m n A) : M.map (·) = M
参数：M : CStarMatrix m n A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarMatrix.map_id`：map_id (M : CStarMatrix m n A) : M.map id = M
-/
theorem map_id' (M : CStarMatrix m n A) : M.map (·) = M := map_id M
/-
**CStarMatrix.map_map** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：map_map {C : Type*} {M : Matrix m n A} {f : A -> B} {g : B -> C} : (M.map 
f).map g = M.map (g ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem map_map {C : Type*} {M : Matrix m n A} {f : A → B} {g : B → C} :
    (M.map f).map g = M.map (g ∘ f) := by ext; rfl
/-
**CStarMatrix.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：map_injective {f : A -> B} (hf : Function.Injective f) : Function.Injectiv
e fun M : CStarMatrix m n A => M.map f
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarMatrix.ext`：ext {M₁ M₂ : CStarMatrix m n A} (h : forall i j, M₁ i j
 = M₂ i j) : M₁ = M₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CStarMatrix.ext_iff`：ext_iff {M N : CStarMatrix m n A} : (forall i j, M 
i j = N i j) ↔ M = N
-/
theorem map_injective {f : A → B} (hf : Function.Injective f) :
    Function.Injective fun M : CStarMatrix m n A => M.map f := fun _ _ h =>
  ext fun i j => hf <| ext_iff.mpr h i j

/-- The transpose of a matrix. -/
/-
**CStarMatrix.transpose** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：transpose (M : CStarMatrix m n A) : CStarMatrix n m A
参数：M : CStarMatrix m n A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transpose of a matrix.
-/
def transpose (M : CStarMatrix m n A) : CStarMatrix n m A :=
  ofMatrix fun x y => M y x

@[simp]
/-
**CStarMatrix.transpose_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：transpose_apply (M : CStarMatrix m n A) (i j) : transpose M i j = M j i
参数：M : CStarMatrix m n A；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_apply (M : CStarMatrix m n A) (i j) : transpose M i j = M j i :=
  rfl

/-- The conjugate transpose of a matrix defined in term of `star`. -/
/-
**CStarMatrix.conjTranspose** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：conjTranspose [Star A] (M : CStarMatrix m n A) : CStarMatrix n m A
参数：M : CStarMatrix m n A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugate transpose of a matrix defined in term of `star`.
-/
def conjTranspose [Star A] (M : CStarMatrix m n A) : CStarMatrix n m A :=
  M.transpose.map star

@[simp]
/-
**CStarMatrix.conjTranspose_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：conjTranspose_apply [Star A] (M : CStarMatrix m n A) (i j) : conjTranspose
 M i j = star (M j i)
参数：M : CStarMatrix m n A；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjTranspose_apply [Star A] (M : CStarMatrix m n A) (i j) :
    conjTranspose M i j = star (M j i) := rfl
/-
**CStarMatrix.instStar** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instStar [Star A] : Star (CStarMatrix n n A) where star M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStar [Star A] : Star (CStarMatrix n n A) where
  star M := M.conjTranspose
/-
**CStarMatrix.star_eq_conjTranspose** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：star_eq_conjTranspose [Star A] {M : CStarMatrix n n A} : star M = M.conjTr
anspose
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma star_eq_conjTranspose [Star A] {M : CStarMatrix n n A} : star M = M.conjTranspose := rfl
/-
**CStarMatrix.instInvolutiveStar** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instInvolutiveStar [InvolutiveStar A] : InvolutiveStar (CStarMatrix n n A)
 where star_involutive
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveStar [InvolutiveStar A] : InvolutiveStar (CStarMatrix n n A) where
  star_involutive := star_involutive (R := Matrix n n A)
/-
**CStarMatrix.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instInhabited [Inhabited A] : Inhabited (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited [Inhabited A] : Inhabited (CStarMatrix m n A) :=
  inferInstanceAs <| Inhabited (Matrix m n A)
/-
**CStarMatrix.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instDecidableEq [DecidableEq A] [Fintype m] [Fintype n] : DecidableEq (CSt
arMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableEq [DecidableEq A] [Fintype m] [Fintype n] :
    DecidableEq (CStarMatrix m n A) :=
  inferInstanceAs <| DecidableEq (Matrix m n A)
/-
**CStarMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (α) [Fintype α] :
    Fintype (CStarMatrix m n α) :=
  inferInstanceAs <| Fintype (Matrix m n α)
/-
**CStarMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m} [Finite m] [Finite n] (α) [Finite α] : Finite (CStarMatrix m n α) :=
  inferInstanceAs <| Finite (Matrix m n α)
/-
**CStarMatrix.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAdd [Add A] : Add (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd [Add A] : Add (CStarMatrix m n A) :=
  inferInstanceAs <| Add (Matrix m n A)
/-
**CStarMatrix.instAddSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddSemigroup [AddSemigroup A] : AddSemigroup (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddSemigroup [AddSemigroup A] : AddSemigroup (CStarMatrix m n A) :=
  inferInstanceAs <| AddSemigroup (Matrix m n A)
/-
**CStarMatrix.instAddCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddCommSemigroup [AddCommSemigroup A] : AddCommSemigroup (CStarMatrix 
m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommSemigroup [AddCommSemigroup A] : AddCommSemigroup (CStarMatrix m n A) :=
  inferInstanceAs <| AddCommSemigroup (Matrix m n A)
/-
**CStarMatrix.instZero** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instZero [Zero A] : Zero (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero [Zero A] : Zero (CStarMatrix m n A) :=
  inferInstanceAs <| Zero (Matrix m n A)
/-
**CStarMatrix.instAddZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddZeroClass [AddZeroClass A] : AddZeroClass (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddZeroClass [AddZeroClass A] : AddZeroClass (CStarMatrix m n A) :=
  inferInstanceAs <| AddZeroClass (Matrix m n A)
/-
**CStarMatrix.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instSMul [SMul R A] : SMul R (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul [SMul R A] : SMul R (CStarMatrix m n A) :=
  inferInstanceAs <| SMul R (Matrix m n A)
/-
**CStarMatrix.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddMonoid [AddMonoid A] : AddMonoid (CStarMatrix m n A) where nsmul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid [AddMonoid A] : AddMonoid (CStarMatrix m n A) where
  nsmul := letI := instSMul (R := ℕ) (A := A) (m := m) (n := n); (· • · )
  __ : AddMonoid (CStarMatrix m n A) := inferInstanceAs <| AddMonoid (Matrix m n A)
/-
**CStarMatrix.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddCommMonoid [AddCommMonoid A] : AddCommMonoid (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid [AddCommMonoid A] : AddCommMonoid (CStarMatrix m n A) :=
  inferInstanceAs <| AddCommMonoid (Matrix m n A)
/-
**CStarMatrix.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNeg [Neg A] : Neg (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg [Neg A] : Neg (CStarMatrix m n A) :=
  inferInstanceAs <| Neg (Matrix m n A)
/-
**CStarMatrix.instSub** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instSub [Sub A] : Sub (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub [Sub A] : Sub (CStarMatrix m n A) :=
  inferInstanceAs <| Sub (Matrix m n A)
/-
**CStarMatrix.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddGroup [AddGroup A] : AddGroup (CStarMatrix m n A) where zsmul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroup [AddGroup A] : AddGroup (CStarMatrix m n A) where
  zsmul := letI := instSMul (R := ℤ) (A := A) (m := m) (n := n); (· • · )
  __ : AddGroup (CStarMatrix m n A) := inferInstanceAs <| AddGroup (Matrix m n A)
/-
**CStarMatrix.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddCommGroup [AddCommGroup A] : AddCommGroup (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup A] : AddCommGroup (CStarMatrix m n A) :=
  inferInstanceAs <| AddCommGroup (Matrix m n A)
/-
**CStarMatrix.instUnique** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instUnique [Unique A] : Unique (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUnique [Unique A] : Unique (CStarMatrix m n A) :=
  inferInstanceAs <| Unique (Matrix m n A)
/-
**CStarMatrix.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instSubsingleton [Subsingleton A] : Subsingleton (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSubsingleton [Subsingleton A] : Subsingleton (CStarMatrix m n A) :=
  inferInstanceAs <| Subsingleton (Matrix m n A)
/-
**CStarMatrix.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNontrivial [Nonempty m] [Nonempty n] [Nontrivial A] : Nontrivial (CSta
rMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNontrivial [Nonempty m] [Nonempty n] [Nontrivial A] : Nontrivial (CStarMatrix m n A) :=
  inferInstanceAs <| Nontrivial (Matrix m n A)
/-
**CStarMatrix.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instSMulCommClass [SMul R A] [SMul S A] [SMulCommClass R S A] : SMulCommCl
ass R S (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass [SMul R A] [SMul S A] [SMulCommClass R S A] :
    SMulCommClass R S (CStarMatrix m n A) :=
  inferInstanceAs <| SMulCommClass R S (Matrix m n A)
/-
**CStarMatrix.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instIsScalarTower [SMul R S] [SMul R A] [SMul S A] [IsScalarTower R S A] :
 IsScalarTower R S (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower [SMul R S] [SMul R A] [SMul S A] [IsScalarTower R S A] :
    IsScalarTower R S (CStarMatrix m n A) :=
  inferInstanceAs <| IsScalarTower R S (Matrix m n A)
/-
**CStarMatrix.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instIsCentralScalar [SMul R A] [SMul Rᵐᵒᵖ A] [IsCentralScalar R A] : IsCen
tralScalar R (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsCentralScalar [SMul R A] [SMul Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (CStarMatrix m n A) :=
  inferInstanceAs <| IsCentralScalar R (Matrix m n A)
/-
**CStarMatrix.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instMulAction [Monoid R] [MulAction R A] : MulAction R (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction [Monoid R] [MulAction R A] : MulAction R (CStarMatrix m n A) :=
  inferInstanceAs <| MulAction R (Matrix m n A)
/-
**CStarMatrix.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instDistribMulAction [Monoid R] [AddMonoid A] [DistribMulAction R A] : Dis
tribMulAction R (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid R] [AddMonoid A] [DistribMulAction R A] :
    DistribMulAction R (CStarMatrix m n A) :=
  inferInstanceAs <| DistribMulAction R (Matrix m n A)
/-
**CStarMatrix.instModule** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (CStarMa
trix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (CStarMatrix m n A) :=
  inferInstanceAs <| Module R (Matrix m n A)

@[simp]
/-
**CStarMatrix.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：zero_apply [Zero A] (i : m) (j : n) : (0 : CStarMatrix m n A) i j = 0
参数：i : m；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply [Zero A] (i : m) (j : n) : (0 : CStarMatrix m n A) i j = 0 := rfl
/-
**CStarMatrix.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} [inst : Add A] (M N : CStar
Matrix m n A) (i : m) (j : n),   (M + N) i j = M i j + N i j
参数：M N : CStarMatrix m n A；i : m；j : n；M + N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem add_apply [Add A] (M N : CStarMatrix m n A) (i : m) (j : n) :
    (M + N) i j = (M i j) + (N i j) := rfl
/-
**CStarMatrix.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} {B : Type u_6} [inst : SMul
 B A] (r : B) (M : CStarMatrix m n A) (i : m)   (j : n), (r • M) i j = r • M i j
参数：r : B；M : CStarMatrix m n A；i : m；j : n；r • M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem smul_apply [SMul B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n) :
    (r • M) i j = r • (M i j) := rfl
/-
**CStarMatrix.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} [inst : Sub A] (M N : CStar
Matrix m n A) (i : m) (j : n),   (M - N) i j = M i j - N i j
参数：M N : CStarMatrix m n A；i : m；j : n；M - N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sub_apply [Sub A] (M N : CStarMatrix m n A) (i : m) (j : n) :
    (M - N) i j = (M i j) - (N i j) := rfl
/-
**CStarMatrix.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} [inst : Neg A] (M : CStarMa
trix m n A) (i : m) (j : n), (-M) i j = -M i j
参数：M : CStarMatrix m n A；i : m；j : n；-M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem neg_apply [Neg A] (M : CStarMatrix m n A) (i : m) (j : n) :
    (-M) i j = -(M i j) := rfl

@[simp]
/-
**CStarMatrix.conjTranspose_zero** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：conjTranspose_zero [AddMonoid A] [StarAddMonoid A] : conjTranspose (0 : CS
tarMatrix m n A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarMatrix.ext`：ext {M₁ M₂ : CStarMatrix m n A} (h : forall i j, M₁ i j
 = M₂ i j) : M₁ = M₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjTranspose_zero [AddMonoid A] [StarAddMonoid A] :
    conjTranspose (0 : CStarMatrix m n A) = 0 := by ext; simp

/-! simp-normal form pulls `of` to the outside, to match the `Matrix` API. -/

/-
**CStarMatrix.of_zero** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} [inst : Zero A], CStarMatri
x.ofMatrix 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
simp-normal form pulls `of` to the outside, to match the `Matrix` API.
-/
@[simp] theorem of_zero [Zero A] : ofMatrix (0 : Matrix m n A) = 0 := rfl
/-
**CStarMatrix.of_add_of** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} [inst : Add A] (f g : Matri
x m n A),   CStarMatrix.ofMatrix f + CStarMatrix.ofMatrix g = CStarMatrix.ofMatr
ix (f + g)
参数：f g : Matrix m n A；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
simp-normal form pulls `of` to the outside, to match the `Matrix` API.
-/
@[simp] theorem of_add_of [Add A] (f g : Matrix m n A) :
    ofMatrix f + ofMatrix g = ofMatrix (f + g) := rfl

@[simp]
/-
**CStarMatrix.of_sub_of** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：of_sub_of [Sub A] (f g : Matrix m n A) : ofMatrix f - ofMatrix g = ofMatri
x (f - g)
参数：f g : Matrix m n A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_sub_of [Sub A] (f g : Matrix m n A) : ofMatrix f - ofMatrix g = ofMatrix (f - g) :=
  rfl
/-
**CStarMatrix.neg_of** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} [inst : Neg A] (f : Matrix 
m n A),   -CStarMatrix.ofMatrix f = CStarMatrix.ofMatrix (-f)
参数：f : Matrix m n A；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem neg_of [Neg A] (f : Matrix m n A) : -ofMatrix f = ofMatrix (-f) := rfl
/-
**CStarMatrix.smul_of** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} {A : Type u_5} [inst : SMul
 R A] (r : R) (f : Matrix m n A),   r • CStarMatrix.ofMatrix f = CStarMatrix.ofM
atrix (r • f)
参数：r : R；f : Matrix m n A；r • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem smul_of [SMul R A] (r : R) (f : Matrix m n A) :
    r • ofMatrix f = ofMatrix (r • f) := rfl
/-
**CStarMatrix.star_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：star_apply [Star A] {f : CStarMatrix n n A} {i j : n} : (star f) i j = sta
r (f j i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CStarMatrix.star_eq_conjTranspose`：star_eq_conjTranspose [Star A] {M : C
StarMatrix n n A} : star M = M.conjTranspose
· 使用定理 `CStarMatrix.conjTranspose_apply`：conjTranspose_apply [Star A] (M : CStar
Matrix m n A) (i j) : conjTranspose M i j = star (M j i)
-/
theorem star_apply [Star A] {f : CStarMatrix n n A} {i j : n} :
    (star f) i j = star (f j i) := by
  rw [star_eq_conjTranspose, conjTranspose_apply]
/-
**CStarMatrix.star_apply_of_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix
`。
形式化陈述：star_apply_of_isSelfAdjoint [Star A] {f : CStarMatrix n n A} (hf : IsSelfA
djoint f) {i j : n} : star (f i j) = f j i
参数：hf : IsSelfAdjoint f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarMatrix.star_apply`：star_apply [Star A] {f : CStarMatrix n n A} {i j
 : n} : (star f) i j = star (f j i)
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
-/
theorem star_apply_of_isSelfAdjoint [Star A] {f : CStarMatrix n n A} (hf : IsSelfAdjoint f)
    {i j : n} : star (f i j) = f j i := by
  rw [← star_apply, IsSelfAdjoint.star_eq hf]
/-
**CStarMatrix.instStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instStarAddMonoid [AddMonoid A] [StarAddMonoid A] : StarAddMonoid (CStarMa
trix n n A) where star_add
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarAddMonoid [AddMonoid A] [StarAddMonoid A] : StarAddMonoid (CStarMatrix n n A) where
  star_add := star_add (R := Matrix n n A)
/-
**CStarMatrix.instStarModule** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instStarModule [Star R] [Star A] [SMul R A] [StarModule R A] : StarModule 
R (CStarMatrix n n A) where star_smul r a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `Matrix.instStarModule`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst 
: Star α] [inst_1 : Star β] [inst_2 : SMul α β] [StarModule α β],   StarModule α
 (Matrix n …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instStarModule [Star R] [Star A] [SMul R A] [StarModule R A] :
    StarModule R (CStarMatrix n n A) where
  star_smul r a := star_smul r (ofMatrix.symm a)

/-- The equivalence to matrices, bundled as a linear equivalence. -/
/-
**CStarMatrix.ofMatrix** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrix {m n A : Type*} : Matrix m n A ≃ CStarMatrix m n A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The equivalence to matrices, bundled as a linear equivalence.
-/
def ofMatrixₗ [AddCommMonoid A] [Semiring R] [Module R A] :
    (Matrix m n A) ≃ₗ[R] CStarMatrix m n A := LinearEquiv.refl _ _

/-- The semilinear map constructed by applying a semilinear map to all the entries of the matrix. -/
@[simps]
/-
**CStarMatrix.map** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：map (M : CStarMatrix m n A) (f : A -> B) : CStarMatrix m n B
参数：M : CStarMatrix m n A；f : A -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The semilinear map constructed by applying a semilinear map to all the entries o
f the matrix.
-/
def mapₗ [Semiring R] [Semiring S] {σ : R →+* S} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module S B] (f : A →ₛₗ[σ] B) : CStarMatrix m n A →ₛₗ[σ] CStarMatrix m n B where
  toFun := fun M => M.map f
  map_add' M N := by ext; simp
  map_smul' r M := by ext; simp

section decidable

variable [DecidableEq n]

section zero_one

variable [Zero A] [One A]

/-
**CStarMatrix.instOne** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instOne : One (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (CStarMatrix n n A) := inferInstanceAs <| One (Matrix n n A)
/-
**CStarMatrix.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：one_apply {i j} : (1 : CStarMatrix n n A) i j = if i = j then 1 else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply {i j} : (1 : CStarMatrix n n A) i j = if i = j then 1 else 0 := rfl

@[simp]
/-
**CStarMatrix.one_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：one_apply_eq (i) : (1 : CStarMatrix n n A) i i = 1
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
-/
theorem one_apply_eq (i) : (1 : CStarMatrix n n A) i i = 1 := Matrix.one_apply_eq _
/-
**CStarMatrix.one_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {n : Type u_2} {A : Type u_5} [inst : DecidableEq n] [inst_1 : Zero A] [
inst_2 : One A] {i j : n}, i ≠ j → 1 i j = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
-/
@[simp] theorem one_apply_ne {i j} : i ≠ j → (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne
/-
**CStarMatrix.one_apply_ne'** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：one_apply_ne' {i j} : j != i -> (1 : CStarMatrix n n A) i j = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.one_apply_ne'`：one_apply_ne' {i j} : j != i -> (1 : Matrix n n α)
 i j = 0
-/
theorem one_apply_ne' {i j} : j ≠ i → (1 : CStarMatrix n n A) i j = 0 := Matrix.one_apply_ne'

end zero_one

/-
**CStarMatrix.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddMonoidWithOne [AddMonoidWithOne A] : AddMonoidWithOne (CStarMatrix 
n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne [AddMonoidWithOne A] : AddMonoidWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddMonoidWithOne (Matrix n n A)
/-
**CStarMatrix.instAddGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddGroupWithOne [AddGroupWithOne A] : AddGroupWithOne (CStarMatrix n n
 A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroupWithOne [AddGroupWithOne A] : AddGroupWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddGroupWithOne (Matrix n n A)
/-
**CStarMatrix.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddCommMonoidWithOne [AddCommMonoidWithOne A] : AddCommMonoidWithOne (
CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne A] :
    AddCommMonoidWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddCommMonoidWithOne (Matrix n n A)
/-
**CStarMatrix.instAddCommGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAddCommGroupWithOne [AddCommGroupWithOne A] : AddCommGroupWithOne (CSt
arMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne A] :
    AddCommGroupWithOne (CStarMatrix n n A) :=
  inferInstanceAs <| AddCommGroupWithOne (Matrix n n A)

-- We want to be lower priority than `instHMul`, but without this we can't have operands with
-- implicit dimensions.
@[default_instance 100]
/-
**CStarMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] :
    HMul (CStarMatrix l m A) (CStarMatrix m n A) (CStarMatrix l n A) where
  hMul M N := ofMatrix (ofMatrix.symm M * ofMatrix.symm N)
/-
**CStarMatrix.** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype n] [Mul A] [AddCommMonoid A] : Mul (CStarMatrix n n A) where mul M N := M * N

end decidable

/-
**CStarMatrix.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：mul_apply {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatr
ix l m A} {N : CStarMatrix m n A} {i k} : (M * N) i k = ∑ j, M i j * N j k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = ∑ j, M i j * N j k := rfl
/-
**CStarMatrix.mul_apply'** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：mul_apply' {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMat
rix l m A} {N : CStarMatrix m n A} {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun
 j => N j k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply' {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
    {N : CStarMatrix m n A} {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k := rfl

@[simp]
/-
**CStarMatrix.smul_mul** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：smul_mul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [Dis
tribMulAction R A] [IsScalarTower R A A] (a : R) (M : CStarMatrix m n A) (N : CS
tarMatrix n l A) : (a • M) * N = a • (M * N)
参数：a : R；M : CStarMatrix m n A；N : CStarMatrix n l A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
-/
theorem smul_mul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [IsScalarTower R A A] (a : R) (M : CStarMatrix m n A) (N : CStarMatrix n l A) :
    (a • M) * N = a • (M * N) := Matrix.smul_mul a M N
/-
**CStarMatrix.mul_smul** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：mul_smul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [Dis
tribMulAction R A] [SMulCommClass R A A] (M : CStarMatrix m n A) (a : R) (N : CS
tarMatrix n l A) : M * (a • N) = a • (M * N)
参数：M : CStarMatrix m n A；a : R；N : CStarMatrix n l A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_smul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {R : Typ
e u_7} {α : Type v} [inst : AddCommMonoid α] [inst_1 : Mul α]   [inst_2 : Fintyp
e n] …
-/
theorem mul_smul {l : Type*} [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A] [DistribMulAction R A]
    [SMulCommClass R A A] (M : CStarMatrix m n A) (a : R) (N : CStarMatrix n l A) :
    M * (a • N) = a • (M * N) := Matrix.mul_smul M a N

@[simp]
/-
**CStarMatrix.mul_zero** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} {o : Type u_7} [inst : Fint
ype n] [inst_1 : NonUnitalNonAssocSemiring A]   (M : CStarMatrix m n A), M * 0 =
 0
参数：M : CStarMatrix m n A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_zero`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (M : Matrix m n
 α), …
-/
protected theorem mul_zero {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (0 : CStarMatrix n o A) = 0 := Matrix.mul_zero _

@[simp]
/-
**CStarMatrix.zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} {l : Type u_7} [inst : Fint
ype m] [inst_1 : NonUnitalNonAssocSemiring A]   (M : CStarMatrix m n A), 0 * M =
 0
参数：M : CStarMatrix m n A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.zero_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Typ
e v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (M : Matrix m n
 α), …
-/
protected theorem zero_mul {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix m n A) : (0 : CStarMatrix l m A) * M = 0 := Matrix.zero_mul _
/-
**CStarMatrix.mul_add** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} {o : Type u_7} [inst : Fint
ype n] [inst_1 : NonUnitalNonAssocSemiring A]   (L : CStarMatrix m n A) (M N : C
StarMatrix n o A), L * (M + N) = L * M + L * N
参数：L : CStarMatrix m n A；M N : CStarMatrix n o A；M + N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mul_add`：∀ {m : Type u_2} {n : Type u_3} {o : Type u_4} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype n]   (L : Matrix m n 
α) (…
-/
protected theorem mul_add {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
    (L : CStarMatrix m n A) (M N : CStarMatrix n o A) :
    L * (M + N) = L * M + L * N := Matrix.mul_add _ _ _
/-
**CStarMatrix.add_mul** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {A : Type u_5} {l : Type u_7} [inst : Fint
ype m] [inst_1 : NonUnitalNonAssocSemiring A]   (L M : CStarMatrix l m A) (N : C
StarMatrix m n A), (L + M) * N = L * N + M * N
参数：L M : CStarMatrix l m A；N : CStarMatrix m n A；L + M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.add_mul`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {α : Type
 v} [inst : NonUnitalNonAssocSemiring α] [inst_1 : Fintype m]   (L M : Matrix l 
m α)…
-/
protected theorem add_mul {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L + M) * N = L * N + M * N := Matrix.add_mul _ _ _
/-
**CStarMatrix.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatr
ix`。
形式化陈述：instNonUnitalNonAssocSemiring [Fintype n] [NonUnitalNonAssocSemiring A] : 
NonUnitalNonAssocSemiring (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring [Fintype n] [NonUnitalNonAssocSemiring A] :
    NonUnitalNonAssocSemiring (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalNonAssocSemiring (Matrix n n A)
/-
**CStarMatrix.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNonUnitalNonAssocRing [Fintype n] [NonUnitalNonAssocRing A] : NonUnita
lNonAssocRing (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [Fintype n] [NonUnitalNonAssocRing A] :
    NonUnitalNonAssocRing (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalNonAssocRing (Matrix n n A)
/-
**CStarMatrix.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNonUnitalSemiring [Fintype n] [NonUnitalSemiring A] : NonUnitalSemirin
g (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring [Fintype n] [NonUnitalSemiring A] :
    NonUnitalSemiring (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalSemiring (Matrix n n A)
/-
**CStarMatrix.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNonAssocSemiring [Fintype n] [DecidableEq n] [NonAssocSemiring A] : No
nAssocSemiring (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [Fintype n] [DecidableEq n] [NonAssocSemiring A] :
    NonAssocSemiring (CStarMatrix n n A) :=
  inferInstanceAs <| NonAssocSemiring (Matrix n n A)
/-
**CStarMatrix.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNonUnitalRing [Fintype n] [NonUnitalRing A] : NonUnitalRing (CStarMatr
ix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [Fintype n] [NonUnitalRing A] :
    NonUnitalRing (CStarMatrix n n A) :=
  inferInstanceAs <| NonUnitalRing (Matrix n n A)
/-
**CStarMatrix.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing A] : NonAssocRi
ng (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing A] :
    NonAssocRing (CStarMatrix n n A) :=
  inferInstanceAs <| NonAssocRing (Matrix n n A)
/-
**CStarMatrix.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instSemiring [Fintype n] [DecidableEq n] [Semiring A] : Semiring (CStarMat
rix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Fintype n] [DecidableEq n] [Semiring A] :
    Semiring (CStarMatrix n n A) :=
  inferInstanceAs <| Semiring (Matrix n n A)
/-
**CStarMatrix.instRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instRing [Fintype n] [DecidableEq n] [Ring A] : Ring (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Fintype n] [DecidableEq n] [Ring A] : Ring (CStarMatrix n n A) :=
  inferInstanceAs <| Ring (Matrix n n A)

/-- `ofMatrix` bundled as a ring equivalence. -/
/-
**CStarMatrix.ofMatrixRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrixRingEquiv [Fintype n] [Semiring A] : Matrix n n A ≃+* CStarMatrix 
n n A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofMatrix` bundled as a ring equivalence.
-/
def ofMatrixRingEquiv [Fintype n] [Semiring A] :
    Matrix n n A ≃+* CStarMatrix n n A :=
  { ofMatrix with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
/-
**CStarMatrix.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instStarRing [Fintype n] [NonUnitalSemiring A] [StarRing A] : StarRing (CS
tarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing [Fintype n] [NonUnitalSemiring A] [StarRing A] :
    StarRing (CStarMatrix n n A) := inferInstanceAs <| StarRing (Matrix n n A)
/-
**CStarMatrix.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instAlgebra [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Alg
ebra R A] : Algebra R (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra R (CStarMatrix n n A) := inferInstanceAs <| Algebra R (Matrix n n A)

/-- `ofMatrix` bundled as a star algebra equivalence. -/
/-
**CStarMatrix.ofMatrixStarAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrixStarAlgEquiv [Fintype n] [SMul Complex A] [Semiring A] [StarRing A
] : Matrix n n A ≃⋆ₐ[Complex] CStarMatrix n n A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofMatrix` bundled as a star algebra equivalence.
-/
def ofMatrixStarAlgEquiv [Fintype n] [SMul ℂ A] [Semiring A] [StarRing A] :
    Matrix n n A ≃⋆ₐ[ℂ] CStarMatrix n n A :=
  { ofMatrixRingEquiv with
    map_star' := fun _ => rfl
    map_smul' := fun _ _ => rfl }
/-
**CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CStarM
atrix`。
形式化陈述：ofMatrix_eq_ofMatrixStarAlgEquiv [Fintype n] [SMul Complex A] [Semiring A]
 [StarRing A] : (ofMatrix : Matrix n n A -> CStarMatrix n n A) = (ofMatrixStarAl
gEquiv : Matrix n n A -> CStarMatrix n n A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofMatrix_eq_ofMatrixStarAlgEquiv [Fintype n] [SMul ℂ A] [Semiring A] [StarRing A] :
    (ofMatrix : Matrix n n A → CStarMatrix n n A)
      = (ofMatrixStarAlgEquiv : Matrix n n A → CStarMatrix n n A) := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (R) (A) in
/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
/-
**CStarMatrix.reindex** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map that reindexes a matrix's rows and columns with equivalent types
 is an
equivalence.
-/
def reindexₗ {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) : CStarMatrix m n A ≃ₗ[R] CStarMatrix l o A :=
  { Matrix.reindex eₘ eₙ with
    map_add' M N := by ext; simp
    map_smul' r M := by ext; simp }

@[simp]
/-
**CStarMatrix.reindex** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reindexₗ_apply {l o : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    {eₘ : m ≃ l} {eₙ : n ≃ o} {M : CStarMatrix m n A} {i : l} {j : o} :
    reindexₗ R A eₘ eₙ M i j = Matrix.reindex eₘ eₙ M i j := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
/-
**CStarMatrix.reindex** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map that reindexes a matrix's rows and columns with equivalent types
 is an
equivalence.
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
      rw [star_apply, star_apply]
      simp [Matrix.submatrix_apply] }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CStarMatrix.reindex** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reindexₐ_apply [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A]
    [Module R A] {e : m ≃ n} {M : CStarMatrix m m A}
    {i : n} {j : n} : reindexₐ R A e M i j = Matrix.reindex e e M i j := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CStarMatrix.map** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：map (M : CStarMatrix m n A) (f : A -> B) : CStarMatrix m n B
参数：M : CStarMatrix m n A；f : A -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapₗ_reindexₐ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] [AddCommMonoid B] [Mul B] [Module R B] [Star B] {e : m ≃ n} {M : CStarMatrix m m A}
    (φ : A →ₗ[R] B) : reindexₐ R B e (M.mapₗ φ) = ((reindexₐ R A e M).mapₗ φ) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CStarMatrix.reindex** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reindexₐ_symm [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] {e : m ≃ n} : reindexₐ R A e.symm = (reindexₐ R A e).symm := by
  simp [reindexₐ, reindexₗ]

set_option backward.isDefEq.respectTransparency.types false in
/-- Applying a non-unital ⋆-algebra homomorphism to every entry of a matrix is itself a
⋆-algebra homomorphism on matrices. -/
@[simps]
/-
**CStarMatrix.map** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：map (M : CStarMatrix m n A) (f : A -> B) : CStarMatrix m n B
参数：M : CStarMatrix m n A；f : A -> B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying a non-unital ⋆-algebra homomorphism to every entry of a matrix is itsel
f a
⋆-algebra homomorphism on matrices.
-/
def mapₙₐ [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B) :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix n n B where
  toFun := fun M => M.mapₗ (f : A →ₗ[R] B)
  map_smul' := by simp
  map_zero' := by simp [map_zero]
  map_add' := by simp [map_add]
  map_mul' M N := by
    ext
    -- Un-squeezing this `simp` seems to add about half a second elaboration time.
    simp only [mapₗ_apply, map, LinearMap.coe_coe, ofMatrix_apply, mul_apply, map_sum, map_mul,
      ofMatrix_apply]
  map_star' M := by ext; simp [map, star_apply, map_star]
/-
**CStarMatrix.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `CStarMatrix`。
形式化陈述：algebraMap_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
 [Algebra R A] {r : R} {i j : n} : (algebraMap R (CStarMatrix n n A) r) i j = if
 i = j then algebraMap R A r else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Algebra R A] {r : R} {i j : n} :
    (algebraMap R (CStarMatrix n n A) r) i j = if i = j then algebraMap R A r else 0 := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (n) (R) (A) in
/-- The ⋆-algebra equivalence between `A` and 1×1 matrices with its entry in `A`. -/
/-
**CStarMatrix.toOneByOne** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：toOneByOne [Unique n] [Semiring R] [AddCommMonoid A] [Mul A] [Star A] [Mod
ule R A] : A ≃⋆ₐ[R] CStarMatrix n n A where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ⋆-algebra equivalence between `A` and 1×1 matrices with its entry in `A`.
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
/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on `C⋆ᵐᵒᵈ (n → A)`. -/
/-
**CStarMatrix.toCLM** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：toCLM : CStarMatrix m n A ->ₗ[Complex] C⋆ᵐᵒᵈ(A, m -> A) ->L[Complex] C⋆ᵐᵒᵈ
(A, n -> A) where toFun M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `CStarMatrix m n A` as a continuous linear map acting on `C⋆ᵐᵒᵈ (n →
 A)`.
-/
noncomputable def toCLM : CStarMatrix m n A →ₗ[ℂ] C⋆ᵐᵒᵈ(A, m → A) →L[ℂ] C⋆ᵐᵒᵈ(A, n → A) where
  toFun M := { toFun := (WithCStarModule.equivL ℂ).symm ∘ M.vecMul ∘ WithCStarModule.equivL ℂ
               map_add' := M.add_vecMul
               map_smul' := M.smul_vecMul }
  map_add' M₁ M₂ := by
    ext
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, _root_.add_apply, WithCStarModule.add_apply]
    rw [Matrix.vecMul_add, Pi.add_apply]
  map_smul' c M := by
    ext x i
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      WithCStarModule.equivL_apply, WithCStarModule.equivL_symm_apply,
      WithCStarModule.equiv_symm_pi_apply, _root_.smul_apply,
      WithCStarModule.smul_apply, RingHom.id_apply]
    rw [Matrix.vecMul_smul, Pi.smul_apply]
/-
**CStarMatrix.toCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：toCLM_apply {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)} : toCLM M v = (
WithCStarModule.equiv _ _).symm (M.vecMul v)
参数：A, m -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
lemma toCLM_apply {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m → A)} :
    toCLM M v = (WithCStarModule.equiv _ _).symm (M.vecMul v) := rfl
/-
**CStarMatrix.toCLM_apply_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：toCLM_apply_eq_sum {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)} : toCLM 
M v = (WithCStarModule.equiv _ _).symm (fun j => ∑ i, v i * M i j)
参数：A, m -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithCStarModule.ext`：∀ {A : Type u_1} {ι : Type u_2} {E : ι → Type u_3} 
{x y : WithCStarModule A ((i : ι) → E i)},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toCLM_apply_eq_sum {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m → A)} :
    toCLM M v = (WithCStarModule.equiv _ _).symm (fun j => ∑ i, v i * M i j) := by
  ext i
  simp [toCLM_apply, Matrix.vecMul, dotProduct]



set_option backward.isDefEq.respectTransparency false in
/-- Interpret a `CStarMatrix m n A` as a continuous linear map acting on `C⋆ᵐᵒᵈ (n → A)`. This
version is specialized to the case `m = n` and is bundled as a non-unital algebra homomorphism. -/
/-
**CStarMatrix.toCLMNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：toCLMNonUnitalAlgHom [Fintype n] : CStarMatrix n n A ->ₙₐ[Complex] (C⋆ᵐᵒᵈ(
A, n -> A) ->L[Complex] C⋆ᵐᵒᵈ(A, n -> A))ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `CStarMatrix m n A` as a continuous linear map acting on `C⋆ᵐᵒᵈ (n →
 A)`. This
version is specialized to the case `m = n` and is bundled as a non-unital algebr
a homomorphism.
-/
noncomputable def toCLMNonUnitalAlgHom [Fintype n] :
    CStarMatrix n n A →ₙₐ[ℂ] (C⋆ᵐᵒᵈ(A, n → A) →L[ℂ] C⋆ᵐᵒᵈ(A, n → A))ᵐᵒᵖ :=
  { (MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ (toCLM (n := n) (m := n)) with
    map_zero' := by simp
    map_mul' := by
      intros
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        LinearEquiv.coe_coe, MulOpposite.coe_opLinearEquiv, Function.comp_apply,
        ← MulOpposite.op_mul, MulOpposite.op_inj]
      ext
      simp [toCLM] }
/-
**CStarMatrix.toCLMNonUnitalAlgHom_eq_toCLM** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatr
ix`。
形式化陈述：toCLMNonUnitalAlgHom_eq_toCLM [Fintype n] {M : CStarMatrix n n A} : toCLMN
onUnitalAlgHom (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `WithCStarModule.instIsUniformAddGroup`：∀ {A : Type u_3} {E : Type u_4} [
inst : AddCommGroup E] [inst_1 : UniformSpace E] [IsUniformAddGroup E],   IsUnif
ormAddGroup (WithCStarModul…
· 使用定理 `Pi.instIsUniformAddGroup`：∀ {ι : Type u_4} {G : ι → Type u_5} [inst : (i
 : ι) → UniformSpace (G i)] [inst_1 : (i : ι) → AddGroup (G i)]   [∀ (i : ι), Is
UniformAddGrou…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
lemma toCLMNonUnitalAlgHom_eq_toCLM [Fintype n] {M : CStarMatrix n n A} :
    toCLMNonUnitalAlgHom (A := A) M = MulOpposite.op (toCLM M) := rfl

set_option backward.isDefEq.respectTransparency false in
open WithCStarModule in
@[simp high]
/-
**CStarMatrix.toCLM_apply_single** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：toCLM_apply_single [DecidableEq m] {M : CStarMatrix m n A} {i : m} (a : A)
 : (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) = (equiv _ _).symm (fun j => a
 * M i j)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithCStarModule.ext`：∀ {A : Type u_1} {ι : Type u_2} {E : ι → Type u_3} 
{x y : WithCStarModule A ((i : ι) → E i)},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_vecMul`：single_vecMul [Fintype m] [DecidableEq m] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (i : m) (x : R) : Pi.single i x ᵥ* M = 
x • M.row …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toCLM_apply_single [DecidableEq m] {M : CStarMatrix m n A} {i : m} (a : A) :
    (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) = (equiv _ _).symm (fun j => a * M i j) := by
  ext
  simp [toCLM_apply, equiv, Equiv.refl]

open WithCStarModule in
/-
**CStarMatrix.toCLM_apply_single_apply** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：toCLM_apply_single_apply [DecidableEq m] {M : CStarMatrix m n A} {i : m} {
j : n} (a : A) : (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) j = a * M i j
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CStarMatrix.toCLM_apply_single`：toCLM_apply_single [DecidableEq m] {M : 
CStarMatrix m n A} {i : m} (a : A) : (toCLM M) (equiv _ _ |>.symm <| Pi.single i
 a) = (equiv _ _).sy…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toCLM_apply_single_apply [DecidableEq m] {M : CStarMatrix m n A} {i : m} {j : n} (a : A) :
    (toCLM M) (equiv _ _ |>.symm <| Pi.single i a) j = a * M i j := by simp
/-
**CStarMatrix.toCLM_injective** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：toCLM_injective : Function.Injective (toCLM (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `CStarMatrix.ext`：ext {M₁ M₂ : CStarMatrix m n A} (h : forall i j, M₁ i j
 = M₂ i j) : M₁ = M₂
· 使用定理 `CStarMatrix.zero_apply`：zero_apply [Zero A] (i : m) (j : n) : (0 : CStar
Matrix m n A) i j = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CStarMatrix.toCLM_apply_single_apply`：toCLM_apply_single_apply [Decidabl
eEq m] {M : CStarMatrix m n A} {i : m} {j : n} (a : A) : (toCLM M) (equiv _ _ |>
.symm <| Pi.single i a) j …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 34 条，此处仅展示前 30 条）
-/
lemma toCLM_injective : Function.Injective (toCLM (A := A) (m := m) (n := n)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro M h
  ext i j
  rw [zero_apply, ← norm_eq_zero, ← sq_eq_zero_iff, sq, ← CStarRing.norm_star_mul_self,
    ← toCLM_apply_single_apply]
  simp [h]

variable [PartialOrder A] [StarOrderedRing A]

open WithCStarModule in
/-
**CStarMatrix.mul_entry_mul_eq_inner_toCLM** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatri
x`。
形式化陈述：mul_entry_mul_eq_inner_toCLM [Fintype n] [DecidableEq m] [DecidableEq n] {
M : CStarMatrix m n A} {i : m} {j : n} (a b : A) : a * M i j * star b .symm (Pi.
single j b), toCLM M (equiv _ _ |>.symm <| Pi.single i a)⟫_A
参数：a b : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `CStarMatrix.toCLM_apply_single`：toCLM_apply_single [DecidableEq m] {M : 
CStarMatrix m n A} {i : m} (a : A) : (toCLM M) (equiv _ _ |>.symm <| Pi.single i
 a) = (equiv _ _).sy…
· 使用引理 `WithCStarModule.inner_single_left`：inner_single_left [DecidableEq ι] (x 
: C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i) : .symm Pi.single i y, x⟫_A = ⟪y, x i⟫_A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_entry_mul_eq_inner_toCLM [Fintype n] [DecidableEq m] [DecidableEq n]
    {M : CStarMatrix m n A} {i : m} {j : n} (a b : A) :
    a * M i j * star b
      = ⟪equiv _ _ |>.symm (Pi.single j b), toCLM M (equiv _ _ |>.symm <| Pi.single i a)⟫_A := by
  simp [mul_assoc, inner_def]

variable [Fintype n]

set_option backward.isDefEq.respectTransparency.types false in
open WithCStarModule in
/-
**CStarMatrix.inner_toCLM_conjTranspose_left** 是 Mathlib 中的一个引理，位于命名空间 `CStarMat
rix`。
形式化陈述：inner_toCLM_conjTranspose_left {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, n -> 
A)} {w : C⋆ᵐᵒᵈ(A, m -> A)} : ⟪toCLM Mᴴ v, w⟫_A = ⟪v, toCLM M w⟫_A
参数：A, n -> A；A, m -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CStarMatrix.toCLM_apply_eq_sum`：toCLM_apply_eq_sum {M : CStarMatrix m n 
A} {v : C⋆ᵐᵒᵈ(A, m -> A)} : toCLM M v = (WithCStarModule.equiv _ _).symm (fun j 
=> ∑ i, v i * M i j)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_toCLM_conjTranspose_left {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, n → A)}
    {w : C⋆ᵐᵒᵈ(A, m → A)} : ⟪toCLM Mᴴ v, w⟫_A = ⟪v, toCLM M w⟫_A := by
  simp only [toCLM_apply_eq_sum, pi_inner, equiv_symm_pi_apply, inner_def, Finset.mul_sum,
    Matrix.conjTranspose_apply, star_sum, star_mul, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CStarMatrix.inner_toCLM_conjTranspose_right** 是 Mathlib 中的一个引理，位于命名空间 `CStarMa
trix`。
形式化陈述：inner_toCLM_conjTranspose_right {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m ->
 A)} {w : C⋆ᵐᵒᵈ(A, n -> A)} : ⟪v, toCLM Mᴴ w⟫_A = ⟪toCLM M v, w⟫_A
参数：A, m -> A；A, n -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用引理 `CStarMatrix.inner_toCLM_conjTranspose_left`：inner_toCLM_conjTranspose_le
ft {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, n -> A)} {w : C⋆ᵐᵒᵈ(A, m -> A)} : ⟪toCL
M Mᴴ v, w⟫_A = ⟪v, toCLM M w⟫_A
-/
lemma inner_toCLM_conjTranspose_right {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m → A)}
    {w : C⋆ᵐᵒᵈ(A, n → A)} : ⟪v, toCLM Mᴴ w⟫_A = ⟪toCLM M v, w⟫_A := by
  apply Eq.symm
  simpa using inner_toCLM_conjTranspose_left (M := Mᴴ) (v := v) (w := w)

/-- The operator norm on `CStarMatrix m n A`. -/
/-
**CStarMatrix.instNorm** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNorm : Norm (CStarMatrix m n A) where norm M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The operator norm on `CStarMatrix m n A`.
-/
noncomputable instance instNorm : Norm (CStarMatrix m n A) where
  norm M := ‖toCLM M‖
/-
**CStarMatrix.norm_def** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：norm_def {M : CStarMatrix m n A} : ‖M‖ = ‖toCLM M‖
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_def {M : CStarMatrix m n A} : ‖M‖ = ‖toCLM M‖ := rfl
/-
**CStarMatrix.norm_def'** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：norm_def' {M : CStarMatrix n n A} : ‖M‖ = ‖toCLMNonUnitalAlgHom (A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_def' {M : CStarMatrix n n A} : ‖M‖ = ‖toCLMNonUnitalAlgHom (A := A) M‖ := rfl
/-
**CStarMatrix.normedSpaceCore** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：normedSpaceCore : NormedSpace.Core Complex (CStarMatrix m n A) where norm_
nonneg M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_nonneg`：opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0
 <= ‖f‖
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CStarMatrix.norm_def`：norm_def {M : CStarMatrix m n A} : ‖M‖ = ‖toCLM M‖
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `CStarMatrix.toCLM_injective`：toCLM_injective : Function.Injective (toCLM
 (A
-/
lemma normedSpaceCore : NormedSpace.Core ℂ (CStarMatrix m n A) where
  norm_nonneg M := (toCLM M).opNorm_nonneg
  norm_smul c M := by rw [norm_def, norm_def, map_smul, norm_smul _ (toCLM M)]
  norm_triangle M₁ M₂ := by simpa [← map_add] using! norm_add_le (toCLM M₁) (toCLM M₂)
  norm_eq_zero_iff := by
    simpa only [norm_def, norm_eq_zero, ← injective_iff_map_eq_zero'] using! toCLM_injective

open WithCStarModule in
/-
**CStarMatrix.norm_entry_le_norm** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：norm_entry_le_norm {M : CStarMatrix m n A} {i : m} {j : n} : ‖M i j‖ <= ‖M
‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CStarMatrix.toCLM_apply_single_apply`：toCLM_apply_single_apply [Decidabl
eEq m] {M : CStarMatrix m n A} {i : m} {j : n} (a : A) : (toCLM M) (equiv _ _ |>
.symm <| Pi.single i a) j …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `WithCStarModule.norm_apply_le_norm`：norm_apply_le_norm (x : C⋆ᵐᵒᵈ(A, Π i
, E i)) (i : ι) : ‖x i‖ <= ‖x‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `WithCStarModule.norm_single`：norm_single [DecidableEq ι] (i : ι) (y : E 
i) : .symm Pi.single i y‖ = ‖y‖
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `eq_zero_or_norm_pos`：∀ {E : Type u_5} [inst : NormedAddGroup E] (a : E),
 a = 0 ∨ 0 < ‖a‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用引理 `RCLike.instMulPosReflectLE`：instMulPosReflectLE : MulPosReflectLE K
-/
lemma norm_entry_le_norm {M : CStarMatrix m n A} {i : m} {j : n} :
    ‖M i j‖ ≤ ‖M‖ := by
  classical
  suffices ‖M i j‖ * ‖M i j‖ ≤ ‖M‖ * ‖M i j‖ by
    obtain (h | h) := eq_zero_or_norm_pos (M i j)
    · simp [h, norm_def]
    · exact le_of_mul_le_mul_right this h
  rw [← CStarRing.norm_star_mul_self, ← toCLM_apply_single_apply]
  apply norm_apply_le_norm _ _ |>.trans
  apply (toCLM M).le_opNorm _ |>.trans
  simp [norm_def]

open CStarModule in
/-
**CStarMatrix.norm_le_of_forall_inner_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`
。
形式化陈述：norm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : Real>=0} (h : fora
ll v w, ‖⟪w, toCLM M v⟫_A‖ <= C * ‖v‖ * ‖w‖) : ‖M‖ <= C
参数：h : forall v w, ‖⟪w, toCLM M v⟫_A‖ <= C * ‖v‖ * ‖w‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用引理 `RCLike.instMulPosReflectLE`：instMulPosReflectLE : MulPosReflectLE K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CStarModule.norm_sq_eq`：norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖
-/
lemma norm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, toCLM M v⟫_A‖ ≤ C * ‖v‖ * ‖w‖) : ‖M‖ ≤ C := by
  refine (toCLM M).opNorm_le_bound (by simp) fun v ↦ ?_
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
/-
**CStarMatrix.normedSpaceAux** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def normedSpaceAux : NormedSpace ℂ (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore

/- In this `Aux` section, we locally activate the following instances: a norm on `CStarMatrix`
which induces a topology that is not defeq with the matrix one, and the elementwise norm on
matrices, in order to show that the two topologies are in fact equal -/
open scoped Matrix.Norms.Elementwise

/-
**CStarMatrix.nnnorm_le_of_forall_inner_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatri
x`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma nnnorm_le_of_forall_inner_le {M : CStarMatrix m n A} {C : ℝ≥0}
    (h : ∀ v w, ‖⟪w, CStarMatrix.toCLM M v⟫_A‖₊ ≤ C * ‖v‖₊ * ‖w‖₊) : ‖M‖₊ ≤ C :=
  CStarMatrix.norm_le_of_forall_inner_le fun v w => h v w

open Finset in
/-
**CStarMatrix.lipschitzWith_toMatrixAux** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lipschitzWith_toMatrixAux :
    LipschitzWith 1 (ofMatrixₗ.symm (R := ℂ) : CStarMatrix m n A → Matrix m n A) := by
  refine AddMonoidHomClass.lipschitz_of_bound_nnnorm _ _ fun M => ?_
  rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Matrix.norm_le_iff (norm_nonneg _)]
  exact fun _ _ ↦ CStarMatrix.norm_entry_le_norm

open CStarMatrix WithCStarModule in
/-
**CStarMatrix.antilipschitzWith_toMatrixAux** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatr
ix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma antilipschitzWith_toMatrixAux :
    AntilipschitzWith (Fintype.card n * Fintype.card m)
      (ofMatrixₗ.symm (R := ℂ) : CStarMatrix m n A → Matrix m n A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound _ fun M => ?_
  calc
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
      rw [norm_def]
      refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
      simp only [toCLM_apply_eq_sum, Finset.sum_mul]
      apply pi_norm_le_sum_norm _ |>.trans
      gcongr with i _
      apply norm_sum_le _ _ |>.trans
      gcongr with j _
      apply norm_mul_le _ _ |>.trans
      rw [mul_comm]
      gcongr
      exact norm_apply_le_norm v j
    _ ≤ ∑ _ : n, ∑ _ : m, ‖ofMatrixₗ.symm (R := ℂ) M‖ := by
      gcongr with j _ i _
      exact ofMatrixₗ.symm (R := ℂ) M |>.norm_entry_le_entrywise_sup_norm
    _ = _ := by simp [mul_assoc]
/-
**CStarMatrix.uniformInducing_toMatrixAux** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma uniformInducing_toMatrixAux :
    IsUniformInducing (ofMatrix.symm : CStarMatrix m n A → Matrix m n A) :=
  AntilipschitzWith.isUniformInducing antilipschitzWith_toMatrixAux
    lipschitzWith_toMatrixAux.uniformContinuous

set_option backward.isDefEq.respectTransparency false in
/-
**CStarMatrix.uniformity_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma uniformity_eq_aux :
    𝓤 (CStarMatrix m n A) = (𝓤[Pi.uniformSpace _] :
      Filter (CStarMatrix m n A × CStarMatrix m n A)) := by
  have :
    (fun x : CStarMatrix m n A × CStarMatrix m n A => ⟨ofMatrix.symm x.1, ofMatrix.symm x.2⟩)
      = id := by
    ext i <;> rfl
  rw [← uniformInducing_toMatrixAux.comap_uniformity, this, Filter.comap_id]
  rfl

open Bornology in
/-
**CStarMatrix.cobounded_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**CStarMatrix.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instTopologicalSpace : TopologicalSpace (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace : TopologicalSpace (CStarMatrix m n A) :=
  inferInstanceAs <| TopologicalSpace (Matrix m n A)
/-
**CStarMatrix.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instUniformSpace : UniformSpace (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniformSpace : UniformSpace (CStarMatrix m n A) :=
  inferInstanceAs <| UniformSpace (Matrix m n A)

-- TODO: we are missing `Bornology (Matrix m n A)`
/-
**CStarMatrix.instBornology** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instBornology : Bornology (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBornology : Bornology (CStarMatrix m n A) :=
  inferInstanceAs <| Bornology (m → n → A)
/-
**CStarMatrix.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instCompleteSpace : CompleteSpace (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteSpace : CompleteSpace (CStarMatrix m n A) :=
  inferInstanceAs <| CompleteSpace (Matrix m n A)
/-
**CStarMatrix.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instT2Space : T2Space (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instT2Space : T2Space (CStarMatrix m n A) := inferInstanceAs <| T2Space (Matrix m n A)
/-
**CStarMatrix.instT3Space** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instT3Space : T3Space (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instT3Space : T3Space (CStarMatrix m n A) := inferInstanceAs <| T3Space (Matrix m n A)
/-
**CStarMatrix.instIsTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instIsTopologicalAddGroup : IsTopologicalAddGroup (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (CStarMatrix m n A) :=
  inferInstanceAs <| IsTopologicalAddGroup (Matrix m n A)
/-
**CStarMatrix.instIsUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instIsUniformAddGroup : IsUniformAddGroup (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsUniformAddGroup : IsUniformAddGroup (CStarMatrix m n A) :=
  inferInstanceAs <| IsUniformAddGroup (Matrix m n A)
/-
**CStarMatrix.instContinuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instContinuousSMul {R : Type*} [SMul R A] [TopologicalSpace R] [Continuous
SMul R A] : ContinuousSMul R (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instContinuousSMul {R : Type*} [SMul R A] [TopologicalSpace R] [ContinuousSMul R A] :
    ContinuousSMul R (CStarMatrix m n A) :=
  inferInstanceAs <| ContinuousSMul R (Matrix m n A)
/-
**CStarMatrix.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNormedAddCommGroup : NormedAddCommGroup (CStarMatrix m n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (CStarMatrix m n A) :=
  fast_instance% .ofCoreReplaceAll CStarMatrix.normedSpaceCore ?_ (fun _ ↦ ?_)
where finally
  exacts [CStarMatrix.uniformity_eq_aux.symm, Filter.ext_iff.1 CStarMatrix.cobounded_eq_aux.symm _]
/-
**CStarMatrix.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNormedSpace : NormedSpace Complex (CStarMatrix m n A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarMatrix.normedSpaceCore`：normedSpaceCore : NormedSpace.Core Complex 
(CStarMatrix m n A) where norm_nonneg M
-/
noncomputable instance instNormedSpace : NormedSpace ℂ (CStarMatrix m n A) :=
  .ofCore CStarMatrix.normedSpaceCore
/-
**CStarMatrix.instNonUnitalNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNonUnitalNormedRing : NonUnitalNormedRing (CStarMatrix n n A) where __
 : NonUnitalRing (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNonUnitalNormedRing :
    NonUnitalNormedRing (CStarMatrix n n A) where
  __ : NonUnitalRing (CStarMatrix n n A) := inferInstance
  __ : NormedAddCommGroup (CStarMatrix n n A) := inferInstance
  norm_mul_le _ _ := by simpa only [norm_def', map_mul] using norm_mul_le _ _

open ContinuousLinearMap CStarModule in
/-- Matrices with entries in a C⋆-algebra form a C⋆-algebra. -/
/-
**CStarMatrix.instCStarRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instCStarRing : CStarRing (CStarMatrix n n A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarRing.of_le_norm_mul_star_self`：of_le_norm_mul_star_self [NonUnitalN
ormedRing E] [StarRing E] (h : forall x : E, ‖x‖ * ‖x‖ <= ‖x * x⋆‖) : CStarRing 
E
· 使用定理 `WithCStarModule.instContinuousAdd`：∀ {A : Type u_3} {E : Type u_4} [inst
 : AddCommGroup E] [inst_1 : UniformSpace E] [ContinuousAdd E],   ContinuousAdd 
(WithCStarModule A E)
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `WithCStarModule.instContinuousSMul`：∀ (R : Type u_1) {A : Type u_3} {E :
 Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpace R]   [inst_2 : AddComm
Group E] [inst_3 : Unifo…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNorm_le_iff`：opNorm_le_iff {f : E ->SL[σ₁₂] F} {M 
: Real} (hMp : 0 <= M) : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M * ‖x‖
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CStarMatrix.inner_toCLM_conjTranspose_right`：inner_toCLM_conjTranspose_r
ight {M : CStarMatrix m n A} {v : C⋆ᵐᵒᵈ(A, m -> A)} {w : C⋆ᵐᵒᵈ(A, n -> A)} : ⟪v,
 toCLM Mᴴ w⟫_A = ⟪toCLM M v, w⟫_A
· 使用引理 `CStarModule.norm_inner_le`：norm_inner_le {x y : E} : ‖⟪x, y⟫‖ <= ‖x‖ * ‖
y‖
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
Matrices with entries in a C⋆-algebra form a C⋆-algebra.
-/
instance instCStarRing : CStarRing (CStarMatrix n n A) :=
  .of_le_norm_mul_star_self fun M ↦ by
    have hmain : ‖M‖ ≤ √‖M * star M‖ := by
      change ‖toCLM M‖ ≤ √‖M * star M‖
      rw [opNorm_le_iff (by positivity)]
      intro v
      rw [norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose_right]
      have h₁ : ‖⟪v, (toCLM Mᴴ) ((toCLM M) v)⟫_A‖ ≤ ‖M * star M‖ * ‖v‖ ^ 2 := calc
          _ ≤ ‖v‖ * ‖(toCLM Mᴴ) (toCLM M v)‖ := norm_inner_le (C⋆ᵐᵒᵈ(A, n → A))
          _ ≤ ‖v‖ * ‖(toCLM Mᴴ).comp (toCLM M)‖ * ‖v‖ := by
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
      rw [h₂, ← Real.sqrt_mul]
      · gcongr
      positivity
    rw [← Real.sqrt_le_sqrt_iff (by positivity)]
    simp [hmain]

/-- Matrices with entries in a non-unital C⋆-algebra form a non-unital C⋆-algebra. -/
/-
**CStarMatrix.instNonUnitalCStarAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (CStarMatrix n n A) wher
e smul_assoc x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Matrices with entries in a non-unital C⋆-algebra form a non-unital C⋆-algebra.
-/
noncomputable instance instNonUnitalCStarAlgebra :
    NonUnitalCStarAlgebra (CStarMatrix n n A) where
  smul_assoc x y z := by simp
  smul_comm m a b := (Matrix.mul_smul _ _ _).symm
/-
**CStarMatrix.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instPartialOrder : PartialOrder (CStarMatrix n n A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instPartialOrder :
    PartialOrder (CStarMatrix n n A) := CStarAlgebra.spectralOrder _
/-
**CStarMatrix.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instStarOrderedRing : StarOrderedRing (CStarMatrix n n A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.spectralOrderedRing`：CStarAlgebra.spectralOrderedRing : @St
arOrderedRing A _ (CStarAlgebra.spectralOrder A) _
-/
instance instStarOrderedRing :
    StarOrderedRing (CStarMatrix n n A) := CStarAlgebra.spectralOrderedRing _

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-
**CStarMatrix.instNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNormedRing : NormedRing (CStarMatrix n n A) where dist_eq _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNormedRing : NormedRing (CStarMatrix n n A) where
  dist_eq _ _ := rfl
  norm_mul_le := norm_mul_le
/-
**CStarMatrix.instNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `CStarMatrix`。
形式化陈述：instNormedAlgebra : NormedAlgebra Complex (CStarMatrix n n A) where norm_s
mul_le r M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (CStarMatrix n n A) where
  norm_smul_le r M := by simpa only [norm_def, map_smul] using (toCLM M).opNorm_smul_le r

/-- Matrices with entries in a unital C⋆-algebra form a unital C⋆-algebra. -/
/-
**CStarMatrix.instCStarAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：{A : Type u_1} →   [inst : CStarAlgebra A] →     [inst_1 : PartialOrder A]
 →       [StarOrderedRing A] → {n : Type u_2} → [Fintype n] → [DecidableEq n] → 
CStarAlgebra (CStarMatrix n n A)
参数：CStarMatrix n n A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Matrices with entries in a unital C⋆-algebra form a unital C⋆-algebra.
-/
noncomputable instance instCStarAlgebra : CStarAlgebra (CStarMatrix n n A) where

end Unital

section

variable {m n A : Type*} [NonUnitalCStarAlgebra A]

/-
**CStarMatrix.uniformEmbedding_ofMatrix** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：uniformEmbedding_ofMatrix : IsUniformEmbedding (ofMatrix : Matrix m n A ->
 CStarMatrix m n A) where comap_uniformity
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_id'`：comap_id' : comap (fun x => x) f = f
-/
lemma uniformEmbedding_ofMatrix :
    IsUniformEmbedding (ofMatrix : Matrix m n A → CStarMatrix m n A) where
  comap_uniformity := Filter.comap_id'
  injective := fun ⦃_ _⦄ a ↦ a

/-- `ofMatrix` bundled as a continuous linear equivalence. -/
/-
**CStarMatrix.ofMatrixL** 是 Mathlib 中的一个定义，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrixL : Matrix m n A ≃L[Complex] CStarMatrix m n A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofMatrix` bundled as a continuous linear equivalence.
-/
def ofMatrixL : Matrix m n A ≃L[ℂ] CStarMatrix m n A :=
  { ofMatrixₗ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }
/-
**CStarMatrix.ofMatrix_eq_ofMatrixL** 是 Mathlib 中的一个引理，位于命名空间 `CStarMatrix`。
形式化陈述：ofMatrix_eq_ofMatrixL : (ofMatrix : Matrix m n A -> CStarMatrix m n A) = (
ofMatrixL : Matrix m n A -> CStarMatrix m n A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofMatrix_eq_ofMatrixL :
    (ofMatrix : Matrix m n A → CStarMatrix m n A)
      = (ofMatrixL : Matrix m n A → CStarMatrix m n A) := rfl

end

end CStarMatrix

