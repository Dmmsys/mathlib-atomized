/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.UniformSpace.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-! # Type synonym for types with a `CStarModule` structure

It is often the case that we want to construct a `CStarModule` instance on a type that is already
endowed with a norm, but this norm is not the one associated to its `CStarModule` structure. For
this reason, we create a type synonym `WithCStarModule` which is endowed with the requisite
`CStarModule` instance. We also introduce the scoped notation `C⋆ᵐᵒᵈ` for this type synonym.

The common use cases are, when `A` is a C⋆-algebra:

+ `E × F` where `E` and `F` are `CStarModule`s over `A`
+ `Π i, E i` where `E i` is a `CStarModule` over `A` and `i : ι` with `ι` a `Fintype`

In this way, the set up is very similar to the `WithLp` type synonym, although there is no way to
reuse `WithLp` because the norms *do not* coincide in general.

The `WithCStarModule` synonym is of vital importance, especially because the `CStarModule` class
marks `A` as an `outParam`. Indeed, we want to infer `A` from the type of `E`, but, as with modules,
a type `E` can be a `CStarModule` over different C⋆-algebras. For example, note that if `A` is a
C⋆-algebra, then so is `A × A`, and therefore we may consider both `A` and `A × A` as `CStarModule`s
over themselves, respectively. However, we may *also* consider `A × A` as a `CStarModule` over `A`.
However, by utilizing the type synonym, these actually correspond to *different types*, namely:

+ `A` as a `CStarModule` over `A` corresponds to `A`
+ `A × A` as a `CStarModule` over `A × A` corresponds to `A × A`
+ `A × A` as a `CStarModule` over `A` corresponds to `C⋆ᵐᵒᵈ (A × A)`

## Main definitions

* `WithCStarModule A E`: a copy of `E` to be equipped with a `CStarModule A` structure.
* `WithCStarModule.equiv A E`: the canonical equivalence between `WithCStarModule A E` and `E`.
* `WithCStarModule.linearEquiv ℂ A E`: the canonical `ℂ`-module isomorphism between
  `WithCStarModule A E` and `E`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type, and allows all the structure-copying code to be shared.
-/

@[expose] public section

set_option linter.unusedVariables false in
/-- A type synonym for endowing a given type with a `CStarModule` structure. This has the scoped
notation `C⋆ᵐᵒᵈ`. -/
@[nolint unusedArguments]
/-
**WithCStarModule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WithCStarModule (A E : Type*)
参数：A E : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for endowing a given type with a `CStarModule` structure. This ha
s the scoped
notation `C⋆ᵐᵒᵈ`.
-/
def WithCStarModule (A E : Type*) := E

namespace WithCStarModule

@[inherit_doc]
scoped notation "C⋆ᵐᵒᵈ(" A ", " E ")" => WithCStarModule A E

section Basic

variable (R R' A E : Type*)

/-- The canonical equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`. This should always be used to
convert back and forth between the representations. -/
/-
**WithCStarModule.equiv** 是 Mathlib 中的一个定义，位于命名空间 `WithCStarModule`。
形式化陈述：equiv : WithCStarModule A E ≃ E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The canonical equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`. This should always be u
sed to
convert back and forth between the representations.
-/
def equiv : WithCStarModule A E ≃ E := Equiv.refl _
/-
**WithCStarModule.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instNontrivial [Nontrivial E] : Nontrivial C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNontrivial [Nontrivial E] : Nontrivial C⋆ᵐᵒᵈ(A, E) := ‹Nontrivial E›
/-
**WithCStarModule.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instInhabited [Inhabited E] : Inhabited C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited [Inhabited E] : Inhabited C⋆ᵐᵒᵈ(A, E) := ‹Inhabited E›
/-
**WithCStarModule.instNonempty** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instNonempty [Nonempty E] : Nonempty C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonempty [Nonempty E] : Nonempty C⋆ᵐᵒᵈ(A, E) := ‹Nonempty E›
/-
**WithCStarModule.instUnique** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instUnique [Unique E] : Unique C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUnique [Unique E] : Unique C⋆ᵐᵒᵈ(A, E) := ‹Unique E›

/-! ## `C⋆ᵐᵒᵈ(A, E)` inherits various module-adjacent structures from `E`. -/

/-
**WithCStarModule.instZero** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instZero [Zero E] : Zero C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## `C⋆ᵐᵒᵈ(A, E)` inherits various module-adjacent structures from `E`.
-/
instance instZero [Zero E] : Zero C⋆ᵐᵒᵈ(A, E) := ‹Zero E›
/-
**WithCStarModule.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instAdd [Add E] : Add C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd [Add E] : Add C⋆ᵐᵒᵈ(A, E) := ‹Add E›
/-
**WithCStarModule.instSub** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instSub [Sub E] : Sub C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub [Sub E] : Sub C⋆ᵐᵒᵈ(A, E) := ‹Sub E›
/-
**WithCStarModule.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instNeg [Neg E] : Neg C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg [Neg E] : Neg C⋆ᵐᵒᵈ(A, E) := ‹Neg E›
/-
**WithCStarModule.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instAddMonoid [AddMonoid E] : AddMonoid C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid [AddMonoid E] : AddMonoid C⋆ᵐᵒᵈ(A, E) := ‹AddMonoid E›
/-
**WithCStarModule.instSubNegMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instSubNegMonoid [SubNegMonoid E] : SubNegMonoid C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSubNegMonoid [SubNegMonoid E] : SubNegMonoid C⋆ᵐᵒᵈ(A, E) := ‹SubNegMonoid E›
/-
**WithCStarModule.instSubNegZeroMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModul
e`。
形式化陈述：instSubNegZeroMonoid [SubNegZeroMonoid E] : SubNegZeroMonoid C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSubNegZeroMonoid [SubNegZeroMonoid E] : SubNegZeroMonoid C⋆ᵐᵒᵈ(A, E) :=
  ‹SubNegZeroMonoid E›
/-
**WithCStarModule.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instAddCommGroup [AddCommGroup E] : AddCommGroup C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup E] : AddCommGroup C⋆ᵐᵒᵈ(A, E) := ‹AddCommGroup E›
/-
**WithCStarModule.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instSMul {R : Type*} [SMul R E] : SMul R C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul {R : Type*} [SMul R E] : SMul R C⋆ᵐᵒᵈ(A, E) := ‹SMul R E›
/-
**WithCStarModule.instModule** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instModule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] : Module
 R C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    Module R C⋆ᵐᵒᵈ(A, E) :=
  ‹Module R E›
/-
**WithCStarModule.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instIsScalarTower [SMul R R'] [SMul R E] [SMul R' E] [IsScalarTower R R' E
] : IsScalarTower R R' C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower [SMul R R'] [SMul R E] [SMul R' E]
    [IsScalarTower R R' E] : IsScalarTower R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹IsScalarTower R R' E›
/-
**WithCStarModule.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instSMulCommClass [SMul R E] [SMul R' E] [SMulCommClass R R' E] : SMulComm
Class R R' C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulCommClass [SMul R E] [SMul R' E] [SMulCommClass R R' E] :
    SMulCommClass R R' C⋆ᵐᵒᵈ(A, E) :=
  ‹SMulCommClass R R' E›

section Equiv

variable {R A E}
variable [SMul R E] (c : R) (x y : C⋆ᵐᵒᵈ(A, E)) (x' y' : E)

/-! `WithCStarModule.equiv` preserves the module structure. -/

section AddCommGroup

variable [AddCommGroup E]

@[simp]
/-
**WithCStarModule.equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_zero : equiv A E 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_zero : equiv A E 0 = 0 :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_symm_zero : (equiv A E).symm 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_zero : (equiv A E).symm 0 = 0 :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_add** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_add : equiv A E (x + y) = equiv A E x + equiv A E y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_add : equiv A E (x + y) = equiv A E x + equiv A E y :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_add** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_symm_add : (equiv A E).symm (x' + y') = (equiv A E).symm x' + (equiv
 A E).symm y'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_add :
    (equiv A E).symm (x' + y') = (equiv A E).symm x' + (equiv A E).symm y' :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_sub : equiv A E (x - y) = equiv A E x - equiv A E y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_sub : equiv A E (x - y) = equiv A E x - equiv A E y :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_symm_sub : (equiv A E).symm (x' - y') = (equiv A E).symm x' - (equiv
 A E).symm y'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_sub :
    (equiv A E).symm (x' - y') = (equiv A E).symm x' - (equiv A E).symm y' :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_neg : equiv A E (-x) = -equiv A E x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_neg : equiv A E (-x) = -equiv A E x :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_symm_neg : (equiv A E).symm (-x') = -(equiv A E).symm x'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_neg : (equiv A E).symm (-x') = -(equiv A E).symm x' :=
  rfl

end AddCommGroup

@[simp]
/-
**WithCStarModule.equiv_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_smul : equiv A E (c • x) = c • equiv A E x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_smul : equiv A E (c • x) = c • equiv A E x :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_symm_smul : (equiv A E).symm (c • x') = c • (equiv A E).symm x'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_smul : (equiv A E).symm (c • x') = c • (equiv A E).symm x' :=
  rfl

end Equiv

/-- `WithCStarModule.equiv` as an additive equivalence. -/
/-
**WithCStarModule.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithCStarModule`。
形式化陈述：addEquiv [AddCommGroup E] : C⋆ᵐᵒᵈ(A, E) ≃+ E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`WithCStarModule.equiv` as an additive equivalence.
-/
def addEquiv [AddCommGroup E] : C⋆ᵐᵒᵈ(A, E) ≃+ E :=
  { AddEquiv.refl _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }

/-- `WithCStarModule.equiv` as a linear equivalence. -/
@[simps -fullyApplied]
/-
**WithCStarModule.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithCStarModule`。
形式化陈述：linearEquiv [Semiring R] [AddCommGroup E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃ₗ[R]
 E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`WithCStarModule.equiv` as a linear equivalence.
-/
def linearEquiv [Semiring R] [AddCommGroup E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃ₗ[R] E :=
  { LinearEquiv.refl _ _ with
    toFun := equiv _ _
    invFun := (equiv _ _).symm }
/-
**WithCStarModule.map_top_submodule** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：map_top_submodule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
 (⊤ : Submodule R E).map (linearEquiv R A E).symm.toLinearMap = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_eq_top_iff`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
-/
lemma map_top_submodule {R : Type*} [Semiring R] [AddCommGroup E] [Module R E] :
    (⊤ : Submodule R E).map (linearEquiv R A E).symm.toLinearMap = ⊤ :=
  Submodule.map_eq_top_iff.mpr rfl
/-
**WithCStarModule.instModuleFinite** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
形式化陈述：instModuleFinite [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite
 R E] : Module.Finite R C⋆ᵐᵒᵈ(A, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModuleFinite [Semiring R] [AddCommGroup E] [Module R E] [Module.Finite R E] :
    Module.Finite R C⋆ᵐᵒᵈ(A, E) := ‹Module.Finite R E›

/-! ## `C⋆ᵐᵒᵈ(A, E)` inherits the uniformity and bornology from `E`. -/

variable {A E}

/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [u : UniformSpace E] : UniformSpace C⋆ᵐᵒᵈ(A, E) := u.comap <| equiv A E
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Bornology E] : Bornology C⋆ᵐᵒᵈ(A, E) := Bornology.induced <| equiv A E


/-- `WithCStarModule.equiv` as a uniform equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`. -/
/-
**WithCStarModule.uniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithCStarModule`。
形式化陈述：uniformEquiv [UniformSpace E] : C⋆ᵐᵒᵈ(A, E) ≃ᵤ E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithCStarModule.equiv` as a uniform equivalence between `C⋆ᵐᵒᵈ(A, E)` and `E`.
-/
def uniformEquiv [UniformSpace E] : C⋆ᵐᵒᵈ(A, E) ≃ᵤ E :=
  equiv A E |>.toUniformEquivOfIsUniformInducing ⟨rfl⟩

/-- `WithCStarModule.equiv` as a continuous linear equivalence between `C⋆ᵐᵒᵈ E` and `E`. -/
@[simps! apply symm_apply]
/-
**WithCStarModule.equivL** 是 Mathlib 中的一个定义，位于命名空间 `WithCStarModule`。
形式化陈述：equivL [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E] : C⋆ᵐᵒᵈ
(A, E) ≃L[R] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithCStarModule.equiv` as a continuous linear equivalence between `C⋆ᵐᵒᵈ E` and
 `E`.
-/
def equivL [Semiring R] [AddCommGroup E] [UniformSpace E] [Module R E] : C⋆ᵐᵒᵈ(A, E) ≃L[R] E :=
  { linearEquiv R A E with
    continuous_toFun := UniformEquiv.continuous uniformEquiv
    continuous_invFun := UniformEquiv.continuous uniformEquiv.symm }
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniformSpace E] [CompleteSpace E] : CompleteSpace C⋆ᵐᵒᵈ(A, E) :=
  uniformEquiv.completeSpace_iff.mpr inferInstance
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup E] [UniformSpace E] [ContinuousAdd E] : ContinuousAdd C⋆ᵐᵒᵈ(A, E) :=
  ContinuousAdd.induced (addEquiv A E)
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] : IsUniformAddGroup C⋆ᵐᵒᵈ(A, E) :=
  IsUniformAddGroup.comap (addEquiv A E)
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [TopologicalSpace R] [AddCommGroup E] [UniformSpace E] [Module R E]
    [ContinuousSMul R E] : ContinuousSMul R C⋆ᵐᵒᵈ(A, E) :=
  ContinuousSMul.induced (linearEquiv R A E)

end Basic

/-! ## Prod

Register simplification lemmas for the applications of `WithCStarModule (E × F)` elements, as
the usual lemmas for `Prod` will not trigger. -/

section Prod

variable {R A E F : Type*}
variable [SMul R E] [SMul R F]
variable (x y : C⋆ᵐᵒᵈ(A, E × F)) (c : R)

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F]

@[simp]
/-
**WithCStarModule.zero_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：zero_fst : (0 : C⋆ᵐᵒᵈ(A, E × F)).fst = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_fst : (0 : C⋆ᵐᵒᵈ(A, E × F)).fst = 0 :=
  rfl

@[simp]
/-
**WithCStarModule.zero_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：zero_snd : (0 : C⋆ᵐᵒᵈ(A, E × F)).snd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_snd : (0 : C⋆ᵐᵒᵈ(A, E × F)).snd = 0 :=
  rfl

@[simp]
/-
**WithCStarModule.add_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：add_fst : (x + y).fst = x.fst + y.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_fst : (x + y).fst = x.fst + y.fst :=
  rfl

@[simp]
/-
**WithCStarModule.add_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：add_snd : (x + y).snd = x.snd + y.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_snd : (x + y).snd = x.snd + y.snd :=
  rfl

@[simp]
/-
**WithCStarModule.sub_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：sub_fst : (x - y).fst = x.fst - y.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_fst : (x - y).fst = x.fst - y.fst :=
  rfl

@[simp]
/-
**WithCStarModule.sub_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：sub_snd : (x - y).snd = x.snd - y.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_snd : (x - y).snd = x.snd - y.snd :=
  rfl

@[simp]
/-
**WithCStarModule.neg_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：neg_fst : (-x).fst = -x.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_fst : (-x).fst = -x.fst :=
  rfl

@[simp]
/-
**WithCStarModule.neg_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：neg_snd : (-x).snd = -x.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_snd : (-x).snd = -x.snd :=
  rfl

end AddCommGroup

@[simp]
/-
**WithCStarModule.smul_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：smul_fst : (c • x).fst = c • x.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_fst : (c • x).fst = c • x.fst :=
  rfl

@[simp]
/-
**WithCStarModule.smul_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：smul_snd : (c • x).snd = c • x.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_snd : (c • x).snd = c • x.snd :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
/-
**WithCStarModule.equiv_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_fst (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).fst = x.fst
参数：x : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the unapplied versions of these lemmas are deliberately omitted, as th
ey break
the use of the type synonym.
-/
theorem equiv_fst (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).fst = x.fst :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_snd (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).snd = x.snd
参数：x : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_snd (x : C⋆ᵐᵒᵈ(A, E × F)) : (equiv A (E × F) x).snd = x.snd :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_fst** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_symm_fst (x : E × F) : ((equiv A (E × F)).symm x).fst = x.fst
参数：x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_fst (x : E × F) : ((equiv A (E × F)).symm x).fst = x.fst :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_snd** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_symm_snd (x : E × F) : ((equiv A (E × F)).symm x).snd = x.snd
参数：x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_snd (x : E × F) : ((equiv A (E × F)).symm x).snd = x.snd :=
  rfl

end Prod

/-! ## Pi

Register simplification lemmas for the applications of `WithCStarModule (Π i, E i)` elements, as
the usual lemmas for `Pi` will not trigger.

We also provide a `CoeFun` instance for `WithCStarModule (Π i, E i)`. -/

section Pi

/-- The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithCStarModule.equiv`. -/
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The following should not be a `FunLike` instance because then the coercion `⇑` w
ould get
unfolded to `FunLike.coe` instead of `WithCStarModule.equiv`.
-/
instance {A ι : Type*} (E : ι → Type*) : CoeFun (C⋆ᵐᵒᵈ(A, Π i, E i)) (fun _ ↦ Π i, E i) where
  coe := equiv _ _

@[ext]
/-
**WithCStarModule.ext** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：∀ {A : Type u_1} {ι : Type u_2} {E : ι → Type u_3} {x y : WithCStarModule 
A ((i : ι) → E i)},   (∀ (i : ι), x i = y i) → x = y
参数：(i : ι) → E i；∀ (i : ι), x i = y i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem ext {A ι : Type*} {E : ι → Type*} {x y : C⋆ᵐᵒᵈ(A, Π i, E i)}
    (h : ∀ i, x i = y i) : x = y :=
  funext h

variable {R A ι : Type*} {E : ι → Type*}
variable [∀ i, SMul R (E i)]
variable (c : R) (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι)

section AddCommGroup

variable [∀ i, AddCommGroup (E i)]

@[simp]
/-
**WithCStarModule.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：zero_apply : (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply : (0 : C⋆ᵐᵒᵈ(A, Π i, E i)) i = 0 :=
  rfl

@[simp]
/-
**WithCStarModule.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：add_apply : (x + y) i = x i + y i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
/-
**WithCStarModule.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：sub_apply : (x - y) i = x i - y i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
/-
**WithCStarModule.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：neg_apply : (-x) i = -x i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-x) i = -x i :=
  rfl

end AddCommGroup

@[simp]
/-
**WithCStarModule.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：smul_apply : (c • x) i = c • x i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply : (c • x) i = c • x i :=
  rfl

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
/-
**WithCStarModule.equiv_pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule`。
形式化陈述：equiv_pi_apply (i : ι) : equiv _ _ x i = x i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the unapplied versions of these lemmas are deliberately omitted, as th
ey break
the use of the type synonym.
-/
theorem equiv_pi_apply (i : ι) : equiv _ _ x i = x i :=
  rfl

@[simp]
/-
**WithCStarModule.equiv_symm_pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCStarModule
`。
形式化陈述：equiv_symm_pi_apply (x : forall i, E i) (i : ι) : (equiv A _).symm x i = x
 i
参数：x : forall i, E i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equiv_symm_pi_apply (x : ∀ i, E i) (i : ι) :
    (equiv A _).symm x i = x i :=
  rfl

end Pi

end WithCStarModule

