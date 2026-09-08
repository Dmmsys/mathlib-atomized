/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The category of finitely generated modules over a ring is essentially small

This file proves that `FGModuleCat R`, the category of finitely generated modules over a ring `R`,
is essentially small, by providing an explicit small model. However, for applications, it is
recommended to use the standard `CategoryTheory.SmallModel (FGModuleCat R)` instead.

-/

@[expose] public section

universe v w u

variable (R : Type u) [Ring R]

open CategoryTheory

/-- A (category-theoretically) small version of `FGModuleCat R`. This is used to prove that
`FGModuleCat R` is essentially small. For actual use, it might be recommended to use the canonical
`CategoryTheory.SmallModel` instead of this construction. -/
/-
**FGModuleRepr** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Ring R] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (category-theoretically) small version of `FGModuleCat R`. This is used to pro
ve that
`FGModuleCat R` is essentially small. For actual use, it might be recommended to
 use the canonical
`CategoryTheory.SmallModel` instead of this construction.
-/
structure FGModuleRepr : Type u where
  /-- The natural number `n` that defines the module as a quotient of `Fin n → R` (i.e. `R^n`). -/
  (n : ℕ)
  /-- The kernel of the surjective map from `Fin n → R` (i.e. `R^n`) to the module represented. -/
  (S : Submodule R (Fin n → R))

namespace FGModuleRepr

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

variable {R} in
/-- The finite module represented by an object of the type `FGModuleRepr R`, which is the quotient
of `Fin n → R` (i.e. `Rⁿ`) by the submodule `S` provided. -/
/-
**FGModuleRepr.repr** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleRepr`。
形式化陈述：repr (x : FGModuleRepr R) : Type u
参数：x : FGModuleRepr R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite module represented by an object of the type `FGModuleRepr R`, which i
s the quotient
of `Fin n → R` (i.e. `Rⁿ`) by the submodule `S` provided.
-/
def repr (x : FGModuleRepr R) : Type u :=
  _ ⧸ x.S
deriving AddCommGroup, Module R
/-
**FGModuleRepr.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleRepr`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (FGModuleRepr R) (Type u) :=
  ⟨repr⟩
/-
**FGModuleRepr.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleRepr`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : FGModuleRepr R) : Module.Finite R x :=
  inferInstanceAs <| Module.Finite R (_ ⧸ x.S)

/-- A non-canonical representation of a finite module (as a quotient of `Rⁿ`). -/
@[instance_reducible]
/-
**FGModuleRepr.ofFinite** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleRepr`。
形式化陈述：ofFinite : FGModuleRepr R where n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.exists_fin_quot_equiv`：exists_fin_quot_equiv (R M : Type*)
 [Ring R] [AddCommGroup M] [Module R M] [Module.Finite R M] : exists (n : Nat) (
S : Submodule R (Fin n ->…

--- 原说明 ---
A non-canonical representation of a finite module (as a quotient of `Rⁿ`).
-/
noncomputable def ofFinite : FGModuleRepr R where
  n := (Module.Finite.exists_fin_quot_equiv R M).choose
  S := (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose

/-- The non-canonical representation `ofFinite` of a finite module is actually isomorphic to
the given module. -/
/-
**FGModuleRepr.ofFiniteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleRepr`。
形式化陈述：ofFiniteEquiv : ofFinite R M ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-canonical representation `ofFinite` of a finite module is actually isomo
rphic to
the given module.
-/
noncomputable def ofFiniteEquiv : ofFinite R M ≃ₗ[R] M :=
  Classical.choice (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose_spec
/-
**FGModuleRepr.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleRepr`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (FGModuleRepr R) :=
  inferInstanceAs (Category (InducedCategory _
    (fun x : FGModuleRepr R ↦ FGModuleCat.of R x)))
/-
**FGModuleRepr.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleRepr`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SmallCategory (FGModuleRepr R) where

/-- The canonical embedding of this small category to the canonical (large) category
`FGModuleCat R`. -/
/-
**FGModuleRepr.embed** 是 Mathlib 中的一个定义，位于命名空间 `FGModuleRepr`。
形式化陈述：embed : FGModuleRepr.{u} R ⥤ FGModuleCat.{max u v} R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleRepr.instFiniteRepr`：∀ (R : Type u) [inst : Ring R] (x : FGModul
eRepr R), Module.Finite R x.repr

--- 原说明 ---
The canonical embedding of this small category to the canonical (large) category
`FGModuleCat R`.
-/
def embed : FGModuleRepr.{u} R ⥤ FGModuleCat.{max u v} R :=
  inducedFunctor _ ⋙ FGModuleCat.ulift R
/-
**FGModuleRepr.** 是 Mathlib 中的一个实例，位于命名空间 `FGModuleRepr`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (embed R).IsEquivalence where
  faithful := (fullyFaithfulInducedFunctor _).faithful.comp _ _
  full := (fullyFaithfulInducedFunctor _).full.comp _ _
  essSurj := ⟨fun M ↦ ⟨ofFinite R M,
    ⟨(ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩

end FGModuleRepr

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EssentiallySmall.{u} (FGModuleCat.{v} R) :=
  letI : EssentiallySmall.{u} (FGModuleCat.{max u v} R) :=
    ⟨_, _, ⟨(FGModuleRepr.embed R).asEquivalence.symm⟩⟩
  essentiallySmall_of_fully_faithful (FGModuleCat.ulift.{v, max u v} R)

open FGModuleRepr in
-- There is probably a proof using `embedIsEquivalence` or `EssentiallySmall`.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (FGModuleCat.ulift.{max u v, w} R).IsEquivalence where
  essSurj := ⟨fun M ↦ ⟨(embed R).obj (ofFinite R M),
    ⟨(ULift.moduleEquiv.trans <| ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩
