/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!

# Ulift functor for ModuleCat

In this file, we define the obvious functor `ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R` and prove
it is exact, fully faithful and preserves projective and injective objects.

-/

@[expose] public section

universe v' v u

variable (R : Type u)

open CategoryTheory

namespace ModuleCat

section Ring

variable [Ring R]

/-- Universe lift functor for `R`-module. -/
@[simps obj map, pp_with_univ]
/-
**ModuleCat.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：uliftFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universe lift functor for `R`-module.
-/
def uliftFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R where
  obj X := ModuleCat.of R (ULift.{v', v} X)
  map f := ModuleCat.ofHom <|
    ULift.moduleEquiv.symm.toLinearMap.comp (f.hom.comp ULift.moduleEquiv.toLinearMap)

/-- The universe lift functor for `R`-module is fully faithful. -/
/-
**ModuleCat.fullyFaithfulUliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where preimage 
f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universe lift functor for `R`-module is fully faithful.
-/
def fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where
  preimage f := ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.symm.toLinearMap))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The `ULift` functor on `ModuleCat` is compatible with the one defined on categories of types. -/
@[simps! +dsimpLhs]
/-
**ModuleCat.uliftFunctorForgetIso** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：uliftFunctorForgetIso : ModuleCat.uliftFunctor.{v'} R ⋙ forget _ ≅ forget 
_ ⋙ CategoryTheory.uliftFunctor.{v'}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ULift` functor on `ModuleCat` is compatible with the one defined on categor
ies of types.
-/
def uliftFunctorForgetIso :
    ModuleCat.uliftFunctor.{v'} R ⋙ forget _ ≅
    forget _ ⋙ CategoryTheory.uliftFunctor.{v'} :=
  .refl _
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftFunctor.{v', v} R).Full := (fullyFaithfulUliftFunctor R).full
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftFunctor.{v', v} R).Faithful := (fullyFaithfulUliftFunctor R).faithful
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftFunctor R).Additive where
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R) :=
  let : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R ⋙ forget _) := by
    change Limits.PreservesLimitsOfSize.{v, v} (forget (ModuleCat R) ⋙
      CategoryTheory.uliftFunctor.{v'})
    infer_instance
  Limits.preservesLimits_of_reflects_of_preserves (uliftFunctor.{v', v} R) (forget _)
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesFiniteLimits (uliftFunctor.{v', v} R) :=
  Limits.PreservesLimitsOfSize.preservesFiniteLimits _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.uliftFunctor_map_exact** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat`。
形式化陈述：uliftFunctor_map_exact (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact) 
: (S.map (uliftFunctor R)).Exact
参数：S : ShortComplex (ModuleCat.{v} R)；h : S.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.instAdditiveUliftFunctor`：∀ (R : Type u) [inst : Ring R], (Mod
uleCat.uliftFunctor.{u_2, u_1, u} R).Additive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma uliftFunctor_map_exact (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact) :
    (S.map (uliftFunctor R)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp [uliftFunctor]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  cat_disch
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesFiniteColimits (uliftFunctor.{v', v} R) := by
  have := ((CategoryTheory.Functor.exact_tfae (uliftFunctor.{v', v} R)).out 1 3).mp
    (uliftFunctor_map_exact R)
  exact this.2

set_option backward.defeqAttrib.useBackward true in
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] : (uliftFunctor.{v', v} R).PreservesProjectiveObjects where
  projective_obj {M} proj := by
    have := small_lift.{u, v'} R
    dsimp
    infer_instance
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] : (uliftFunctor.{v', v} R).PreservesInjectiveObjects where
  injective_obj {M} inj := (Module.injective_iff_injective_object R _).mp
    (Module.ulift_injective_of_injective R ((Module.injective_iff_injective_object R M).mpr inj))

end Ring

/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing R] : (uliftFunctor.{v', v} R).Linear R where

end ModuleCat

