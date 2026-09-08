/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Injective

/-!

# Category of abelian groups has enough injectives

Given an abelian group `A`, then `i : A ⟶ ∏_{A⋆} ℚ ⧸ ℤ` defined by `i : a ↦ c ↦ c a` is an
injective presentation for `A`, hence category of abelian groups has enough injectives.

## Main results

- `AddCommGrpCat.enoughInjectives` : the category of abelian groups (written additively) has
  enough injectives.
- `CommGrpCat.enoughInjectives` : the category of abelian groups (written multiplicatively) has
  enough injectives.

## Implementation notes

This file is split from `Mathlib/Algebra/Category/Grp/Injective.lean` to prevent import loops.
-/

public section

open CategoryTheory

universe u

namespace AddCommGrpCat

open CharacterModule

/-
**AddCommGrpCat.enoughInjectives** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
形式化陈述：enoughInjectives : EnoughInjectives AddCommGrpCat.{u} where presentation A
_
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `CharacterModule.instLinearMapClassIntAddCircleRatOfNat`：∀ (A : Type uA) 
[inst : AddCommGroup A], LinearMapClass (CharacterModule A) ℤ A (AddCircle 1)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGrpCat.mono_iff_injective`：∀ {A B : AddCommGrpCat} (f : A ⟶ B), C
ategoryTheory.Mono f ↔ Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom 
f)
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `CharacterModule.eq_zero_of_character_apply`：eq_zero_of_character_apply {
a : A} (h : forall c : CharacterModule A, c a = 0) : a = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
instance enoughInjectives : EnoughInjectives AddCommGrpCat.{u} where
  presentation A_ := Nonempty.intro
    { J := of <| (CharacterModule A_) → ULift.{u} (AddCircle (1 : ℚ))
      injective := injective_of_divisible _
      f := ofHom ⟨⟨fun a i ↦ ULift.up (i a), by aesop⟩, by aesop⟩
      mono := (AddCommGrpCat.mono_iff_injective _).mpr <| (injective_iff_map_eq_zero _).mpr
        fun _ h0 ↦ eq_zero_of_character_apply (congr_arg ULift.down <| congr_fun h0 ·) }

end AddCommGrpCat


namespace CommGrpCat

/-
**CommGrpCat.enoughInjectives** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
形式化陈述：enoughInjectives : EnoughInjectives CommGrpCat.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnoughInjectives.of_equivalence`：∀ {C : Type u₁} {D : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (e : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance enoughInjectives : EnoughInjectives CommGrpCat.{u} :=
  EnoughInjectives.of_equivalence commGroupAddCommGroupEquivalence.functor

end CommGrpCat

