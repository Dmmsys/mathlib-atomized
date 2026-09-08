/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Monoid objects internal to monoidal opposites

In this file, we record the equivalence between `Mon C` and `Mon Cᴹᵒᵖ`.
-/

@[expose] public section

namespace MonObj

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {C : Type*} [Category* C] [MonoidalCategory C]

section mop

variable (M : C) [MonObj M]

set_option backward.defeqAttrib.useBackward true in
/-- If `M : C` is a monoid object, then `mop M : Cᴹᵒᵖ` too. -/
@[simps!]
/-
**MonObj.mopMonObj** 是 Mathlib 中的一个实例，位于命名空间 `MonObj`。
形式化陈述：mopMonObj : MonObj (mop M) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M : C` is a monoid object, then `mop M : Cᴹᵒᵖ` too.
-/
instance mopMonObj : MonObj (mop M) where
  mul := MonObj.mul.mop
  one := MonObj.one.mop
  mul_one := by
    apply mopEquiv C |>.fullyFaithfulInverse.map_injective
    simp
  one_mul := by
    apply mopEquiv C |>.fullyFaithfulInverse.map_injective
    simp
  mul_assoc := by
    apply mopEquiv C |>.fullyFaithfulInverse.map_injective
    simp

variable {M} in
/-- If `f` is a morphism of monoid objects internal to `C`,
then `f.mop` is a morphism of monoid objects internal to `Cᴹᵒᵖ`. -/
/-
**MonObj.mop_isMonHom** 是 Mathlib 中的一个实例，位于命名空间 `MonObj`。
形式化陈述：mop_isMonHom {N : C} [MonObj N] (f : M ⟶ N) [IsMonHom f] : IsMonHom f.mop 
where mul_hom
参数：f : M ⟶ N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…

--- 原说明 ---
If `f` is a morphism of monoid objects internal to `C`,
then `f.mop` is a morphism of monoid objects internal to `Cᴹᵒᵖ`.
-/
instance mop_isMonHom {N : C} [MonObj N]
    (f : M ⟶ N) [IsMonHom f] : IsMonHom f.mop where
  mul_hom := by
    apply mopEquiv C |>.fullyFaithfulInverse.map_injective
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
    apply mopEquiv C |>.fullyFaithfulInverse.map_injective
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

end mop

section unmop

variable (M : Cᴹᵒᵖ) [MonObj M]

set_option backward.defeqAttrib.useBackward true in
/-- If `M : Cᴹᵒᵖ` is a monoid object, then `unmop M : C` too. -/
@[simps -isSimp] -- not making them simp because it causes a loop.
/-
**MonObj.unmopMonObj** 是 Mathlib 中的一个实例，位于命名空间 `MonObj`。
形式化陈述：unmopMonObj : MonObj (unmop M) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M : Cᴹᵒᵖ` is a monoid object, then `unmop M : C` too.
-/
instance unmopMonObj : MonObj (unmop M) where
  mul := MonObj.mul.unmop
  one := MonObj.one.unmop
  mul_one := by
    apply mopEquiv C |>.fullyFaithfulFunctor.map_injective
    simp
  one_mul := by
    apply mopEquiv C |>.fullyFaithfulFunctor.map_injective
    simp
  mul_assoc := by
    apply mopEquiv C |>.fullyFaithfulFunctor.map_injective
    simp

variable {M} in
/-- If `f` is a morphism of monoid objects internal to `Cᴹᵒᵖ`,
so is `f.unmop`. -/
/-
**MonObj.unmop_isMonHom** 是 Mathlib 中的一个实例，位于命名空间 `MonObj`。
形式化陈述：unmop_isMonHom {N : Cᴹᵒᵖ} [MonObj N] (f : M ⟶ N) [IsMonHom f] : IsMonHom f
.unmop where mul_hom
参数：f : M ⟶ N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsMonHom.one_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsMonHom.mul_hom`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}   {i
nst_2 : CategoryTheor…

--- 原说明 ---
If `f` is a morphism of monoid objects internal to `Cᴹᵒᵖ`,
so is `f.unmop`.
-/
instance unmop_isMonHom {N : Cᴹᵒᵖ} [MonObj N]
    (f : M ⟶ N) [IsMonHom f] : IsMonHom f.unmop where
  mul_hom := by
    apply mopEquiv C |>.fullyFaithfulFunctor.map_injective
    simpa [-IsMonHom.mul_hom] using! IsMonHom.mul_hom f
  one_hom := by
    apply mopEquiv C |>.fullyFaithfulFunctor.map_injective
    simpa [-IsMonHom.one_hom] using! IsMonHom.one_hom f

end unmop

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C`. -/
@[simps!]
/-
**MonObj.mopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonObj`。
形式化陈述：mopEquiv : Mon C ≌ Mon Cᴹᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C`.
-/
def mopEquiv : Mon C ≌ Mon Cᴹᵒᵖ where
  functor :=
    { obj M := ⟨mop M.X⟩
      map f := ⟨f.hom.mop⟩ }
  inverse :=
    { obj M := ⟨unmop M.X⟩
      map f := ⟨f.hom.unmop⟩ }
  unitIso := .refl _
  counitIso := .refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C` lies over
the equivalence `C ≌ Cᴹᵒᵖ` via the forgetful functors. -/
@[simps!]
/-
**MonObj.mopEquivCompForgetIso** 是 Mathlib 中的一个定义，位于命名空间 `MonObj`。
形式化陈述：mopEquivCompForgetIso : (mopEquiv C).functor ⋙ Mon.forget Cᴹᵒᵖ ≅ Mon.forge
t C ⋙ (MonoidalOpposite.mopEquiv C).functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C` lies over
the equivalence `C ≌ Cᴹᵒᵖ` via the forgetful functors.
-/
def mopEquivCompForgetIso :
    (mopEquiv C).functor ⋙ Mon.forget Cᴹᵒᵖ ≅
    Mon.forget C ⋙ (MonoidalOpposite.mopEquiv C).functor :=
  .refl _

end MonObj

