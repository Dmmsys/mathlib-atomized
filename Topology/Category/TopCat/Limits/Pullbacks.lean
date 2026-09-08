/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Pullbacks and pushouts in the category of topological spaces
-/

@[expose] public section

open TopologicalSpace Topology

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [Category.{w} J]

section Pullback

variable {X Y Z : TopCat.{u}}

/-- The first projection from the pullback. -/
/-
**TopCat.pullbackFst** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p
.2 } ⟶ X
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection from the pullback.
-/
abbrev pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
  ofHom ⟨Prod.fst ∘ Subtype.val, by fun_prop⟩
/-
**TopCat.pullbackFst_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：pullbackFst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackFst f g x = x.1.1
参数：f : X ⟶ Z；g : Y ⟶ Z；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackFst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackFst f g x = x.1.1 := rfl

/-- The second projection from the pullback. -/
/-
**TopCat.pullbackSnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p
.2 } ⟶ Y
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection from the pullback.
-/
abbrev pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
  ofHom ⟨Prod.snd ∘ Subtype.val, by fun_prop⟩
/-
**TopCat.pullbackSnd_apply** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：pullbackSnd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackSnd f g x = x.1.2
参数：f : X ⟶ Z；g : Y ⟶ Z；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackSnd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x) : pullbackSnd f g x = x.1.2 := rfl

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
/-
**TopCat.pullbackCone** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`.
-/
def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (by
      dsimp [pullbackFst, pullbackSnd, Function.comp_def]
      ext ⟨x, h⟩
      simpa)

set_option backward.defeqAttrib.useBackward true in
/-- The constructed cone is a limit. -/
/-
**TopCat.pullbackConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackCone f g)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed cone is a limit.
-/
def pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux' _
    (by
      intro S
      constructor; swap
      · exact ofHom
          { toFun := fun x =>
              ⟨⟨S.fst x, S.snd x⟩, by simpa using! ConcreteCategory.congr_hom S.condition x⟩
            continuous_toFun := by fun_prop }
      refine ⟨?_, ?_, ?_⟩
      · delta pullbackCone
        ext a
        dsimp
      · delta pullbackCone
        ext a
        dsimp
      · intro m h₁ h₂
        ext x
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be `ext x`.
        apply Subtype.ext
        apply Prod.ext
        · simpa using! ConcreteCategory.congr_hom h₁ x
        · simpa using! ConcreteCategory.congr_hom h₂ x)

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
/-
**TopCat.pullbackIsoProdSubtype** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) : pullback f g ≅ TopCat.of 
{ p : X × Y // f p.1 = g p.2 }
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of two maps can be identified as a subspace of `X × Y`.
-/
def pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ≅ TopCat.of { p : X × Y // f p.1 = g p.2 } :=
  (limit.isLimit _).conePointUniqueUpToIso (pullbackConeIsLimit f g)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.pullbackIsoProdSubtype_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullbackIsoProdSubtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdS
ubtype f g).inv ≫ pullback.fst _ _ = pullbackFst f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_inv_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoProdSubtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.fst _ _ = pullbackFst f g := by
  simp [pullbackCone, pullbackIsoProdSubtype]
/-
**TopCat.pullbackIsoProdSubtype_inv_fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`
。
形式化陈述：pullbackIsoProdSubtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X 
× Y // f p.1 = g p.2 }) : pullback.fst f g ((pullbackIsoProdSubtype f g).inv x) 
= (x : X × Y).fst
参数：f : X ⟶ Z；g : Y ⟶ Z；x : { p : X × Y // f p.1 = g p.2 }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst`：pullbackIsoProdSubtype_inv_fst (f
 : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdSubtype f g).inv ≫ pullback.fst _ _ = pu
llbackFst f g
-/
theorem pullbackIsoProdSubtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    pullback.fst f g ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).fst :=
  ConcreteCategory.congr_hom (pullbackIsoProdSubtype_inv_fst f g) x

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.pullbackIsoProdSubtype_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullbackIsoProdSubtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdS
ubtype f g).inv ≫ pullback.snd _ _ = pullbackSnd f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_inv_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackIsoProdSubtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.snd _ _ = pullbackSnd f g := by
  simp [pullbackCone, pullbackIsoProdSubtype]
/-
**TopCat.pullbackIsoProdSubtype_inv_snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`
。
形式化陈述：pullbackIsoProdSubtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X 
× Y // f p.1 = g p.2 }) : pullback.snd f g ((pullbackIsoProdSubtype f g).inv x) 
= (x : X × Y).snd
参数：f : X ⟶ Z；g : Y ⟶ Z；x : { p : X × Y // f p.1 = g p.2 }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd`：pullbackIsoProdSubtype_inv_snd (f
 : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdSubtype f g).inv ≫ pullback.snd _ _ = pu
llbackSnd f g
-/
theorem pullbackIsoProdSubtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    pullback.snd f g ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).snd :=
  ConcreteCategory.congr_hom (pullbackIsoProdSubtype_inv_snd f g) x
/-
**TopCat.pullbackIsoProdSubtype_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullbackIsoProdSubtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdS
ubtype f g).hom ≫ pullbackFst f g = pullback.fst _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst`：pullbackIsoProdSubtype_inv_fst (f
 : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdSubtype f g).inv ≫ pullback.fst _ _ = pu
llbackFst f g
-/
theorem pullbackIsoProdSubtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).hom ≫ pullbackFst f g = pullback.fst _ _ := by
  rw [← Iso.eq_inv_comp, pullbackIsoProdSubtype_inv_fst]
/-
**TopCat.pullbackIsoProdSubtype_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullbackIsoProdSubtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdS
ubtype f g).hom ≫ pullbackSnd f g = pullback.snd _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd`：pullbackIsoProdSubtype_inv_snd (f
 : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdSubtype f g).inv ≫ pullback.snd _ _ = pu
llbackSnd f g
-/
theorem pullbackIsoProdSubtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).hom ≫ pullbackSnd f g = pullback.snd _ _ := by
  rw [← Iso.eq_inv_comp, pullbackIsoProdSubtype_inv_snd]
/-
**TopCat.pullbackIsoProdSubtype_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullbackIsoProdSubtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z} (x : ↑(pullback f
 g)) : (pullbackIsoProdSubtype f g).hom x = ⟨⟨pullback.fst f g x, pullback.snd f
 g x⟩, by simpa using CategoryTheory.congr_fun pullback.condition x⟩
参数：x : ↑(pullback f g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
-/
theorem pullbackIsoProdSubtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z}
    (x : ↑(pullback f g)) :
    (pullbackIsoProdSubtype f g).hom x =
      ⟨⟨pullback.fst f g x, pullback.snd f g x⟩, by
        simpa using CategoryTheory.congr_fun pullback.condition x⟩ := rfl
/-
**TopCat.pullback_topology** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullback_topology {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : (pullback
 f g).str = induced (pullback.fst f g) X.str ⊓ induced (pullback.snd f g) Y.str
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
-/
theorem pullback_topology {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).str =
      induced (pullback.fst f g) X.str ⊓
        induced (pullback.snd f g) Y.str := by
  let homeo := homeoOfIso (pullbackIsoProdSubtype f g)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (induced _ ((induced Prod.fst X.str) ⊓ (induced Prod.snd Y.str))) = _
  simp only [induced_compose, induced_inf]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.range_pullback_to_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：range_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : Set.
range (prod.lift (pullback.fst f g) (pullback.snd f g)) = { x | (Limits.prod.fst
 ≫ f) x = (Limits.prod.snd ≫ g) x }
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Concrete.limit_ext`：limit_ext [HasLimit F] (x y : 
ToType (limit F)) : (forall j, limit.π F j x = limit.π F j y) -> x = y
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsRightAdjointForgetContinuousMapCarrier`：(CategoryTheory.for
get TopCat).IsRightAdjoint
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst`：pullbackIsoProdSubtype_inv_fst (f
 : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdSubtype f g).inv ≫ pullback.fst _ _ = pu
llbackFst f g
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd`：pullbackIsoProdSubtype_inv_snd (f
 : X ⟶ Z) (g : Y ⟶ Z) : (pullbackIsoProdSubtype f g).inv ≫ pullback.snd _ _ = pu
llbackSnd f g
-/
theorem range_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (prod.lift (pullback.fst f g) (pullback.snd f g)) =
      { x | (Limits.prod.fst ≫ f) x = (Limits.prod.snd ≫ g) x } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp only [← ConcreteCategory.comp_apply, Set.mem_ofPred_eq]
    simp [pullback.condition]
  · rintro (h : f (_, _).1 = g (_, _).2)
    use (pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, h⟩
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;>
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, limit.lift_π] <;>
      -- This used to be `simp` before https://github.com/leanprover/lean4/pull/2644
      cat_disch

/-- The pullback along an embedding is (isomorphic to) the preimage. -/
noncomputable
/-
**TopCat.pullbackHomeoPreimage** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：pullbackHomeoPreimage {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpa
ce Y] [TopologicalSpace Z] (f : X -> Z) (hf : Continuous f) (g : Y -> Z) (hg : I
sEmbedding g) : { p : X × Y // f p.1 = g p.2 } ≃ₜ f ⁻¹' Set.range g where toFun
参数：f : X -> Z；hf : Continuous f；g : Y -> Z；hg : IsEmbedding g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pullbackHomeoPreimage
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Z) (hf : Continuous f) (g : Y → Z) (hg : IsEmbedding g) :
    { p : X × Y // f p.1 = g p.2 } ≃ₜ f ⁻¹' Set.range g where
  toFun := fun x ↦ ⟨x.1.1, _, x.2.symm⟩
  invFun := fun x ↦ ⟨⟨x.1, Exists.choose x.2⟩, (Exists.choose_spec x.2).symm⟩
  left_inv := by
    intro x
    ext <;> dsimp
    apply hg.injective
    convert! x.prop
    exact Exists.choose_spec (p := fun y ↦ g y = f (↑x : X × Y).1) _
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine continuous_subtype_val.prodMk <| hg.isInducing.continuous_iff.mpr ?_
    convert! hf.comp continuous_subtype_val
    ext x
    exact Exists.choose_spec x.2

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.isInducing_pullback_to_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isInducing_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
 IsInducing ⇑(prod.lift (pullback.fst f g) (pullback.snd f g))
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.pullback_topology`：pullback_topology {X Y Z : TopCat.{u}} (f : X 
⟶ Z) (g : Y ⟶ Z) : (pullback f g).str = induced (pullback.fst f g) X.str ⊓ induc
ed (pullback.s…
· 使用定理 `TopCat.prod_topology`：prod_topology {X Y : TopCat.{u}} : (X ⨯ Y).str = i
nduced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓ induced (Limits.prod.snd : X ⨯ Y ⟶ 
_) Y.str
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInducing_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsInducing <| ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨by simp [prod_topology, pullback_topology, induced_compose, ← coe_comp]⟩
/-
**TopCat.isEmbedding_pullback_to_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) 
: IsEmbedding ⇑(prod.lift (pullback.fst f g) (pullback.snd f g))
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.isInducing_pullback_to_prod`：isInducing_pullback_to_prod {X Y Z :
 TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : IsInducing ⇑(prod.lift (pullback.fst f g)
 (pullback.snd f g))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.mono_iff_injective`：mono_iff_injective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Mono f ↔ Function.Injective f
-/
theorem isEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsEmbedding <| ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨isInducing_pullback_to_prod f g, (TopCat.mono_iff_injective _).mp inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X ⟶ Y ×ₜ Z`. -/
/-
**TopCat.range_pullback_map** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：range_pullback_map {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g
₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : Mono i₃] (e
q₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : Set.range (pullback.map f₁ f
₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) = (pullback.fst g₁ g₂) ⁻¹' Set.range i₁ inter (pullbac
k.snd g₁ g₂) ⁻¹' Set.range i₂
参数：f₁ : W ⟶ S；f₂ : X ⟶ S；g₁ : Y ⟶ T；g₂ : Z ⟶ T；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁；eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `exists_apply_eq_apply`：∀ {α : Sort u_2} {β : Sort u_1} (f : α → β) (a' :
 α), ∃ a, f a = f a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.mono_iff_injective`：mono_iff_injective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.Concrete.limit_ext`：limit_ext [HasLimit F] (x y : 
ToType (limit F)) : (forall j, limit.π F j x = limit.π F j y) -> x = y
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsRightAdjointForgetContinuousMapCarrier`：(CategoryTheory.for
get TopCat).IsRightAdjoint
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst_assoc`：∀ {X Y Z : TopCat} (f : X ⟶
 Z) (g : Y ⟶ Z) {Z_1 : TopCat} (h : X ⟶ Z_1),   CategoryTheory.CategoryStruct.co
mp (TopCat.pullbackIsoProdSubtype…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd_assoc`：∀ {X Y Z : TopCat} (f : X ⟶
 Z) (g : Y ⟶ Z) {Z_1 : TopCat} (h : Y ⟶ Z_1),   CategoryTheory.CategoryStruct.co
mp (TopCat.pullbackIsoProdSubtype…

--- 原说明 ---
If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X 
⟶ Y ×ₜ Z`.
-/
theorem range_pullback_map {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Set.range (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) =
      (pullback.fst g₁ g₂) ⁻¹' Set.range i₁ ∩ (pullback.snd g₁ g₂) ⁻¹' Set.range i₂ := by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    simp only [limit.lift_π, PullbackCone.mk_π_app]
    exact ⟨exists_apply_eq_apply _ _, exists_apply_eq_apply _ _⟩
  rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  have : f₁ x₁ = f₂ x₂ := by
    apply (TopCat.mono_iff_injective _).mp H₃
    rw [← ConcreteCategory.comp_apply, eq₁, ← ConcreteCategory.comp_apply, eq₂,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx₁, hx₂,
      ← ConcreteCategory.comp_apply, pullback.condition, ConcreteCategory.comp_apply]
  use (pullbackIsoProdSubtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩
  apply Concrete.limit_ext
  rintro (_ | _ | _) <;>
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  · simp [hx₁, ← limit.w _ WalkingCospan.Hom.inl]
  · simp [hx₁]
  · simp [hx₂]
/-
**TopCat.pullback_fst_range** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullback_fst_range {X Y S : TopCat.{u}} (f : X ⟶ S) (g : Y ⟶ S) : Set.rang
e (pullback.fst f g) = { x : X | exists y : Y, f x = g y }
参数：f : X ⟶ S；g : Y ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst_apply`：pullbackIsoProdSubtype_inv_
fst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.fst f g ((pullbackIsoProdSubtyp…
-/
theorem pullback_fst_range {X Y S : TopCat.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g) = { x : X | ∃ y : Y, f x = g y } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    use pullback.snd f g y
    exact CategoryTheory.congr_fun pullback.condition y
  · rintro ⟨y, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_fst_apply]
/-
**TopCat.pullback_snd_range** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullback_snd_range {X Y S : TopCat.{u}} (f : X ⟶ S) (g : Y ⟶ S) : Set.rang
e (pullback.snd f g) = { y : Y | exists x : X, f x = g y }
参数：f : X ⟶ S；g : Y ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd_apply`：pullbackIsoProdSubtype_inv_
snd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.snd f g ((pullbackIsoProdSubtyp…
-/
theorem pullback_snd_range {X Y S : TopCat.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g) = { y : Y | ∃ x : X, f x = g y } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    use pullback.fst f g x
    exact CategoryTheory.congr_fun pullback.condition x
  · rintro ⟨x, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, eq⟩
    rw [pullbackIsoProdSubtype_inv_snd_apply]

set_option backward.isDefEq.respectTransparency false in
/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

```
W ⟶ Y
 ↘   ↘
  S ⟶ T
 ↗   ↗
X ⟶ Z
```
-/
/-
**TopCat.pullback_map_isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullback_map_isEmbedding {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶
 S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : IsEmbedding i₁) (H
₂ : IsEmbedding i₂) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫
 g₂) : IsEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂)
参数：f₁ : W ⟶ S；f₂ : X ⟶ S；g₁ : Y ⟶ T；g₂ : Z ⟶ T；H₁ : IsEmbedding i₁；H₂ : IsEmbedd
ing i₂；i₃ : S ⟶ T；eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁；eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `TopCat.isEmbedding_prodMap`：isEmbedding_prodMap {W X Y Z : TopCat.{u}} {
f : W ⟶ X} {g : Y ⟶ Z} (hf : IsEmbedding f) (hg : IsEmbedding g) : IsEmbedding (
Limits.prod.map …
· 使用定理 `TopCat.isEmbedding_pullback_to_prod`：isEmbedding_pullback_to_prod {X Y Z
 : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : IsEmbedding ⇑(prod.lift (pullback.fst f
 g) (pullback.snd f g))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…

--- 原说明 ---
If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

```
W ⟶ Y
 ↘   ↘
  S ⟶ T
 ↗   ↗
X ⟶ Z
```
-/
theorem pullback_map_isEmbedding {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S)
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : IsEmbedding i₁)
    (H₂ : IsEmbedding i₂) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    IsEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine .of_comp (ContinuousMap.continuous_toFun _)
    (show Continuous (prod.lift (pullback.fst g₁ g₂) (pullback.snd g₁ g₂)) from
        ContinuousMap.continuous_toFun _)
      ?_
  suffices
    IsEmbedding (prod.lift (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) ≫ Limits.prod.map i₁ i₂) by
    simpa [← coe_comp] using this
  rw [coe_comp]
  exact (isEmbedding_prodMap H₁ H₂).comp (isEmbedding_pullback_to_prod _ _)

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embeddings, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.

```
W ⟶ Y
 ↘   ↘
  S ⟶ T
 ↗   ↗
X ⟶ Z
```
-/
/-
**TopCat.pullback_map_isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullback_map_isOpenEmbedding {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ :
 X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : IsOpenEmbeddin
g i₁) (H₂ : IsOpenEmbedding i₂) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ 
≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : IsOpenEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i
₂ i₃ eq₁ eq₂)
参数：f₁ : W ⟶ S；f₂ : X ⟶ S；g₁ : Y ⟶ T；g₂ : Z ⟶ T；H₁ : IsOpenEmbedding i₁；H₂ : IsOp
enEmbedding i₂；i₃ : S ⟶ T；eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁；eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `TopCat.pullback_map_isEmbedding`：pullback_map_isEmbedding {W X Y Z S T :
 TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i
₂ : X ⟶ Z} (H₁ : IsEm…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.range_pullback_map`：range_pullback_map {W X Y Z S T : TopCat.{u}}
 (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (
i₃ : S ⟶ T) [H₃…
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…

--- 原说明 ---
If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embedding
s, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.

```
W ⟶ Y
 ↘   ↘
  S ⟶ T
 ↗   ↗
X ⟶ Z
```
-/
theorem pullback_map_isOpenEmbedding {W X Y Z S T : TopCat.{u}} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : IsOpenEmbedding i₁)
    (H₂ : IsOpenEmbedding i₂) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : IsOpenEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  constructor
  · apply
      pullback_map_isEmbedding f₁ f₂ g₁ g₂ H₁.isEmbedding H₂.isEmbedding i₃ eq₁ eq₂
  · rw [range_pullback_map]
    apply IsOpen.inter <;> apply Continuous.isOpen_preimage
    · apply ContinuousMap.continuous_toFun
    · exact H₁.isOpen_range
    · apply ContinuousMap.continuous_toFun
    · exact H₂.isOpen_range


set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.snd_isEmbedding_of_left** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：snd_isEmbedding_of_left {X Y S : TopCat.{u}} {f : X ⟶ S} (H : IsEmbedding 
f) (g : Y ⟶ S) : IsEmbedding ⇑(pullback.snd f g)
参数：H : IsEmbedding f；g : Y ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `TopCat.pullback_map_isEmbedding`：pullback_map_isEmbedding {W X Y Z S T :
 TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i
₂ : X ⟶ Z} (H₁ : IsEm…
-/
lemma snd_isEmbedding_of_left {X Y S : TopCat.{u}} {f : X ⟶ S} (H : IsEmbedding f) (g : Y ⟶ S) :
    IsEmbedding <| ⇑(pullback.snd f g) := by
  convert!
    (homeoOfIso (asIso (pullback.snd (𝟙 S) g))).isEmbedding.comp
      (pullback_map_isEmbedding (i₂ := 𝟙 Y) f g (𝟙 S) g H (homeoOfIso (Iso.refl _)).isEmbedding
        (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.fst_isEmbedding_of_right** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：fst_isEmbedding_of_right {X Y S : TopCat.{u}} (f : X ⟶ S) {g : Y ⟶ S} (H :
 IsEmbedding g) : IsEmbedding ⇑(pullback.fst f g)
参数：f : X ⟶ S；H : IsEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `TopCat.pullback_map_isEmbedding`：pullback_map_isEmbedding {W X Y Z S T :
 TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i
₂ : X ⟶ Z} (H₁ : IsEm…
-/
theorem fst_isEmbedding_of_right {X Y S : TopCat.{u}} (f : X ⟶ S) {g : Y ⟶ S}
    (H : IsEmbedding g) : IsEmbedding <| ⇑(pullback.fst f g) := by
  convert!
    (homeoOfIso (asIso (pullback.fst f (𝟙 S)))).isEmbedding.comp
      (pullback_map_isEmbedding (i₁ := 𝟙 X) f g f (𝟙 _) (homeoOfIso (Iso.refl _)).isEmbedding H
        (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]
/-
**TopCat.isEmbedding_of_pullback** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isEmbedding_of_pullback {X Y S : TopCat.{u}} {f : X ⟶ S} {g : Y ⟶ S} (H₁ :
 IsEmbedding f) (H₂ : IsEmbedding g) : IsEmbedding (limit.π (cospan f g) Walking
Cospan.one)
参数：H₁ : IsEmbedding f；H₂ : IsEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用引理 `TopCat.snd_isEmbedding_of_left`：snd_isEmbedding_of_left {X Y S : TopCat.
{u}} {f : X ⟶ S} (H : IsEmbedding f) (g : Y ⟶ S) : IsEmbedding ⇑(pullback.snd f 
g)
-/
theorem isEmbedding_of_pullback {X Y S : TopCat.{u}} {f : X ⟶ S} {g : Y ⟶ S} (H₁ : IsEmbedding f)
    (H₂ : IsEmbedding g) : IsEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert! H₂.comp (snd_isEmbedding_of_left H₁ g)
  rw [← coe_comp, ← limit.w _ WalkingCospan.Hom.inr]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.snd_isOpenEmbedding_of_left** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：snd_isOpenEmbedding_of_left {X Y S : TopCat.{u}} {f : X ⟶ S} (H : IsOpenEm
bedding f) (g : Y ⟶ S) : IsOpenEmbedding ⇑(pullback.snd f g)
参数：H : IsOpenEmbedding f；g : Y ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `TopCat.pullback_map_isOpenEmbedding`：pullback_map_isOpenEmbedding {W X Y
 Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W
 ⟶ Y} {i₂ : X ⟶ Z} (H₁ : …
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
-/
theorem snd_isOpenEmbedding_of_left {X Y S : TopCat.{u}} {f : X ⟶ S} (H : IsOpenEmbedding f)
    (g : Y ⟶ S) : IsOpenEmbedding <| ⇑(pullback.snd f g) := by
  convert!
    (homeoOfIso (asIso (pullback.snd (𝟙 S) g))).isOpenEmbedding.comp
      (pullback_map_isOpenEmbedding (i₂ := 𝟙 Y) f g (𝟙 _) g H
        (homeoOfIso (Iso.refl _)).isOpenEmbedding (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.fst_isOpenEmbedding_of_right** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：fst_isOpenEmbedding_of_right {X Y S : TopCat.{u}} (f : X ⟶ S) {g : Y ⟶ S} 
(H : IsOpenEmbedding g) : IsOpenEmbedding ⇑(pullback.fst f g)
参数：f : X ⟶ S；H : IsOpenEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `TopCat.pullback_map_isOpenEmbedding`：pullback_map_isOpenEmbedding {W X Y
 Z S T : TopCat.{u}} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W
 ⟶ Y} {i₂ : X ⟶ Z} (H₁ : …
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
-/
theorem fst_isOpenEmbedding_of_right {X Y S : TopCat.{u}} (f : X ⟶ S) {g : Y ⟶ S}
    (H : IsOpenEmbedding g) : IsOpenEmbedding <| ⇑(pullback.fst f g) := by
  convert!
    (homeoOfIso (asIso (pullback.fst f (𝟙 S)))).isOpenEmbedding.comp
      (pullback_map_isOpenEmbedding (i₁ := 𝟙 X) f g f (𝟙 _)
        (homeoOfIso (Iso.refl _)).isOpenEmbedding H (𝟙 _) rfl (by simp))
  simp [homeoOfIso, ← coe_comp]

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
/-
**TopCat.isOpenEmbedding_of_pullback** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isOpenEmbedding_of_pullback {X Y S : TopCat.{u}} {f : X ⟶ S} {g : Y ⟶ S} (
H₁ : IsOpenEmbedding f) (H₂ : IsOpenEmbedding g) : IsOpenEmbedding (limit.π (cos
pan f g) WalkingCospan.one)
参数：H₁ : IsOpenEmbedding f；H₂ : IsOpenEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `CategoryTheory.Limits.limit.w`：∀ {J : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   (F
 : CategoryTheory.F…
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `TopCat.snd_isOpenEmbedding_of_left`：snd_isOpenEmbedding_of_left {X Y S :
 TopCat.{u}} {f : X ⟶ S} (H : IsOpenEmbedding f) (g : Y ⟶ S) : IsOpenEmbedding ⇑
(pullback.snd f g)

--- 原说明 ---
If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`.
-/
theorem isOpenEmbedding_of_pullback {X Y S : TopCat.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (H₁ : IsOpenEmbedding f) (H₂ : IsOpenEmbedding g) :
    IsOpenEmbedding (limit.π (cospan f g) WalkingCospan.one) := by
  convert! H₂.comp (snd_isOpenEmbedding_of_left H₁ g)
  rw [← coe_comp, ← limit.w _ WalkingCospan.Hom.inr]
  rfl
/-
**TopCat.fst_iso_of_right_embedding_range_subset** 是 Mathlib 中的一个定理，位于命名空间 `TopC
at`。
形式化陈述：fst_iso_of_right_embedding_range_subset {X Y S : TopCat.{u}} (f : X ⟶ S) {
g : Y ⟶ S} (hg : IsEmbedding g) (H : Set.range f subseteq Set.range g) : IsIso (
pullback.fst f g)
参数：f : X ⟶ S；hg : IsEmbedding g；H : Set.range f subseteq Set.range g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `TopCat.fst_isEmbedding_of_right`：fst_isEmbedding_of_right {X Y S : TopCa
t.{u}} (f : X ⟶ S) {g : Y ⟶ S} (H : IsEmbedding g) : IsEmbedding ⇑(pullback.fst 
f g)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.pullback_fst_range`：pullback_fst_range {X Y S : TopCat.{u}} (f : 
X ⟶ S) (g : Y ⟶ S) : Set.range (pullback.fst f g) = { x : X | exists y : Y, f x 
= g y }
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem fst_iso_of_right_embedding_range_subset {X Y S : TopCat.{u}} (f : X ⟶ S) {g : Y ⟶ S}
    (hg : IsEmbedding g) (H : Set.range f ⊆ Set.range g) :
    IsIso (pullback.fst f g) := by
  let esto : (pullback f g : TopCat) ≃ₜ X :=
    (fst_isEmbedding_of_right f hg).toHomeomorph.trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_fst_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec.symm⟩⟩ }
  convert! (isoOfHomeo esto).isIso_hom
/-
**TopCat.snd_iso_of_left_embedding_range_subset** 是 Mathlib 中的一个定理，位于命名空间 `TopCa
t`。
形式化陈述：snd_iso_of_left_embedding_range_subset {X Y S : TopCat.{u}} {f : X ⟶ S} (h
f : IsEmbedding f) (g : Y ⟶ S) (H : Set.range g subseteq Set.range f) : IsIso (p
ullback.snd f g)
参数：hf : IsEmbedding f；g : Y ⟶ S；H : Set.range g subseteq Set.range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用引理 `TopCat.snd_isEmbedding_of_left`：snd_isEmbedding_of_left {X Y S : TopCat.
{u}} {f : X ⟶ S} (H : IsEmbedding f) (g : Y ⟶ S) : IsEmbedding ⇑(pullback.snd f 
g)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.pullback_snd_range`：pullback_snd_range {X Y S : TopCat.{u}} (f : 
X ⟶ S) (g : Y ⟶ S) : Set.range (pullback.snd f g) = { y : Y | exists x : X, f x 
= g y }
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem snd_iso_of_left_embedding_range_subset {X Y S : TopCat.{u}} {f : X ⟶ S} (hf : IsEmbedding f)
    (g : Y ⟶ S) (H : Set.range g ⊆ Set.range f) : IsIso (pullback.snd f g) := by
  let esto : (pullback f g : TopCat) ≃ₜ Y :=
    (snd_isEmbedding_of_left hf g).toHomeomorph.trans
      { toFun := Subtype.val
        invFun := fun x =>
          ⟨x, by
            rw [pullback_snd_range]
            exact ⟨_, (H (Set.mem_range_self x)).choose_spec⟩⟩ }
  convert! (isoOfHomeo esto).isIso_hom
/-
**TopCat.pullback_snd_image_fst_preimage** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) : (pul
lback.snd f g) '' (pullback.fst f g) ⁻¹' U = g ⁻¹' f '' U
参数：f : X ⟶ Z；g : Y ⟶ Z；U : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst_apply`：pullbackIsoProdSubtype_inv_
fst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.fst f g ((pullbackIsoProdSubtyp…
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd_apply`：pullbackIsoProdSubtype_inv_
snd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.snd f g ((pullbackIsoProdSubtyp…
-/
theorem pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) :
    (pullback.snd f g) '' (pullback.fst f g) ⁻¹' U =
      g ⁻¹' f '' U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨(pullback.fst f g) y, hy, CategoryTheory.congr_fun pullback.condition y⟩
  · rintro ⟨y, hy, eq⟩
  -- next 5 lines were
  -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, by simpa, by simp⟩` before https://github.com/leanprover-community/mathlib4/pull/13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert! hy
      rw [pullbackIsoProdSubtype_inv_fst_apply]
    · rw [pullbackIsoProdSubtype_inv_snd_apply]
/-
**TopCat.pullback_fst_image_snd_preimage** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) : (pul
lback.fst f g) '' (pullback.snd f g) ⁻¹' U = f ⁻¹' g '' U
参数：f : X ⟶ Z；g : Y ⟶ Z；U : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd_apply`：pullbackIsoProdSubtype_inv_
snd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.snd f g ((pullbackIsoProdSubtyp…
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst_apply`：pullbackIsoProdSubtype_inv_
fst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.fst f g ((pullbackIsoProdSubtyp…
-/
theorem pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) :
    (pullback.fst f g) '' (pullback.snd f g) ⁻¹' U =
      f ⁻¹' g '' U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨(pullback.snd f g) y, hy,
        (CategoryTheory.congr_fun pullback.condition y).symm⟩
  · rintro ⟨y, hy, eq⟩
    -- next 5 lines were
    -- `exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, by simpa, by simp⟩`
    -- before https://github.com/leanprover-community/mathlib4/pull/13170
    refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, eq.symm⟩, ?_, ?_⟩
    · simp only [coe_of, Set.mem_preimage]
      convert! hy
      rw [pullbackIsoProdSubtype_inv_snd_apply]
    · rw [pullbackIsoProdSubtype_inv_fst_apply]

end Pullback

section

variable {X Y : TopCat.{u}} {f g : X ⟶ Y}

/-
**TopCat.isOpen_iff_of_isColimit_cofork** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isOpen_iff_of_isColimit_cofork (c : Cofork f g) (hc : IsColimit c) (U : Se
t c.pt) : IsOpen U ↔ IsOpen (c.π ⁻¹' U)
参数：c : Cofork f g；hc : IsColimit c；U : Set c.pt。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TopCat.isOpen_iff_of_isColimit`：isOpen_iff_of_isColimit (X : Set c.pt) :
 IsOpen X ↔ forall (j : J), IsOpen (c.ι.app j ⁻¹' X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
lemma isOpen_iff_of_isColimit_cofork (c : Cofork f g) (hc : IsColimit c) (U : Set c.pt) :
    IsOpen U ↔ IsOpen (c.π ⁻¹' U) := by
  rw [isOpen_iff_of_isColimit _ hc]
  constructor
  · intro h
    exact h .one
  · rintro h (_ | _)
    · rw [← c.w .left]
      exact Continuous.isOpen_preimage f.hom.continuous (c.π ⁻¹' U) h
    · exact h
/-
**TopCat.isQuotientMap_of_isColimit_cofork** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：isQuotientMap_of_isColimit_cofork (c : Cofork f g) (hc : IsColimit c) : Is
QuotientMap c.π
参数：c : Cofork f g；hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.isQuotientMap_iff`：∀ {X : Type u_3} {Y : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y),   Topology.IsQuotient
Map f ↔ Topology…
· 使用定理 `Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen`：∀ {X : Type u_1} {Y
 : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y],   (∀ (s : Set Y), IsOpen (f ⁻¹' s) ↔ …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `TopCat.isOpen_iff_of_isColimit_cofork`：isOpen_iff_of_isColimit_cofork (c
 : Cofork f g) (hc : IsColimit c) (U : Set c.pt) : IsOpen U ↔ IsOpen (c.π ⁻¹' U)
· 使用定理 `CategoryTheory.Limits.epi_of_isColimit_cofork`：epi_of_isColimit_cofork {
c : Cofork f g} (i : IsColimit c) : Epi c.π
-/
lemma isQuotientMap_of_isColimit_cofork (c : Cofork f g) (hc : IsColimit c) :
    IsQuotientMap c.π := by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ ?_, ?_⟩
  · exact (isOpen_iff_of_isColimit_cofork c hc s).symm
  · simpa only [← epi_iff_surjective] using epi_of_isColimit_cofork hc
/-
**TopCat.coequalizer_isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：coequalizer_isOpen_iff (U : Set ((coequalizer f g :) : Type u)) : IsOpen U
 ↔ IsOpen (coequalizer.π f g ⁻¹' U)
参数：U : Set ((coequalizer f g :) : Type u)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用引理 `TopCat.isOpen_iff_of_isColimit_cofork`：isOpen_iff_of_isColimit_cofork (c
 : Cofork f g) (hc : IsColimit c) (U : Set c.pt) : IsOpen U ↔ IsOpen (c.π ⁻¹' U)
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…
-/
theorem coequalizer_isOpen_iff (U : Set ((coequalizer f g :) : Type u)) :
    IsOpen U ↔ IsOpen (coequalizer.π f g ⁻¹' U) :=
  isOpen_iff_of_isColimit_cofork _ (coequalizerIsCoequalizer f g) _

end

end TopCat

