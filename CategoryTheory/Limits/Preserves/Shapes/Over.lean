/-
Copyright (c) 2025 Yaël Dillies, Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Moisés Herradón Cueto
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.WithTerminal.FinCategory
public import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# If a functor preserves limits, so does the induced functor in the `Over` or `Under` category

Suppose we are given categories `C` and `D`, and object `X : C`, and a functor `F : C ⥤ D`.
`F` induces a functor `Over.post F : Over X ⥤ Over (F.obj X)`. If `F` preserves limits of a
certain shape `WithTerminal J`, then `Over.post F` preserves limits of shape `J`.
As a corollary, if `F` preserves finite limits, or limits of a certain size, so does `Over.post F`.

Dually, if `F` preserves certain colimits, `Under.post F` will preserve certain colimits as well.
-/

public section

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {X : C} {F : C ⥤ D}

-- TODO: Do we even want to keep `WidePullbackShape` around?
/-
**CategoryTheory.Limits.PreservesLimitsOfShape.ofWidePullbacks** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.PreservesLimitsOfShape`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {J : Type u_1}   [CategoryTheory.Limits.PreservesLimitsOfShape (CategoryTheory.
Limits.WidePullbackShape J) F],   CategoryTheory.Limits.PreservesLimitsOfShape (
CategoryTheory.WithTerminal (CategoryTheory.Discrete J)) F
参数：CategoryTheory.Limits.WidePullbackShape J；CategoryTheory.WithTerminal (Catego
ryTheory.Discrete J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
-/
instance PreservesLimitsOfShape.ofWidePullbacks {J : Type*}
    [PreservesLimitsOfShape (WidePullbackShape J) F] :
    PreservesLimitsOfShape (WithTerminal <| Discrete J) F :=
  preservesLimitsOfShape_of_equiv WithTerminal.widePullbackShapeEquiv F

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open WithTerminal in
/-
**CategoryTheory.Limits.PreservesLimitsOfShape.overPost** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.PreservesLimitsOfShape`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {X : C} {F : CategoryTheory.Functor C D}   [CategoryTh
eory.Limits.PreservesLimitsOfShape (CategoryTheory.WithTerminal J) F],   Categor
yTheory.Limits.PreservesLimitsOfShape J (CategoryTheory.Over.post F)
参数：CategoryTheory.WithTerminal J；CategoryTheory.Over.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
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
-/
instance PreservesLimitsOfShape.overPost [PreservesLimitsOfShape (WithTerminal J) F] :
    PreservesLimitsOfShape J (Over.post F (X := X)) where
  preservesLimit.preserves {coneK} isLimitConeK :=
    have isLimitConeD := (IsLimit.postcomposeHomEquiv liftFromOverComp.symm _).symm <|
      isLimitOfPreserves F (isLimitEquiv.symm isLimitConeK)
    ⟨isLimitEquiv <| isLimitConeD.ofIsoLimit <| Cone.ext (.refl _) fun | .star | .of a => by aesop⟩
/-
**CategoryTheory.Limits.PreservesFiniteLimits.overPost** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.PreservesFiniteLimits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : C} {F : CategoryTheory.Func
tor C D} [CategoryTheory.Limits.PreservesFiniteLimits F],   CategoryTheory.Limit
s.PreservesFiniteLimits (CategoryTheory.Over.post F)
参数：CategoryTheory.Over.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.overPost`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance PreservesFiniteLimits.overPost [PreservesFiniteLimits F] :
    PreservesFiniteLimits (Over.post F (X := X)) where
  preservesFiniteLimits _ := inferInstance
/-
**CategoryTheory.Limits.PreservesLimitsOfSize.overPost** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.PreservesLimitsOfSize`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : C} {F : CategoryTheory.Func
tor C D} [CategoryTheory.Limits.PreservesLimitsOfSize.{w', w, v₁, v₂, u₁, u₂} F]
,   CategoryTheory.Limits.PreservesLimitsOfSize.{w', w, v₁, v₂, max u₁ v₁, max u
₂ v₂} (CategoryTheory.Over.post F)
参数：CategoryTheory.Over.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.overPost`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance PreservesLimitsOfSize.overPost [PreservesLimitsOfSize.{w', w} F] :
    PreservesLimitsOfSize.{w', w} (Over.post F (X := X)) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open WithInitial in
/-
**CategoryTheory.Limits.PreservesColimitsOfShape.underPost** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.PreservesColimitsOfShape`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst_2 : CategoryT
heory.Category.{w', w} J] {X : C} {F : CategoryTheory.Functor C D}   [CategoryTh
eory.Limits.PreservesColimitsOfShape (CategoryTheory.WithInitial J) F],   Catego
ryTheory.Limits.PreservesColimitsOfShape J (CategoryTheory.Under.post F)
参数：CategoryTheory.WithInitial J；CategoryTheory.Under.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance PreservesColimitsOfShape.underPost [PreservesColimitsOfShape (WithInitial J) F] :
    PreservesColimitsOfShape J (Under.post F (X := X)) where
  preservesColimit.preserves {coconeK} isColimitCoconeK :=
    have isColimitCoconeD := (IsColimit.precomposeHomEquiv liftFromUnderComp _).symm <|
      isColimitOfPreserves F (isColimitEquiv.symm isColimitCoconeK)
    ⟨isColimitEquiv <| isColimitCoconeD.ofIsoColimit <|
      Cocone.ext (.refl _) fun | .star | .of a => by aesop⟩
/-
**CategoryTheory.Limits.PreservesFiniteColimits.underPost** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.PreservesFiniteColimits`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : C} {F : CategoryTheory.Func
tor C D} [CategoryTheory.Limits.PreservesFiniteColimits F],   CategoryTheory.Lim
its.PreservesFiniteColimits (CategoryTheory.Under.post F)
参数：CategoryTheory.Under.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.underPost`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance PreservesFiniteColimits.underPost [PreservesFiniteColimits F] :
    PreservesFiniteColimits (Under.post F (X := X)) where
  preservesFiniteColimits _ := inferInstance
/-
**CategoryTheory.Limits.PreservesColimitsOfSize.underPost** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.PreservesColimitsOfSize`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {X : C} {F : CategoryTheory.Func
tor C D} [CategoryTheory.Limits.PreservesColimitsOfSize.{w', w, v₁, v₂, u₁, u₂} 
F],   CategoryTheory.Limits.PreservesColimitsOfSize.{w', w, v₁, v₂, max u₁ v₁, m
ax u₂ v₂} (CategoryTheory.Under.post F)
参数：CategoryTheory.Under.post F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.underPost`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance PreservesColimitsOfSize.underPost [PreservesColimitsOfSize.{w', w} F] :
    PreservesColimitsOfSize.{w', w} (Under.post F (X := X)) where

end CategoryTheory.Limits

