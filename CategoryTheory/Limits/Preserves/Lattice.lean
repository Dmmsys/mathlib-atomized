/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Lattice Homs that Preserve Limits and Colimits

This file provides instances for when OrderHom.toFunctor preserves limits/colimits.
In particular, if `f` preserves finite infs/sups (i.e. is from a InfTopHomClass/SupBotHomClass)
then `(toOrderHom f).toFunctor` preserves finite limits/colimits. If `f` preserves
arbitrary infs/sups (i.e. is from a sInfHomClass/sSupHomClass) then `(toOrderHom f).toFunctor`
preserves all limits/colimits.

-/

public section

open OrderHomClass

namespace CategoryTheory.Limits.CompleteLattice

universe w w' u v

variable {α : Type u} {β : Type v} {F : Type*} [FunLike F α β] (f : F)

section

variable [SemilatticeInf α] [OrderTop α] [SemilatticeInf β] [OrderTop β] [InfTopHomClass F α β]

/-
**CategoryTheory.Limits.CompleteLattice.preservesLimit_finite_toFunctor** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：preservesLimit_finite_toFunctor {J : Type w} [SmallCategory J] [FinCategor
y J] (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor
参数：K : J ⥤ α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.CompleteLattice.finiteLimitCone_cone_pt`：∀ {α : Ty
pe u} {J : Type w} [inst : CategoryTheory.SmallCategory J] [inst_1 : CategoryThe
ory.FinCategory J]   [inst_2 : SemilatticeInf α] [i…
· 使用定理 `map_finset_inf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeInf α] [inst_1 : OrderTop α]   [inst_2 : SemilatticeInf
 β] …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance preservesLimit_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor :=
  preservesLimit_of_preserves_limit_cone (finiteLimitCone K).isLimit <|
    (finiteLimitCone _).isLimit.ofIsoLimit
      (Cone.ext (eqToIso (show Finset.univ.inf _ = f _ by aesop)) (by subsingleton))
/-
**CategoryTheory.Limits.CompleteLattice.preservesLimitsOfShape_finite_toFunctor*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : SemilatticeInf α]   [inst_2 : OrderTop α] [inst_3 : SemilatticeInf β] 
[inst_4 : OrderTop β] [inst_5 : InfTopHomClass F α β] {J : Type w}   [inst_6 : C
ategoryTheory.SmallCategory J] [CategoryTheory.FinCategory J],   CategoryTheory.
Limits.PreservesLimitsOfShape J (↑f).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
-/
instance preservesLimitsOfShape_finite_toFunctor {J : Type w} [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J (toOrderHom f).toFunctor where
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteLimits (toOrderHom f).toFunctor where
  preservesFiniteLimits _ _ _ := inferInstance

end

section

variable [SemilatticeSup α] [OrderBot α] [SemilatticeSup β] [OrderBot β] [SupBotHomClass F α β]

/-
**CategoryTheory.Limits.CompleteLattice.preservesColimit_finite_toFunctor** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：preservesColimit_finite_toFunctor {J : Type w} [SmallCategory J] [FinCateg
ory J] (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor
参数：K : J ⥤ α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `SupHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : SemilatticeSu
p β] [SupHomClass…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.CompleteLattice.finiteColimitCocone_cocone_pt`：∀ {
α : Type u} {J : Type w} [inst : CategoryTheory.SmallCategory J] [inst_1 : Categ
oryTheory.FinCategory J]   [inst_2 : SemilatticeSup α] [i…
· 使用定理 `map_finset_sup`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeSup α] [inst_1 : OrderBot α]   [inst_2 : SemilatticeSup
 β] …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance preservesColimit_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor :=
  preservesColimit_of_preserves_colimit_cocone (finiteColimitCocone K).isColimit <|
    (finiteColimitCocone _).isColimit.ofIsoColimit
      (Cocone.ext (eqToIso (show Finset.univ.sup _ = f _ by aesop)) (by subsingleton))
/-
**CategoryTheory.Limits.CompleteLattice.preservesColimitsOfShape_finite_toFuncto
r** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : SemilatticeSup α]   [inst_2 : OrderBot α] [inst_3 : SemilatticeSup β] 
[inst_4 : OrderBot β] [inst_5 : SupBotHomClass F α β] {J : Type w}   [inst_6 : C
ategoryTheory.SmallCategory J] [CategoryTheory.FinCategory J],   CategoryTheory.
Limits.PreservesColimitsOfShape J (↑f).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : SemilatticeSu
p β] [SupHomClass…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
-/
instance preservesColimitsOfShape_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] : PreservesColimitsOfShape J (toOrderHom f).toFunctor where
/-
**CategoryTheory.Limits.CompleteLattice.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits.CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteColimits (toOrderHom f).toFunctor where
  preservesFiniteColimits _ _ _ := inferInstance

end

section

variable [CompleteLattice α] [CompleteLattice β]

/-
**CategoryTheory.Limits.CompleteLattice.preservesLimit_toFunctor** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：preservesLimit_toFunctor [sInfHomClass F α β] {J : Type w} [Category.{w'} 
J] (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor
参数：K : J ⥤ α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sInfHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sInfHomCl…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.CompleteLattice.limitCone_cone_pt`：∀ {α : Type u} 
[inst : CompleteLattice α] {J : Type w} [inst_1 : CategoryTheory.Category.{w', w
} J]   (F : CategoryTheory.Functor J α), (Cat…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_iInf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Sort u_6} 
[inst : FunLike F α β] [inst_1 : InfSet α]   [inst_2 : InfSet β] [sInfHomClass…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance preservesLimit_toFunctor [sInfHomClass F α β] {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor :=
  preservesLimit_of_preserves_limit_cone (limitCone K).isLimit <|
    (limitCone _).isLimit.ofIsoLimit (Cone.ext (eqToIso (by aesop)) (by subsingleton))
/-
**CategoryTheory.Limits.CompleteLattice.preservesLimitsOfShape_toFunctor** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_3 : sInfHomCla
ss F α β] {J : Type w} [inst_4 : CategoryTheory.Category.{w', w} J],   CategoryT
heory.Limits.PreservesLimitsOfShape J (↑f).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sInfHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sInfHomCl…
-/
instance preservesLimitsOfShape_toFunctor [sInfHomClass F α β] {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J (toOrderHom f).toFunctor where
/-
**CategoryTheory.Limits.CompleteLattice.preservesLimitsOfSize_toFunctor** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_3 : sInfHomCla
ss F α β],   CategoryTheory.Limits.PreservesLimitsOfSize.{w', w, u, v, u, v} (↑f
).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sInfHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sInfHomCl…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.preservesLimitsOfShape_toFunctor`：
∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) [inst_
1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_…
-/
instance preservesLimitsOfSize_toFunctor [sInfHomClass F α β] :
    PreservesLimitsOfSize.{w', w} (toOrderHom f).toFunctor where
/-
**CategoryTheory.Limits.CompleteLattice.preservesLimits_toFunctor** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_3 : sInfHomCla
ss F α β], CategoryTheory.Limits.PreservesLimits (↑f).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : SemilatticeIn
f β] [InfHomClass…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sInfHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sInfHomCl…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.preservesLimitsOfShape_toFunctor`：
∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) [inst_
1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_…
-/
instance preservesLimits_toFunctor [sInfHomClass F α β] :
    PreservesLimits (toOrderHom f).toFunctor where
/-
**CategoryTheory.Limits.CompleteLattice.preservesColimit_toFunctor** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：preservesColimit_toFunctor [sSupHomClass F α β] {J : Type w} [Category.{w'
} J] (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor
参数：K : J ⥤ α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `SupHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : SemilatticeSu
p β] [SupHomClass…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.CompleteLattice.colimitCocone_cocone_pt`：∀ {α : Ty
pe u} [inst : CompleteLattice α] {J : Type w} [inst_1 : CategoryTheory.Category.
{w', w} J]   (F : CategoryTheory.Functor J α), (Cat…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_iSup`：map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g
 : ι -> α) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance preservesColimit_toFunctor [sSupHomClass F α β] {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor :=
  preservesColimit_of_preserves_colimit_cocone (colimitCocone K).isColimit <|
    (colimitCocone _).isColimit.ofIsoColimit (Cocone.ext (eqToIso (by aesop)) (by subsingleton))
/-
**CategoryTheory.Limits.CompleteLattice.preservesColimitsOfShape_toFunctor** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_3 : sSupHomCla
ss F α β] {J : Type w} [inst_4 : CategoryTheory.Category.{w', w} J],   CategoryT
heory.Limits.PreservesColimitsOfShape J (↑f).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : SemilatticeSu
p β] [SupHomClass…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
-/
instance preservesColimitsOfShape_toFunctor [sSupHomClass F α β] {J : Type w} [Category.{w'} J] :
    PreservesColimitsOfShape J (toOrderHom f).toFunctor where
/-
**CategoryTheory.Limits.CompleteLattice.preservesColimitsOfSize_toFunctor** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_3 : sSupHomCla
ss F α β],   CategoryTheory.Limits.PreservesColimitsOfSize.{w', w, u, v, u, v} (
↑f).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : SemilatticeSu
p β] [SupHomClass…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.preservesColimitsOfShape_toFunctor
`：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) [ins
t_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_…
-/
instance preservesColimitsOfSize_toFunctor [sSupHomClass F α β] :
    PreservesColimitsOfSize.{w', w} (toOrderHom f).toFunctor where
/-
**CategoryTheory.Limits.CompleteLattice.preservesColimits_toFunctor** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.CompleteLattice`。
形式化陈述：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) 
[inst_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_3 : sSupHomCla
ss F α β], CategoryTheory.Limits.PreservesColimits (↑f).toFunctor
参数：f : F；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.toOrderHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : FunLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : SemilatticeSu
p β] [SupHomClass…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `sSupHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : CompleteLa
ttice β] [sSupHomCl…
· 使用定理 `CategoryTheory.Limits.CompleteLattice.preservesColimitsOfShape_toFunctor
`：∀ {α : Type u} {β : Type v} {F : Type u_1} [inst : FunLike F α β] (f : F) [ins
t_1 : CompleteLattice α]   [inst_2 : CompleteLattice β] [inst_…
-/
instance preservesColimits_toFunctor [sSupHomClass F α β] :
    PreservesColimits (toOrderHom f).toFunctor where

end

end CategoryTheory.Limits.CompleteLattice

