/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Preservation of filtered colimits and cofiltered limits.

Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits). See e.g. `Mathlib/Algebra/Category/MonCat/FilteredColimits.lean`.

Note also that using the results in the file `Mathlib/CategoryTheory/Presentable/Directed.lean`,
in order to show that a functor preserves filtered colimits, it would be
sufficient to check that it preserves colimits indexed by nonempty directed
types.

-/

public section


open CategoryTheory

open CategoryTheory.Functor

namespace CategoryTheory.Limits

universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

section FilteredColimits

section Preserves

-- This should be used with explicit universe variables.
/-- `PreservesFilteredColimitsOfSize.{w', w} F` means that `F` sends all colimit cocones over any
filtered diagram `J ⥤ C` to colimit cocones, where `J : Type w` with `[Category.{w'} J]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes in
-- `PreservesFilteredColimitsOfSize`, `ReflectsFilteredColimitsOfSize`,
-- `PreservesCofilteredLimitsOfSize`, and `ReflectsCofilteredLimitsOfSize` would default to
-- universe output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.PreservesFilteredColimitsOfSize** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class PreservesFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  preserves_filtered_colimits :
    ∀ (J : Type w) [Category.{w'} J] [IsFiltered J], PreservesColimitsOfShape J F

/--
A functor is said to preserve filtered colimits, if it preserves all colimits of shape `J`, where
`J` is a filtered category which is small relative to the universe in which morphisms of the source
live.
-/
/-
**CategoryTheory.Limits.PreservesFilteredColimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：PreservesFilteredColimits (F : C ⥤ D) : Prop
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to preserve filtered colimits, if it preserves all colimits of
 shape `J`, where
`J` is a filtered category which is small relative to the universe in which morp
hisms of the source
live.
-/
abbrev PreservesFilteredColimits (F : C ⥤ D) : Prop :=
  PreservesFilteredColimitsOfSize.{v₂, v₂} F

attribute [instance 100] PreservesFilteredColimitsOfSize.preserves_filtered_colimits
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PreservesColimits.preservesFilteredColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w'} F] : PreservesFilteredColimitsOfSize.{w, w'} F where
  preserves_filtered_colimits _ := inferInstance
/-
**CategoryTheory.Limits.comp_preservesFilteredColimits** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：comp_preservesFilteredColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFilteredC
olimitsOfSize.{w, w'} F] [PreservesFilteredColimitsOfSize.{w, w'} G] : Preserves
FilteredColimitsOfSize.{w, w'} (F ⋙ G) where preserves_filtered_colimits _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance comp_preservesFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFilteredColimitsOfSize.{w, w'} F] [PreservesFilteredColimitsOfSize.{w, w'} G] :
      PreservesFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_filtered_colimits _ := inferInstance

/-- A functor preserving larger filtered colimits also preserves smaller filtered colimits. -/
/-
**CategoryTheory.Limits.preservesFilteredColimitsOfSize_of_univLE** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [Un
ivLE.{w₂, w₂'}] [PreservesFilteredColimitsOfSize.{w', w₂'} F] : PreservesFiltere
dColimitsOfSize.{w, w₂} F where preserves_filtered_colimits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A functor preserving larger filtered colimits also preserves smaller filtered co
limits.
-/
lemma preservesFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesFilteredColimitsOfSize.{w', w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w₂} F where
  preserves_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact preservesColimitsOfShape_of_equiv e F

/--
`PreservesFilteredColimitsOfSize_shrink.{w, w'} F` tries to obtain
`PreservesFilteredColimitsOfSize.{w, w'} F` from some other `PreservesFilteredColimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFilteredColimitsOfSize_shrink (F : C ⥤ D) [PreservesFilteredColim
itsOfSize.{max w w₂, max w' w₂'} F] : PreservesFilteredColimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFilteredColimitsOfSize_of_univLE`：preserv
esFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'
}] [PreservesFilteredColimitsOfSize.{w', w₂'} F] : Pr…

--- 原说明 ---
`PreservesFilteredColimitsOfSize_shrink.{w, w'} F` tries to obtain
`PreservesFilteredColimitsOfSize.{w, w'} F` from some other `PreservesFilteredCo
limitsOfSize F`.
-/
lemma preservesFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w'} F :=
  preservesFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Preserving filtered colimits at any universe implies preserving filtered colimits at universe `0`.
-/
/-
**CategoryTheory.Limits.preservesSmallestFilteredColimits_of_preservesFilteredCo
limits** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesSmallestFilteredColimits_of_preservesFilteredColimits (F : C ⥤ D)
 [PreservesFilteredColimitsOfSize.{w', w} F] : PreservesFilteredColimitsOfSize.{
0, 0} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink`：preservesF
ilteredColimitsOfSize_shrink (F : C ⥤ D) [PreservesFilteredColimitsOfSize.{max w
 w₂, max w' w₂'} F] : PreservesFilteredColimitsOfS…

--- 原说明 ---
Preserving filtered colimits at any universe implies preserving filtered colimit
s at universe `0`.
-/
lemma preservesSmallestFilteredColimits_of_preservesFilteredColimits (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w', w} F] : PreservesFilteredColimitsOfSize.{0, 0} F :=
  preservesFilteredColimitsOfSize_shrink F

end Preserves

section Reflects

-- This should be used with explicit universe variables.
/-- `ReflectsFilteredColimitsOfSize.{w', w} F` means that whenever the image of a filtered cocone
under `F` is a colimit cocone, the original cocone was already a colimit. -/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.ReflectsFilteredColimitsOfSize** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ReflectsFilteredColimitsOfSize.{w', w} F` means that whenever the image of a fi
ltered cocone
under `F` is a colimit cocone, the original cocone was already a colimit.
-/
class ReflectsFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  reflects_filtered_colimits :
    ∀ (J : Type w) [Category.{w'} J] [IsFiltered J], ReflectsColimitsOfShape J F

/--
A functor is said to reflect filtered colimits, if it reflects all colimits of shape `J`, where
`J` is a filtered category which is small relative to the universe in which morphisms of the source
live.
-/
/-
**CategoryTheory.Limits.ReflectsFilteredColimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：ReflectsFilteredColimits (F : C ⥤ D) : Prop
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to reflect filtered colimits, if it reflects all colimits of s
hape `J`, where
`J` is a filtered category which is small relative to the universe in which morp
hisms of the source
live.
-/
abbrev ReflectsFilteredColimits (F : C ⥤ D) : Prop :=
  ReflectsFilteredColimitsOfSize.{v₂, v₂} F

attribute [instance 100] ReflectsFilteredColimitsOfSize.reflects_filtered_colimits
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ReflectsColimits.reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsColimitsOfSize.{w, w'} F] : ReflectsFilteredColimitsOfSize.{w, w'} F where
  reflects_filtered_colimits _ := inferInstance
/-
**CategoryTheory.Limits.comp_reflectsFilteredColimits** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：comp_reflectsFilteredColimits (F : C ⥤ D) (G : D ⥤ E) [ReflectsFilteredCol
imitsOfSize.{w, w'} F] [ReflectsFilteredColimitsOfSize.{w, w'} G] : ReflectsFilt
eredColimitsOfSize.{w, w'} (F ⋙ G) where reflects_filtered_colimits _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_reflectsColimitsOfShape`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsFilteredColimitsOfSize.reflects_filtered_c
olimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u
₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance comp_reflectsFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFilteredColimitsOfSize.{w, w'} F] [ReflectsFilteredColimitsOfSize.{w, w'} G] :
      ReflectsFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_filtered_colimits _ := inferInstance

/-- A functor reflecting larger filtered colimits also reflects smaller filtered colimits. -/
/-
**CategoryTheory.Limits.reflectsFilteredColimitsOfSize_of_univLE** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [Uni
vLE.{w₂, w₂'}] [ReflectsFilteredColimitsOfSize.{w', w₂'} F] : ReflectsFilteredCo
limitsOfSize.{w, w₂} F where reflects_filtered_colimits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv`：reflectsColimits
OfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Re
flectsColimitsOfShape J F] : ReflectsColimit…
· 使用定理 `CategoryTheory.Limits.ReflectsFilteredColimitsOfSize.reflects_filtered_c
olimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u
₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A functor reflecting larger filtered colimits also reflects smaller filtered col
imits.
-/
lemma reflectsFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsFilteredColimitsOfSize.{w', w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w₂} F where
  reflects_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact reflectsColimitsOfShape_of_equiv e F

/--
`ReflectsFilteredColimitsOfSize_shrink.{w, w'} F` tries to obtain
`ReflectsFilteredColimitsOfSize.{w, w'} F` from some other `ReflectsFilteredColimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.reflectsFilteredColimitsOfSize_shrink** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFilteredColimitsOfSize_shrink (F : C ⥤ D) [ReflectsFilteredColimit
sOfSize.{max w w₂, max w' w₂'} F] : ReflectsFilteredColimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsFilteredColimitsOfSize_of_univLE`：reflects
FilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
 [ReflectsFilteredColimitsOfSize.{w', w₂'} F] : Refl…

--- 原说明 ---
`ReflectsFilteredColimitsOfSize_shrink.{w, w'} F` tries to obtain
`ReflectsFilteredColimitsOfSize.{w, w'} F` from some other `ReflectsFilteredColi
mitsOfSize F`.
-/
lemma reflectsFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w'} F :=
  reflectsFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Reflecting filtered colimits at any universe implies reflecting filtered colimits at universe `0`.
-/
/-
**CategoryTheory.Limits.reflectsSmallestFilteredColimits_of_reflectsFilteredColi
mits** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (F : C ⥤ D) [
ReflectsFilteredColimitsOfSize.{w', w} F] : ReflectsFilteredColimitsOfSize.{0, 0
} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsFilteredColimitsOfSize_shrink`：reflectsFil
teredColimitsOfSize_shrink (F : C ⥤ D) [ReflectsFilteredColimitsOfSize.{max w w₂
, max w' w₂'} F] : ReflectsFilteredColimitsOfSize…

--- 原说明 ---
Reflecting filtered colimits at any universe implies reflecting filtered colimit
s at universe `0`.
-/
lemma reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{w', w} F] : ReflectsFilteredColimitsOfSize.{0, 0} F :=
  reflectsFilteredColimitsOfSize_shrink F

end Reflects

end FilteredColimits

section CofilteredLimits

section Preserves

-- This should be used with explicit universe variables.
/-- `PreservesCofilteredLimitsOfSize.{w', w} F` means that `F` sends all limit cones over any
cofiltered diagram `J ⥤ C` to limit cones, where `J : Type w` with `[Category.{w'} J]`. -/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.PreservesCofilteredLimitsOfSize** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PreservesCofilteredLimitsOfSize.{w', w} F` means that `F` sends all limit cones
 over any
cofiltered diagram `J ⥤ C` to limit cones, where `J : Type w` with `[Category.{w
'} J]`.
-/
class PreservesCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  preserves_cofiltered_limits :
    ∀ (J : Type w) [Category.{w'} J] [IsCofiltered J], PreservesLimitsOfShape J F

/--
A functor is said to preserve cofiltered limits, if it preserves all limits of shape `J`, where
`J` is a cofiltered category which is small relative to the universe in which morphisms of the
source live.
-/
/-
**CategoryTheory.Limits.PreservesCofilteredLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：PreservesCofilteredLimits (F : C ⥤ D) : Prop
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to preserve cofiltered limits, if it preserves all limits of s
hape `J`, where
`J` is a cofiltered category which is small relative to the universe in which mo
rphisms of the
source live.
-/
abbrev PreservesCofilteredLimits (F : C ⥤ D) : Prop :=
  PreservesCofilteredLimitsOfSize.{v₂, v₂} F

attribute [instance 100] PreservesCofilteredLimitsOfSize.preserves_cofiltered_limits
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PreservesLimits.preservesCofilteredLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w'} F] : PreservesCofilteredLimitsOfSize.{w, w'} F where
  preserves_cofiltered_limits _ := inferInstance
/-
**CategoryTheory.Limits.comp_preservesCofilteredLimits** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：comp_preservesCofilteredLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesCofiltere
dLimitsOfSize.{w, w'} F] [PreservesCofilteredLimitsOfSize.{w, w'} G] : Preserves
CofilteredLimitsOfSize.{w, w'} (F ⋙ G) where preserves_cofiltered_limits _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesCofilteredLimitsOfSize.preserves_cofilter
ed_limits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance comp_preservesCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesCofilteredLimitsOfSize.{w, w'} F] [PreservesCofilteredLimitsOfSize.{w, w'} G] :
      PreservesCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_cofiltered_limits _ := inferInstance

/-- A functor preserving larger cofiltered limits also preserves smaller cofiltered limits. -/
/-
**CategoryTheory.Limits.preservesCofilteredLimitsOfSize_of_univLE** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [Un
ivLE.{w₂, w₂'}] [PreservesCofilteredLimitsOfSize.{w', w₂'} F] : PreservesCofilte
redLimitsOfSize.{w, w₂} F where preserves_cofiltered_limits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.Limits.PreservesCofilteredLimitsOfSize.preserves_cofilter
ed_limits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A functor preserving larger cofiltered limits also preserves smaller cofiltered 
limits.
-/
lemma preservesCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesCofilteredLimitsOfSize.{w', w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w₂} F where
  preserves_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact preservesLimitsOfShape_of_equiv e F

/--
`PreservesCofilteredLimitsOfSizeShrink.{w, w'} F` tries to obtain
`PreservesCofilteredLimitsOfSize.{w, w'} F` from some other `PreservesCofilteredLimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.preservesCofilteredLimitsOfSize_shrink** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesCofilteredLimitsOfSize_shrink (F : C ⥤ D) [PreservesCofilteredLim
itsOfSize.{max w w₂, max w' w₂'} F] : PreservesCofilteredLimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesCofilteredLimitsOfSize_of_univLE`：preserv
esCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'
}] [PreservesCofilteredLimitsOfSize.{w', w₂'} F] : Pr…

--- 原说明 ---
`PreservesCofilteredLimitsOfSizeShrink.{w, w'} F` tries to obtain
`PreservesCofilteredLimitsOfSize.{w, w'} F` from some other `PreservesCofiltered
LimitsOfSize F`.
-/
lemma preservesCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w'} F :=
  preservesCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Preserving cofiltered limits at any universe implies preserving cofiltered limits at universe `0`.
-/
/-
**CategoryTheory.Limits.preservesSmallestCofilteredLimits_of_preservesCofiltered
Limits** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesSmallestCofilteredLimits_of_preservesCofilteredLimits (F : C ⥤ D)
 [PreservesCofilteredLimitsOfSize.{w', w} F] : PreservesCofilteredLimitsOfSize.{
0, 0} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesCofilteredLimitsOfSize_shrink`：preservesC
ofilteredLimitsOfSize_shrink (F : C ⥤ D) [PreservesCofilteredLimitsOfSize.{max w
 w₂, max w' w₂'} F] : PreservesCofilteredLimitsOfS…

--- 原说明 ---
Preserving cofiltered limits at any universe implies preserving cofiltered limit
s at universe `0`.
-/
lemma preservesSmallestCofilteredLimits_of_preservesCofilteredLimits (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{w', w} F] : PreservesCofilteredLimitsOfSize.{0, 0} F :=
  preservesCofilteredLimitsOfSize_shrink F

end Preserves

section Reflects

-- This should be used with explicit universe variables.
/-- `ReflectsCofilteredLimitsOfSize.{w', w} F` means that whenever the image of a cofiltered cone
under `F` is a limit cone, the original cone was already a limit. -/
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Limits.ReflectsCofilteredLimitsOfSize** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ReflectsCofilteredLimitsOfSize.{w', w} F` means that whenever the image of a co
filtered cone
under `F` is a limit cone, the original cone was already a limit.
-/
class ReflectsCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  reflects_cofiltered_limits :
    ∀ (J : Type w) [Category.{w'} J] [IsCofiltered J], ReflectsLimitsOfShape J F

/--
A functor is said to reflect cofiltered limits, if it reflects all limits of shape `J`, where
`J` is a cofiltered category which is small relative to the universe in which morphisms of the
source live.
-/
/-
**CategoryTheory.Limits.ReflectsCofilteredLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：ReflectsCofilteredLimits (F : C ⥤ D) : Prop
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to reflect cofiltered limits, if it reflects all limits of sha
pe `J`, where
`J` is a cofiltered category which is small relative to the universe in which mo
rphisms of the
source live.
-/
abbrev ReflectsCofilteredLimits (F : C ⥤ D) : Prop :=
  ReflectsCofilteredLimitsOfSize.{v₂, v₂} F

attribute [instance 100] ReflectsCofilteredLimitsOfSize.reflects_cofiltered_limits
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ReflectsLimits.reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsLimitsOfSize.{w, w'} F] : ReflectsCofilteredLimitsOfSize.{w, w'} F where
  reflects_cofiltered_limits _ := inferInstance
/-
**CategoryTheory.Limits.comp_reflectsCofilteredLimits** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：comp_reflectsCofilteredLimits (F : C ⥤ D) (G : D ⥤ E) [ReflectsCofilteredL
imitsOfSize.{w, w'} F] [ReflectsCofilteredLimitsOfSize.{w, w'} G] : ReflectsCofi
lteredLimitsOfSize.{w, w'} (F ⋙ G) where reflects_cofiltered_limits _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_reflectsLimitsOfShape`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.ReflectsCofilteredLimitsOfSize.reflects_cofiltered
_limits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u
₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance comp_reflectsCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsCofilteredLimitsOfSize.{w, w'} F] [ReflectsCofilteredLimitsOfSize.{w, w'} G] :
      ReflectsCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_cofiltered_limits _ := inferInstance

/-- A functor reflecting larger cofiltered limits also reflects smaller cofiltered limits. -/
/-
**CategoryTheory.Limits.reflectsCofilteredLimitsOfSize_of_univLE** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [Uni
vLE.{w₂, w₂'}] [ReflectsCofilteredLimitsOfSize.{w', w₂'} F] : ReflectsCofiltered
LimitsOfSize.{w, w₂} F where reflects_cofiltered_limits J _ _
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsCofiltered.of_equivalence`：of_equivalence (h : C ≌ D) :
 IsCofiltered D
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv`：reflectsLimitsOfSh
ape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Reflec
tsLimitsOfShape J F] : ReflectsLimitsOfSha…
· 使用定理 `CategoryTheory.Limits.ReflectsCofilteredLimitsOfSize.reflects_cofiltered
_limits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u
₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
A functor reflecting larger cofiltered limits also reflects smaller cofiltered l
imits.
-/
lemma reflectsCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsCofilteredLimitsOfSize.{w', w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w₂} F where
  reflects_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact reflectsLimitsOfShape_of_equiv e F

/--
`ReflectsCofilteredLimitsOfSize_shrink.{w, w'} F` tries to obtain
`ReflectsCofilteredLimitsOfSize.{w, w'} F` from some other `ReflectsCofilteredLimitsOfSize F`.
-/
/-
**CategoryTheory.Limits.reflectsCofilteredLimitsOfSize_shrink** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsCofilteredLimitsOfSize_shrink (F : C ⥤ D) [ReflectsCofilteredLimit
sOfSize.{max w w₂, max w' w₂'} F] : ReflectsCofilteredLimitsOfSize.{w, w'} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsCofilteredLimitsOfSize_of_univLE`：reflects
CofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
 [ReflectsCofilteredLimitsOfSize.{w', w₂'} F] : Refl…

--- 原说明 ---
`ReflectsCofilteredLimitsOfSize_shrink.{w, w'} F` tries to obtain
`ReflectsCofilteredLimitsOfSize.{w, w'} F` from some other `ReflectsCofilteredLi
mitsOfSize F`.
-/
lemma reflectsCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w'} F :=
  reflectsCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
Reflecting cofiltered limits at any universe implies reflecting cofiltered limits at universe `0`.
-/
/-
**CategoryTheory.Limits.reflectsSmallestCofilteredLimits_of_reflectsCofilteredLi
mits** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits (F : C ⥤ D) [
ReflectsCofilteredLimitsOfSize.{w', w} F] : ReflectsCofilteredLimitsOfSize.{0, 0
} F
参数：F : C ⥤ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsCofilteredLimitsOfSize_shrink`：reflectsCof
ilteredLimitsOfSize_shrink (F : C ⥤ D) [ReflectsCofilteredLimitsOfSize.{max w w₂
, max w' w₂'} F] : ReflectsCofilteredLimitsOfSize…

--- 原说明 ---
Reflecting cofiltered limits at any universe implies reflecting cofiltered limit
s at universe `0`.
-/
lemma reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{w', w} F] : ReflectsCofilteredLimitsOfSize.{0, 0} F :=
  reflectsCofilteredLimitsOfSize_shrink F

end Reflects

end CofilteredLimits

end CategoryTheory.Limits

