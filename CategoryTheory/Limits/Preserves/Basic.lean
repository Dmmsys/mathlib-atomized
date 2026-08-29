/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C ⥤ D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/

@[expose] public section


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category theory universes].
universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/--
Definition of `PreservesLimit` / `PreservesLimit` 的定义

English:
class PreservesLimit
  parameters: (K : J ⥤ C) (F : C ⥤ D)
  axioms and operations (1):
    - preserves({c : Cone K} (hc : IsLimit c)) : Nonempty (IsLimit (F.mapCone c))

中文:
类 保持极限
  参数: (K : J ⥤ C) (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves({c : 锥 K} (hc : 是极限 c)) : 非空 (是极限 (F.mapCone c))

Depends on / 依赖: hom_ext, isTerminalUnit, isTerminalUnit.hom_ext
-/
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cone K} (hc : IsLimit c) : Nonempty (IsLimit (F.mapCone c))

/--
Definition of `PreservesColimit` / `PreservesColimit` 的定义

English:
class PreservesColimit
  parameters: (K : J ⥤ C) (F : C ⥤ D)
  axioms and operations (1):
    - preserves({c : Cocone K} (hc : IsColimit c)) : Nonempty (IsColimit (F.mapCocone c))

中文:
类 保持余极限
  参数: (K : J ⥤ C) (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves({c : 余锥 K} (hc : 是余极限 c)) : 非空 (是余极限 (F.mapCocone c))

Depends on / 依赖: IsIso.hom_inv_id, MonoidalCategory, MonoidalCategory.tensorHom_comp_tensorHom, cat_disch, copy_comp_natural, hom_inv_id, infer_instance, tensorHom_comp_tensorHom
-/
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cocone K} (hc : IsColimit c) : Nonempty (IsColimit (F.mapCocone c))

/--
Definition of `PreservesLimitsOfShape` / `PreservesLimitsOfShape` 的定义

English:
class PreservesLimitsOfShape
  parameters: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  axioms and operations (1):
    - preservesLimit : forall {K : J ⥤ C}, PreservesLimit K F  [default: by infer_instance]

中文:
类 保持形状极限
  参数: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  公理与运算 (1 个):
    - preservesLimit : 对任意 {K : J ⥤ C}, 保持极限 K F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesLimit : forall {K : J ⥤ C}, PreservesLimit K F := by infer_instance

/--
Definition of `PreservesColimitsOfShape` / `PreservesColimitsOfShape` 的定义

English:
class PreservesColimitsOfShape
  parameters: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  axioms and operations (1):
    - preservesColimit : forall {K : J ⥤ C}, PreservesColimit K F  [default: by infer_instance]

中文:
类 保持形状余极限
  参数: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  公理与运算 (1 个):
    - preservesColimit : 对任意 {K : J ⥤ C}, 保持余极限 K F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesColimit : forall {K : J ⥤ C}, PreservesColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- `PreservesLimitsOfSize.{v u} F` means that `F` sends all limit cones over any
diagram `J ⥤ C` to limit cones, where `J : Type u` with `[Category.{v} J]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `w, w'` in
-- `PreservesLimitsOfSize`, `PreservesColimitsOfSize`, `ReflectsLimitsOfSize`, and
-- `ReflectsColimitsOfSize` would default to universe output parameters.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/--
Definition of `PreservesLimitsOfSize` / `PreservesLimitsOfSize` 的定义

English:
class PreservesLimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preservesLimitsOfShape : forall {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F  [default: by infer_instance]

中文:
类 保持LimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preservesLimitsOfShape : 对任意 {J : 类型 w} [范畴.{w'} J], 保持形状极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesLimitsOfSize (F : C ⥤ D) : Prop where
  preservesLimitsOfShape : forall {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F := by
    infer_instance

/--
Definition of `PreservesLimits` / `PreservesLimits` 的定义

English:
abbreviation PreservesLimits
  signature: (F : C ⥤ D)
  body: PreservesLimitsOfSize.{v₂, v₂} F

中文:
缩写 PreservesLimits
  签名: (F : C ⥤ D)
  定义体: PreservesLimitsOfSize.{v₂, v₂} F

Depends on / 依赖: PreservesLimitsOfSize
-/
abbrev PreservesLimits (F : C ⥤ D) :=
  PreservesLimitsOfSize.{v₂, v₂} F

-- This should be used with explicit universe variables.
/-- `PreservesColimitsOfSize.{v u} F` means that `F` sends all colimit cocones over any
diagram `J ⥤ C` to colimit cocones, where `J : Type u` with `[Category.{v} J]`. -/
@[univ_out_params, pp_with_univ]
/--
Definition of `PreservesColimitsOfSize` / `PreservesColimitsOfSize` 的定义

English:
class PreservesColimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preservesColimitsOfShape : forall {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F  [default: by infer_instance]

中文:
类 保持余limitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preservesColimitsOfShape : 对任意 {J : 类型 w} [范畴.{w'} J], 保持形状余极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesColimitsOfSize (F : C ⥤ D) : Prop where
  preservesColimitsOfShape : forall {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F := by
    infer_instance

/--
Definition of `PreservesColimits` / `PreservesColimits` 的定义

English:
abbreviation PreservesColimits
  signature: (F : C ⥤ D)
  body: PreservesColimitsOfSize.{v₂, v₂} F

中文:
缩写 PreservesColimits
  签名: (F : C ⥤ D)
  定义体: PreservesColimitsOfSize.{v₂, v₂} F

Depends on / 依赖: PreservesColimitsOfSize
-/
abbrev PreservesColimits (F : C ⥤ D) :=
  PreservesColimitsOfSize.{v₂, v₂} F

-- see Note [lower instance priority]
attribute [instance 100]
  PreservesLimitsOfShape.preservesLimit PreservesLimitsOfSize.preservesLimitsOfShape
  PreservesColimitsOfShape.preservesColimit
  PreservesColimitsOfSize.preservesColimitsOfShape

-- see Note [lower instance priority]
/--
Definition of `isLimitOfPreserves` / `isLimitOfPreserves` 的定义

English:
definition isLimitOfPreserves
  signature: (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F]
  body: (PreservesLimit.preserves t).some

中文:
定义 isLimitOfPreserves
  签名: (F : C ⥤ D) {c : 锥 K} (t : 是极限 c) [保持极限 K F]
  定义体: (PreservesLimit.preserves t).some

Depends on / 依赖: PreservesLimit, PreservesLimit.preserves, preserves
-/
def isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F] :
    IsLimit (F.mapCone c) :=
  (PreservesLimit.preserves t).some

/--
Definition of `isColimitOfPreserves` / `isColimitOfPreserves` 的定义

English:
definition isColimitOfPreserves
  signature: (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [PreservesColimit K F]
  body: (PreservesColimit.preserves t).some

中文:
定义 isColimitOfPreserves
  签名: (F : C ⥤ D) {c : 余锥 K} (t : 是余极限 c) [保持余极限 K F]
  定义体: (PreservesColimit.preserves t).some

Depends on / 依赖: PreservesColimit, PreservesColimit.preserves, preserves
-/
def isColimitOfPreserves (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [PreservesColimit K F] :
    IsColimit (F.mapCocone c) :=
  (PreservesColimit.preserves t).some

/--
Instance `preservesLimit_subsingleton` / 实例 `preservesLimit_subsingleton`

English:
instance preservesLimit_subsingleton
  signature: (K : J ⥤ C) (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 preservesLimit_subsingleton
  签名: (K : J ⥤ C) (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance preservesLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `preservesColimit_subsingleton` / 实例 `preservesColimit_subsingleton`

English:
instance preservesColimit_subsingleton
  signature: (K : J ⥤ C) (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 preservesColimit_subsingleton
  签名: (K : J ⥤ C) (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance preservesColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (PreservesColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `preservesLimitsOfShape_subsingleton` / 实例 `preservesLimitsOfShape_subsingleton`

English:
instance preservesLimitsOfShape_subsingleton
  signature: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 preservesLimitsOfShape_subsingleton
  签名: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance preservesLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `preservesColimitsOfShape_subsingleton` / 实例 `preservesColimitsOfShape_subsingleton`

English:
instance preservesColimitsOfShape_subsingleton
  signature: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 preservesColimitsOfShape_subsingleton
  签名: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance preservesColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `preservesLimitsOfSize_subsingleton` / 实例 `preservesLimitsOfSize_subsingleton`

English:
instance preservesLimitsOfSize_subsingleton
  signature: (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 preservesLimitsOfSize_subsingleton
  签名: (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance preservesLimitsOfSize_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `preservesColimitsOfSize_subsingleton` / 实例 `preservesColimitsOfSize_subsingleton`

English:
instance preservesColimitsOfSize_subsingleton
  signature: (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 preservesColimitsOfSize_subsingleton
  签名: (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance preservesColimitsOfSize_subsingleton (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `id_preservesLimitsOfSize` / 实例 `id_preservesLimitsOfSize`

English:
instance id_preservesLimitsOfSize
  signature: : PreservesLimitsOfSize.{w', w} (𝟭 C) where
  body: {
      preservesLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases 

中文:
实例 id_preservesLimitsOfSize
  签名: : 保持LimitsOfSize.{w', w} (𝟭 C) where
  定义体: {
      preservesLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases 

Depends on / 依赖: h.fac, h.lift, h.uniq, naturality, preservesLimit, s.pt
-/
instance id_preservesLimitsOfSize : PreservesLimitsOfSize.{w', w} (𝟭 C) where
  preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

/--
Instance `id_preservesColimitsOfSize` / 实例 `id_preservesColimitsOfSize`

English:
instance id_preservesColimitsOfSize
  signature: : PreservesColimitsOfSize.{w', w} (𝟭 C) where
  body: {
      preservesColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcase

中文:
实例 id_preservesColimitsOfSize
  签名: : 保持余limitsOfSize.{w', w} (𝟭 C) where
  定义体: {
      preservesColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcase

Depends on / 依赖: Algebra, Iso.refl, Monad.Algebra.isoMk, X.assoc, X.unit, h.desc, h.fac, h.uniq, naturality, preservesColimit, s.pt
-/
instance id_preservesColimitsOfSize : PreservesColimitsOfSize.{w', w} (𝟭 C) where
  preservesColimitsOfShape {J} 𝒥 :=
    {
      preservesColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimit
  signature: K] {F
  body: ⟨_, isLimitOfPreserves F (limit.isLimit K)⟩

中文:
实例 [有极限
  签名: K] {F
  定义体: ⟨_, isLimitOfPreserves F (limit.isLimit K)⟩

Depends on / 依赖: isLimit, isLimitOfPreserves, limit.isLimit
-/
instance [HasLimit K] {F : C ⥤ D} [PreservesLimit K F] : HasLimit (K ⋙ F) where
  exists_limit := ⟨_, isLimitOfPreserves F (limit.isLimit K)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimit
  signature: K] {F
  body: ⟨_, isColimitOfPreserves F (colimit.isColimit K)⟩

中文:
实例 [有余极限
  签名: K] {F
  定义体: ⟨_, isColimitOfPreserves F (colimit.isColimit K)⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isColimitOfPreserves
-/
instance [HasColimit K] {F : C ⥤ D} [PreservesColimit K F] : HasColimit (K ⋙ F) where
  exists_colimit := ⟨_, isColimitOfPreserves F (colimit.isColimit K)⟩

/--
lemma `PreservesLimit.mk'` / 引理 `PreservesLimit.mk'`

English:
lemma PreservesLimit.mk'
  given: {F : C ⥤ D} (h : HasLimit K -> PreservesLimit K F)
  proof: (h ⟨_, hc⟩).preserves hc

中文:
引理 保持极限.mk'
  条件: {F : C ⥤ D} (h : 有极限 K -> 保持极限 K F)
  证明: (h ⟨_, hc⟩).preserves hc

Depends on / 依赖: preserves
-/
lemma PreservesLimit.mk' {F : C ⥤ D} (h : HasLimit K -> PreservesLimit K F) :
    PreservesLimit K F where
  preserves hc := (h ⟨_, hc⟩).preserves hc

/--
lemma `PreservesColimit.mk'` / 引理 `PreservesColimit.mk'`

English:
lemma PreservesColimit.mk'
  given: {F : C ⥤ D} (h : HasColimit K -> PreservesColimit K F)
  proof: (h ⟨_, hc⟩).preserves hc

中文:
引理 保持余极限.mk'
  条件: {F : C ⥤ D} (h : 有余极限 K -> 保持余极限 K F)
  证明: (h ⟨_, hc⟩).preserves hc

Depends on / 依赖: preserves
-/
lemma PreservesColimit.mk' {F : C ⥤ D} (h : HasColimit K -> PreservesColimit K F) :
    PreservesColimit K F where
  preserves hc := (h ⟨_, hc⟩).preserves hc

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

/--
Instance `comp_preservesLimit` / 实例 `comp_preservesLimit`

English:
instance comp_preservesLimit
  signature: [PreservesLimit K F] [PreservesLimit (K ⋙ F) G]
  body: ⟨isLimitOfPreserves G (isLimitOfPreserves F hc)⟩

中文:
实例 comp_preservesLimit
  签名: [保持极限 K F] [保持极限 (K ⋙ F) G]
  定义体: ⟨isLimitOfPreserves G (isLimitOfPreserves F hc)⟩

Depends on / 依赖: isLimitOfPreserves
-/
instance comp_preservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] :
    PreservesLimit K (F ⋙ G) where
  preserves hc := ⟨isLimitOfPreserves G (isLimitOfPreserves F hc)⟩

/--
Instance `comp_preservesLimitsOfShape` / 实例 `comp_preservesLimitsOfShape`

English:
instance comp_preservesLimitsOfShape
  signature: [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G]

中文:
实例 comp_preservesLimitsOfShape
  签名: [保持形状极限 J F] [保持形状极限 J G]

Depends on / 依赖: Coalgebra, Comonad, Comonad.Coalgebra.isoMk, Iso.refl, X.coassoc, X.counit, coassoc, counit
-/
instance comp_preservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) where

/--
Instance `comp_preservesLimits` / 实例 `comp_preservesLimits`

English:
instance comp_preservesLimits
  signature: [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G]

中文:
实例 comp_preservesLimits
  签名: [保持LimitsOfSize.{w', w} F] [保持LimitsOfSize.{w', w} G]
-/
instance comp_preservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) where

/--
Instance `comp_preservesColimit` / 实例 `comp_preservesColimit`

English:
instance comp_preservesColimit
  signature: [PreservesColimit K F] [PreservesColimit (K ⋙ F) G]
  body: ⟨isColimitOfPreserves G (isColimitOfPreserves F hc)⟩

中文:
实例 comp_preservesColimit
  签名: [保持余极限 K F] [保持余极限 (K ⋙ F) G]
  定义体: ⟨isColimitOfPreserves G (isColimitOfPreserves F hc)⟩

Depends on / 依赖: isColimitOfPreserves
-/
instance comp_preservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] :
    PreservesColimit K (F ⋙ G) where
  preserves hc := ⟨isColimitOfPreserves G (isColimitOfPreserves F hc)⟩

/--
Instance `comp_preservesColimitsOfShape` / 实例 `comp_preservesColimitsOfShape`

English:
instance comp_preservesColimitsOfShape
  signature: [PreservesColimitsOfShape J F]

中文:
实例 comp_preservesColimitsOfShape
  签名: [保持形状余极限 J F]

Depends on / 依赖: MonadicRightAdjoint, MonadicRightAdjoint.eqv
-/
instance comp_preservesColimitsOfShape [PreservesColimitsOfShape J F]
    [PreservesColimitsOfShape J G] : PreservesColimitsOfShape J (F ⋙ G) where

/--
Instance `comp_preservesColimits` / 实例 `comp_preservesColimits`

English:
instance comp_preservesColimits
  signature: [PreservesColimitsOfSize.{w', w} F]

中文:
实例 comp_preservesColimits
  签名: [保持余limitsOfSize.{w', w} F]

Depends on / 依赖: isRightAdjoint, monadicAdjunction
-/
instance comp_preservesColimits [PreservesColimitsOfSize.{w', w} F]
    [PreservesColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} (F ⋙ G) where

end

/--
lemma `preservesLimit_of_preserves_limit_cone` / 引理 `preservesLimit_of_preserves_limit_cone`

English:
lemma preservesLimit_of_preserves_limit_cone
  statement: {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
  proof: ⟨IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩

中文:
引理 preservesLimit_of_preserves_limit_cone
  结论: {F : C ⥤ D} {t : 锥 K} (h : 是极限 t)
  证明: ⟨IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩

Depends on / 依赖: Functor, Functor.mapIso, IsLimit, IsLimit.ofIsoLimit, IsLimit.uniqueUpToIso, T.free, mapIso, ofIsoLimit, uniqueUpToIso
-/
lemma preservesLimit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
    (hF : IsLimit (F.mapCone t)) : PreservesLimit K F where
  preserves h' := ⟨IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩

/--
lemma `preservesLimit_iff_isLimit_mapCone` / 引理 `preservesLimit_iff_isLimit_mapCone`

English:
lemma preservesLimit_iff_isLimit_mapCone
  given: {F : C ⥤ D} {t : Cone K} (h : IsLimit t)
  proof: ⟨fun _ => ⟨isLimitOfPreserves _ h⟩, fun h' => preservesLimit_of_preserves_limit_cone h h'.some⟩

中文:
引理 preservesLimit_iff_isLimit_mapCone
  条件: {F : C ⥤ D} {t : 锥 K} (h : 是极限 t)
  证明: ⟨fun _ => ⟨isLimitOfPreserves _ h⟩, fun h' => preservesLimit_of_preserves_limit_cone h h'.some⟩

Depends on / 依赖: isLimitOfPreserves, preservesLimit_of_preserves_limit_cone
-/
lemma preservesLimit_iff_isLimit_mapCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) :
    PreservesLimit K F ↔ Nonempty (IsLimit (F.mapCone t)) :=
  ⟨fun _ => ⟨isLimitOfPreserves _ h⟩, fun h' => preservesLimit_of_preserves_limit_cone h h'.some⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesLimit_of_iso_diagram` / 引理 `preservesLimit_of_iso_diagram`

English:
lemma preservesLimit_of_iso_diagram
  statement: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  proof: ⟨by
    apply IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsLimit.postcomposeInvEquiv h c).symm t
    apply IsLimit.ofIsoLimit (isLimitOfPreserves F this)
    exact Cone.ext (Iso.refl _)⟩

中文:
引理 preservesLimit_of_iso_diagram
  结论: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  证明: ⟨by
    apply IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsLimit.postcomposeInvEquiv h c).symm t
    apply IsLimit.ofIsoLimit (isLimitOfPreserves F this)
    exact Cone.ext (Iso.refl _)⟩

Depends on / 依赖: Cone.ext, Functor, Functor.isoWhiskerRight, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeInvEquiv, Iso.refl, isLimitOfPreserves, isoWhiskerRight, ofIsoLimit, postcomposeInvEquiv
-/
lemma preservesLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesLimit K₁ F] : PreservesLimit K₂ F where
  preserves {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsLimit.postcomposeInvEquiv h c).symm t
    apply IsLimit.ofIsoLimit (isLimitOfPreserves F this)
    exact Cone.ext (Iso.refl _)⟩

/--
lemma `preservesLimit_iff_of_iso_diagram` / 引理 `preservesLimit_iff_of_iso_diagram`

English:
lemma preservesLimit_iff_of_iso_diagram
  given: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  proof: ⟨fun _ => preservesLimit_of_iso_diagram _ h, fun _ => preservesLimit_of_iso_diagram _ h.symm⟩

中文:
引理 preservesLimit_iff_of_iso_diagram
  条件: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  证明: ⟨fun _ => preservesLimit_of_iso_diagram _ h, fun _ => preservesLimit_of_iso_diagram _ h.symm⟩

Depends on / 依赖: ComonadicLeftAdjoint, ComonadicLeftAdjoint.eqv, h.symm, preservesLimit_of_iso_diagram
-/
lemma preservesLimit_iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) :
    PreservesLimit K₁ F ↔ PreservesLimit K₂ F :=
  ⟨fun _ => preservesLimit_of_iso_diagram _ h, fun _ => preservesLimit_of_iso_diagram _ h.symm⟩

/--
lemma `preservesLimit_of_natIso` / 引理 `preservesLimit_of_natIso`

English:
lemma preservesLimit_of_natIso
  given: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F]
  proof: ⟨IsLimit.mapConeEquiv h (isLimitOfPreserves F t)⟩

中文:
引理 preservesLimit_of_natIso
  条件: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [保持极限 K F]
  证明: ⟨IsLimit.mapConeEquiv h (isLimitOfPreserves F t)⟩

Depends on / 依赖: IsLimit, IsLimit.mapConeEquiv, comonadicAdjunction, isLeftAdjoint, isLimitOfPreserves, mapConeEquiv
-/
lemma preservesLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] :
    PreservesLimit K G where
  preserves t := ⟨IsLimit.mapConeEquiv h (isLimitOfPreserves F t)⟩

/--
lemma `preservesLimit_iff_of_natIso` / 引理 `preservesLimit_iff_of_natIso`

English:
lemma preservesLimit_iff_of_natIso
  given: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G)
  proof: ⟨fun _ => preservesLimit_of_natIso _ h, fun _ => preservesLimit_of_natIso _ h.symm⟩

中文:
引理 preservesLimit_iff_of_natIso
  条件: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G)
  证明: ⟨fun _ => preservesLimit_of_natIso _ h, fun _ => preservesLimit_of_natIso _ h.symm⟩

Depends on / 依赖: G.cofree, cofree, h.symm, preservesLimit_of_natIso
-/
lemma preservesLimit_iff_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimit K F ↔ PreservesLimit K G :=
  ⟨fun _ => preservesLimit_of_natIso _ h, fun _ => preservesLimit_of_natIso _ h.symm⟩

/--
lemma `preservesLimitsOfShape_of_natIso` / 引理 `preservesLimitsOfShape_of_natIso`

English:
lemma preservesLimitsOfShape_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F]
  proof: preservesLimit_of_natIso K h

中文:
引理 preservesLimitsOfShape_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [保持形状极限 J F]
  证明: preservesLimit_of_natIso K h

Depends on / 依赖: preservesLimit_of_natIso
-/
lemma preservesLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := preservesLimit_of_natIso K h

/--
lemma `preservesLimitsOfShape_iff_of_natIso` / 引理 `preservesLimitsOfShape_iff_of_natIso`

English:
lemma preservesLimitsOfShape_iff_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G)
  proof: ⟨fun _ => preservesLimitsOfShape_of_natIso h, fun _ => preservesLimitsOfShape_of_natIso h.symm⟩

中文:
引理 preservesLimitsOfShape_iff_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G)
  证明: ⟨fun _ => preservesLimitsOfShape_of_natIso h, fun _ => preservesLimitsOfShape_of_natIso h.symm⟩

Depends on / 依赖: h.symm, preservesLimitsOfShape_of_natIso
-/
lemma preservesLimitsOfShape_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimitsOfShape J F ↔ PreservesLimitsOfShape J G :=
  ⟨fun _ => preservesLimitsOfShape_of_natIso h, fun _ => preservesLimitsOfShape_of_natIso h.symm⟩

/--
lemma `preservesLimits_of_natIso` / 引理 `preservesLimits_of_natIso`

English:
lemma preservesLimits_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F]
  proof: preservesLimitsOfShape_of_natIso h

中文:
引理 preservesLimits_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [保持LimitsOfSize.{w, w'} F]
  证明: preservesLimitsOfShape_of_natIso h

Depends on / 依赖: preservesLimitsOfShape_of_natIso
-/
lemma preservesLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G where
  preservesLimitsOfShape := preservesLimitsOfShape_of_natIso h

/--
lemma `preservesLimitsOfSize_iff_of_natIso` / 引理 `preservesLimitsOfSize_iff_of_natIso`

English:
lemma preservesLimitsOfSize_iff_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G)
  proof: ⟨fun _ => preservesLimits_of_natIso h, fun _ => preservesLimits_of_natIso h.symm⟩

中文:
引理 preservesLimitsOfSize_iff_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G)
  证明: ⟨fun _ => preservesLimits_of_natIso h, fun _ => preservesLimits_of_natIso h.symm⟩

Depends on / 依赖: h.symm, preservesLimits_of_natIso
-/
lemma preservesLimitsOfSize_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesLimitsOfSize.{w, w'} F ↔ PreservesLimitsOfSize.{w, w'} G :=
  ⟨fun _ => preservesLimits_of_natIso h, fun _ => preservesLimits_of_natIso h.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesLimitsOfShape_of_equiv` / 引理 `preservesLimitsOfShape_of_equiv`

English:
lemma preservesLimitsOfShape_of_equiv
  statement: {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  proof: { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isLimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsLimit.postcomposeHomEquiv equ _).symm this).ofIsoLimit
        refine Cone.ext (Iso.refl _) fun j => ?_
        simp 

中文:
引理 preservesLimitsOfShape_of_equiv
  结论: {J' : 类型 w₂} [范畴.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  证明: { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isLimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsLimit.postcomposeHomEquiv equ _).symm this).ofIsoLimit
        refine Cone.ext (Iso.refl _) fun j => ?_
        simp 

Depends on / 依赖: Cone.ext, Functor, Functor.map_comp, IsLimit, IsLimit.postcomposeHomEquiv, Iso.refl, e.invFunIdAssoc, e.symm, invFunIdAssoc, isLimitOfPreserves, map_comp, ofIsoLimit, postcomposeHomEquiv, preserves, t.whiskerEquivalence, whiskerEquivalence
-/
lemma preservesLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F where
  preservesLimit {K} :=
    { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isLimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsLimit.postcomposeHomEquiv equ _).symm this).ofIsoLimit
        refine Cone.ext (Iso.refl _) fun j => ?_
        simp [equ, ← Functor.map_comp]⟩ }

/--
lemma `preservesLimitsOfSize_of_univLE` / 引理 `preservesLimitsOfSize_of_univLE`

English:
lemma preservesLimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  proof: preservesLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

中文:
引理 preservesLimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  证明: preservesLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

Depends on / 依赖: preservesLimitsOfShape_of_equiv
-/
lemma preservesLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesLimitsOfSize.{w', w₂'} F] : PreservesLimitsOfSize.{w, w₂} F where
  preservesLimitsOfShape {J} := preservesLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/--
lemma `preservesLimitsOfSize_shrink` / 引理 `preservesLimitsOfSize_shrink`

English:
lemma preservesLimitsOfSize_shrink
  given: (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F]
  proof: preservesLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 preservesLimitsOfSize_shrink
  条件: (F : C ⥤ D) [保持LimitsOfSize.{最大值 w w₂, 最大值 w' w₂'} F]
  证明: preservesLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: preservesLimitsOfSize_of_univLE
-/
lemma preservesLimitsOfSize_shrink (F : C ⥤ D) [PreservesLimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesLimitsOfSize.{w, w'} F := preservesLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `preservesSmallestLimits_of_preservesLimits` / 引理 `preservesSmallestLimits_of_preservesLimits`

English:
lemma preservesSmallestLimits_of_preservesLimits
  given: (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F]
  proof: preservesLimitsOfSize_shrink F

中文:
引理 preservesSmallestLimits_of_preservesLimits
  条件: (F : C ⥤ D) [保持LimitsOfSize.{v₃, u₃} F]
  证明: preservesLimitsOfSize_shrink F

Depends on / 依赖: preservesLimitsOfSize_shrink
-/
lemma preservesSmallestLimits_of_preservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃} F] :
    PreservesLimitsOfSize.{0, 0} F :=
  preservesLimitsOfSize_shrink F

/--
lemma `preservesColimit_of_preserves_colimit_cocone` / 引理 `preservesColimit_of_preserves_colimit_cocone`

English:
lemma preservesColimit_of_preserves_colimit_cocone
  statement: {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
  proof: ⟨fun h' => ⟨IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩⟩

中文:
引理 preservesColimit_of_preserves_colimit_cocone
  结论: {F : C ⥤ D} {t : 余锥 K} (h : 是余极限 t)
  证明: ⟨fun h' => ⟨IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩⟩

Depends on / 依赖: Functor, Functor.mapIso, IsColimit, IsColimit.ofIsoColimit, IsColimit.uniqueUpToIso, Reflective, mapIso, monadicOfReflective, ofIsoColimit, uniqueUpToIso
-/
lemma preservesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
    (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F :=
  ⟨fun h' => ⟨IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩⟩

/--
lemma `preservesColimit_iff_isColimit_mapCocone` / 引理 `preservesColimit_iff_isColimit_mapCocone`

English:
lemma preservesColimit_iff_isColimit_mapCocone
  given: {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
  proof: ⟨fun _ => ⟨isColimitOfPreserves _ h⟩,
    fun h' => preservesColimit_of_preserves_colimit_cocone h h'.some⟩

中文:
引理 preservesColimit_iff_isColimit_mapCocone
  条件: {F : C ⥤ D} {t : 余锥 K} (h : 是余极限 t)
  证明: ⟨fun _ => ⟨isColimitOfPreserves _ h⟩,
    fun h' => preservesColimit_of_preserves_colimit_cocone h h'.some⟩

Depends on / 依赖: Coreflective, comonadicOfCoreflective, isColimitOfPreserves, preservesColimit_of_preserves_colimit_cocone
-/
lemma preservesColimit_iff_isColimit_mapCocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t) :
    PreservesColimit K F ↔ Nonempty (IsColimit (F.mapCocone t)) :=
  ⟨fun _ => ⟨isColimitOfPreserves _ h⟩,
    fun h' => preservesColimit_of_preserves_colimit_cocone h h'.some⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesColimit_of_iso_diagram` / 引理 `preservesColimit_of_iso_diagram`

English:
lemma preservesColimit_of_iso_diagram
  statement: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  proof: ⟨by
    apply IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsColimit.precomposeHomEquiv h c).symm t
    apply IsColimit.ofIsoColimit (isColimitOfPreserves F this)
    exact Cocone.ext (Iso.refl _)⟩

中文:
引理 preservesColimit_of_iso_diagram
  结论: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  证明: ⟨by
    apply IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsColimit.precomposeHomEquiv h c).symm t
    apply IsColimit.ofIsoColimit (isColimitOfPreserves F this)
    exact Cocone.ext (Iso.refl _)⟩

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.isoWhiskerRight, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, isColimitOfPreserves, isoWhiskerRight, ofIsoColimit, precomposeHomEquiv
-/
lemma preservesColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [PreservesColimit K₁ F] :
    PreservesColimit K₂ F where
  preserves {c} t := ⟨by
    apply IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _ _
    have := (IsColimit.precomposeHomEquiv h c).symm t
    apply IsColimit.ofIsoColimit (isColimitOfPreserves F this)
    exact Cocone.ext (Iso.refl _)⟩

/--
lemma `preservesColimit_iff_of_iso_diagram` / 引理 `preservesColimit_iff_of_iso_diagram`

English:
lemma preservesColimit_iff_of_iso_diagram
  given: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  proof: ⟨fun _ => preservesColimit_of_iso_diagram _ h, fun _ => preservesColimit_of_iso_diagram _ h.symm⟩

中文:
引理 preservesColimit_iff_of_iso_diagram
  条件: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  证明: ⟨fun _ => preservesColimit_of_iso_diagram _ h, fun _ => preservesColimit_of_iso_diagram _ h.symm⟩

Depends on / 依赖: h.symm, preservesColimit_of_iso_diagram
-/
lemma preservesColimit_iff_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) :
    PreservesColimit K₁ F ↔ PreservesColimit K₂ F :=
  ⟨fun _ => preservesColimit_of_iso_diagram _ h, fun _ => preservesColimit_of_iso_diagram _ h.symm⟩

/--
lemma `preservesColimit_of_natIso` / 引理 `preservesColimit_of_natIso`

English:
lemma preservesColimit_of_natIso
  given: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F]
  proof: ⟨IsColimit.mapCoconeEquiv h (isColimitOfPreserves F t)⟩

中文:
引理 preservesColimit_of_natIso
  条件: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [保持余极限 K F]
  证明: ⟨IsColimit.mapCoconeEquiv h (isColimitOfPreserves F t)⟩

Depends on / 依赖: IsColimit, IsColimit.mapCoconeEquiv, isColimitOfPreserves, mapCoconeEquiv
-/
lemma preservesColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] :
    PreservesColimit K G where
  preserves t := ⟨IsColimit.mapCoconeEquiv h (isColimitOfPreserves F t)⟩

/--
lemma `preservesColimit_iff_of_natIso` / 引理 `preservesColimit_iff_of_natIso`

English:
lemma preservesColimit_iff_of_natIso
  given: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G)
  proof: ⟨fun _ => preservesColimit_of_natIso _ h, fun _ => preservesColimit_of_natIso _ h.symm⟩

中文:
引理 preservesColimit_iff_of_natIso
  条件: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G)
  证明: ⟨fun _ => preservesColimit_of_natIso _ h, fun _ => preservesColimit_of_natIso _ h.symm⟩

Depends on / 依赖: h.symm, preservesColimit_of_natIso
-/
lemma preservesColimit_iff_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) :
    PreservesColimit K F ↔ PreservesColimit K G :=
  ⟨fun _ => preservesColimit_of_natIso _ h, fun _ => preservesColimit_of_natIso _ h.symm⟩

/--
lemma `preservesColimitsOfShape_of_natIso` / 引理 `preservesColimitsOfShape_of_natIso`

English:
lemma preservesColimitsOfShape_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F]
  proof: preservesColimit_of_natIso K h

中文:
引理 preservesColimitsOfShape_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [保持形状余极限 J F]
  证明: preservesColimit_of_natIso K h

Depends on / 依赖: preservesColimit_of_natIso
-/
lemma preservesColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := preservesColimit_of_natIso K h

/--
lemma `preservesColimitsOfShape_iff_of_natIso` / 引理 `preservesColimitsOfShape_iff_of_natIso`

English:
lemma preservesColimitsOfShape_iff_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G)
  proof: ⟨fun _ => preservesColimitsOfShape_of_natIso h, fun _ => preservesColimitsOfShape_of_natIso h.symm⟩

中文:
引理 preservesColimitsOfShape_iff_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G)
  证明: ⟨fun _ => preservesColimitsOfShape_of_natIso h, fun _ => preservesColimitsOfShape_of_natIso h.symm⟩

Depends on / 依赖: h.symm, preservesColimitsOfShape_of_natIso
-/
lemma preservesColimitsOfShape_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesColimitsOfShape J F ↔ PreservesColimitsOfShape J G :=
  ⟨fun _ => preservesColimitsOfShape_of_natIso h, fun _ => preservesColimitsOfShape_of_natIso h.symm⟩

/--
lemma `preservesColimits_of_natIso` / 引理 `preservesColimits_of_natIso`

English:
lemma preservesColimits_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F]
  proof: preservesColimitsOfShape_of_natIso h

中文:
引理 preservesColimits_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [保持余limitsOfSize.{w, w'} F]
  证明: preservesColimitsOfShape_of_natIso h

Depends on / 依赖: preservesColimitsOfShape_of_natIso
-/
lemma preservesColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} G where
  preservesColimitsOfShape {_J} _𝒥₁ := preservesColimitsOfShape_of_natIso h

/--
lemma `preservesColimitsOfSize_iff_of_natIso` / 引理 `preservesColimitsOfSize_iff_of_natIso`

English:
lemma preservesColimitsOfSize_iff_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G)
  proof: ⟨fun _ => preservesColimits_of_natIso h, fun _ => preservesColimits_of_natIso h.symm⟩

中文:
引理 preservesColimitsOfSize_iff_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G)
  证明: ⟨fun _ => preservesColimits_of_natIso h, fun _ => preservesColimits_of_natIso h.symm⟩

Depends on / 依赖: h.symm, preservesColimits_of_natIso
-/
lemma preservesColimitsOfSize_iff_of_natIso {F G : C ⥤ D} (h : F ≅ G) :
    PreservesColimitsOfSize.{w, w'} F ↔ PreservesColimitsOfSize.{w, w'} G :=
  ⟨fun _ => preservesColimits_of_natIso h, fun _ => preservesColimits_of_natIso h.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `preservesColimitsOfShape_of_equiv` / 引理 `preservesColimitsOfShape_of_equiv`

English:
lemma preservesColimitsOfShape_of_equiv
  statement: {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  proof: { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isColimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsColimit.precomposeInvEquiv equ _).symm this).ofIsoColimit
        refine Cocone.ext (Iso.refl _) fun j => ?_
      

中文:
引理 preservesColimitsOfShape_of_equiv
  结论: {J' : 类型 w₂} [范畴.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  证明: { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isColimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsColimit.precomposeInvEquiv equ _).symm this).ofIsoColimit
        refine Cocone.ext (Iso.refl _) fun j => ?_
      

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.map_comp, IsColimit, IsColimit.precomposeInvEquiv, Iso.refl, e.invFunIdAssoc, e.symm, invFunIdAssoc, isColimitOfPreserves, map_comp, ofIsoColimit, precomposeInvEquiv, preserves, t.whiskerEquivalence, whiskerEquivalence
-/
lemma preservesColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J' F where
  preservesColimit {K} :=
    { preserves := fun {c} t => ⟨by
        let equ := e.invFunIdAssoc (K ⋙ F)
        have := (isColimitOfPreserves F (t.whiskerEquivalence e)).whiskerEquivalence e.symm
        apply ((IsColimit.precomposeInvEquiv equ _).symm this).ofIsoColimit
        refine Cocone.ext (Iso.refl _) fun j => ?_
        simp [equ, ← Functor.map_comp]⟩ }

/--
lemma `preservesColimitsOfSize_of_univLE` / 引理 `preservesColimitsOfSize_of_univLE`

English:
lemma preservesColimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  proof: preservesColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

中文:
引理 preservesColimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  证明: preservesColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

Depends on / 依赖: preservesColimitsOfShape_of_equiv
-/
lemma preservesColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [PreservesColimitsOfSize.{w', w₂'} F] : PreservesColimitsOfSize.{w, w₂} F where
  preservesColimitsOfShape {J} := preservesColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/--
lemma `preservesColimitsOfSize_shrink` / 引理 `preservesColimitsOfSize_shrink`

English:
lemma preservesColimitsOfSize_shrink
  statement: (F : C ⥤ D)
  proof: preservesColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 preservesColimitsOfSize_shrink
  结论: (F : C ⥤ D)
  证明: preservesColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: preservesColimitsOfSize_of_univLE
-/
lemma preservesColimitsOfSize_shrink (F : C ⥤ D)
    [PreservesColimitsOfSize.{max w w₂, max w' w₂'} F] :
    PreservesColimitsOfSize.{w, w'} F := preservesColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `preservesSmallestColimits_of_preservesColimits` / 引理 `preservesSmallestColimits_of_preservesColimits`

English:
lemma preservesSmallestColimits_of_preservesColimits
  statement: (F : C ⥤ D)
  proof: preservesColimitsOfSize_shrink F

中文:
引理 preservesSmallestColimits_of_preservesColimits
  结论: (F : C ⥤ D)
  证明: preservesColimitsOfSize_shrink F

Depends on / 依赖: preservesColimitsOfSize_shrink
-/
lemma preservesSmallestColimits_of_preservesColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{v₃, u₃} F] :
    PreservesColimitsOfSize.{0, 0} F :=
  preservesColimitsOfSize_shrink F

/--
Definition of `ReflectsLimit` / `ReflectsLimit` 的定义

English:
class ReflectsLimit
  parameters: (K : J ⥤ C) (F : C ⥤ D)
  axioms and operations (1):
    - reflects({c : Cone K} (hc : IsLimit (F.mapCone c))) : Nonempty (IsLimit c)

中文:
类 反映极限
  参数: (K : J ⥤ C) (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects({c : 锥 K} (hc : 是极限 (F.mapCone c))) : 非空 (是极限 c)
-/
class ReflectsLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects {c : Cone K} (hc : IsLimit (F.mapCone c)) : Nonempty (IsLimit c)

/--
Definition of `ReflectsColimit` / `ReflectsColimit` 的定义

English:
class ReflectsColimit
  parameters: (K : J ⥤ C) (F : C ⥤ D)
  axioms and operations (1):
    - reflects({c : Cocone K} (hc : IsColimit (F.mapCocone c))) : Nonempty (IsColimit c)

中文:
类 反映余极限
  参数: (K : J ⥤ C) (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects({c : 余锥 K} (hc : 是余极限 (F.mapCocone c))) : 非空 (是余极限 c)
-/
class ReflectsColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects {c : Cocone K} (hc : IsColimit (F.mapCocone c)) : Nonempty (IsColimit c)

/--
Definition of `ReflectsLimitsOfShape` / `ReflectsLimitsOfShape` 的定义

English:
class ReflectsLimitsOfShape
  parameters: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  axioms and operations (1):
    - reflectsLimit : forall {K : J ⥤ C}, ReflectsLimit K F  [default: by infer_instance]

中文:
类 反映形状极限
  参数: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  公理与运算 (1 个):
    - reflectsLimit : 对任意 {K : J ⥤ C}, 反映极限 K F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class ReflectsLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  reflectsLimit : forall {K : J ⥤ C}, ReflectsLimit K F := by infer_instance

/--
Definition of `ReflectsColimitsOfShape` / `ReflectsColimitsOfShape` 的定义

English:
class ReflectsColimitsOfShape
  parameters: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  axioms and operations (1):
    - reflectsColimit : forall {K : J ⥤ C}, ReflectsColimit K F  [default: by infer_instance]

中文:
类 反映形状余极限
  参数: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  公理与运算 (1 个):
    - reflectsColimit : 对任意 {K : J ⥤ C}, 反映余极限 K F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  reflectsColimit : forall {K : J ⥤ C}, ReflectsColimit K F := by infer_instance

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
@[univ_out_params, pp_with_univ]
/--
Definition of `ReflectsLimitsOfSize` / `ReflectsLimitsOfSize` 的定义

English:
class ReflectsLimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflectsLimitsOfShape : forall {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F  [default: by infer_instance]

中文:
类 ReflectsLimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflectsLimitsOfShape : 对任意 {J : 类型 w} [范畴.{w'} J], 反映形状极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class ReflectsLimitsOfSize (F : C ⥤ D) : Prop where
  reflectsLimitsOfShape : forall {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F := by
    infer_instance

/--
Definition of `ReflectsLimits` / `ReflectsLimits` 的定义

English:
abbreviation ReflectsLimits
  signature: (F : C ⥤ D)
  body: ReflectsLimitsOfSize.{v₂, v₂} F

中文:
缩写 ReflectsLimits
  签名: (F : C ⥤ D)
  定义体: ReflectsLimitsOfSize.{v₂, v₂} F

Depends on / 依赖: ReflectsLimitsOfSize
-/
abbrev ReflectsLimits (F : C ⥤ D) :=
  ReflectsLimitsOfSize.{v₂, v₂} F

-- This should be used with explicit universe variables.
/-- A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
@[univ_out_params, pp_with_univ]
/--
Definition of `ReflectsColimitsOfSize` / `ReflectsColimitsOfSize` 的定义

English:
class ReflectsColimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflectsColimitsOfShape : forall {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F  [default: by infer_instance]

中文:
类 ReflectsColimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflectsColimitsOfShape : 对任意 {J : 类型 w} [范畴.{w'} J], 反映形状余极限 J F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class ReflectsColimitsOfSize (F : C ⥤ D) : Prop where
  reflectsColimitsOfShape : forall {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F := by
    infer_instance

/--
Definition of `ReflectsColimits` / `ReflectsColimits` 的定义

English:
abbreviation ReflectsColimits
  signature: (F : C ⥤ D)
  body: ReflectsColimitsOfSize.{v₂, v₂} F

中文:
缩写 ReflectsColimits
  签名: (F : C ⥤ D)
  定义体: ReflectsColimitsOfSize.{v₂, v₂} F

Depends on / 依赖: ReflectsColimitsOfSize
-/
abbrev ReflectsColimits (F : C ⥤ D) :=
  ReflectsColimitsOfSize.{v₂, v₂} F

/--
Definition of `isLimitOfReflects` / `isLimitOfReflects` 的定义

English:
definition isLimitOfReflects
  signature: (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c))
  body: (ReflectsLimit.reflects t).some

中文:
定义 isLimitOfReflects
  签名: (F : C ⥤ D) {c : 锥 K} (t : 是极限 (F.mapCone c))
  定义体: (ReflectsLimit.reflects t).some

Depends on / 依赖: ReflectsLimit, ReflectsLimit.reflects, reflects
-/
def isLimitOfReflects (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c))
    [ReflectsLimit K F] : IsLimit c :=
  (ReflectsLimit.reflects t).some

/--
Definition of `isColimitOfReflects` / `isColimitOfReflects` 的定义

English:
definition isColimitOfReflects
  signature: (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone c))
  body: (ReflectsColimit.reflects t).some

中文:
定义 isColimitOfReflects
  签名: (F : C ⥤ D) {c : 余锥 K} (t : 是余极限 (F.mapCocone c))
  定义体: (ReflectsColimit.reflects t).some

Depends on / 依赖: ReflectsColimit, ReflectsColimit.reflects, reflects
-/
def isColimitOfReflects (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone c))
    [ReflectsColimit K F] : IsColimit c :=
  (ReflectsColimit.reflects t).some

/--
Instance `reflectsLimit_subsingleton` / 实例 `reflectsLimit_subsingleton`

English:
instance reflectsLimit_subsingleton
  signature: (K : J ⥤ C) (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 reflectsLimit_subsingleton
  签名: (K : J ⥤ C) (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance reflectsLimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsLimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `reflectsColimit_subsingleton` / 实例 `reflectsColimit_subsingleton`

English:
instance reflectsColimit_subsingleton
  signature: (K : J ⥤ C) (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 reflectsColimit_subsingleton
  签名: (K : J ⥤ C) (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance reflectsColimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) :
    Subsingleton (ReflectsColimit K F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `reflectsLimitsOfShape_subsingleton` / 实例 `reflectsLimitsOfShape_subsingleton`

English:
instance reflectsLimitsOfShape_subsingleton
  signature: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 reflectsLimitsOfShape_subsingleton
  签名: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance reflectsLimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `reflectsColimitsOfShape_subsingleton` / 实例 `reflectsColimitsOfShape_subsingleton`

English:
instance reflectsColimitsOfShape_subsingleton
  signature: (J : Type w) [Category.{w'} J] (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 reflectsColimitsOfShape_subsingleton
  签名: (J : 类型 w) [范畴.{w'} J] (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance reflectsColimitsOfShape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfShape J F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `reflects_limits_subsingleton` / 实例 `reflects_limits_subsingleton`

English:
instance reflects_limits_subsingleton
  signature: (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 reflects_limits_subsingleton
  签名: (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance reflects_limits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

/--
Instance `reflects_colimits_subsingleton` / 实例 `reflects_colimits_subsingleton`

English:
instance reflects_colimits_subsingleton
  signature: (F : C ⥤ D)
  body: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

中文:
实例 reflects_colimits_subsingleton
  签名: (F : C ⥤ D)
  定义体: by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!
-/
instance reflects_colimits_subsingleton (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfSize.{w', w} F) := by
  constructor; rintro ⟨a⟩ ⟨b⟩; congr!

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimit_of_reflectsLimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimit K F :=
  ReflectsLimitsOfShape.reflectsLimit

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimit_of_reflectsColimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimit K F :=
  ReflectsColimitsOfShape.reflectsColimit

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitsOfShape_of_reflectsLimits (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w', w} F] : ReflectsLimitsOfShape J F :=
  ReflectsLimitsOfSize.reflectsLimitsOfShape

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitsOfShape_of_reflectsColimits
    (J : Type w) [Category.{w'} J]
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w', w} F] : ReflectsColimitsOfShape J F :=
  ReflectsColimitsOfSize.reflectsColimitsOfShape

/--
Instance `id_reflectsLimits` / 实例 `id_reflectsLimits`

English:
instance id_reflectsLimits
  signature: : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  body: { reflectsLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with 

中文:
实例 id_reflectsLimits
  签名: : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  定义体: { reflectsLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with 

Depends on / 依赖: h.fac, h.lift, h.uniq, naturality, reflectsLimit, s.pt
-/
instance id_reflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  reflectsLimitsOfShape {J} 𝒥 :=
    { reflectsLimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.lift ⟨s.pt, fun j => s.π.app j, fun _ _ f => s.π.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

/--
Instance `id_reflectsColimits` / 实例 `id_reflectsColimits`

English:
instance id_reflectsColimits
  signature: : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where
  body: { reflectsColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s wit

中文:
实例 id_reflectsColimits
  签名: : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where
  定义体: { reflectsColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s wit

Depends on / 依赖: h.desc, h.fac, h.uniq, naturality, reflectsColimit, s.pt
-/
instance id_reflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where
  reflectsColimitsOfShape {J} 𝒥 :=
    { reflectsColimit := fun {K} =>
        ⟨fun {c} h =>
          ⟨fun s => h.desc ⟨s.pt, fun j => s.ι.app j, fun _ _ f => s.ι.naturality f⟩, by
            cases K; rcases c with ⟨_, _, _⟩; intro s j; cases s; exact h.fac _ j, by
            cases K; rcases c with ⟨_, _, _⟩; intro s m w; rcases s with ⟨_, _, _⟩;
              exact h.uniq _ m w⟩⟩ }

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)

/--
Instance `comp_reflectsLimit` / 实例 `comp_reflectsLimit`

English:
instance comp_reflectsLimit
  signature: [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G]
  body: ⟨fun h => ReflectsLimit.reflects (isLimitOfReflects G h)⟩

中文:
实例 comp_reflectsLimit
  签名: [反映极限 K F] [反映极限 (K ⋙ F) G]
  定义体: ⟨fun h => ReflectsLimit.reflects (isLimitOfReflects G h)⟩

Depends on / 依赖: ReflectsLimit, ReflectsLimit.reflects, isLimitOfReflects, reflects
-/
instance comp_reflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] :
    ReflectsLimit K (F ⋙ G) :=
  ⟨fun h => ReflectsLimit.reflects (isLimitOfReflects G h)⟩

/--
Instance `comp_reflectsLimitsOfShape` / 实例 `comp_reflectsLimitsOfShape`

English:
instance comp_reflectsLimitsOfShape
  signature: [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G]

中文:
实例 comp_reflectsLimitsOfShape
  签名: [反映形状极限 J F] [反映形状极限 J G]
-/
instance comp_reflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) where

/--
Instance `comp_reflectsLimits` / 实例 `comp_reflectsLimits`

English:
instance comp_reflectsLimits
  signature: [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G]

中文:
实例 comp_reflectsLimits
  签名: [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G]

Depends on / 依赖: Hom.ext
-/
instance comp_reflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) where

/--
Instance `comp_reflectsColimit` / 实例 `comp_reflectsColimit`

English:
instance comp_reflectsColimit
  signature: [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G]
  body: ⟨fun h => ReflectsColimit.reflects (isColimitOfReflects G h)⟩

中文:
实例 comp_reflectsColimit
  签名: [反映余极限 K F] [反映余极限 (K ⋙ F) G]
  定义体: ⟨fun h => ReflectsColimit.reflects (isColimitOfReflects G h)⟩

Depends on / 依赖: ReflectsColimit, ReflectsColimit.reflects, isColimitOfReflects, reflects
-/
instance comp_reflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] :
    ReflectsColimit K (F ⋙ G) :=
  ⟨fun h => ReflectsColimit.reflects (isColimitOfReflects G h)⟩

/--
Instance `comp_reflectsColimitsOfShape` / 实例 `comp_reflectsColimitsOfShape`

English:
instance comp_reflectsColimitsOfShape
  signature: [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G]

中文:
实例 comp_reflectsColimitsOfShape
  签名: [反映形状余极限 J F] [反映形状余极限 J G]
-/
instance comp_reflectsColimitsOfShape [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G] :
    ReflectsColimitsOfShape J (F ⋙ G) where

/--
Instance `comp_reflectsColimits` / 实例 `comp_reflectsColimits`

English:
instance comp_reflectsColimits
  signature: [ReflectsColimitsOfSize.{w', w} F]

中文:
实例 comp_reflectsColimits
  签名: [ReflectsColimitsOfSize.{w', w} F]
-/
instance comp_reflectsColimits [ReflectsColimitsOfSize.{w', w} F]
    [ReflectsColimitsOfSize.{w', w} G] : ReflectsColimitsOfSize.{w', w} (F ⋙ G) where

/--
lemma `preservesLimit_of_reflects_of_preserves` / 引理 `preservesLimit_of_reflects_of_preserves`

English:
lemma preservesLimit_of_reflects_of_preserves
  given: [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G]
  proof: ⟨fun h => ⟨by
    apply isLimitOfReflects G
    apply isLimitOfPreserves (F ⋙ G) h⟩⟩

中文:
引理 preservesLimit_of_reflects_of_preserves
  条件: [保持极限 K (F ⋙ G)] [反映极限 (K ⋙ F) G]
  证明: ⟨fun h => ⟨by
    apply isLimitOfReflects G
    apply isLimitOfPreserves (F ⋙ G) h⟩⟩

Depends on / 依赖: isLimitOfPreserves, isLimitOfReflects
-/
lemma preservesLimit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] :
    PreservesLimit K F :=
  ⟨fun h => ⟨by
    apply isLimitOfReflects G
    apply isLimitOfPreserves (F ⋙ G) h⟩⟩

/--
lemma `preservesLimitsOfShape_of_reflects_of_preserves` / 引理 `preservesLimitsOfShape_of_reflects_of_preserves`

English:
lemma preservesLimitsOfShape_of_reflects_of_preserves
  statement: [PreservesLimitsOfShape J (F ⋙ G)]
  proof: preservesLimit_of_reflects_of_preserves F G

中文:
引理 preservesLimitsOfShape_of_reflects_of_preserves
  结论: [保持形状极限 J (F ⋙ G)]
  证明: preservesLimit_of_reflects_of_preserves F G

Depends on / 依赖: preservesLimit_of_reflects_of_preserves
-/
lemma preservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)]
    [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F where
  preservesLimit := preservesLimit_of_reflects_of_preserves F G

/--
lemma `preservesLimits_of_reflects_of_preserves` / 引理 `preservesLimits_of_reflects_of_preserves`

English:
lemma preservesLimits_of_reflects_of_preserves
  statement: [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
  proof: preservesLimitsOfShape_of_reflects_of_preserves F G

中文:
引理 preservesLimits_of_reflects_of_preserves
  结论: [保持LimitsOfSize.{w', w} (F ⋙ G)]
  证明: preservesLimitsOfShape_of_reflects_of_preserves F G

Depends on / 依赖: preservesLimitsOfShape_of_reflects_of_preserves
-/
lemma preservesLimits_of_reflects_of_preserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsLimitsOfSize.{w', w} G] : PreservesLimitsOfSize.{w', w} F where
  preservesLimitsOfShape := preservesLimitsOfShape_of_reflects_of_preserves F G

set_option backward.defeqAttrib.useBackward true in
/--
lemma `reflectsLimit_of_iso_diagram` / 引理 `reflectsLimit_of_iso_diagram`

English:
lemma reflectsLimit_of_iso_diagram
  given: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F]
  proof: ⟨by
    apply IsLimit.postcomposeInvEquiv h c (isLimitOfReflects F _)
    apply ((IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoLimit _
    exact Cone.ext (Iso.refl _)⟩

中文:
引理 reflectsLimit_of_iso_diagram
  条件: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [反映极限 K₁ F]
  证明: ⟨by
    apply IsLimit.postcomposeInvEquiv h c (isLimitOfReflects F _)
    apply ((IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoLimit _
    exact Cone.ext (Iso.refl _)⟩

Depends on / 依赖: Cone.ext, Functor, Functor.isoWhiskerRight, IsLimit, IsLimit.postcomposeInvEquiv, Iso.refl, isLimitOfReflects, isoWhiskerRight, ofIsoLimit, postcomposeInvEquiv
-/
lemma reflectsLimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] :
    ReflectsLimit K₂ F where
  reflects {c} t := ⟨by
    apply IsLimit.postcomposeInvEquiv h c (isLimitOfReflects F _)
    apply ((IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoLimit _
    exact Cone.ext (Iso.refl _)⟩

/--
lemma `reflectsLimit_of_natIso` / 引理 `reflectsLimit_of_natIso`

English:
lemma reflectsLimit_of_natIso
  given: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F]
  proof: ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

中文:
引理 reflectsLimit_of_natIso
  条件: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [反映极限 K F]
  证明: ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

Depends on / 依赖: IsLimit, IsLimit.mapConeEquiv, ReflectsLimit, ReflectsLimit.reflects, h.symm, mapConeEquiv, reflects
-/
lemma reflectsLimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] :
    ReflectsLimit K G where
  reflects t := ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

/--
lemma `reflectsLimitsOfShape_of_natIso` / 引理 `reflectsLimitsOfShape_of_natIso`

English:
lemma reflectsLimitsOfShape_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F]
  proof: reflectsLimit_of_natIso K h

中文:
引理 reflectsLimitsOfShape_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [反映形状极限 J F]
  证明: reflectsLimit_of_natIso K h

Depends on / 依赖: reflectsLimit_of_natIso
-/
lemma reflectsLimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G where
  reflectsLimit {K} := reflectsLimit_of_natIso K h

/--
lemma `reflectsLimits_of_natIso` / 引理 `reflectsLimits_of_natIso`

English:
lemma reflectsLimits_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F]
  proof: reflectsLimitsOfShape_of_natIso h

中文:
引理 reflectsLimits_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F]
  证明: reflectsLimitsOfShape_of_natIso h

Depends on / 依赖: reflectsLimitsOfShape_of_natIso
-/
lemma reflectsLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_natIso h

/--
lemma `reflectsLimitsOfShape_of_equiv` / 引理 `reflectsLimitsOfShape_of_equiv`

English:
lemma reflectsLimitsOfShape_of_equiv
  statement: {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  proof: { reflects := fun {c} t => ⟨by
        apply IsLimit.ofWhiskerEquivalence e
        apply isLimitOfReflects F
        apply IsLimit.ofIsoLimit _ (Functor.mapConeWhisker _).symm
        exact IsLimit.whiskerEquivalence t _⟩ }

中文:
引理 reflectsLimitsOfShape_of_equiv
  结论: {J' : 类型 w₂} [范畴.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  证明: { reflects := fun {c} t => ⟨by
        apply IsLimit.ofWhiskerEquivalence e
        apply isLimitOfReflects F
        apply IsLimit.ofIsoLimit _ (Functor.mapConeWhisker _).symm
        exact IsLimit.whiskerEquivalence t _⟩ }

Depends on / 依赖: Functor, Functor.mapConeWhisker, IsLimit, IsLimit.ofIsoLimit, IsLimit.ofWhiskerEquivalence, IsLimit.whiskerEquivalence, isLimitOfReflects, mapConeWhisker, ofIsoLimit, ofWhiskerEquivalence, reflects, whiskerEquivalence
-/
lemma reflectsLimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsLimitsOfShape J F] : ReflectsLimitsOfShape J' F where
  reflectsLimit {K} :=
    { reflects := fun {c} t => ⟨by
        apply IsLimit.ofWhiskerEquivalence e
        apply isLimitOfReflects F
        apply IsLimit.ofIsoLimit _ (Functor.mapConeWhisker _).symm
        exact IsLimit.whiskerEquivalence t _⟩ }

/--
lemma `reflectsLimitsOfSize_of_univLE` / 引理 `reflectsLimitsOfSize_of_univLE`

English:
lemma reflectsLimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  proof: reflectsLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

中文:
引理 reflectsLimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  证明: reflectsLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

Depends on / 依赖: reflectsLimitsOfShape_of_equiv
-/
lemma reflectsLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsLimitsOfSize.{w', w₂'} F] : ReflectsLimitsOfSize.{w, w₂} F where
  reflectsLimitsOfShape {J} := reflectsLimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/--
lemma `reflectsLimitsOfSize_shrink` / 引理 `reflectsLimitsOfSize_shrink`

English:
lemma reflectsLimitsOfSize_shrink
  given: (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F]
  proof: reflectsLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 reflectsLimitsOfSize_shrink
  条件: (F : C ⥤ D) [ReflectsLimitsOfSize.{最大值 w w₂, 最大值 w' w₂'} F]
  证明: reflectsLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: reflectsLimitsOfSize_of_univLE
-/
lemma reflectsLimitsOfSize_shrink (F : C ⥤ D) [ReflectsLimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsLimitsOfSize.{w, w'} F := reflectsLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `reflectsSmallestLimits_of_reflectsLimits` / 引理 `reflectsSmallestLimits_of_reflectsLimits`

English:
lemma reflectsSmallestLimits_of_reflectsLimits
  given: (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F]
  proof: reflectsLimitsOfSize_shrink F

中文:
引理 reflectsSmallestLimits_of_reflectsLimits
  条件: (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F]
  证明: reflectsLimitsOfSize_shrink F

Depends on / 依赖: reflectsLimitsOfSize_shrink
-/
lemma reflectsSmallestLimits_of_reflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
    ReflectsLimitsOfSize.{0, 0} F :=
  reflectsLimitsOfSize_shrink F

/-- If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F` (see also `JointlyReflectIsomorphisms.jointlyReflectsColimit` in
the file `CategoryTheory/Functor/ReflectsIso/Limits.lean` for the corresponding result
for a family of functors which joinly reflect isomorphisms).
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
/--
lemma `reflectsLimit_of_reflectsIsomorphisms` / 引理 `reflectsLimit_of_reflectsIsomorphisms`

English:
lemma reflectsLimit_of_reflectsIsomorphisms
  statement: (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
  proof: by
    suffices IsIso (IsLimit.lift (limit.isLimit F) c) from ⟨by
      apply IsLimit.ofPointIso (limit.isLimit F)⟩
    change IsIso ((Cone.forget _).map ((limit.isLimit F).liftConeMorphism c))
    suffices IsIso (IsLimit.liftConeMorphism (limit.isLimit F) c) from by
      apply (Cone.forget F).map_

中文:
引理 reflectsLimit_of_reflectsIsomorphisms
  结论: (F : J ⥤ C) (G : C ⥤ D) [G.反映同构]
  证明: by
    suffices IsIso (IsLimit.lift (limit.isLimit F) c) from ⟨by
      apply IsLimit.ofPointIso (limit.isLimit F)⟩
    change IsIso ((Cone.forget _).map ((limit.isLimit F).liftConeMorphism c))
    suffices IsIso (IsLimit.liftConeMorphism (limit.isLimit F) c) from by
      apply (Cone.forget F).map_

Depends on / 依赖: Cone.forget, Cone.functoriality, IsLimit, IsLimit.lift, IsLimit.liftConeMorphism, IsLimit.ofPointIso, forget, functoriality, hom_isIso, isIso_of_reflects_iso, isLimit, isLimitOfPreserves, liftConeMorphism, limit.isLimit, map_isIso, ofPointIso, t.hom_isIso
-/
lemma reflectsLimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasLimit F] [PreservesLimit F G] : ReflectsLimit F G where
  reflects {c} t := by
    suffices IsIso (IsLimit.lift (limit.isLimit F) c) from ⟨by
      apply IsLimit.ofPointIso (limit.isLimit F)⟩
    change IsIso ((Cone.forget _).map ((limit.isLimit F).liftConeMorphism c))
    suffices IsIso (IsLimit.liftConeMorphism (limit.isLimit F) c) from by
      apply (Cone.forget F).map_isIso _
    suffices IsIso ((Cone.functoriality F G).map
      (IsLimit.liftConeMorphism (limit.isLimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cone.functoriality F G)
    exact t.hom_isIso (isLimitOfPreserves G (limit.isLimit F)) _

/--
lemma `reflectsLimitsOfShape_of_reflectsIsomorphisms` / 引理 `reflectsLimitsOfShape_of_reflectsIsomorphisms`

English:
lemma reflectsLimitsOfShape_of_reflectsIsomorphisms
  statement: {G : C ⥤ D} [G.ReflectsIsomorphisms]
  proof: reflectsLimit_of_reflectsIsomorphisms F G

中文:
引理 reflectsLimitsOfShape_of_reflectsIsomorphisms
  结论: {G : C ⥤ D} [G.反映同构]
  证明: reflectsLimit_of_reflectsIsomorphisms F G

Depends on / 依赖: reflectsLimit_of_reflectsIsomorphisms
-/
lemma reflectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G where
  reflectsLimit {F} := reflectsLimit_of_reflectsIsomorphisms F G

/--
lemma `reflectsLimits_of_reflectsIsomorphisms` / 引理 `reflectsLimits_of_reflectsIsomorphisms`

English:
lemma reflectsLimits_of_reflectsIsomorphisms
  statement: {G : C ⥤ D} [G.ReflectsIsomorphisms]
  proof: reflectsLimitsOfShape_of_reflectsIsomorphisms

中文:
引理 reflectsLimits_of_reflectsIsomorphisms
  结论: {G : C ⥤ D} [G.反映同构]
  证明: reflectsLimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
lemma reflectsLimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasLimitsOfSize.{w', w} C] [PreservesLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} G where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_reflectsIsomorphisms

/--
lemma `preservesColimit_of_reflects_of_preserves` / 引理 `preservesColimit_of_reflects_of_preserves`

English:
lemma preservesColimit_of_reflects_of_preserves
  proof: ⟨fun {c} h => ⟨by
    apply isColimitOfReflects G
    apply isColimitOfPreserves (F ⋙ G) h⟩⟩

中文:
引理 preservesColimit_of_reflects_of_preserves
  证明: ⟨fun {c} h => ⟨by
    apply isColimitOfReflects G
    apply isColimitOfPreserves (F ⋙ G) h⟩⟩

Depends on / 依赖: isColimitOfPreserves, isColimitOfReflects
-/
lemma preservesColimit_of_reflects_of_preserves
    [PreservesColimit K (F ⋙ G)] [ReflectsColimit (K ⋙ F) G] :
    PreservesColimit K F :=
  ⟨fun {c} h => ⟨by
    apply isColimitOfReflects G
    apply isColimitOfPreserves (F ⋙ G) h⟩⟩

/--
lemma `preservesColimitsOfShape_of_reflects_of_preserves` / 引理 `preservesColimitsOfShape_of_reflects_of_preserves`

English:
lemma preservesColimitsOfShape_of_reflects_of_preserves
  statement: [PreservesColimitsOfShape J (F ⋙ G)]
  proof: preservesColimit_of_reflects_of_preserves F G

中文:
引理 preservesColimitsOfShape_of_reflects_of_preserves
  结论: [保持形状余极限 J (F ⋙ G)]
  证明: preservesColimit_of_reflects_of_preserves F G

Depends on / 依赖: preservesColimit_of_reflects_of_preserves
-/
lemma preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShape J (F ⋙ G)]
    [ReflectsColimitsOfShape J G] : PreservesColimitsOfShape J F where
  preservesColimit := preservesColimit_of_reflects_of_preserves F G

/--
lemma `preservesColimits_of_reflects_of_preserves` / 引理 `preservesColimits_of_reflects_of_preserves`

English:
lemma preservesColimits_of_reflects_of_preserves
  statement: [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
  proof: preservesColimitsOfShape_of_reflects_of_preserves F G

中文:
引理 preservesColimits_of_reflects_of_preserves
  结论: [保持余limitsOfSize.{w', w} (F ⋙ G)]
  证明: preservesColimitsOfShape_of_reflects_of_preserves F G

Depends on / 依赖: preservesColimitsOfShape_of_reflects_of_preserves
-/
lemma preservesColimits_of_reflects_of_preserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} F where
  preservesColimitsOfShape := preservesColimitsOfShape_of_reflects_of_preserves F G

set_option backward.defeqAttrib.useBackward true in
/--
lemma `reflectsColimit_of_iso_diagram` / 引理 `reflectsColimit_of_iso_diagram`

English:
lemma reflectsColimit_of_iso_diagram
  statement: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  proof: ⟨by
    apply IsColimit.precomposeHomEquiv h c (isColimitOfReflects F _)
    apply ((IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoColimit _
    exact Cocone.ext (Iso.refl _)⟩

中文:
引理 reflectsColimit_of_iso_diagram
  结论: {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
  证明: ⟨by
    apply IsColimit.precomposeHomEquiv h c (isColimitOfReflects F _)
    apply ((IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoColimit _
    exact Cocone.ext (Iso.refl _)⟩

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.isoWhiskerRight, IsColimit, IsColimit.precomposeHomEquiv, Iso.refl, isColimitOfReflects, isoWhiskerRight, ofIsoColimit, precomposeHomEquiv
-/
lemma reflectsColimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂)
    [ReflectsColimit K₁ F] :
    ReflectsColimit K₂ F where
  reflects {c} t := ⟨by
    apply IsColimit.precomposeHomEquiv h c (isColimitOfReflects F _)
    apply ((IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight h F :) _).symm t).ofIsoColimit _
    exact Cocone.ext (Iso.refl _)⟩

/--
lemma `reflectsColimit_of_natIso` / 引理 `reflectsColimit_of_natIso`

English:
lemma reflectsColimit_of_natIso
  given: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F]
  proof: ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)

中文:
引理 reflectsColimit_of_natIso
  条件: (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [反映余极限 K F]
  证明: ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)

Depends on / 依赖: IsColimit, IsColimit.mapCoconeEquiv, ReflectsColimit, ReflectsColimit.reflects, h.symm, mapCoconeEquiv, reflects
-/
lemma reflectsColimit_of_natIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] :
    ReflectsColimit K G where
  reflects t := ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)

/--
lemma `reflectsColimitsOfShape_of_natIso` / 引理 `reflectsColimitsOfShape_of_natIso`

English:
lemma reflectsColimitsOfShape_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F]
  proof: reflectsColimit_of_natIso K h

中文:
引理 reflectsColimitsOfShape_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [反映形状余极限 J F]
  证明: reflectsColimit_of_natIso K h

Depends on / 依赖: reflectsColimit_of_natIso
-/
lemma reflectsColimitsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] :
    ReflectsColimitsOfShape J G where
  reflectsColimit {K} := reflectsColimit_of_natIso K h

/--
lemma `reflectsColimits_of_natIso` / 引理 `reflectsColimits_of_natIso`

English:
lemma reflectsColimits_of_natIso
  given: {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F]
  proof: reflectsColimitsOfShape_of_natIso h

中文:
引理 reflectsColimits_of_natIso
  条件: {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F]
  证明: reflectsColimitsOfShape_of_natIso h

Depends on / 依赖: reflectsColimitsOfShape_of_natIso
-/
lemma reflectsColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} G where
  reflectsColimitsOfShape := reflectsColimitsOfShape_of_natIso h

/--
lemma `reflectsColimitsOfShape_of_equiv` / 引理 `reflectsColimitsOfShape_of_equiv`

English:
lemma reflectsColimitsOfShape_of_equiv
  statement: {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  proof: { reflects := fun {c} t => ⟨by
        apply IsColimit.ofWhiskerEquivalence e
        apply isColimitOfReflects F
        apply IsColimit.ofIsoColimit _ (Functor.mapCoconeWhisker _).symm
        exact IsColimit.whiskerEquivalence t _⟩ }

中文:
引理 reflectsColimitsOfShape_of_equiv
  结论: {J' : 类型 w₂} [范畴.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
  证明: { reflects := fun {c} t => ⟨by
        apply IsColimit.ofWhiskerEquivalence e
        apply isColimitOfReflects F
        apply IsColimit.ofIsoColimit _ (Functor.mapCoconeWhisker _).symm
        exact IsColimit.whiskerEquivalence t _⟩ }

Depends on / 依赖: Functor, Functor.mapCoconeWhisker, IsColimit, IsColimit.ofIsoColimit, IsColimit.ofWhiskerEquivalence, IsColimit.whiskerEquivalence, isColimitOfReflects, mapCoconeWhisker, ofIsoColimit, ofWhiskerEquivalence, reflects, whiskerEquivalence
-/
lemma reflectsColimitsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [ReflectsColimitsOfShape J F] : ReflectsColimitsOfShape J' F where
  reflectsColimit :=
    { reflects := fun {c} t => ⟨by
        apply IsColimit.ofWhiskerEquivalence e
        apply isColimitOfReflects F
        apply IsColimit.ofIsoColimit _ (Functor.mapCoconeWhisker _).symm
        exact IsColimit.whiskerEquivalence t _⟩ }

/--
lemma `reflectsColimitsOfSize_of_univLE` / 引理 `reflectsColimitsOfSize_of_univLE`

English:
lemma reflectsColimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  proof: reflectsColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

中文:
引理 reflectsColimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
  证明: reflectsColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

Depends on / 依赖: reflectsColimitsOfShape_of_equiv
-/
lemma reflectsColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}] [UnivLE.{w₂, w₂'}]
    [ReflectsColimitsOfSize.{w', w₂'} F] : ReflectsColimitsOfSize.{w, w₂} F where
  reflectsColimitsOfShape {J} := reflectsColimitsOfShape_of_equiv
    ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm F

/--
lemma `reflectsColimitsOfSize_shrink` / 引理 `reflectsColimitsOfSize_shrink`

English:
lemma reflectsColimitsOfSize_shrink
  given: (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F]
  proof: reflectsColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 reflectsColimitsOfSize_shrink
  条件: (F : C ⥤ D) [ReflectsColimitsOfSize.{最大值 w w₂, 最大值 w' w₂'} F]
  证明: reflectsColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: reflectsColimitsOfSize_of_univLE
-/
lemma reflectsColimitsOfSize_shrink (F : C ⥤ D) [ReflectsColimitsOfSize.{max w w₂, max w' w₂'} F] :
    ReflectsColimitsOfSize.{w, w'} F := reflectsColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `reflectsSmallestColimits_of_reflectsColimits` / 引理 `reflectsSmallestColimits_of_reflectsColimits`

English:
lemma reflectsSmallestColimits_of_reflectsColimits
  given: (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F]
  proof: reflectsColimitsOfSize_shrink F

中文:
引理 reflectsSmallestColimits_of_reflectsColimits
  条件: (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F]
  证明: reflectsColimitsOfSize_shrink F

Depends on / 依赖: reflectsColimitsOfSize_shrink
-/
lemma reflectsSmallestColimits_of_reflectsColimits (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃, u₃} F] :
    ReflectsColimitsOfSize.{0, 0} F :=
  reflectsColimitsOfSize_shrink F

/-- If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F` (see also `JointlyReflectIsomorphisms.jointlyReflectsLimit` in
the file `CategoryTheory/Functor/ReflectsIso/Limits.lean` for the corresponding result
for a family of functors which joinly reflect isomorphisms).
-/ -- Porting note: previous behavior of apply pushed instance holes into hypotheses, this errors
/--
lemma `reflectsColimit_of_reflectsIsomorphisms` / 引理 `reflectsColimit_of_reflectsIsomorphisms`

English:
lemma reflectsColimit_of_reflectsIsomorphisms
  statement: (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
  proof: by
    suffices IsIso (IsColimit.desc (colimit.isColimit F) c) from ⟨by
      apply IsColimit.ofPointIso (colimit.isColimit F)⟩
    change IsIso ((Cocone.forget _).map ((colimit.isColimit F).descCoconeMorphism c))
    suffices IsIso (IsColimit.descCoconeMorphism (colimit.isColimit F) c) from by
    

中文:
引理 reflectsColimit_of_reflectsIsomorphisms
  结论: (F : J ⥤ C) (G : C ⥤ D) [G.反映同构]
  证明: by
    suffices IsIso (IsColimit.desc (colimit.isColimit F) c) from ⟨by
      apply IsColimit.ofPointIso (colimit.isColimit F)⟩
    change IsIso ((Cocone.forget _).map ((colimit.isColimit F).descCoconeMorphism c))
    suffices IsIso (IsColimit.descCoconeMorphism (colimit.isColimit F) c) from by
    

Depends on / 依赖: Cocone, Cocone.forget, Cocone.functoriality, IsColimit, IsColimit.desc, IsColimit.descCoconeMorphism, IsColimit.ofPointIso, colimit, colimit.isColimit, descCoconeMorphism, forget, functoriality, isColimit, isColimitOf, isIso_of_reflects_iso, map_isIso, ofPointIso
-/
lemma reflectsColimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [HasColimit F] [PreservesColimit F G] : ReflectsColimit F G where
  reflects {c} t := by
    suffices IsIso (IsColimit.desc (colimit.isColimit F) c) from ⟨by
      apply IsColimit.ofPointIso (colimit.isColimit F)⟩
    change IsIso ((Cocone.forget _).map ((colimit.isColimit F).descCoconeMorphism c))
    suffices IsIso (IsColimit.descCoconeMorphism (colimit.isColimit F) c) from by
      apply (Cocone.forget F).map_isIso _
    suffices IsIso ((Cocone.functoriality F G).map
      (IsColimit.descCoconeMorphism (colimit.isColimit F) c)) from by
        apply isIso_of_reflects_iso _ (Cocone.functoriality F G)
    exact (isColimitOfPreserves G (colimit.isColimit F)).hom_isIso t _

/--
lemma `reflectsColimitsOfShape_of_reflectsIsomorphisms` / 引理 `reflectsColimitsOfShape_of_reflectsIsomorphisms`

English:
lemma reflectsColimitsOfShape_of_reflectsIsomorphisms
  statement: {G : C ⥤ D} [G.ReflectsIsomorphisms]
  proof: reflectsColimit_of_reflectsIsomorphisms F G

中文:
引理 reflectsColimitsOfShape_of_reflectsIsomorphisms
  结论: {G : C ⥤ D} [G.反映同构]
  证明: reflectsColimit_of_reflectsIsomorphisms F G

Depends on / 依赖: reflectsColimit_of_reflectsIsomorphisms
-/
lemma reflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfShape J C] [PreservesColimitsOfShape J G] : ReflectsColimitsOfShape J G where
  reflectsColimit {F} := reflectsColimit_of_reflectsIsomorphisms F G

/--
lemma `reflectsColimits_of_reflectsIsomorphisms` / 引理 `reflectsColimits_of_reflectsIsomorphisms`

English:
lemma reflectsColimits_of_reflectsIsomorphisms
  statement: {G : C ⥤ D} [G.ReflectsIsomorphisms]
  proof: reflectsColimitsOfShape_of_reflectsIsomorphisms

中文:
引理 reflectsColimits_of_reflectsIsomorphisms
  结论: {G : C ⥤ D} [G.反映同构]
  证明: reflectsColimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsColimitsOfShape_of_reflectsIsomorphisms
-/
lemma reflectsColimits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms]
    [HasColimitsOfSize.{w', w} C] [PreservesColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} G where
  reflectsColimitsOfShape := reflectsColimitsOfShape_of_reflectsIsomorphisms

end

section

open CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_app_coconePt_of_preservesColimit` / 引理 `isIso_app_coconePt_of_preservesColimit`

English:
lemma isIso_app_coconePt_of_preservesColimit
  proof: by
  let e := IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves L hc) (isColimitOfPreserves L' hc) (asIso (whiskerLeft K α))
  convert! (inferInstance : IsIso e.hom)
  apply (isColimitOfPreserves L hc).hom_ext fun j => ?_
  simp only [Functor.comp_obj, Functor.mapCocone_pt, Functor.mapCoco

中文:
引理 isIso_app_coconePt_of_preservesColimit
  证明: by
  let e := IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves L hc) (isColimitOfPreserves L' hc) (asIso (whiskerLeft K α))
  convert! (inferInstance : IsIso e.hom)
  apply (isColimitOfPreserves L hc).hom_ext fun j => ?_
  simp only [Functor.comp_obj, Functor.mapCocone_pt, Functor.mapCoco

Depends on / 依赖: Functor, Functor.comp_obj, Functor.mapCocone_, Functor.mapCocone_pt, IsColimit, IsColimit.coconePointsIsoOfNatIso, IsColimit.coconePointsIsoOfNatIso_hom, NatTrans, NatTrans.naturality, asIso_hom, coconePointsIsoOfNatIso, coconePointsIsoOfNatIso_hom, comp_obj, convert, e.hom, hom_ext, isColimitOfPreserves, mapCocone, mapCocone_pt, naturality
-/
lemma isIso_app_coconePt_of_preservesColimit
    {C D J : Type*} [Category* C] [Category* D] [Category* J] (K : J ⥤ C) {L L' : C ⥤ D}
    (α : L ⟶ L') [IsIso (whiskerLeft K α)] (c : Cocone K) (hc : IsColimit c)
    [PreservesColimit K L] [PreservesColimit K L'] :
    IsIso (α.app c.pt) := by
  let e := IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves L hc) (isColimitOfPreserves L' hc) (asIso (whiskerLeft K α))
  convert! (inferInstance : IsIso e.hom)
  apply (isColimitOfPreserves L hc).hom_ext fun j => ?_
  simp only [Functor.comp_obj, Functor.mapCocone_pt, Functor.mapCocone_ι_app,
    NatTrans.naturality, IsColimit.coconePointsIsoOfNatIso_hom, asIso_hom, e]
  refine (((isColimitOfPreserves L hc).ι_map (L'.mapCocone c) (whiskerLeft K α) j).trans ?_).symm
  simp

end

variable (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `fullyFaithful_reflectsLimits` / 实例 `fullyFaithful_reflectsLimits`

English:
instance fullyFaithful_reflectsLimits
  signature: [F.Full] [F.Faithful]
  body: { reflectsLimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsLimit.mkConeMorphism fun _ =>
                (Cone.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (Cone.functoriality K F).map_injective _
              intro s m
             

中文:
实例 fullyFaithful_reflectsLimits
  签名: [F.满] [F.忠实]
  定义体: { reflectsLimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsLimit.mkConeMorphism fun _ =>
                (Cone.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (Cone.functoriality K F).map_injective _
              intro s m
             

Depends on / 依赖: Cone.functoriality, Functor, Functor.map_preimage, IsLimit, IsLimit.mkConeMorphism, backward, backward.isDefEq.respectTransparency.types, functoriality, isDefEq, liftConeMorphism, map_injective, map_preimage, mkConeMorphism, preimage, reflects, reflectsLimit, respectTransparency, set_option, t.liftConeMorphism, t.uniq_cone_morphism
-/
instance fullyFaithful_reflectsLimits [F.Full] [F.Faithful] : ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {J} 𝒥₁ :=
    { reflectsLimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsLimit.mkConeMorphism fun _ =>
                (Cone.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (Cone.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cone_morphism⟩ } }
set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `fullyFaithful_reflectsColimits` / 实例 `fullyFaithful_reflectsColimits`

English:
instance fullyFaithful_reflectsColimits
  signature: [F.Full] [F.Faithful]
  body: { reflectsColimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsColimit.mkCoconeMorphism fun _ =>
                (Cocone.functoriality K F).preimage (t.descCoconeMorphism _)) <| by
              apply fun s m => (Cocone.functoriality K F).map_injective _
              intro s m
 

中文:
实例 fullyFaithful_reflectsColimits
  签名: [F.满] [F.忠实]
  定义体: { reflectsColimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsColimit.mkCoconeMorphism fun _ =>
                (Cocone.functoriality K F).preimage (t.descCoconeMorphism _)) <| by
              apply fun s m => (Cocone.functoriality K F).map_injective _
              intro s m
 

Depends on / 依赖: Cocone, Cocone.functoriality, Functor, Functor.map_preimage, IsColimit, IsColimit.mkCoconeMorphism, descCoconeMorphism, functoriality, map_injective, map_preimage, mkCoconeMorphism, preimage, reflects, reflectsColimit, t.descCoconeMorphism, t.uniq_cocone_morphism, uniq_cocone_morphism
-/
instance fullyFaithful_reflectsColimits [F.Full] [F.Faithful] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {J} 𝒥₁ :=
    { reflectsColimit := fun {K} =>
        { reflects := fun {c} t =>
            ⟨(IsColimit.mkCoconeMorphism fun _ =>
                (Cocone.functoriality K F).preimage (t.descCoconeMorphism _)) <| by
              apply fun s m => (Cocone.functoriality K F).map_injective _
              intro s m
              rw [Functor.map_preimage]
              apply t.uniq_cocone_morphism⟩ } }

end CategoryTheory.Limits
