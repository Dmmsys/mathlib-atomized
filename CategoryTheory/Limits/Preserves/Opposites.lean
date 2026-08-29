/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limit preservation properties of `Functor.op` and related constructions

We formulate conditions about `F` which imply that `F.op`, `F.unop`, `F.leftOp` and `F.rightOp`
preserve certain (co)limits and vice versa.

-/

public section


universe w w' v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

/--
lemma `preservesLimit_op` / 引理 `preservesLimit_op`

English:
lemma preservesLimit_op
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F]
  proof: ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

中文:
引理 preservesLimit_op
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [保持余极限 K.leftOp F]
  证明: ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

Depends on / 依赖: isColimitCoconeLeftOpOfCone, isColimitOfPreserves, isLimitConeRightOpOfCocone
-/
lemma preservesLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.op where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

/--
lemma `preservesLimit_of_op` / 引理 `preservesLimit_of_op`

English:
lemma preservesLimit_of_op
  given: (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op]
  proof: ⟨isLimitOfOp (isColimitOfPreserves F.op (IsLimit.op hc))⟩

中文:
引理 preservesLimit_of_op
  条件: (K : J ⥤ C) (F : C ⥤ D) [保持余极限 K.op F.op]
  证明: ⟨isLimitOfOp (isColimitOfPreserves F.op (IsLimit.op hc))⟩

Depends on / 依赖: F.op, IsLimit, IsLimit.op, isColimitOfPreserves, isLimitOfOp
-/
lemma preservesLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesColimit K.op F.op] :
    PreservesLimit K F where
  preserves {_} hc := ⟨isLimitOfOp (isColimitOfPreserves F.op (IsLimit.op hc))⟩

/--
lemma `preservesLimit_leftOp` / 引理 `preservesLimit_leftOp`

English:
lemma preservesLimit_leftOp
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F]
  proof: ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

中文:
引理 preservesLimit_leftOp
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [保持余极限 K.leftOp F]
  证明: ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

Depends on / 依赖: isColimitCoconeLeftOpOfCone, isColimitOfPreserves, isLimitConeUnopOfCocone
-/
lemma preservesLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F] :
    PreservesLimit K F.leftOp where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F (isColimitCoconeLeftOpOfCone _ hc))⟩

/--
lemma `preservesLimit_of_leftOp` / 引理 `preservesLimit_of_leftOp`

English:
lemma preservesLimit_of_leftOp
  given: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op F.leftOp]
  proof: ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.leftOp (IsLimit.op hc))⟩

中文:
引理 preservesLimit_of_leftOp
  条件: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [保持余极限 K.op F.leftOp]
  证明: ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.leftOp (IsLimit.op hc))⟩

Depends on / 依赖: F.leftOp, IsLimit, IsLimit.op, isColimitOfPreserves, isLimitOfCoconeLeftOpOfCone, leftOp
-/
lemma preservesLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesColimit K.op F.leftOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.leftOp (IsLimit.op hc))⟩

/--
lemma `preservesLimit_rightOp` / 引理 `preservesLimit_rightOp`

English:
lemma preservesLimit_rightOp
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F]
  proof: ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)⟩

中文:
引理 preservesLimit_rightOp
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [保持余极限 K.op F]
  证明: ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)⟩

Depends on / 依赖: hc.op, isColimitOfPreserves, isLimitConeRightOpOfCocone
-/
lemma preservesLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.op F] :
    PreservesLimit K F.rightOp where
  preserves {_} hc :=
    ⟨isLimitConeRightOpOfCocone _ (isColimitOfPreserves F hc.op)⟩

/--
lemma `preservesLimit_of_rightOp` / 引理 `preservesLimit_of_rightOp`

English:
lemma preservesLimit_of_rightOp
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.leftOp F.rightOp]
  proof: ⟨isLimitOfOp (isColimitOfPreserves F.rightOp (isColimitCoconeLeftOpOfCone _ hc))⟩

中文:
引理 preservesLimit_of_rightOp
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [保持余极限 K.leftOp F.rightOp]
  证明: ⟨isLimitOfOp (isColimitOfPreserves F.rightOp (isColimitCoconeLeftOpOfCone _ hc))⟩

Depends on / 依赖: F.rightOp, isColimitCoconeLeftOpOfCone, isColimitOfPreserves, isLimitOfOp, rightOp
-/
lemma preservesLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesColimit K.leftOp F.rightOp] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfOp (isColimitOfPreserves F.rightOp (isColimitCoconeLeftOpOfCone _ hc))⟩

/--
lemma `preservesLimit_unop` / 引理 `preservesLimit_unop`

English:
lemma preservesLimit_unop
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F]
  proof: ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)⟩

中文:
引理 preservesLimit_unop
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持余极限 K.op F]
  证明: ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)⟩

Depends on / 依赖: hc.op, isColimitOfPreserves, isLimitConeUnopOfCocone
-/
lemma preservesLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.op F] :
    PreservesLimit K F.unop where
  preserves {_} hc :=
    ⟨isLimitConeUnopOfCocone _ (isColimitOfPreserves F hc.op)⟩

/--
lemma `preservesLimit_of_unop` / 引理 `preservesLimit_of_unop`

English:
lemma preservesLimit_of_unop
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F.unop]
  proof: ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

中文:
引理 preservesLimit_of_unop
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持余极限 K.leftOp F.unop]
  证明: ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

Depends on / 依赖: F.unop, isColimitCoconeLeftOpOfCone, isColimitOfPreserves, isLimitOfCoconeLeftOpOfCone
-/
lemma preservesLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimit K.leftOp F.unop] :
    PreservesLimit K F where
  preserves {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfPreserves F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

/--
lemma `preservesColimit_op` / 引理 `preservesColimit_op`

English:
lemma preservesColimit_op
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F]
  proof: ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

中文:
引理 preservesColimit_op
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [保持极限 K.leftOp F]
  证明: ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

Depends on / 依赖: isColimitCoconeRightOpOfCone, isLimitConeLeftOpOfCocone, isLimitOfPreserves
-/
lemma preservesColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.op where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

/--
lemma `preservesColimit_of_op` / 引理 `preservesColimit_of_op`

English:
lemma preservesColimit_of_op
  given: (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op]
  proof: ⟨isColimitOfOp (isLimitOfPreserves F.op (IsColimit.op hc))⟩

中文:
引理 preservesColimit_of_op
  条件: (K : J ⥤ C) (F : C ⥤ D) [保持极限 K.op F.op]
  证明: ⟨isColimitOfOp (isLimitOfPreserves F.op (IsColimit.op hc))⟩

Depends on / 依赖: F.op, IsColimit, IsColimit.op, isColimitOfOp, isLimitOfPreserves
-/
lemma preservesColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [PreservesLimit K.op F.op] :
    PreservesColimit K F where
  preserves {_} hc := ⟨isColimitOfOp (isLimitOfPreserves F.op (IsColimit.op hc))⟩

/--
lemma `preservesColimit_leftOp` / 引理 `preservesColimit_leftOp`

English:
lemma preservesColimit_leftOp
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F]
  proof: ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

中文:
引理 preservesColimit_leftOp
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [保持极限 K.leftOp F]
  证明: ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

Depends on / 依赖: isColimitCoconeUnopOfCone, isLimitConeLeftOpOfCocone, isLimitOfPreserves
-/
lemma preservesColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F] :
    PreservesColimit K F.leftOp where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F (isLimitConeLeftOpOfCocone _ hc))⟩

/--
lemma `preservesColimit_of_leftOp` / 引理 `preservesColimit_of_leftOp`

English:
lemma preservesColimit_of_leftOp
  given: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op F.leftOp]
  proof: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.leftOp (IsColimit.op hc))⟩

中文:
引理 preservesColimit_of_leftOp
  条件: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [保持极限 K.op F.leftOp]
  证明: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.leftOp (IsColimit.op hc))⟩

Depends on / 依赖: F.leftOp, IsColimit, IsColimit.op, isColimitOfConeLeftOpOfCocone, isLimitOfPreserves, leftOp
-/
lemma preservesColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [PreservesLimit K.op F.leftOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.leftOp (IsColimit.op hc))⟩

/--
lemma `preservesColimit_rightOp` / 引理 `preservesColimit_rightOp`

English:
lemma preservesColimit_rightOp
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F]
  proof: ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)⟩

中文:
引理 preservesColimit_rightOp
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [保持极限 K.op F]
  证明: ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)⟩

Depends on / 依赖: hc.op, isColimitCoconeRightOpOfCone, isLimitOfPreserves
-/
lemma preservesColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.op F] :
    PreservesColimit K F.rightOp where
  preserves {_} hc :=
    ⟨isColimitCoconeRightOpOfCone _ (isLimitOfPreserves F hc.op)⟩

/--
lemma `preservesColimit_of_rightOp` / 引理 `preservesColimit_of_rightOp`

English:
lemma preservesColimit_of_rightOp
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.leftOp F.rightOp]
  proof: ⟨isColimitOfOp (isLimitOfPreserves F.rightOp (isLimitConeLeftOpOfCocone _ hc))⟩

中文:
引理 preservesColimit_of_rightOp
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [保持极限 K.leftOp F.rightOp]
  证明: ⟨isColimitOfOp (isLimitOfPreserves F.rightOp (isLimitConeLeftOpOfCocone _ hc))⟩

Depends on / 依赖: F.rightOp, isColimitOfOp, isLimitConeLeftOpOfCocone, isLimitOfPreserves, rightOp
-/
lemma preservesColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [PreservesLimit K.leftOp F.rightOp] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfOp (isLimitOfPreserves F.rightOp (isLimitConeLeftOpOfCocone _ hc))⟩

/--
lemma `preservesColimit_unop` / 引理 `preservesColimit_unop`

English:
lemma preservesColimit_unop
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F]
  proof: ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)⟩

中文:
引理 preservesColimit_unop
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持极限 K.op F]
  证明: ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)⟩

Depends on / 依赖: hc.op, isColimitCoconeUnopOfCone, isLimitOfPreserves
-/
lemma preservesColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.op F] :
    PreservesColimit K F.unop where
  preserves {_} hc :=
    ⟨isColimitCoconeUnopOfCone _ (isLimitOfPreserves F hc.op)⟩

/--
lemma `preservesColimit_of_unop` / 引理 `preservesColimit_of_unop`

English:
lemma preservesColimit_of_unop
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F.unop]
  proof: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

中文:
引理 preservesColimit_of_unop
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持极限 K.leftOp F.unop]
  证明: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

Depends on / 依赖: F.unop, isColimitOfConeLeftOpOfCocone, isLimitConeLeftOpOfCocone, isLimitOfPreserves
-/
lemma preservesColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimit K.leftOp F.unop] :
    PreservesColimit K F where
  preserves {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfPreserves F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

section

variable (J)

/--
lemma `preservesLimitsOfShape_op` / 引理 `preservesLimitsOfShape_op`

English:
lemma preservesLimitsOfShape_op
  given: (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F]
  proof: preservesLimit_op K F

中文:
引理 preservesLimitsOfShape_op
  条件: (F : C ⥤ D) [保持形状余极限 Jᵒᵖ F]
  证明: preservesLimit_op K F

Depends on / 依赖: preservesLimit_op
-/
lemma preservesLimitsOfShape_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.op where preservesLimit {K} := preservesLimit_op K F

/--
lemma `preservesLimitsOfShape_leftOp` / 引理 `preservesLimitsOfShape_leftOp`

English:
lemma preservesLimitsOfShape_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F]
  proof: preservesLimit_leftOp K F

中文:
引理 preservesLimitsOfShape_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持形状余极限 Jᵒᵖ F]
  证明: preservesLimit_leftOp K F

Depends on / 依赖: preservesLimit_leftOp
-/
lemma preservesLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.leftOp where preservesLimit {K} := preservesLimit_leftOp K F

/--
lemma `preservesLimitsOfShape_rightOp` / 引理 `preservesLimitsOfShape_rightOp`

English:
lemma preservesLimitsOfShape_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F]
  proof: preservesLimit_rightOp K F

中文:
引理 preservesLimitsOfShape_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持形状余极限 Jᵒᵖ F]
  证明: preservesLimit_rightOp K F

Depends on / 依赖: preservesLimit_rightOp
-/
lemma preservesLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.rightOp where preservesLimit {K} := preservesLimit_rightOp K F

/--
lemma `preservesLimitsOfShape_unop` / 引理 `preservesLimitsOfShape_unop`

English:
lemma preservesLimitsOfShape_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F]
  proof: preservesLimit_unop K F

中文:
引理 preservesLimitsOfShape_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持形状余极限 Jᵒᵖ F]
  证明: preservesLimit_unop K F

Depends on / 依赖: preservesLimit_unop
-/
lemma preservesLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F] :
    PreservesLimitsOfShape J F.unop where preservesLimit {K} := preservesLimit_unop K F

/--
lemma `preservesColimitsOfShape_op` / 引理 `preservesColimitsOfShape_op`

English:
lemma preservesColimitsOfShape_op
  given: (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F]
  proof: preservesColimit_op K F

中文:
引理 preservesColimitsOfShape_op
  条件: (F : C ⥤ D) [保持形状极限 Jᵒᵖ F]
  证明: preservesColimit_op K F

Depends on / 依赖: preservesColimit_op
-/
lemma preservesColimitsOfShape_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.op where preservesColimit {K} := preservesColimit_op K F

/--
lemma `preservesColimitsOfShape_leftOp` / 引理 `preservesColimitsOfShape_leftOp`

English:
lemma preservesColimitsOfShape_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F]
  proof: preservesColimit_leftOp K F

中文:
引理 preservesColimitsOfShape_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持形状极限 Jᵒᵖ F]
  证明: preservesColimit_leftOp K F

Depends on / 依赖: preservesColimit_leftOp
-/
lemma preservesColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.leftOp where preservesColimit {K} := preservesColimit_leftOp K F

/--
lemma `preservesColimitsOfShape_rightOp` / 引理 `preservesColimitsOfShape_rightOp`

English:
lemma preservesColimitsOfShape_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F]
  proof: preservesColimit_rightOp K F

中文:
引理 preservesColimitsOfShape_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持形状极限 Jᵒᵖ F]
  证明: preservesColimit_rightOp K F

Depends on / 依赖: preservesColimit_rightOp
-/
lemma preservesColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.rightOp where preservesColimit {K} := preservesColimit_rightOp K F

/--
lemma `preservesColimitsOfShape_unop` / 引理 `preservesColimitsOfShape_unop`

English:
lemma preservesColimitsOfShape_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F]
  proof: preservesColimit_unop K F

中文:
引理 preservesColimitsOfShape_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持形状极限 Jᵒᵖ F]
  证明: preservesColimit_unop K F

Depends on / 依赖: preservesColimit_unop
-/
lemma preservesColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F] :
    PreservesColimitsOfShape J F.unop where preservesColimit {K} := preservesColimit_unop K F

/--
lemma `preservesLimitsOfShape_of_op` / 引理 `preservesLimitsOfShape_of_op`

English:
lemma preservesLimitsOfShape_of_op
  given: (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op]
  proof: preservesLimit_of_op K F

中文:
引理 preservesLimitsOfShape_of_op
  条件: (F : C ⥤ D) [保持形状余极限 Jᵒᵖ F.op]
  证明: preservesLimit_of_op K F

Depends on / 依赖: preservesLimit_of_op
-/
lemma preservesLimitsOfShape_of_op (F : C ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.op] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_op K F

/--
lemma `preservesLimitsOfShape_of_leftOp` / 引理 `preservesLimitsOfShape_of_leftOp`

English:
lemma preservesLimitsOfShape_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp]
  proof: preservesLimit_of_leftOp K F

中文:
引理 preservesLimitsOfShape_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持形状余极限 Jᵒᵖ F.leftOp]
  证明: preservesLimit_of_leftOp K F

Depends on / 依赖: preservesLimit_of_leftOp
-/
lemma preservesLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_leftOp K F

/--
lemma `preservesLimitsOfShape_of_rightOp` / 引理 `preservesLimitsOfShape_of_rightOp`

English:
lemma preservesLimitsOfShape_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp]
  proof: preservesLimit_of_rightOp K F

中文:
引理 preservesLimitsOfShape_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持形状余极限 Jᵒᵖ F.rightOp]
  证明: preservesLimit_of_rightOp K F

Depends on / 依赖: preservesLimit_of_rightOp
-/
lemma preservesLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_rightOp K F

/--
lemma `preservesLimitsOfShape_of_unop` / 引理 `preservesLimitsOfShape_of_unop`

English:
lemma preservesLimitsOfShape_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop]
  proof: preservesLimit_of_unop K F

中文:
引理 preservesLimitsOfShape_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持形状余极限 Jᵒᵖ F.unop]
  证明: preservesLimit_of_unop K F

Depends on / 依赖: preservesLimit_of_unop
-/
lemma preservesLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfShape Jᵒᵖ F.unop] :
    PreservesLimitsOfShape J F where preservesLimit {K} := preservesLimit_of_unop K F

/--
lemma `preservesColimitsOfShape_of_op` / 引理 `preservesColimitsOfShape_of_op`

English:
lemma preservesColimitsOfShape_of_op
  given: (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op]
  proof: preservesColimit_of_op K F

中文:
引理 preservesColimitsOfShape_of_op
  条件: (F : C ⥤ D) [保持形状极限 Jᵒᵖ F.op]
  证明: preservesColimit_of_op K F

Depends on / 依赖: preservesColimit_of_op
-/
lemma preservesColimitsOfShape_of_op (F : C ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.op] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_op K F

/--
lemma `preservesColimitsOfShape_of_leftOp` / 引理 `preservesColimitsOfShape_of_leftOp`

English:
lemma preservesColimitsOfShape_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp]
  proof: preservesColimit_of_leftOp K F

中文:
引理 preservesColimitsOfShape_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持形状极限 Jᵒᵖ F.leftOp]
  证明: preservesColimit_of_leftOp K F

Depends on / 依赖: preservesColimit_of_leftOp
-/
lemma preservesColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.leftOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_leftOp K F

/--
lemma `preservesColimitsOfShape_of_rightOp` / 引理 `preservesColimitsOfShape_of_rightOp`

English:
lemma preservesColimitsOfShape_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp]
  proof: preservesColimit_of_rightOp K F

中文:
引理 preservesColimitsOfShape_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持形状极限 Jᵒᵖ F.rightOp]
  证明: preservesColimit_of_rightOp K F

Depends on / 依赖: preservesColimit_of_rightOp
-/
lemma preservesColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfShape Jᵒᵖ F.rightOp] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_rightOp K F

/--
lemma `preservesColimitsOfShape_of_unop` / 引理 `preservesColimitsOfShape_of_unop`

English:
lemma preservesColimitsOfShape_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop]
  proof: preservesColimit_of_unop K F

中文:
引理 preservesColimitsOfShape_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持形状极限 Jᵒᵖ F.unop]
  证明: preservesColimit_of_unop K F

Depends on / 依赖: preservesColimit_of_unop
-/
lemma preservesColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfShape Jᵒᵖ F.unop] :
    PreservesColimitsOfShape J F where preservesColimit {K} := preservesColimit_of_unop K F

end

/--
lemma `preservesLimitsOfSize_op` / 引理 `preservesLimitsOfSize_op`

English:
lemma preservesLimitsOfSize_op
  given: (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F]
  proof: preservesLimitsOfShape_op _ _

中文:
引理 preservesLimitsOfSize_op
  条件: (F : C ⥤ D) [保持余limitsOfSize.{w, w'} F]
  证明: preservesLimitsOfShape_op _ _

Depends on / 依赖: preservesLimitsOfShape_op
-/
lemma preservesLimitsOfSize_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/--
lemma `preservesLimitsOfSize_leftOp` / 引理 `preservesLimitsOfSize_leftOp`

English:
lemma preservesLimitsOfSize_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F]
  proof: preservesLimitsOfShape_leftOp _ _

中文:
引理 preservesLimitsOfSize_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持余limitsOfSize.{w, w'} F]
  证明: preservesLimitsOfShape_leftOp _ _

Depends on / 依赖: preservesLimitsOfShape_leftOp
-/
lemma preservesLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/--
lemma `preservesLimitsOfSize_rightOp` / 引理 `preservesLimitsOfSize_rightOp`

English:
lemma preservesLimitsOfSize_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F]
  proof: preservesLimitsOfShape_rightOp _ _

中文:
引理 preservesLimitsOfSize_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持余limitsOfSize.{w, w'} F]
  证明: preservesLimitsOfShape_rightOp _ _

Depends on / 依赖: preservesLimitsOfShape_rightOp
-/
lemma preservesLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/--
lemma `preservesLimitsOfSize_unop` / 引理 `preservesLimitsOfSize_unop`

English:
lemma preservesLimitsOfSize_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F]
  proof: preservesLimitsOfShape_unop _ _

中文:
引理 preservesLimitsOfSize_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持余limitsOfSize.{w, w'} F]
  证明: preservesLimitsOfShape_unop _ _

Depends on / 依赖: preservesLimitsOfShape_unop
-/
lemma preservesLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/--
lemma `preservesColimitsOfSize_op` / 引理 `preservesColimitsOfSize_op`

English:
lemma preservesColimitsOfSize_op
  given: (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F]
  proof: preservesColimitsOfShape_op _ _

中文:
引理 preservesColimitsOfSize_op
  条件: (F : C ⥤ D) [保持LimitsOfSize.{w, w'} F]
  证明: preservesColimitsOfShape_op _ _

Depends on / 依赖: preservesColimitsOfShape_op
-/
lemma preservesColimitsOfSize_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/--
lemma `preservesColimitsOfSize_leftOp` / 引理 `preservesColimitsOfSize_leftOp`

English:
lemma preservesColimitsOfSize_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F]
  proof: preservesColimitsOfShape_leftOp _ _

中文:
引理 preservesColimitsOfSize_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持LimitsOfSize.{w, w'} F]
  证明: preservesColimitsOfShape_leftOp _ _

Depends on / 依赖: preservesColimitsOfShape_leftOp
-/
lemma preservesColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/--
lemma `preservesColimitsOfSize_rightOp` / 引理 `preservesColimitsOfSize_rightOp`

English:
lemma preservesColimitsOfSize_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F]
  proof: preservesColimitsOfShape_rightOp _ _

中文:
引理 preservesColimitsOfSize_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持LimitsOfSize.{w, w'} F]
  证明: preservesColimitsOfShape_rightOp _ _

Depends on / 依赖: preservesColimitsOfShape_rightOp
-/
lemma preservesColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/--
lemma `preservesColimitsOfSize_unop` / 引理 `preservesColimitsOfSize_unop`

English:
lemma preservesColimitsOfSize_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F]
  proof: preservesColimitsOfShape_unop _ _

中文:
引理 preservesColimitsOfSize_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持LimitsOfSize.{w, w'} F]
  证明: preservesColimitsOfShape_unop _ _

Depends on / 依赖: preservesColimitsOfShape_unop
-/
lemma preservesColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/--
lemma `preservesLimitsOfSize_of_op` / 引理 `preservesLimitsOfSize_of_op`

English:
lemma preservesLimitsOfSize_of_op
  given: (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F.op]
  proof: preservesLimitsOfShape_of_op _ _

中文:
引理 preservesLimitsOfSize_of_op
  条件: (F : C ⥤ D) [保持余limitsOfSize.{w, w'} F.op]
  证明: preservesLimitsOfShape_of_op _ _

Depends on / 依赖: preservesLimitsOfShape_of_op
-/
lemma preservesLimitsOfSize_of_op (F : C ⥤ D) [PreservesColimitsOfSize.{w, w'} F.op] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/--
lemma `preservesLimitsOfSize_of_leftOp` / 引理 `preservesLimitsOfSize_of_leftOp`

English:
lemma preservesLimitsOfSize_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.leftOp]
  proof: preservesLimitsOfShape_of_leftOp _ _

中文:
引理 preservesLimitsOfSize_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持余limitsOfSize.{w, w'} F.leftOp]
  证明: preservesLimitsOfShape_of_leftOp _ _

Depends on / 依赖: preservesLimitsOfShape_of_leftOp
-/
lemma preservesLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.leftOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/--
lemma `preservesLimitsOfSize_of_rightOp` / 引理 `preservesLimitsOfSize_of_rightOp`

English:
lemma preservesLimitsOfSize_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F.rightOp]
  proof: preservesLimitsOfShape_of_rightOp _ _

中文:
引理 preservesLimitsOfSize_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持余limitsOfSize.{w, w'} F.rightOp]
  证明: preservesLimitsOfShape_of_rightOp _ _

Depends on / 依赖: preservesLimitsOfShape_of_rightOp
-/
lemma preservesLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimitsOfSize.{w, w'} F.rightOp] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/--
lemma `preservesLimitsOfSize_of_unop` / 引理 `preservesLimitsOfSize_of_unop`

English:
lemma preservesLimitsOfSize_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.unop]
  proof: preservesLimitsOfShape_of_unop _ _

中文:
引理 preservesLimitsOfSize_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持余limitsOfSize.{w, w'} F.unop]
  证明: preservesLimitsOfShape_of_unop _ _

Depends on / 依赖: preservesLimitsOfShape_of_unop
-/
lemma preservesLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimitsOfSize.{w, w'} F.unop] :
    PreservesLimitsOfSize.{w, w'} F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/--
lemma `preservesColimitsOfSize_of_op` / 引理 `preservesColimitsOfSize_of_op`

English:
lemma preservesColimitsOfSize_of_op
  given: (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F.op]
  proof: preservesColimitsOfShape_of_op _ _

中文:
引理 preservesColimitsOfSize_of_op
  条件: (F : C ⥤ D) [保持LimitsOfSize.{w, w'} F.op]
  证明: preservesColimitsOfShape_of_op _ _

Depends on / 依赖: preservesColimitsOfShape_of_op
-/
lemma preservesColimitsOfSize_of_op (F : C ⥤ D) [PreservesLimitsOfSize.{w, w'} F.op] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/--
lemma `preservesColimitsOfSize_of_leftOp` / 引理 `preservesColimitsOfSize_of_leftOp`

English:
lemma preservesColimitsOfSize_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.leftOp]
  proof: preservesColimitsOfShape_of_leftOp _ _

中文:
引理 preservesColimitsOfSize_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持LimitsOfSize.{w, w'} F.leftOp]
  证明: preservesColimitsOfShape_of_leftOp _ _

Depends on / 依赖: preservesColimitsOfShape_of_leftOp
-/
lemma preservesColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.leftOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/--
lemma `preservesColimitsOfSize_of_rightOp` / 引理 `preservesColimitsOfSize_of_rightOp`

English:
lemma preservesColimitsOfSize_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F.rightOp]
  proof: preservesColimitsOfShape_of_rightOp _ _

中文:
引理 preservesColimitsOfSize_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持LimitsOfSize.{w, w'} F.rightOp]
  证明: preservesColimitsOfShape_of_rightOp _ _

Depends on / 依赖: preservesColimitsOfShape_of_rightOp
-/
lemma preservesColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimitsOfSize.{w, w'} F.rightOp] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/--
lemma `preservesColimitsOfSize_of_unop` / 引理 `preservesColimitsOfSize_of_unop`

English:
lemma preservesColimitsOfSize_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.unop]
  proof: preservesColimitsOfShape_of_unop _ _

中文:
引理 preservesColimitsOfSize_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持LimitsOfSize.{w, w'} F.unop]
  证明: preservesColimitsOfShape_of_unop _ _

Depends on / 依赖: preservesColimitsOfShape_of_unop
-/
lemma preservesColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimitsOfSize.{w, w'} F.unop] :
    PreservesColimitsOfSize.{w, w'} F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/--
lemma `preservesLimits_op` / 引理 `preservesLimits_op`

English:
lemma preservesLimits_op
  given: (F : C ⥤ D) [PreservesColimits F]
  statement: PreservesLimits F.op where
  proof: preservesLimitsOfShape_op _ _

中文:
引理 preservesLimits_op
  条件: (F : C ⥤ D) [PreservesColimits F]
  结论: PreservesLimits F.op where
  证明: preservesLimitsOfShape_op _ _

Depends on / 依赖: preservesLimitsOfShape_op
-/
lemma preservesLimits_op (F : C ⥤ D) [PreservesColimits F] : PreservesLimits F.op where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_op _ _

/--
lemma `preservesLimits_leftOp` / 引理 `preservesLimits_leftOp`

English:
lemma preservesLimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesColimits F]
  statement: PreservesLimits F.leftOp where
  proof: preservesLimitsOfShape_leftOp _ _

中文:
引理 preservesLimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [PreservesColimits F]
  结论: PreservesLimits F.leftOp where
  证明: preservesLimitsOfShape_leftOp _ _

Depends on / 依赖: preservesLimitsOfShape_leftOp
-/
lemma preservesLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.leftOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_leftOp _ _

/--
lemma `preservesLimits_rightOp` / 引理 `preservesLimits_rightOp`

English:
lemma preservesLimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesColimits F]
  statement: PreservesLimits F.rightOp where
  proof: preservesLimitsOfShape_rightOp _ _

中文:
引理 preservesLimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [PreservesColimits F]
  结论: PreservesLimits F.rightOp where
  证明: preservesLimitsOfShape_rightOp _ _

Depends on / 依赖: preservesLimitsOfShape_rightOp
-/
lemma preservesLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F] : PreservesLimits F.rightOp where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_rightOp _ _

/--
lemma `preservesLimits_unop` / 引理 `preservesLimits_unop`

English:
lemma preservesLimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F]
  statement: PreservesLimits F.unop where
  proof: preservesLimitsOfShape_unop _ _

中文:
引理 preservesLimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F]
  结论: PreservesLimits F.unop where
  证明: preservesLimitsOfShape_unop _ _

Depends on / 依赖: preservesLimitsOfShape_unop
-/
lemma preservesLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F] : PreservesLimits F.unop where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_unop _ _

/--
lemma `preservesColimits_op` / 引理 `preservesColimits_op`

English:
lemma preservesColimits_op
  given: (F : C ⥤ D) [PreservesLimits F]
  statement: PreservesColimits F.op where
  proof: preservesColimitsOfShape_op _ _

中文:
引理 preservesColimits_op
  条件: (F : C ⥤ D) [PreservesLimits F]
  结论: PreservesColimits F.op where
  证明: preservesColimitsOfShape_op _ _

Depends on / 依赖: preservesColimitsOfShape_op
-/
lemma preservesColimits_op (F : C ⥤ D) [PreservesLimits F] : PreservesColimits F.op where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_op _ _

/--
lemma `preservesColimits_leftOp` / 引理 `preservesColimits_leftOp`

English:
lemma preservesColimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesLimits F]
  statement: PreservesColimits F.leftOp where
  proof: preservesColimitsOfShape_leftOp _ _

中文:
引理 preservesColimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [PreservesLimits F]
  结论: PreservesColimits F.leftOp where
  证明: preservesColimitsOfShape_leftOp _ _

Depends on / 依赖: preservesColimitsOfShape_leftOp
-/
lemma preservesColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.leftOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_leftOp _ _

/--
lemma `preservesColimits_rightOp` / 引理 `preservesColimits_rightOp`

English:
lemma preservesColimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesLimits F]
  proof: preservesColimitsOfShape_rightOp _ _

中文:
引理 preservesColimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [PreservesLimits F]
  证明: preservesColimitsOfShape_rightOp _ _

Depends on / 依赖: preservesColimitsOfShape_rightOp
-/
lemma preservesColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F] :
    PreservesColimits F.rightOp where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_rightOp _ _

/--
lemma `preservesColimits_unop` / 引理 `preservesColimits_unop`

English:
lemma preservesColimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F]
  statement: PreservesColimits F.unop where
  proof: preservesColimitsOfShape_unop _ _

中文:
引理 preservesColimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F]
  结论: PreservesColimits F.unop where
  证明: preservesColimitsOfShape_unop _ _

Depends on / 依赖: preservesColimitsOfShape_unop
-/
lemma preservesColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F] : PreservesColimits F.unop where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_unop _ _

/--
lemma `preservesLimits_of_op` / 引理 `preservesLimits_of_op`

English:
lemma preservesLimits_of_op
  given: (F : C ⥤ D) [PreservesColimits F.op]
  statement: PreservesLimits F where
  proof: preservesLimitsOfShape_of_op _ _

中文:
引理 preservesLimits_of_op
  条件: (F : C ⥤ D) [PreservesColimits F.op]
  结论: PreservesLimits F where
  证明: preservesLimitsOfShape_of_op _ _

Depends on / 依赖: preservesLimitsOfShape_of_op
-/
lemma preservesLimits_of_op (F : C ⥤ D) [PreservesColimits F.op] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_op _ _

/--
lemma `preservesLimits_of_leftOp` / 引理 `preservesLimits_of_leftOp`

English:
lemma preservesLimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp]
  statement: PreservesLimits F where
  proof: preservesLimitsOfShape_of_leftOp _ _

中文:
引理 preservesLimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp]
  结论: PreservesLimits F where
  证明: preservesLimitsOfShape_of_leftOp _ _

Depends on / 依赖: preservesLimitsOfShape_of_leftOp
-/
lemma preservesLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesColimits F.leftOp] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_leftOp _ _

/--
lemma `preservesLimits_of_rightOp` / 引理 `preservesLimits_of_rightOp`

English:
lemma preservesLimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp]
  proof: preservesLimitsOfShape_of_rightOp _ _

中文:
引理 preservesLimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp]
  证明: preservesLimitsOfShape_of_rightOp _ _

Depends on / 依赖: preservesLimitsOfShape_of_rightOp
-/
lemma preservesLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesColimits F.rightOp] :
    PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_rightOp _ _

/--
lemma `preservesLimits_of_unop` / 引理 `preservesLimits_of_unop`

English:
lemma preservesLimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop]
  statement: PreservesLimits F where
  proof: preservesLimitsOfShape_of_unop _ _

中文:
引理 preservesLimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop]
  结论: PreservesLimits F where
  证明: preservesLimitsOfShape_of_unop _ _

Depends on / 依赖: preservesLimitsOfShape_of_unop
-/
lemma preservesLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesColimits F.unop] : PreservesLimits F where
  preservesLimitsOfShape {_} _ := preservesLimitsOfShape_of_unop _ _

/--
lemma `preservesColimits_of_op` / 引理 `preservesColimits_of_op`

English:
lemma preservesColimits_of_op
  given: (F : C ⥤ D) [PreservesLimits F.op]
  statement: PreservesColimits F where
  proof: preservesColimitsOfShape_of_op _ _

中文:
引理 preservesColimits_of_op
  条件: (F : C ⥤ D) [PreservesLimits F.op]
  结论: PreservesColimits F where
  证明: preservesColimitsOfShape_of_op _ _

Depends on / 依赖: preservesColimitsOfShape_of_op
-/
lemma preservesColimits_of_op (F : C ⥤ D) [PreservesLimits F.op] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_op _ _

/--
lemma `preservesColimits_of_leftOp` / 引理 `preservesColimits_of_leftOp`

English:
lemma preservesColimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp]
  proof: preservesColimitsOfShape_of_leftOp _ _

中文:
引理 preservesColimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp]
  证明: preservesColimitsOfShape_of_leftOp _ _

Depends on / 依赖: preservesColimitsOfShape_of_leftOp
-/
lemma preservesColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesLimits F.leftOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_leftOp _ _

/--
lemma `preservesColimits_of_rightOp` / 引理 `preservesColimits_of_rightOp`

English:
lemma preservesColimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp]
  proof: preservesColimitsOfShape_of_rightOp _ _

中文:
引理 preservesColimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp]
  证明: preservesColimitsOfShape_of_rightOp _ _

Depends on / 依赖: preservesColimitsOfShape_of_rightOp
-/
lemma preservesColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesLimits F.rightOp] :
    PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_rightOp _ _

/--
lemma `preservesColimits_of_unop` / 引理 `preservesColimits_of_unop`

English:
lemma preservesColimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop]
  statement: PreservesColimits F where
  proof: preservesColimitsOfShape_of_unop _ _

中文:
引理 preservesColimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop]
  结论: PreservesColimits F where
  证明: preservesColimitsOfShape_of_unop _ _

Depends on / 依赖: preservesColimitsOfShape_of_unop
-/
lemma preservesColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesLimits F.unop] : PreservesColimits F where
  preservesColimitsOfShape {_} _ := preservesColimitsOfShape_of_unop _ _

/--
lemma `preservesFiniteLimits_op` / 引理 `preservesFiniteLimits_op`

English:
lemma preservesFiniteLimits_op
  given: (F : C ⥤ D) [PreservesFiniteColimits F]
  proof: preservesLimitsOfShape_op J F

中文:
引理 preservesFiniteLimits_op
  条件: (F : C ⥤ D) [保持FiniteColimits F]
  证明: preservesLimitsOfShape_op J F

Depends on / 依赖: preservesLimitsOfShape_op
-/
lemma preservesFiniteLimits_op (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.op where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_op J F

/--
lemma `preservesFiniteLimits_leftOp` / 引理 `preservesFiniteLimits_leftOp`

English:
lemma preservesFiniteLimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F]
  proof: preservesLimitsOfShape_leftOp J F

中文:
引理 preservesFiniteLimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持FiniteColimits F]
  证明: preservesLimitsOfShape_leftOp J F

Depends on / 依赖: preservesLimitsOfShape_leftOp
-/
lemma preservesFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.leftOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_leftOp J F

/--
lemma `preservesFiniteLimits_rightOp` / 引理 `preservesFiniteLimits_rightOp`

English:
lemma preservesFiniteLimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F]
  proof: preservesLimitsOfShape_rightOp J F

中文:
引理 preservesFiniteLimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持FiniteColimits F]
  证明: preservesLimitsOfShape_rightOp J F

Depends on / 依赖: preservesLimitsOfShape_rightOp
-/
lemma preservesFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.rightOp where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_rightOp J F

/--
lemma `preservesFiniteLimits_unop` / 引理 `preservesFiniteLimits_unop`

English:
lemma preservesFiniteLimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F]
  proof: preservesLimitsOfShape_unop J F

中文:
引理 preservesFiniteLimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持FiniteColimits F]
  证明: preservesLimitsOfShape_unop J F

Depends on / 依赖: preservesLimitsOfShape_unop
-/
lemma preservesFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F.unop where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_unop J F

/--
lemma `preservesFiniteColimits_op` / 引理 `preservesFiniteColimits_op`

English:
lemma preservesFiniteColimits_op
  given: (F : C ⥤ D) [PreservesFiniteLimits F]
  proof: preservesColimitsOfShape_op J F

中文:
引理 preservesFiniteColimits_op
  条件: (F : C ⥤ D) [保持FiniteLimits F]
  证明: preservesColimitsOfShape_op J F

Depends on / 依赖: preservesColimitsOfShape_op
-/
lemma preservesFiniteColimits_op (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.op where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_op J F

/--
lemma `preservesFiniteColimits_leftOp` / 引理 `preservesFiniteColimits_leftOp`

English:
lemma preservesFiniteColimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F]
  proof: preservesColimitsOfShape_leftOp J F

中文:
引理 preservesFiniteColimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持FiniteLimits F]
  证明: preservesColimitsOfShape_leftOp J F

Depends on / 依赖: preservesColimitsOfShape_leftOp
-/
lemma preservesFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.leftOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_leftOp J F

/--
lemma `preservesFiniteColimits_rightOp` / 引理 `preservesFiniteColimits_rightOp`

English:
lemma preservesFiniteColimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F]
  proof: preservesColimitsOfShape_rightOp J F

中文:
引理 preservesFiniteColimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持FiniteLimits F]
  证明: preservesColimitsOfShape_rightOp J F

Depends on / 依赖: preservesColimitsOfShape_rightOp
-/
lemma preservesFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.rightOp where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_rightOp J F

/--
lemma `preservesFiniteColimits_unop` / 引理 `preservesFiniteColimits_unop`

English:
lemma preservesFiniteColimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F]
  proof: preservesColimitsOfShape_unop J F

中文:
引理 preservesFiniteColimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持FiniteLimits F]
  证明: preservesColimitsOfShape_unop J F

Depends on / 依赖: preservesColimitsOfShape_unop
-/
lemma preservesFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F] :
    PreservesFiniteColimits F.unop where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_unop J F

/--
lemma `preservesFiniteLimits_of_op` / 引理 `preservesFiniteLimits_of_op`

English:
lemma preservesFiniteLimits_of_op
  given: (F : C ⥤ D) [PreservesFiniteColimits F.op]
  proof: preservesLimitsOfShape_of_op J F

中文:
引理 preservesFiniteLimits_of_op
  条件: (F : C ⥤ D) [保持FiniteColimits F.op]
  证明: preservesLimitsOfShape_of_op J F

Depends on / 依赖: preservesLimitsOfShape_of_op
-/
lemma preservesFiniteLimits_of_op (F : C ⥤ D) [PreservesFiniteColimits F.op] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_op J F

/--
lemma `preservesFiniteLimits_of_leftOp` / 引理 `preservesFiniteLimits_of_leftOp`

English:
lemma preservesFiniteLimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F.leftOp]
  proof: preservesLimitsOfShape_of_leftOp J F

中文:
引理 preservesFiniteLimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持FiniteColimits F.leftOp]
  证明: preservesLimitsOfShape_of_leftOp J F

Depends on / 依赖: preservesLimitsOfShape_of_leftOp
-/
lemma preservesFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteColimits F.leftOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_leftOp J F

/--
lemma `preservesFiniteLimits_of_rightOp` / 引理 `preservesFiniteLimits_of_rightOp`

English:
lemma preservesFiniteLimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F.rightOp]
  proof: preservesLimitsOfShape_of_rightOp J F

中文:
引理 preservesFiniteLimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持FiniteColimits F.rightOp]
  证明: preservesLimitsOfShape_of_rightOp J F

Depends on / 依赖: preservesLimitsOfShape_of_rightOp
-/
lemma preservesFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteColimits F.rightOp] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_rightOp J F

/--
lemma `preservesFiniteLimits_of_unop` / 引理 `preservesFiniteLimits_of_unop`

English:
lemma preservesFiniteLimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F.unop]
  proof: preservesLimitsOfShape_of_unop J F

中文:
引理 preservesFiniteLimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持FiniteColimits F.unop]
  证明: preservesLimitsOfShape_of_unop J F

Depends on / 依赖: preservesLimitsOfShape_of_unop
-/
lemma preservesFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteColimits F.unop] :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := preservesLimitsOfShape_of_unop J F

/--
lemma `preservesFiniteColimits_of_op` / 引理 `preservesFiniteColimits_of_op`

English:
lemma preservesFiniteColimits_of_op
  given: (F : C ⥤ D) [PreservesFiniteLimits F.op]
  proof: preservesColimitsOfShape_of_op J F

中文:
引理 preservesFiniteColimits_of_op
  条件: (F : C ⥤ D) [保持FiniteLimits F.op]
  证明: preservesColimitsOfShape_of_op J F

Depends on / 依赖: preservesColimitsOfShape_of_op
-/
lemma preservesFiniteColimits_of_op (F : C ⥤ D) [PreservesFiniteLimits F.op] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_op J F

/--
lemma `preservesFiniteColimits_of_leftOp` / 引理 `preservesFiniteColimits_of_leftOp`

English:
lemma preservesFiniteColimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F.leftOp]
  proof: preservesColimitsOfShape_of_leftOp J F

中文:
引理 preservesFiniteColimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持FiniteLimits F.leftOp]
  证明: preservesColimitsOfShape_of_leftOp J F

Depends on / 依赖: preservesColimitsOfShape_of_leftOp
-/
lemma preservesFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteLimits F.leftOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_leftOp J F

/--
lemma `preservesFiniteColimits_of_rightOp` / 引理 `preservesFiniteColimits_of_rightOp`

English:
lemma preservesFiniteColimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F.rightOp]
  proof: preservesColimitsOfShape_of_rightOp J F

中文:
引理 preservesFiniteColimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持FiniteLimits F.rightOp]
  证明: preservesColimitsOfShape_of_rightOp J F

Depends on / 依赖: preservesColimitsOfShape_of_rightOp
-/
lemma preservesFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteLimits F.rightOp] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_rightOp J F

/--
lemma `preservesFiniteColimits_of_unop` / 引理 `preservesFiniteColimits_of_unop`

English:
lemma preservesFiniteColimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F.unop]
  proof: preservesColimitsOfShape_of_unop J F

中文:
引理 preservesFiniteColimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持FiniteLimits F.unop]
  证明: preservesColimitsOfShape_of_unop J F

Depends on / 依赖: preservesColimitsOfShape_of_unop
-/
lemma preservesFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteLimits F.unop] :
    PreservesFiniteColimits F where
  preservesFiniteColimits J _ _ := preservesColimitsOfShape_of_unop J F

/--
lemma `preservesFiniteProducts_op` / 引理 `preservesFiniteProducts_op`

English:
lemma preservesFiniteProducts_op
  given: (F : C ⥤ D) [PreservesFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures preservesLimitsOfShape_op
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteProducts_op
  条件: (F : C ⥤ D) [保持FiniteCoproducts F]
  证明: by
    apply +allowSynthFailures preservesLimitsOfShape_op
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_of_equiv, preservesLimitsOfShape_op
-/
lemma preservesFiniteProducts_op (F : C ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.op where
  preserves n := by
    apply +allowSynthFailures preservesLimitsOfShape_op
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `preservesFiniteProducts_leftOp` / 引理 `preservesFiniteProducts_leftOp`

English:
lemma preservesFiniteProducts_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures preservesLimitsOfShape_leftOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteProducts_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持FiniteCoproducts F]
  证明: by
    apply +allowSynthFailures preservesLimitsOfShape_leftOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_of_equiv, preservesLimitsOfShape_leftOp
-/
lemma preservesFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_leftOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `preservesFiniteProducts_rightOp` / 引理 `preservesFiniteProducts_rightOp`

English:
lemma preservesFiniteProducts_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures preservesLimitsOfShape_rightOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteProducts_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持FiniteCoproducts F]
  证明: by
    apply +allowSynthFailures preservesLimitsOfShape_rightOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_of_equiv, preservesLimitsOfShape_rightOp
-/
lemma preservesFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_rightOp
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `preservesFiniteProducts_unop` / 引理 `preservesFiniteProducts_unop`

English:
lemma preservesFiniteProducts_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures preservesLimitsOfShape_unop
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteProducts_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持FiniteCoproducts F]
  证明: by
    apply +allowSynthFailures preservesLimitsOfShape_unop
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_of_equiv, preservesLimitsOfShape_unop
-/
lemma preservesFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteCoproducts F] :
    PreservesFiniteProducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesLimitsOfShape_unop
    exact preservesColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `preservesFiniteCoproducts_op` / 引理 `preservesFiniteCoproducts_op`

English:
lemma preservesFiniteCoproducts_op
  given: (F : C ⥤ D) [PreservesFiniteProducts F]
  proof: by
    apply +allowSynthFailures preservesColimitsOfShape_op
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteCoproducts_op
  条件: (F : C ⥤ D) [保持FiniteProducts F]
  证明: by
    apply +allowSynthFailures preservesColimitsOfShape_op
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_op, preservesLimitsOfShape_of_equiv
-/
lemma preservesFiniteCoproducts_op (F : C ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.op where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_op
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `preservesFiniteCoproducts_leftOp` / 引理 `preservesFiniteCoproducts_leftOp`

English:
lemma preservesFiniteCoproducts_leftOp
  given: (F : C ⥤ Dᵒᵖ) [PreservesFiniteProducts F]
  proof: by
    apply +allowSynthFailures preservesColimitsOfShape_leftOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteCoproducts_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [保持FiniteProducts F]
  证明: by
    apply +allowSynthFailures preservesColimitsOfShape_leftOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_leftOp, preservesLimitsOfShape_of_equiv
-/
lemma preservesFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.leftOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_leftOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `preservesFiniteCoproducts_rightOp` / 引理 `preservesFiniteCoproducts_rightOp`

English:
lemma preservesFiniteCoproducts_rightOp
  given: (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F]
  proof: by
    apply +allowSynthFailures preservesColimitsOfShape_rightOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteCoproducts_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [保持FiniteProducts F]
  证明: by
    apply +allowSynthFailures preservesColimitsOfShape_rightOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_rightOp, preservesLimitsOfShape_of_equiv
-/
lemma preservesFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.rightOp where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_rightOp
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `preservesFiniteCoproducts_unop` / 引理 `preservesFiniteCoproducts_unop`

English:
lemma preservesFiniteCoproducts_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteProducts F]
  proof: by
    apply +allowSynthFailures preservesColimitsOfShape_unop
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 preservesFiniteCoproducts_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [保持FiniteProducts F]
  证明: by
    apply +allowSynthFailures preservesColimitsOfShape_unop
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, preservesColimitsOfShape_unop, preservesLimitsOfShape_of_equiv
-/
lemma preservesFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteProducts F] :
    PreservesFiniteCoproducts F.unop where
  preserves _ := by
    apply +allowSynthFailures preservesColimitsOfShape_unop
    exact preservesLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsLimit_op` / 引理 `reflectsLimit_op`

English:
lemma reflectsLimit_op
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsColimit K.leftOp F]
  proof: ⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F (isColimitCoconeLeftOpOfCone _ hc)⟩

中文:
引理 reflectsLimit_op
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [反映余极限 K.leftOp F]
  证明: ⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F (isColimitCoconeLeftOpOfCone _ hc)⟩

Depends on / 依赖: isColimitCoconeLeftOpOfCone, isColimitOfReflects, isLimitOfCoconeLeftOpOfCone
-/
lemma reflectsLimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsColimit K.leftOp F] :
    ReflectsLimit K F.op where
  reflects {_} hc :=
⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F (isColimitCoconeLeftOpOfCone _ hc)⟩

/--
lemma `reflectsLimit_of_op` / 引理 `reflectsLimit_of_op`

English:
lemma reflectsLimit_of_op
  given: (K : J ⥤ C) (F : C ⥤ D) [ReflectsColimit K.op F.op]
  proof: ⟨isLimitOfOp (isColimitOfReflects F.op (IsLimit.op hc))⟩

中文:
引理 reflectsLimit_of_op
  条件: (K : J ⥤ C) (F : C ⥤ D) [反映余极限 K.op F.op]
  证明: ⟨isLimitOfOp (isColimitOfReflects F.op (IsLimit.op hc))⟩

Depends on / 依赖: F.op, IsLimit, IsLimit.op, isColimitOfReflects, isLimitOfOp
-/
lemma reflectsLimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsColimit K.op F.op] :
    ReflectsLimit K F where
  reflects {_} hc := ⟨isLimitOfOp (isColimitOfReflects F.op (IsLimit.op hc))⟩

/--
lemma `reflectsLimit_leftOp` / 引理 `reflectsLimit_leftOp`

English:
lemma reflectsLimit_leftOp
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F]
  proof: ⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F hc.op⟩

中文:
引理 reflectsLimit_leftOp
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [反映余极限 K.leftOp F]
  证明: ⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F hc.op⟩

Depends on / 依赖: hc.op, isColimitOfReflects, isLimitOfCoconeLeftOpOfCone
-/
lemma reflectsLimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F] :
    ReflectsLimit K F.leftOp where
  reflects {_} hc :=
⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F hc.op⟩

/--
lemma `reflectsLimit_of_leftOp` / 引理 `reflectsLimit_of_leftOp`

English:
lemma reflectsLimit_of_leftOp
  given: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.op F.leftOp]
  proof: ⟨isLimitOfOp
      isColimitOfReflects F.leftOp (isColimitOfConeRightOpOfCocone _ hc)⟩

中文:
引理 reflectsLimit_of_leftOp
  条件: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [反映余极限 K.op F.leftOp]
  证明: ⟨isLimitOfOp
      isColimitOfReflects F.leftOp (isColimitOfConeRightOpOfCocone _ hc)⟩

Depends on / 依赖: F.leftOp, isColimitOfConeRightOpOfCocone, isColimitOfReflects, isLimitOfOp, leftOp
-/
lemma reflectsLimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsColimit K.op F.leftOp] :
    ReflectsLimit K F where
  reflects {_} hc :=
⟨isLimitOfOp
      isColimitOfReflects F.leftOp (isColimitOfConeRightOpOfCocone _ hc)⟩

/--
lemma `reflectsLimit_rightOp` / 引理 `reflectsLimit_rightOp`

English:
lemma reflectsLimit_rightOp
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.op F]
  proof: ⟨isLimitOfOp isColimitOfReflects F isColimitOfConeRightOpOfCocone _ hc⟩

中文:
引理 reflectsLimit_rightOp
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [反映余极限 K.op F]
  证明: ⟨isLimitOfOp isColimitOfReflects F isColimitOfConeRightOpOfCocone _ hc⟩

Depends on / 依赖: isColimitOfConeRightOpOfCocone, isColimitOfReflects, isLimitOfOp
-/
lemma reflectsLimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.op F] :
    ReflectsLimit K F.rightOp where
  reflects {_} hc :=
⟨isLimitOfOp isColimitOfReflects F isColimitOfConeRightOpOfCocone _ hc⟩

/--
lemma `reflectsLimit_of_rightOp` / 引理 `reflectsLimit_of_rightOp`

English:
lemma reflectsLimit_of_rightOp
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.leftOp F.rightOp]
  proof: ⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F.rightOp
      isColimitOfConeUnopOfCocone _ hc⟩

中文:
引理 reflectsLimit_of_rightOp
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [反映余极限 K.leftOp F.rightOp]
  证明: ⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F.rightOp
      isColimitOfConeUnopOfCocone _ hc⟩

Depends on / 依赖: F.rightOp, isColimitOfConeUnopOfCocone, isColimitOfReflects, isLimitOfCoconeLeftOpOfCone, rightOp
-/
lemma reflectsLimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsColimit K.leftOp F.rightOp] :
    ReflectsLimit K F where
  reflects {_} hc :=
⟨isLimitOfCoconeLeftOpOfCone _ isColimitOfReflects F.rightOp
      isColimitOfConeUnopOfCocone _ hc⟩

/--
lemma `reflectsLimit_unop` / 引理 `reflectsLimit_unop`

English:
lemma reflectsLimit_unop
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.op F]
  proof: ⟨isLimitOfOp (isColimitOfReflects F hc.op)⟩

中文:
引理 reflectsLimit_unop
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映余极限 K.op F]
  证明: ⟨isLimitOfOp (isColimitOfReflects F hc.op)⟩

Depends on / 依赖: hc.op, isColimitOfReflects, isLimitOfOp
-/
lemma reflectsLimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.op F] :
    ReflectsLimit K F.unop where
  reflects {_} hc := ⟨isLimitOfOp (isColimitOfReflects F hc.op)⟩

/--
lemma `reflectsLimit_of_unop` / 引理 `reflectsLimit_of_unop`

English:
lemma reflectsLimit_of_unop
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F.unop]
  proof: ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfReflects F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

中文:
引理 reflectsLimit_of_unop
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映余极限 K.leftOp F.unop]
  证明: ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfReflects F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

Depends on / 依赖: F.unop, isColimitCoconeLeftOpOfCone, isColimitOfReflects, isLimitOfCoconeLeftOpOfCone
-/
lemma reflectsLimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimit K.leftOp F.unop] :
    ReflectsLimit K F where
  reflects {_} hc :=
    ⟨isLimitOfCoconeLeftOpOfCone _ (isColimitOfReflects F.unop (isColimitCoconeLeftOpOfCone _ hc))⟩

/--
lemma `reflectsColimit_op` / 引理 `reflectsColimit_op`

English:
lemma reflectsColimit_op
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsLimit K.leftOp F]
  proof: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitConeLeftOpOfCocone _ hc))⟩

中文:
引理 reflectsColimit_op
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [反映极限 K.leftOp F]
  证明: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitConeLeftOpOfCocone _ hc))⟩

Depends on / 依赖: isColimitOfConeLeftOpOfCocone, isLimitConeLeftOpOfCocone, isLimitOfReflects
-/
lemma reflectsColimit_op (K : J ⥤ Cᵒᵖ) (F : C ⥤ D) [ReflectsLimit K.leftOp F] :
    ReflectsColimit K F.op where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitConeLeftOpOfCocone _ hc))⟩

/--
lemma `reflectsColimit_of_op` / 引理 `reflectsColimit_of_op`

English:
lemma reflectsColimit_of_op
  given: (K : J ⥤ C) (F : C ⥤ D) [ReflectsLimit K.op F.op]
  proof: ⟨isColimitOfOp (isLimitOfReflects F.op (IsColimit.op hc))⟩

中文:
引理 reflectsColimit_of_op
  条件: (K : J ⥤ C) (F : C ⥤ D) [反映极限 K.op F.op]
  证明: ⟨isColimitOfOp (isLimitOfReflects F.op (IsColimit.op hc))⟩

Depends on / 依赖: F.op, IsColimit, IsColimit.op, isColimitOfOp, isLimitOfReflects
-/
lemma reflectsColimit_of_op (K : J ⥤ C) (F : C ⥤ D) [ReflectsLimit K.op F.op] :
    ReflectsColimit K F where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F.op (IsColimit.op hc))⟩

/--
lemma `reflectsColimit_leftOp` / 引理 `reflectsColimit_leftOp`

English:
lemma reflectsColimit_leftOp
  given: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F]
  proof: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitOfCoconeUnopOfCone _ hc))⟩

中文:
引理 reflectsColimit_leftOp
  条件: (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [反映极限 K.leftOp F]
  证明: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitOfCoconeUnopOfCone _ hc))⟩

Depends on / 依赖: isColimitOfConeLeftOpOfCocone, isLimitOfCoconeUnopOfCone, isLimitOfReflects
-/
lemma reflectsColimit_leftOp (K : J ⥤ Cᵒᵖ) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F] :
    ReflectsColimit K F.leftOp where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F (isLimitOfCoconeUnopOfCone _ hc))⟩

/--
lemma `reflectsColimit_of_leftOp` / 引理 `reflectsColimit_of_leftOp`

English:
lemma reflectsColimit_of_leftOp
  given: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.op F.leftOp]
  proof: ⟨isColimitOfOp (isLimitOfReflects F.leftOp <| isLimitOfCoconeRightOpOfCone _ hc)⟩

中文:
引理 reflectsColimit_of_leftOp
  条件: (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [反映极限 K.op F.leftOp]
  证明: ⟨isColimitOfOp (isLimitOfReflects F.leftOp <| isLimitOfCoconeRightOpOfCone _ hc)⟩

Depends on / 依赖: F.leftOp, isColimitOfOp, isLimitOfCoconeRightOpOfCone, isLimitOfReflects, leftOp
-/
lemma reflectsColimit_of_leftOp (K : J ⥤ C) (F : C ⥤ Dᵒᵖ) [ReflectsLimit K.op F.leftOp] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfOp (isLimitOfReflects F.leftOp <| isLimitOfCoconeRightOpOfCone _ hc)⟩

/--
lemma `reflectsColimit_rightOp` / 引理 `reflectsColimit_rightOp`

English:
lemma reflectsColimit_rightOp
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.op F]
  proof: ⟨isColimitOfOp (isLimitOfReflects F <| isLimitOfCoconeRightOpOfCone _ hc)⟩

中文:
引理 reflectsColimit_rightOp
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [反映极限 K.op F]
  证明: ⟨isColimitOfOp (isLimitOfReflects F <| isLimitOfCoconeRightOpOfCone _ hc)⟩

Depends on / 依赖: isColimitOfOp, isLimitOfCoconeRightOpOfCone, isLimitOfReflects
-/
lemma reflectsColimit_rightOp (K : J ⥤ C) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.op F] :
    ReflectsColimit K F.rightOp where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F <| isLimitOfCoconeRightOpOfCone _ hc)⟩

/--
lemma `reflectsColimit_of_rightOp` / 引理 `reflectsColimit_of_rightOp`

English:
lemma reflectsColimit_of_rightOp
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.leftOp F.rightOp]
  proof: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.rightOp hc.op)⟩

中文:
引理 reflectsColimit_of_rightOp
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [反映极限 K.leftOp F.rightOp]
  证明: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.rightOp hc.op)⟩

Depends on / 依赖: F.rightOp, hc.op, isColimitOfConeLeftOpOfCocone, isLimitOfReflects, rightOp
-/
lemma reflectsColimit_of_rightOp (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ D) [ReflectsLimit K.leftOp F.rightOp] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.rightOp hc.op)⟩

/--
lemma `reflectsColimit_unop` / 引理 `reflectsColimit_unop`

English:
lemma reflectsColimit_unop
  given: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.op F]
  proof: ⟨isColimitOfOp (isLimitOfReflects F hc.op)⟩

中文:
引理 reflectsColimit_unop
  条件: (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映极限 K.op F]
  证明: ⟨isColimitOfOp (isLimitOfReflects F hc.op)⟩

Depends on / 依赖: hc.op, isColimitOfOp, isLimitOfReflects
-/
lemma reflectsColimit_unop (K : J ⥤ C) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.op F] :
    ReflectsColimit K F.unop where
  reflects {_} hc := ⟨isColimitOfOp (isLimitOfReflects F hc.op)⟩

/--
lemma `reflectsColimit_of_unop` / 引理 `reflectsColimit_of_unop`

English:
lemma reflectsColimit_of_unop
  given: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F.unop]
  proof: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

中文:
引理 reflectsColimit_of_unop
  条件: (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映极限 K.leftOp F.unop]
  证明: ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

Depends on / 依赖: F.unop, isColimitOfConeLeftOpOfCocone, isLimitConeLeftOpOfCocone, isLimitOfReflects
-/
lemma reflectsColimit_of_unop (K : J ⥤ Cᵒᵖ) (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimit K.leftOp F.unop] :
    ReflectsColimit K F where
  reflects {_} hc :=
    ⟨isColimitOfConeLeftOpOfCocone _ (isLimitOfReflects F.unop (isLimitConeLeftOpOfCocone _ hc))⟩

section

variable (J)

/--
lemma `reflectsLimitsOfShape_op` / 引理 `reflectsLimitsOfShape_op`

English:
lemma reflectsLimitsOfShape_op
  given: (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F]
  proof: reflectsLimit_op K F

中文:
引理 reflectsLimitsOfShape_op
  条件: (F : C ⥤ D) [反映形状余极限 Jᵒᵖ F]
  证明: reflectsLimit_op K F

Depends on / 依赖: reflectsLimit_op
-/
lemma reflectsLimitsOfShape_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.op where reflectsLimit {K} := reflectsLimit_op K F

/--
lemma `reflectsLimitsOfShape_leftOp` / 引理 `reflectsLimitsOfShape_leftOp`

English:
lemma reflectsLimitsOfShape_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F]
  proof: reflectsLimit_leftOp K F

中文:
引理 reflectsLimitsOfShape_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [反映形状余极限 Jᵒᵖ F]
  证明: reflectsLimit_leftOp K F

Depends on / 依赖: reflectsLimit_leftOp
-/
lemma reflectsLimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.leftOp where reflectsLimit {K} := reflectsLimit_leftOp K F

/--
lemma `reflectsLimitsOfShape_rightOp` / 引理 `reflectsLimitsOfShape_rightOp`

English:
lemma reflectsLimitsOfShape_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F]
  proof: reflectsLimit_rightOp K F

中文:
引理 reflectsLimitsOfShape_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [反映形状余极限 Jᵒᵖ F]
  证明: reflectsLimit_rightOp K F

Depends on / 依赖: reflectsLimit_rightOp
-/
lemma reflectsLimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.rightOp where reflectsLimit {K} := reflectsLimit_rightOp K F

/--
lemma `reflectsLimitsOfShape_unop` / 引理 `reflectsLimitsOfShape_unop`

English:
lemma reflectsLimitsOfShape_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F]
  proof: reflectsLimit_unop K F

中文:
引理 reflectsLimitsOfShape_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映形状余极限 Jᵒᵖ F]
  证明: reflectsLimit_unop K F

Depends on / 依赖: reflectsLimit_unop
-/
lemma reflectsLimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F] :
    ReflectsLimitsOfShape J F.unop where reflectsLimit {K} := reflectsLimit_unop K F

/--
lemma `reflectsColimitsOfShape_op` / 引理 `reflectsColimitsOfShape_op`

English:
lemma reflectsColimitsOfShape_op
  given: (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F]
  proof: reflectsColimit_op K F

中文:
引理 reflectsColimitsOfShape_op
  条件: (F : C ⥤ D) [反映形状极限 Jᵒᵖ F]
  证明: reflectsColimit_op K F

Depends on / 依赖: reflectsColimit_op
-/
lemma reflectsColimitsOfShape_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.op where reflectsColimit {K} := reflectsColimit_op K F

/--
lemma `reflectsColimitsOfShape_leftOp` / 引理 `reflectsColimitsOfShape_leftOp`

English:
lemma reflectsColimitsOfShape_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F]
  proof: reflectsColimit_leftOp K F

中文:
引理 reflectsColimitsOfShape_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [反映形状极限 Jᵒᵖ F]
  证明: reflectsColimit_leftOp K F

Depends on / 依赖: reflectsColimit_leftOp
-/
lemma reflectsColimitsOfShape_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.leftOp where reflectsColimit {K} := reflectsColimit_leftOp K F

/--
lemma `reflectsColimitsOfShape_rightOp` / 引理 `reflectsColimitsOfShape_rightOp`

English:
lemma reflectsColimitsOfShape_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F]
  proof: reflectsColimit_rightOp K F

中文:
引理 reflectsColimitsOfShape_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [反映形状极限 Jᵒᵖ F]
  证明: reflectsColimit_rightOp K F

Depends on / 依赖: reflectsColimit_rightOp
-/
lemma reflectsColimitsOfShape_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.rightOp where reflectsColimit {K} := reflectsColimit_rightOp K F

/--
lemma `reflectsColimitsOfShape_unop` / 引理 `reflectsColimitsOfShape_unop`

English:
lemma reflectsColimitsOfShape_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F]
  proof: reflectsColimit_unop K F

中文:
引理 reflectsColimitsOfShape_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映形状极限 Jᵒᵖ F]
  证明: reflectsColimit_unop K F

Depends on / 依赖: reflectsColimit_unop
-/
lemma reflectsColimitsOfShape_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F] :
    ReflectsColimitsOfShape J F.unop where reflectsColimit {K} := reflectsColimit_unop K F

/--
lemma `reflectsLimitsOfShape_of_op` / 引理 `reflectsLimitsOfShape_of_op`

English:
lemma reflectsLimitsOfShape_of_op
  given: (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op]
  proof: reflectsLimit_of_op K F

中文:
引理 reflectsLimitsOfShape_of_op
  条件: (F : C ⥤ D) [反映形状余极限 Jᵒᵖ F.op]
  证明: reflectsLimit_of_op K F

Depends on / 依赖: reflectsLimit_of_op
-/
lemma reflectsLimitsOfShape_of_op (F : C ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.op] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_op K F

/--
lemma `reflectsLimitsOfShape_of_leftOp` / 引理 `reflectsLimitsOfShape_of_leftOp`

English:
lemma reflectsLimitsOfShape_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.leftOp]
  proof: reflectsLimit_of_leftOp K F

中文:
引理 reflectsLimitsOfShape_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [反映形状余极限 Jᵒᵖ F.leftOp]
  证明: reflectsLimit_of_leftOp K F

Depends on / 依赖: reflectsLimit_of_leftOp
-/
lemma reflectsLimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.leftOp] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_leftOp K F

/--
lemma `reflectsLimitsOfShape_of_rightOp` / 引理 `reflectsLimitsOfShape_of_rightOp`

English:
lemma reflectsLimitsOfShape_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.rightOp]
  proof: reflectsLimit_of_rightOp K F

中文:
引理 reflectsLimitsOfShape_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [反映形状余极限 Jᵒᵖ F.rightOp]
  证明: reflectsLimit_of_rightOp K F

Depends on / 依赖: reflectsLimit_of_rightOp
-/
lemma reflectsLimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfShape Jᵒᵖ F.rightOp] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_rightOp K F

/--
lemma `reflectsLimitsOfShape_of_unop` / 引理 `reflectsLimitsOfShape_of_unop`

English:
lemma reflectsLimitsOfShape_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.unop]
  proof: reflectsLimit_of_unop K F

中文:
引理 reflectsLimitsOfShape_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映形状余极限 Jᵒᵖ F.unop]
  证明: reflectsLimit_of_unop K F

Depends on / 依赖: reflectsLimit_of_unop
-/
lemma reflectsLimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfShape Jᵒᵖ F.unop] :
    ReflectsLimitsOfShape J F where reflectsLimit {K} := reflectsLimit_of_unop K F

/--
lemma `reflectsColimitsOfShape_of_op` / 引理 `reflectsColimitsOfShape_of_op`

English:
lemma reflectsColimitsOfShape_of_op
  given: (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op]
  proof: reflectsColimit_of_op K F

中文:
引理 reflectsColimitsOfShape_of_op
  条件: (F : C ⥤ D) [反映形状极限 Jᵒᵖ F.op]
  证明: reflectsColimit_of_op K F

Depends on / 依赖: reflectsColimit_of_op
-/
lemma reflectsColimitsOfShape_of_op (F : C ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.op] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_op K F

/--
lemma `reflectsColimitsOfShape_of_leftOp` / 引理 `reflectsColimitsOfShape_of_leftOp`

English:
lemma reflectsColimitsOfShape_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.leftOp]
  proof: reflectsColimit_of_leftOp K F

中文:
引理 reflectsColimitsOfShape_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [反映形状极限 Jᵒᵖ F.leftOp]
  证明: reflectsColimit_of_leftOp K F

Depends on / 依赖: reflectsColimit_of_leftOp
-/
lemma reflectsColimitsOfShape_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.leftOp] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_leftOp K F

/--
lemma `reflectsColimitsOfShape_of_rightOp` / 引理 `reflectsColimitsOfShape_of_rightOp`

English:
lemma reflectsColimitsOfShape_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.rightOp]
  proof: reflectsColimit_of_rightOp K F

中文:
引理 reflectsColimitsOfShape_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [反映形状极限 Jᵒᵖ F.rightOp]
  证明: reflectsColimit_of_rightOp K F

Depends on / 依赖: reflectsColimit_of_rightOp
-/
lemma reflectsColimitsOfShape_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfShape Jᵒᵖ F.rightOp] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_rightOp K F

/--
lemma `reflectsColimitsOfShape_of_unop` / 引理 `reflectsColimitsOfShape_of_unop`

English:
lemma reflectsColimitsOfShape_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.unop]
  proof: reflectsColimit_of_unop K F

中文:
引理 reflectsColimitsOfShape_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [反映形状极限 Jᵒᵖ F.unop]
  证明: reflectsColimit_of_unop K F

Depends on / 依赖: reflectsColimit_of_unop
-/
lemma reflectsColimitsOfShape_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfShape Jᵒᵖ F.unop] :
    ReflectsColimitsOfShape J F where reflectsColimit {K} := reflectsColimit_of_unop K F

end

/--
lemma `reflectsLimitsOfSize_op` / 引理 `reflectsLimitsOfSize_op`

English:
lemma reflectsLimitsOfSize_op
  given: (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F]
  proof: reflectsLimitsOfShape_op _ _

中文:
引理 reflectsLimitsOfSize_op
  条件: (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F]
  证明: reflectsLimitsOfShape_op _ _

Depends on / 依赖: reflectsLimitsOfShape_op
-/
lemma reflectsLimitsOfSize_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.op where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_op _ _

/--
lemma `reflectsLimitsOfSize_leftOp` / 引理 `reflectsLimitsOfSize_leftOp`

English:
lemma reflectsLimitsOfSize_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F]
  proof: reflectsLimitsOfShape_leftOp _ _

中文:
引理 reflectsLimitsOfSize_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F]
  证明: reflectsLimitsOfShape_leftOp _ _

Depends on / 依赖: reflectsLimitsOfShape_leftOp
-/
lemma reflectsLimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.leftOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_leftOp _ _

/--
lemma `reflectsLimitsOfSize_rightOp` / 引理 `reflectsLimitsOfSize_rightOp`

English:
lemma reflectsLimitsOfSize_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F]
  proof: reflectsLimitsOfShape_rightOp _ _

中文:
引理 reflectsLimitsOfSize_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F]
  证明: reflectsLimitsOfShape_rightOp _ _

Depends on / 依赖: reflectsLimitsOfShape_rightOp
-/
lemma reflectsLimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.rightOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_rightOp _ _

/--
lemma `reflectsLimitsOfSize_unop` / 引理 `reflectsLimitsOfSize_unop`

English:
lemma reflectsLimitsOfSize_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F]
  proof: reflectsLimitsOfShape_unop _ _

中文:
引理 reflectsLimitsOfSize_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F]
  证明: reflectsLimitsOfShape_unop _ _

Depends on / 依赖: reflectsLimitsOfShape_unop
-/
lemma reflectsLimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsLimitsOfSize.{w, w'} F.unop where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_unop _ _

/--
lemma `reflectsColimitsOfSize_op` / 引理 `reflectsColimitsOfSize_op`

English:
lemma reflectsColimitsOfSize_op
  given: (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F]
  proof: reflectsColimitsOfShape_op _ _

中文:
引理 reflectsColimitsOfSize_op
  条件: (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F]
  证明: reflectsColimitsOfShape_op _ _

Depends on / 依赖: reflectsColimitsOfShape_op
-/
lemma reflectsColimitsOfSize_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.op where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_op _ _

/--
lemma `reflectsColimitsOfSize_leftOp` / 引理 `reflectsColimitsOfSize_leftOp`

English:
lemma reflectsColimitsOfSize_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F]
  proof: reflectsColimitsOfShape_leftOp _ _

中文:
引理 reflectsColimitsOfSize_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F]
  证明: reflectsColimitsOfShape_leftOp _ _

Depends on / 依赖: reflectsColimitsOfShape_leftOp
-/
lemma reflectsColimitsOfSize_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.leftOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_leftOp _ _

/--
lemma `reflectsColimitsOfSize_rightOp` / 引理 `reflectsColimitsOfSize_rightOp`

English:
lemma reflectsColimitsOfSize_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F]
  proof: reflectsColimitsOfShape_rightOp _ _

中文:
引理 reflectsColimitsOfSize_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F]
  证明: reflectsColimitsOfShape_rightOp _ _

Depends on / 依赖: reflectsColimitsOfShape_rightOp
-/
lemma reflectsColimitsOfSize_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.rightOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_rightOp _ _

/--
lemma `reflectsColimitsOfSize_unop` / 引理 `reflectsColimitsOfSize_unop`

English:
lemma reflectsColimitsOfSize_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F]
  proof: reflectsColimitsOfShape_unop _ _

中文:
引理 reflectsColimitsOfSize_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F]
  证明: reflectsColimitsOfShape_unop _ _

Depends on / 依赖: reflectsColimitsOfShape_unop
-/
lemma reflectsColimitsOfSize_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} F.unop where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_unop _ _

/--
lemma `reflectsLimitsOfSize_of_op` / 引理 `reflectsLimitsOfSize_of_op`

English:
lemma reflectsLimitsOfSize_of_op
  given: (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.op]
  proof: reflectsLimitsOfShape_of_op _ _

中文:
引理 reflectsLimitsOfSize_of_op
  条件: (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.op]
  证明: reflectsLimitsOfShape_of_op _ _

Depends on / 依赖: reflectsLimitsOfShape_of_op
-/
lemma reflectsLimitsOfSize_of_op (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.op] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_op _ _

/--
lemma `reflectsLimitsOfSize_of_leftOp` / 引理 `reflectsLimitsOfSize_of_leftOp`

English:
lemma reflectsLimitsOfSize_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.leftOp]
  proof: reflectsLimitsOfShape_of_leftOp _ _

中文:
引理 reflectsLimitsOfSize_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.leftOp]
  证明: reflectsLimitsOfShape_of_leftOp _ _

Depends on / 依赖: reflectsLimitsOfShape_of_leftOp
-/
lemma reflectsLimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.leftOp] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_leftOp _ _

/--
lemma `reflectsLimitsOfSize_of_rightOp` / 引理 `reflectsLimitsOfSize_of_rightOp`

English:
lemma reflectsLimitsOfSize_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.rightOp]
  proof: reflectsLimitsOfShape_of_rightOp _ _

中文:
引理 reflectsLimitsOfSize_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.rightOp]
  证明: reflectsLimitsOfShape_of_rightOp _ _

Depends on / 依赖: reflectsLimitsOfShape_of_rightOp
-/
lemma reflectsLimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimitsOfSize.{w, w'} F.rightOp] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_rightOp _ _

/--
lemma `reflectsLimitsOfSize_of_unop` / 引理 `reflectsLimitsOfSize_of_unop`

English:
lemma reflectsLimitsOfSize_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.unop]
  proof: reflectsLimitsOfShape_of_unop _ _

中文:
引理 reflectsLimitsOfSize_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.unop]
  证明: reflectsLimitsOfShape_of_unop _ _

Depends on / 依赖: reflectsLimitsOfShape_of_unop
-/
lemma reflectsLimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimitsOfSize.{w, w'} F.unop] :
    ReflectsLimitsOfSize.{w, w'} F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_unop _ _

/--
lemma `reflectsColimitsOfSize_of_op` / 引理 `reflectsColimitsOfSize_of_op`

English:
lemma reflectsColimitsOfSize_of_op
  given: (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.op]
  proof: reflectsColimitsOfShape_of_op _ _

中文:
引理 reflectsColimitsOfSize_of_op
  条件: (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.op]
  证明: reflectsColimitsOfShape_of_op _ _

Depends on / 依赖: reflectsColimitsOfShape_of_op
-/
lemma reflectsColimitsOfSize_of_op (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.op] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_op _ _

/--
lemma `reflectsColimitsOfSize_of_leftOp` / 引理 `reflectsColimitsOfSize_of_leftOp`

English:
lemma reflectsColimitsOfSize_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.leftOp]
  proof: reflectsColimitsOfShape_of_leftOp _ _

中文:
引理 reflectsColimitsOfSize_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.leftOp]
  证明: reflectsColimitsOfShape_of_leftOp _ _

Depends on / 依赖: reflectsColimitsOfShape_of_leftOp
-/
lemma reflectsColimitsOfSize_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.leftOp] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_leftOp _ _

/--
lemma `reflectsColimitsOfSize_of_rightOp` / 引理 `reflectsColimitsOfSize_of_rightOp`

English:
lemma reflectsColimitsOfSize_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.rightOp]
  proof: reflectsColimitsOfShape_of_rightOp _ _

中文:
引理 reflectsColimitsOfSize_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.rightOp]
  证明: reflectsColimitsOfShape_of_rightOp _ _

Depends on / 依赖: reflectsColimitsOfShape_of_rightOp
-/
lemma reflectsColimitsOfSize_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimitsOfSize.{w, w'} F.rightOp] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_rightOp _ _

/--
lemma `reflectsColimitsOfSize_of_unop` / 引理 `reflectsColimitsOfSize_of_unop`

English:
lemma reflectsColimitsOfSize_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.unop]
  proof: reflectsColimitsOfShape_of_unop _ _

中文:
引理 reflectsColimitsOfSize_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.unop]
  证明: reflectsColimitsOfShape_of_unop _ _

Depends on / 依赖: reflectsColimitsOfShape_of_unop
-/
lemma reflectsColimitsOfSize_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimitsOfSize.{w, w'} F.unop] :
    ReflectsColimitsOfSize.{w, w'} F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_unop _ _

/--
lemma `reflectsLimits_op` / 引理 `reflectsLimits_op`

English:
lemma reflectsLimits_op
  given: (F : C ⥤ D) [ReflectsColimits F]
  statement: ReflectsLimits F.op where
  proof: reflectsLimitsOfShape_op _ _

中文:
引理 reflectsLimits_op
  条件: (F : C ⥤ D) [ReflectsColimits F]
  结论: ReflectsLimits F.op where
  证明: reflectsLimitsOfShape_op _ _

Depends on / 依赖: reflectsLimitsOfShape_op
-/
lemma reflectsLimits_op (F : C ⥤ D) [ReflectsColimits F] : ReflectsLimits F.op where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_op _ _

/--
lemma `reflectsLimits_leftOp` / 引理 `reflectsLimits_leftOp`

English:
lemma reflectsLimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsColimits F]
  statement: ReflectsLimits F.leftOp where
  proof: reflectsLimitsOfShape_leftOp _ _

中文:
引理 reflectsLimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsColimits F]
  结论: ReflectsLimits F.leftOp where
  证明: reflectsLimitsOfShape_leftOp _ _

Depends on / 依赖: reflectsLimitsOfShape_leftOp
-/
lemma reflectsLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits F.leftOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_leftOp _ _

/--
lemma `reflectsLimits_rightOp` / 引理 `reflectsLimits_rightOp`

English:
lemma reflectsLimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsColimits F]
  statement: ReflectsLimits F.rightOp where
  proof: reflectsLimitsOfShape_rightOp _ _

中文:
引理 reflectsLimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsColimits F]
  结论: ReflectsLimits F.rightOp where
  证明: reflectsLimitsOfShape_rightOp _ _

Depends on / 依赖: reflectsLimitsOfShape_rightOp
-/
lemma reflectsLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F] : ReflectsLimits F.rightOp where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_rightOp _ _

/--
lemma `reflectsLimits_unop` / 引理 `reflectsLimits_unop`

English:
lemma reflectsLimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F]
  statement: ReflectsLimits F.unop where
  proof: reflectsLimitsOfShape_unop _ _

中文:
引理 reflectsLimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F]
  结论: ReflectsLimits F.unop where
  证明: reflectsLimitsOfShape_unop _ _

Depends on / 依赖: reflectsLimitsOfShape_unop
-/
lemma reflectsLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F] : ReflectsLimits F.unop where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_unop _ _

/--
lemma `reflectsColimits_op` / 引理 `reflectsColimits_op`

English:
lemma reflectsColimits_op
  given: (F : C ⥤ D) [ReflectsLimits F]
  statement: ReflectsColimits F.op where
  proof: reflectsColimitsOfShape_op _ _

中文:
引理 reflectsColimits_op
  条件: (F : C ⥤ D) [ReflectsLimits F]
  结论: ReflectsColimits F.op where
  证明: reflectsColimitsOfShape_op _ _

Depends on / 依赖: reflectsColimitsOfShape_op
-/
lemma reflectsColimits_op (F : C ⥤ D) [ReflectsLimits F] : ReflectsColimits F.op where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_op _ _

/--
lemma `reflectsColimits_leftOp` / 引理 `reflectsColimits_leftOp`

English:
lemma reflectsColimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsLimits F]
  statement: ReflectsColimits F.leftOp where
  proof: reflectsColimitsOfShape_leftOp _ _

中文:
引理 reflectsColimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsLimits F]
  结论: ReflectsColimits F.leftOp where
  证明: reflectsColimitsOfShape_leftOp _ _

Depends on / 依赖: reflectsColimitsOfShape_leftOp
-/
lemma reflectsColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimits F.leftOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_leftOp _ _

/--
lemma `reflectsColimits_rightOp` / 引理 `reflectsColimits_rightOp`

English:
lemma reflectsColimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsLimits F]
  proof: reflectsColimitsOfShape_rightOp _ _

中文:
引理 reflectsColimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsLimits F]
  证明: reflectsColimitsOfShape_rightOp _ _

Depends on / 依赖: reflectsColimitsOfShape_rightOp
-/
lemma reflectsColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F] :
    ReflectsColimits F.rightOp where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_rightOp _ _

/--
lemma `reflectsColimits_unop` / 引理 `reflectsColimits_unop`

English:
lemma reflectsColimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F]
  statement: ReflectsColimits F.unop where
  proof: reflectsColimitsOfShape_unop _ _

中文:
引理 reflectsColimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F]
  结论: ReflectsColimits F.unop where
  证明: reflectsColimitsOfShape_unop _ _

Depends on / 依赖: reflectsColimitsOfShape_unop
-/
lemma reflectsColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F] : ReflectsColimits F.unop where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_unop _ _

/--
lemma `reflectsLimits_of_op` / 引理 `reflectsLimits_of_op`

English:
lemma reflectsLimits_of_op
  given: (F : C ⥤ D) [ReflectsColimits F.op]
  statement: ReflectsLimits F where
  proof: reflectsLimitsOfShape_of_op _ _

中文:
引理 reflectsLimits_of_op
  条件: (F : C ⥤ D) [ReflectsColimits F.op]
  结论: ReflectsLimits F where
  证明: reflectsLimitsOfShape_of_op _ _

Depends on / 依赖: reflectsLimitsOfShape_of_op
-/
lemma reflectsLimits_of_op (F : C ⥤ D) [ReflectsColimits F.op] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_op _ _

/--
lemma `reflectsLimits_of_leftOp` / 引理 `reflectsLimits_of_leftOp`

English:
lemma reflectsLimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsColimits F.leftOp]
  statement: ReflectsLimits F where
  proof: reflectsLimitsOfShape_of_leftOp _ _

中文:
引理 reflectsLimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsColimits F.leftOp]
  结论: ReflectsLimits F where
  证明: reflectsLimitsOfShape_of_leftOp _ _

Depends on / 依赖: reflectsLimitsOfShape_of_leftOp
-/
lemma reflectsLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsColimits F.leftOp] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_leftOp _ _

/--
lemma `reflectsLimits_of_rightOp` / 引理 `reflectsLimits_of_rightOp`

English:
lemma reflectsLimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsColimits F.rightOp]
  proof: reflectsLimitsOfShape_of_rightOp _ _

中文:
引理 reflectsLimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsColimits F.rightOp]
  证明: reflectsLimitsOfShape_of_rightOp _ _

Depends on / 依赖: reflectsLimitsOfShape_of_rightOp
-/
lemma reflectsLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsColimits F.rightOp] :
    ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_rightOp _ _

/--
lemma `reflectsLimits_of_unop` / 引理 `reflectsLimits_of_unop`

English:
lemma reflectsLimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F.unop]
  statement: ReflectsLimits F where
  proof: reflectsLimitsOfShape_of_unop _ _

中文:
引理 reflectsLimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F.unop]
  结论: ReflectsLimits F where
  证明: reflectsLimitsOfShape_of_unop _ _

Depends on / 依赖: reflectsLimitsOfShape_of_unop
-/
lemma reflectsLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsColimits F.unop] : ReflectsLimits F where
  reflectsLimitsOfShape {_} _ := reflectsLimitsOfShape_of_unop _ _

/--
lemma `reflectsColimits_of_op` / 引理 `reflectsColimits_of_op`

English:
lemma reflectsColimits_of_op
  given: (F : C ⥤ D) [ReflectsLimits F.op]
  statement: ReflectsColimits F where
  proof: reflectsColimitsOfShape_of_op _ _

中文:
引理 reflectsColimits_of_op
  条件: (F : C ⥤ D) [ReflectsLimits F.op]
  结论: ReflectsColimits F where
  证明: reflectsColimitsOfShape_of_op _ _

Depends on / 依赖: reflectsColimitsOfShape_of_op
-/
lemma reflectsColimits_of_op (F : C ⥤ D) [ReflectsLimits F.op] : ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_op _ _

/--
lemma `reflectsColimits_of_leftOp` / 引理 `reflectsColimits_of_leftOp`

English:
lemma reflectsColimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsLimits F.leftOp]
  proof: reflectsColimitsOfShape_of_leftOp _ _

中文:
引理 reflectsColimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsLimits F.leftOp]
  证明: reflectsColimitsOfShape_of_leftOp _ _

Depends on / 依赖: reflectsColimitsOfShape_of_leftOp
-/
lemma reflectsColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsLimits F.leftOp] :
    ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_leftOp _ _

/--
lemma `reflectsColimits_of_rightOp` / 引理 `reflectsColimits_of_rightOp`

English:
lemma reflectsColimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsLimits F.rightOp]
  proof: reflectsColimitsOfShape_of_rightOp _ _

中文:
引理 reflectsColimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsLimits F.rightOp]
  证明: reflectsColimitsOfShape_of_rightOp _ _

Depends on / 依赖: reflectsColimitsOfShape_of_rightOp
-/
lemma reflectsColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsLimits F.rightOp] :
    ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_rightOp _ _

/--
lemma `reflectsColimits_of_unop` / 引理 `reflectsColimits_of_unop`

English:
lemma reflectsColimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F.unop]
  statement: ReflectsColimits F where
  proof: reflectsColimitsOfShape_of_unop _ _

中文:
引理 reflectsColimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F.unop]
  结论: ReflectsColimits F where
  证明: reflectsColimitsOfShape_of_unop _ _

Depends on / 依赖: reflectsColimitsOfShape_of_unop
-/
lemma reflectsColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsLimits F.unop] : ReflectsColimits F where
  reflectsColimitsOfShape {_} _ := reflectsColimitsOfShape_of_unop _ _

/--
lemma `reflectsFiniteLimits_op` / 引理 `reflectsFiniteLimits_op`

English:
lemma reflectsFiniteLimits_op
  given: (F : C ⥤ D) [ReflectsFiniteColimits F]
  proof: reflectsLimitsOfShape_op J F

中文:
引理 reflectsFiniteLimits_op
  条件: (F : C ⥤ D) [ReflectsFiniteColimits F]
  证明: reflectsLimitsOfShape_op J F

Depends on / 依赖: reflectsLimitsOfShape_op
-/
lemma reflectsFiniteLimits_op (F : C ⥤ D) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.op where
  reflects J _ _ := reflectsLimitsOfShape_op J F

/--
lemma `reflectsFiniteLimits_leftOp` / 引理 `reflectsFiniteLimits_leftOp`

English:
lemma reflectsFiniteLimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F]
  proof: reflectsLimitsOfShape_leftOp J F

中文:
引理 reflectsFiniteLimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F]
  证明: reflectsLimitsOfShape_leftOp J F

Depends on / 依赖: reflectsLimitsOfShape_leftOp
-/
lemma reflectsFiniteLimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.leftOp where
  reflects J _ _ := reflectsLimitsOfShape_leftOp J F

/--
lemma `reflectsFiniteLimits_rightOp` / 引理 `reflectsFiniteLimits_rightOp`

English:
lemma reflectsFiniteLimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F]
  proof: reflectsLimitsOfShape_rightOp J F

中文:
引理 reflectsFiniteLimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F]
  证明: reflectsLimitsOfShape_rightOp J F

Depends on / 依赖: reflectsLimitsOfShape_rightOp
-/
lemma reflectsFiniteLimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.rightOp where
  reflects J _ _ := reflectsLimitsOfShape_rightOp J F

/--
lemma `reflectsFiniteLimits_unop` / 引理 `reflectsFiniteLimits_unop`

English:
lemma reflectsFiniteLimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F]
  proof: reflectsLimitsOfShape_unop J F

中文:
引理 reflectsFiniteLimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F]
  证明: reflectsLimitsOfShape_unop J F

Depends on / 依赖: reflectsLimitsOfShape_unop
-/
lemma reflectsFiniteLimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F] :
    ReflectsFiniteLimits F.unop where
  reflects J _ _ := reflectsLimitsOfShape_unop J F

/--
lemma `reflectsFiniteColimits_op` / 引理 `reflectsFiniteColimits_op`

English:
lemma reflectsFiniteColimits_op
  given: (F : C ⥤ D) [ReflectsFiniteLimits F]
  proof: reflectsColimitsOfShape_op J F

中文:
引理 reflectsFiniteColimits_op
  条件: (F : C ⥤ D) [ReflectsFiniteLimits F]
  证明: reflectsColimitsOfShape_op J F

Depends on / 依赖: reflectsColimitsOfShape_op
-/
lemma reflectsFiniteColimits_op (F : C ⥤ D) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.op where
  reflects J _ _ := reflectsColimitsOfShape_op J F

/--
lemma `reflectsFiniteColimits_leftOp` / 引理 `reflectsFiniteColimits_leftOp`

English:
lemma reflectsFiniteColimits_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F]
  proof: reflectsColimitsOfShape_leftOp J F

中文:
引理 reflectsFiniteColimits_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F]
  证明: reflectsColimitsOfShape_leftOp J F

Depends on / 依赖: reflectsColimitsOfShape_leftOp
-/
lemma reflectsFiniteColimits_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.leftOp where
  reflects J _ _ := reflectsColimitsOfShape_leftOp J F

/--
lemma `reflectsFiniteColimits_rightOp` / 引理 `reflectsFiniteColimits_rightOp`

English:
lemma reflectsFiniteColimits_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F]
  proof: reflectsColimitsOfShape_rightOp J F

中文:
引理 reflectsFiniteColimits_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F]
  证明: reflectsColimitsOfShape_rightOp J F

Depends on / 依赖: reflectsColimitsOfShape_rightOp
-/
lemma reflectsFiniteColimits_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.rightOp where
  reflects J _ _ := reflectsColimitsOfShape_rightOp J F

/--
lemma `reflectsFiniteColimits_unop` / 引理 `reflectsFiniteColimits_unop`

English:
lemma reflectsFiniteColimits_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F]
  proof: reflectsColimitsOfShape_unop J F

中文:
引理 reflectsFiniteColimits_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F]
  证明: reflectsColimitsOfShape_unop J F

Depends on / 依赖: reflectsColimitsOfShape_unop
-/
lemma reflectsFiniteColimits_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F] :
    ReflectsFiniteColimits F.unop where
  reflects J _ _ := reflectsColimitsOfShape_unop J F

/--
lemma `reflectsFiniteLimits_of_op` / 引理 `reflectsFiniteLimits_of_op`

English:
lemma reflectsFiniteLimits_of_op
  given: (F : C ⥤ D) [ReflectsFiniteColimits F.op]
  proof: reflectsLimitsOfShape_of_op J F

中文:
引理 reflectsFiniteLimits_of_op
  条件: (F : C ⥤ D) [ReflectsFiniteColimits F.op]
  证明: reflectsLimitsOfShape_of_op J F

Depends on / 依赖: reflectsLimitsOfShape_of_op
-/
lemma reflectsFiniteLimits_of_op (F : C ⥤ D) [ReflectsFiniteColimits F.op] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_op J F

/--
lemma `reflectsFiniteLimits_of_leftOp` / 引理 `reflectsFiniteLimits_of_leftOp`

English:
lemma reflectsFiniteLimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.leftOp]
  proof: reflectsLimitsOfShape_of_leftOp J F

中文:
引理 reflectsFiniteLimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.leftOp]
  证明: reflectsLimitsOfShape_of_leftOp J F

Depends on / 依赖: reflectsLimitsOfShape_of_leftOp
-/
lemma reflectsFiniteLimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.leftOp] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_leftOp J F

/--
lemma `reflectsFiniteLimits_of_rightOp` / 引理 `reflectsFiniteLimits_of_rightOp`

English:
lemma reflectsFiniteLimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F.rightOp]
  proof: reflectsLimitsOfShape_of_rightOp J F

中文:
引理 reflectsFiniteLimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F.rightOp]
  证明: reflectsLimitsOfShape_of_rightOp J F

Depends on / 依赖: reflectsLimitsOfShape_of_rightOp
-/
lemma reflectsFiniteLimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteColimits F.rightOp] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_rightOp J F

/--
lemma `reflectsFiniteLimits_of_unop` / 引理 `reflectsFiniteLimits_of_unop`

English:
lemma reflectsFiniteLimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.unop]
  proof: reflectsLimitsOfShape_of_unop J F

中文:
引理 reflectsFiniteLimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.unop]
  证明: reflectsLimitsOfShape_of_unop J F

Depends on / 依赖: reflectsLimitsOfShape_of_unop
-/
lemma reflectsFiniteLimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteColimits F.unop] :
    ReflectsFiniteLimits F where
  reflects J _ _ := reflectsLimitsOfShape_of_unop J F

/--
lemma `reflectsFiniteColimits_of_op` / 引理 `reflectsFiniteColimits_of_op`

English:
lemma reflectsFiniteColimits_of_op
  given: (F : C ⥤ D) [ReflectsFiniteLimits F.op]
  proof: reflectsColimitsOfShape_of_op J F

中文:
引理 reflectsFiniteColimits_of_op
  条件: (F : C ⥤ D) [ReflectsFiniteLimits F.op]
  证明: reflectsColimitsOfShape_of_op J F

Depends on / 依赖: reflectsColimitsOfShape_of_op
-/
lemma reflectsFiniteColimits_of_op (F : C ⥤ D) [ReflectsFiniteLimits F.op] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_op J F

/--
lemma `reflectsFiniteColimits_of_leftOp` / 引理 `reflectsFiniteColimits_of_leftOp`

English:
lemma reflectsFiniteColimits_of_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.leftOp]
  proof: reflectsColimitsOfShape_of_leftOp J F

中文:
引理 reflectsFiniteColimits_of_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.leftOp]
  证明: reflectsColimitsOfShape_of_leftOp J F

Depends on / 依赖: reflectsColimitsOfShape_of_leftOp
-/
lemma reflectsFiniteColimits_of_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.leftOp] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_leftOp J F

/--
lemma `reflectsFiniteColimits_of_rightOp` / 引理 `reflectsFiniteColimits_of_rightOp`

English:
lemma reflectsFiniteColimits_of_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F.rightOp]
  proof: reflectsColimitsOfShape_of_rightOp J F

中文:
引理 reflectsFiniteColimits_of_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F.rightOp]
  证明: reflectsColimitsOfShape_of_rightOp J F

Depends on / 依赖: reflectsColimitsOfShape_of_rightOp
-/
lemma reflectsFiniteColimits_of_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteLimits F.rightOp] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_rightOp J F

/--
lemma `reflectsFiniteColimits_of_unop` / 引理 `reflectsFiniteColimits_of_unop`

English:
lemma reflectsFiniteColimits_of_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.unop]
  proof: reflectsColimitsOfShape_of_unop J F

中文:
引理 reflectsFiniteColimits_of_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.unop]
  证明: reflectsColimitsOfShape_of_unop J F

Depends on / 依赖: reflectsColimitsOfShape_of_unop
-/
lemma reflectsFiniteColimits_of_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteLimits F.unop] :
    ReflectsFiniteColimits F where
  reflects J _ _ := reflectsColimitsOfShape_of_unop J F

/--
lemma `reflectsFiniteProducts_op` / 引理 `reflectsFiniteProducts_op`

English:
lemma reflectsFiniteProducts_op
  given: (F : C ⥤ D) [ReflectsFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures reflectsLimitsOfShape_op
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteProducts_op
  条件: (F : C ⥤ D) [ReflectsFiniteCoproducts F]
  证明: by
    apply +allowSynthFailures reflectsLimitsOfShape_op
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_of_equiv, reflectsLimitsOfShape_op
-/
lemma reflectsFiniteProducts_op (F : C ⥤ D) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.op where
  reflects n := by
    apply +allowSynthFailures reflectsLimitsOfShape_op
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsFiniteProducts_leftOp` / 引理 `reflectsFiniteProducts_leftOp`

English:
lemma reflectsFiniteProducts_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures reflectsLimitsOfShape_leftOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteProducts_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F]
  证明: by
    apply +allowSynthFailures reflectsLimitsOfShape_leftOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_of_equiv, reflectsLimitsOfShape_leftOp
-/
lemma reflectsFiniteProducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.leftOp where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_leftOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsFiniteProducts_rightOp` / 引理 `reflectsFiniteProducts_rightOp`

English:
lemma reflectsFiniteProducts_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures reflectsLimitsOfShape_rightOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteProducts_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteCoproducts F]
  证明: by
    apply +allowSynthFailures reflectsLimitsOfShape_rightOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_of_equiv, reflectsLimitsOfShape_rightOp
-/
lemma reflectsFiniteProducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.rightOp where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_rightOp
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsFiniteProducts_unop` / 引理 `reflectsFiniteProducts_unop`

English:
lemma reflectsFiniteProducts_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F]
  proof: by
    apply +allowSynthFailures reflectsLimitsOfShape_unop
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteProducts_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F]
  证明: by
    apply +allowSynthFailures reflectsLimitsOfShape_unop
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_of_equiv, reflectsLimitsOfShape_unop
-/
lemma reflectsFiniteProducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteCoproducts F] :
    ReflectsFiniteProducts F.unop where
  reflects _ := by
    apply +allowSynthFailures reflectsLimitsOfShape_unop
    exact reflectsColimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsFiniteCoproducts_op` / 引理 `reflectsFiniteCoproducts_op`

English:
lemma reflectsFiniteCoproducts_op
  given: (F : C ⥤ D) [ReflectsFiniteProducts F]
  proof: by
    apply +allowSynthFailures reflectsColimitsOfShape_op
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteCoproducts_op
  条件: (F : C ⥤ D) [ReflectsFiniteProducts F]
  证明: by
    apply +allowSynthFailures reflectsColimitsOfShape_op
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_op, reflectsLimitsOfShape_of_equiv
-/
lemma reflectsFiniteCoproducts_op (F : C ⥤ D) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.op where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_op
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsFiniteCoproducts_leftOp` / 引理 `reflectsFiniteCoproducts_leftOp`

English:
lemma reflectsFiniteCoproducts_leftOp
  given: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteProducts F]
  proof: by
    apply +allowSynthFailures reflectsColimitsOfShape_leftOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteCoproducts_leftOp
  条件: (F : C ⥤ Dᵒᵖ) [ReflectsFiniteProducts F]
  证明: by
    apply +allowSynthFailures reflectsColimitsOfShape_leftOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_leftOp, reflectsLimitsOfShape_of_equiv
-/
lemma reflectsFiniteCoproducts_leftOp (F : C ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.leftOp where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_leftOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsFiniteCoproducts_rightOp` / 引理 `reflectsFiniteCoproducts_rightOp`

English:
lemma reflectsFiniteCoproducts_rightOp
  given: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteProducts F]
  proof: by
    apply +allowSynthFailures reflectsColimitsOfShape_rightOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteCoproducts_rightOp
  条件: (F : Cᵒᵖ ⥤ D) [ReflectsFiniteProducts F]
  证明: by
    apply +allowSynthFailures reflectsColimitsOfShape_rightOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_rightOp, reflectsLimitsOfShape_of_equiv
-/
lemma reflectsFiniteCoproducts_rightOp (F : Cᵒᵖ ⥤ D) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.rightOp where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_rightOp
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

/--
lemma `reflectsFiniteCoproducts_unop` / 引理 `reflectsFiniteCoproducts_unop`

English:
lemma reflectsFiniteCoproducts_unop
  given: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteProducts F]
  proof: by
    apply +allowSynthFailures reflectsColimitsOfShape_unop
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

中文:
引理 reflectsFiniteCoproducts_unop
  条件: (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteProducts F]
  证明: by
    apply +allowSynthFailures reflectsColimitsOfShape_unop
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

Depends on / 依赖: Discrete, Discrete.opposite, allowSynthFailures, opposite, reflectsColimitsOfShape_unop, reflectsLimitsOfShape_of_equiv
-/
lemma reflectsFiniteCoproducts_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [ReflectsFiniteProducts F] :
    ReflectsFiniteCoproducts F.unop where
  reflects _ := by
    apply +allowSynthFailures reflectsColimitsOfShape_unop
    exact reflectsLimitsOfShape_of_equiv (Discrete.opposite _).symm _

end CategoryTheory.Limits
