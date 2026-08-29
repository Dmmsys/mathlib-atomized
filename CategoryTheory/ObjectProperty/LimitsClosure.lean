/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.Order.TransfiniteIteration
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Closure of a property of objects under limits of certain shapes

In this file, given a property `P` of objects in a category `C` and
a family of categories `J : α → Type _`, we introduce the closure
`P.limitsClosure J` of `P` under limits of shapes `J a` for all `a : α`,
and under certain smallness assumptions, we show that it is essentially small.

-/

@[expose] public section

universe w w' t v' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  {α : Type t} (J : α -> Type u') [forall a, Category.{v'} (J a)]

/--
Inductive type `limitsClosure` / 归纳类型 `limitsClosure`

English:
inductive limitsClosure
  parameters: : ObjectProperty C
  constructors (3):
    - of_mem: (X : C) (hX : P X) : limitsClosure X
    - of_isoClosure: {X Y : C} (e : X ≅ Y) (hX : limitsClosure X) : limitsClosure Y
    - of_limitPresentation: {X : C} {a : α} (pres : LimitPresentation (J a) X) (h : forall j, limitsClosure (pres.diag.obj j)) : limitsClosure X

中文:
归纳类型 limitsClosure
  参数: : ObjectProperty C
  构造子 (3 个):
    - of_mem: (X : C) (hX : P X) : limitsClosure X
    - of_isoClosure: {X Y : C} (e : X ≅ Y) (hX : limitsClosure X) : limitsClosure Y
    - of_limitPresentation: {X : C} {a : α} (pres : LimitPresentation (J a) X) (h : 对任意 j, limitsClosure (pres.diag.obj j)) : limitsClosure X
-/
inductive limitsClosure : ObjectProperty C
  | of_mem (X : C) (hX : P X) : limitsClosure X
  | of_isoClosure {X Y : C} (e : X ≅ Y) (hX : limitsClosure X) : limitsClosure Y
  | of_limitPresentation {X : C} {a : α} (pres : LimitPresentation (J a) X)
      (h : forall j, limitsClosure (pres.diag.obj j)) : limitsClosure X

@[simp]
/--
lemma `le_limitsClosure` / 引理 `le_limitsClosure`

English:
lemma le_limitsClosure
  statement: P <= P.limitsClosure J
  proof: fun X hX => .of_mem X hX

中文:
引理 le_limitsClosure
  结论: P <= P.limitsClosure J
  证明: fun X hX => .of_mem X hX

Depends on / 依赖: of_mem
-/
lemma le_limitsClosure : P <= P.limitsClosure J :=
  fun X hX => .of_mem X hX

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : (P.limitsClosure J).Nonempty
  body: .mono (P.le_limitsClosure J)

中文:
实例 [P.非空]
  签名: : (P.limitsClosure J).非空
  定义体: .mono (P.le_limitsClosure J)

Depends on / 依赖: P.le_limitsClosure, le_limitsClosure
-/
instance [P.Nonempty] : (P.limitsClosure J).Nonempty := .mono (P.le_limitsClosure J)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.limitsClosure J).IsClosedUnderIsomorphisms
  body: .of_isoClosure e hX

中文:
实例 :
  签名: (P.limitsClosure J).在同构下封闭
  定义体: .of_isoClosure e hX

Depends on / 依赖: of_isoClosure
-/
instance : (P.limitsClosure J).IsClosedUnderIsomorphisms where
  of_iso e hX := .of_isoClosure e hX

instance (a : α) : (P.limitsClosure J).IsClosedUnderLimitsOfShape (J a) where
  limitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_limitPresentation hX.toLimitPresentation hX.prop_diag_obj

variable {P J} in
/--
lemma `limitsClosure_le` / 引理 `limitsClosure_le`

English:
lemma limitsClosure_le
  statement: {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
  proof: by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_limitPresentation pres h h' => exact Q.prop_of_isLimit pres.isLimit h'

中文:
引理 limitsClosure_le
  结论: {Q : ObjectProperty C} [Q.在同构下封闭]
  证明: by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_limitPresentation pres h h' => exact Q.prop_of_isLimit pres.isLimit h'

Depends on / 依赖: Q.prop_of_isLimit, Q.prop_of_iso, isLimit, of_isoClosure, of_limitPresentation, of_mem, pres.isLimit, prop_of_isLimit, prop_of_iso
-/
lemma limitsClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    [forall (a : α), Q.IsClosedUnderLimitsOfShape (J a)] (h : P <= Q) :
    P.limitsClosure J <= Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact h _ hX
  | of_isoClosure e hX hX' => exact Q.prop_of_iso e hX'
  | of_limitPresentation pres h h' => exact Q.prop_of_isLimit pres.isLimit h'

variable {P} in
/--
lemma `limitsClosure_monotone` / 引理 `limitsClosure_monotone`

English:
lemma limitsClosure_monotone
  given: {Q : ObjectProperty C} (h : P <= Q)
  proof: limitsClosure_le (h.trans (Q.le_limitsClosure J))

中文:
引理 limitsClosure_monotone
  条件: {Q : ObjectProperty C} (h : P <= Q)
  证明: limitsClosure_le (h.trans (Q.le_limitsClosure J))

Depends on / 依赖: Q.le_limitsClosure, h.trans, le_limitsClosure, limitsClosure_le
-/
lemma limitsClosure_monotone {Q : ObjectProperty C} (h : P <= Q) :
    P.limitsClosure J <= Q.limitsClosure J :=
  limitsClosure_le (h.trans (Q.le_limitsClosure J))

/--
lemma `limitsClosure_eq_self` / 引理 `limitsClosure_eq_self`

English:
lemma limitsClosure_eq_self
  statement: [P.IsClosedUnderIsomorphisms]
  proof: le_antisymm (limitsClosure_le (le_refl P)) (P.le_limitsClosure J)

@[simp]

中文:
引理 limitsClosure_eq_self
  结论: [P.在同构下封闭]
  证明: le_antisymm (limitsClosure_le (le_refl P)) (P.le_limitsClosure J)

@[simp]

Depends on / 依赖: P.le_limitsClosure, le_antisymm, le_limitsClosure, le_refl, limitsClosure_le
-/
lemma limitsClosure_eq_self [P.IsClosedUnderIsomorphisms]
    [forall (a : α), P.IsClosedUnderLimitsOfShape (J a)] : P.limitsClosure J = P :=
  le_antisymm (limitsClosure_le (le_refl P)) (P.le_limitsClosure J)

@[simp]
/--
lemma `limitsClosure_bot` / 引理 `limitsClosure_bot`

English:
lemma limitsClosure_bot
  given: [forall (a : α), Nonempty (J a)]
  proof: limitsClosure_eq_self _ _

@[simp]

中文:
引理 limitsClosure_bot
  条件: [对任意 (a : α), 非空 (J a)]
  证明: limitsClosure_eq_self _ _

@[simp]

Depends on / 依赖: limitsClosure_eq_self
-/
lemma limitsClosure_bot [forall (a : α), Nonempty (J a)] :
    limitsClosure (⊥ : ObjectProperty C) J = ⊥ :=
  limitsClosure_eq_self _ _

@[simp]
/--
lemma `limitsClosure_top` / 引理 `limitsClosure_top`

English:
lemma limitsClosure_top
  statement: limitsClosure (⊤ : ObjectProperty C) J = ⊤
  proof: limitsClosure_eq_self _ _

中文:
引理 limitsClosure_top
  结论: limitsClosure (⊤ : ObjectProperty C) J = ⊤
  证明: limitsClosure_eq_self _ _

Depends on / 依赖: limitsClosure_eq_self
-/
lemma limitsClosure_top : limitsClosure (⊤ : ObjectProperty C) J = ⊤ :=
  limitsClosure_eq_self _ _

/--
lemma `limitsClosure_isoClosure` / 引理 `limitsClosure_isoClosure`

English:
lemma limitsClosure_isoClosure
  proof: by
  refine le_antisymm (limitsClosure_le ?_)
    (limitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_limitsClosure P J

中文:
引理 limitsClosure_isoClosure
  证明: by
  refine le_antisymm (limitsClosure_le ?_)
    (limitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_limitsClosure P J

Depends on / 依赖: P.le_isoClosure, isoClosure_le_iff, le_antisymm, le_isoClosure, le_limitsClosure, limitsClosure_le, limitsClosure_monotone
-/
lemma limitsClosure_isoClosure :
    P.isoClosure.limitsClosure J = P.limitsClosure J := by
  refine le_antisymm (limitsClosure_le ?_)
    (limitsClosure_monotone _ P.le_isoClosure)
  rw [isoClosure_le_iff]
  exact le_limitsClosure P J

/--
Definition of `limitClosure` / `limitClosure` 的定义

English:
abbreviation limitClosure
  signature: (J : Type*) [Category* J]
  body: P.limitsClosure (fun (_ : Unit) => J)

中文:
缩写 limitClosure
  签名: (J : 类型) [范畴* J]
  定义体: P.limitsClosure (fun (_ : Unit) => J)

Depends on / 依赖: P.limitsClosure, limitsClosure
-/
abbrev limitClosure (J : Type*) [Category* J] : ObjectProperty C :=
  P.limitsClosure (fun (_ : Unit) => J)

instance (J : Type*) [Category* J] : (P.limitClosure J).IsClosedUnderLimitsOfShape J :=
  P.instIsClosedUnderLimitsOfShapeLimitsClosure _ ()

/--
Definition of `strictLimitsClosureStep` / `strictLimitsClosureStep` 的定义

English:
definition strictLimitsClosureStep
  signature: : ObjectProperty C
  body: P ⊔ (⨆ (a : α), P.strictLimitsOfShape (J a))

@[simp]

中文:
定义 strictLimitsClosureStep
  签名: : ObjectProperty C
  定义体: P ⊔ (⨆ (a : α), P.strictLimitsOfShape (J a))

@[simp]

Depends on / 依赖: P.strictLimitsOfShape, strictLimitsOfShape
-/
def strictLimitsClosureStep : ObjectProperty C :=
  P ⊔ (⨆ (a : α), P.strictLimitsOfShape (J a))

@[simp]
/--
lemma `le_strictLimitsClosureStep` / 引理 `le_strictLimitsClosureStep`

English:
lemma le_strictLimitsClosureStep
  statement: P <= P.strictLimitsClosureStep J
  proof: le_sup_left

中文:
引理 le_strictLimitsClosureStep
  结论: P <= P.strictLimitsClosureStep J
  证明: le_sup_left

Depends on / 依赖: le_sup_left
-/
lemma le_strictLimitsClosureStep : P <= P.strictLimitsClosureStep J := le_sup_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : (P.strictLimitsClosureStep J).Nonempty
  body: .mono (P.le_strictLimitsClosureStep J)

中文:
实例 [P.非空]
  签名: : (P.strictLimitsClosureStep J).非空
  定义体: .mono (P.le_strictLimitsClosureStep J)

Depends on / 依赖: P.le_strictLimitsClosureStep, le_strictLimitsClosureStep
-/
instance [P.Nonempty] : (P.strictLimitsClosureStep J).Nonempty :=
  .mono (P.le_strictLimitsClosureStep J)

variable {P} in
/--
lemma `strictLimitsClosureStep_monotone` / 引理 `strictLimitsClosureStep_monotone`

English:
lemma strictLimitsClosureStep_monotone
  given: {Q : ObjectProperty C} (h : P <= Q)
  proof: by
  dsimp [strictLimitsClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨h.trans le_sup_left, fun a =>
(strictLimitsOfShape_monotone (J a) h).trans
.trans le_sup_right⟩ le_iSup (fun a => Q.strictLimitsOfShape (J a)) a

中文:
引理 strictLimitsClosureStep_monotone
  条件: {Q : ObjectProperty C} (h : P <= Q)
  证明: by
  dsimp [strictLimitsClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨h.trans le_sup_left, fun a =>
(strictLimitsOfShape_monotone (J a) h).trans
.trans le_sup_right⟩ le_iSup (fun a => Q.strictLimitsOfShape (J a)) a

Depends on / 依赖: Q.strictLimitsOfShape, h.trans, iSup_le_iff, le_iSup, le_sup_left, le_sup_right, strictLimitsClosureStep, strictLimitsOfShape, strictLimitsOfShape_monotone, sup_le_iff
-/
lemma strictLimitsClosureStep_monotone {Q : ObjectProperty C} (h : P <= Q) :
    P.strictLimitsClosureStep J <= Q.strictLimitsClosureStep J := by
  dsimp [strictLimitsClosureStep]
  simp only [sup_le_iff, iSup_le_iff]
  exact ⟨h.trans le_sup_left, fun a =>
(strictLimitsOfShape_monotone (J a) h).trans
.trans le_sup_right⟩ le_iSup (fun a => Q.strictLimitsOfShape (J a)) a

section

variable {β : Type w'} [LinearOrder β] [OrderBot β] [SuccOrder β] [WellFoundedLT β]

/--
Definition of `strictLimitsClosureIter` / `strictLimitsClosureIter` 的定义

English:
abbreviation strictLimitsClosureIter
  signature: (b : β)
  body: transfiniteIterate (φ := fun Q => Q.strictLimitsClosureStep J) b P

中文:
缩写 strictLimitsClosureIter
  签名: (b : β)
  定义体: transfiniteIterate (φ := fun Q => Q.strictLimitsClosureStep J) b P

Depends on / 依赖: Over.hasLimit_of_hasLimit_liftFromOver, Q.strictLimitsClosureStep, hasLimit_of_hasLimit_liftFromOver, strictLimitsClosureStep, transfiniteIterate
-/
abbrev strictLimitsClosureIter (b : β) : ObjectProperty C :=
  transfiniteIterate (φ := fun Q => Q.strictLimitsClosureStep J) b P

/--
lemma `le_strictLimitsClosureIter` / 引理 `le_strictLimitsClosureIter`

English:
lemma le_strictLimitsClosureIter
  given: (b : β)
  proof: le_of_eq_of_le (transfiniteIterate_bot _ _).symm
    (monotone_transfiniteIterate _ _ (fun _ => le_strictLimitsClosureStep _ _) bot_le)

中文:
引理 le_strictLimitsClosureIter
  条件: (b : β)
  证明: le_of_eq_of_le (transfiniteIterate_bot _ _).symm
    (monotone_transfiniteIterate _ _ (fun _ => le_strictLimitsClosureStep _ _) bot_le)

Depends on / 依赖: bot_le, le_of_eq_of_le, le_strictLimitsClosureStep, monotone_transfiniteIterate, transfiniteIterate_bot
-/
lemma le_strictLimitsClosureIter (b : β) :
    P <= P.strictLimitsClosureIter J b :=
  le_of_eq_of_le (transfiniteIterate_bot _ _).symm
    (monotone_transfiniteIterate _ _ (fun _ => le_strictLimitsClosureStep _ _) bot_le)

instance (b : β) [P.Nonempty] : (P.strictLimitsClosureIter J b).Nonempty :=
  .mono (P.le_strictLimitsClosureIter J b)

/--
lemma `strictLimitsClosureIter_le_limitsClosure` / 引理 `strictLimitsClosureIter_le_limitsClosure`

English:
lemma strictLimitsClosureIter_le_limitsClosure
  given: (b : β)
  proof: by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp
  | succ b hb hb' =>
    rw [strictLimitsClosureIter]; rw [transfiniteIterate_succ _ _ _ hb]; rw [strictLimitsClosureStep]; rw [sup_le_iff]; rw [iSup_le_iff]
    exact ⟨hb', fun a => ((strictLimit

中文:
引理 strictLimitsClosureIter_le_limitsClosure
  条件: (b : β)
  证明: by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp
  | succ b hb hb' =>
    rw [strictLimitsClosureIter]; rw [transfiniteIterate_succ _ _ _ hb]; rw [strictLimitsClosureStep]; rw [sup_le_iff]; rw [iSup_le_iff]
    exact ⟨hb', fun a => ((strictLimit

Depends on / 依赖: Set.mem_Iio, Subtype, Subtype.forall, SuccOrder, SuccOrder.limitRecOn, eq_bot, hb.eq_bot, iSup_le_iff, isSuccLimit, limitRecOn, limitsOfShape_le, limitsOfShape_monotone, mem_Iio, strictLimitsClosureIter, strictLimitsClosureStep, strictLimitsOfShape_le_limitsOfShape, sup_le_iff, transfiniteIterate_limit, transfiniteIterate_succ
-/
lemma strictLimitsClosureIter_le_limitsClosure (b : β) :
    P.strictLimitsClosureIter J b <= P.limitsClosure J := by
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp
  | succ b hb hb' =>
    rw [strictLimitsClosureIter]; rw [transfiniteIterate_succ _ _ _ hb]; rw [strictLimitsClosureStep]; rw [sup_le_iff]; rw [iSup_le_iff]
    exact ⟨hb', fun a => ((strictLimitsOfShape_le_limitsOfShape _ _).trans
      (limitsOfShape_monotone _ hb')).trans (limitsOfShape_le _ _)⟩
  | isSuccLimit b hb hb' =>
    simp only [transfiniteIterate_limit _ _ _ hb,
      iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro c hc
    exact hb' _ hc

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.Small.{w}
  signature: P] [LocallySmall.{w} C] [Small.{w} α]
  body: by
  have H {b c : β} (hbc : b <= c) [Small.{w} (Set.Iio c)] : Small.{w} (Set.Iio b) :=
    small_of_injective (f := fun x => (⟨x.1, lt_of_lt_of_le x.2 hbc⟩ : Set.Iio c))
      (fun _ _ _ => by aesop)
  induction b using SuccOrder.limitRecOn generalizing hb₀ with
  | isMin b hb =>
    obtain rfl := 

中文:
实例 [ObjectProperty.Small.{w}
  签名: P] [LocallySmall.{w} C] [Small.{w} α]
  定义体: by
  have H {b c : β} (hbc : b <= c) [Small.{w} (Set.Iio c)] : Small.{w} (Set.Iio b) :=
    small_of_injective (f := fun x => (⟨x.1, lt_of_lt_of_le x.2 hbc⟩ : Set.Iio c))
      (fun _ _ _ => by aesop)
  induction b using SuccOrder.limitRecOn generalizing hb₀ with
  | isMin b hb =>
    obtain rfl := 

Depends on / 依赖: Order.le_succ, Set.Iio, SuccOrder, SuccOrder.limitRecOn, eq_bot, generalizing, hb.eq_bot, infer_instance, le_succ, limitRecOn, lt_of_lt_of_le, small_of_injective, strictLimitsClosureIter, strictLimitsClosureStep, transfiniteIterate_bot, transfiniteIterate_succ
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [forall a, Small.{w} (J a)] [forall a, LocallySmall.{w} (J a)] (b : β)
    [hb₀ : Small.{w} (Set.Iio b)] :
    ObjectProperty.Small.{w} (P.strictLimitsClosureIter J b) := by
  have H {b c : β} (hbc : b <= c) [Small.{w} (Set.Iio c)] : Small.{w} (Set.Iio b) :=
    small_of_injective (f := fun x => (⟨x.1, lt_of_lt_of_le x.2 hbc⟩ : Set.Iio c))
      (fun _ _ _ => by aesop)
  induction b using SuccOrder.limitRecOn generalizing hb₀ with
  | isMin b hb =>
    obtain rfl := hb.eq_bot
    simp only [transfiniteIterate_bot]
    infer_instance
  | succ b hb hb' =>
    have := H (Order.le_succ b)
    rw [strictLimitsClosureIter]; rw [transfiniteIterate_succ _ _ _ hb]; rw [strictLimitsClosureStep]
    infer_instance
  | isSuccLimit b hb hb' =>
    simp only [transfiniteIterate_limit _ _ _ hb]
    have (c : Set.Iio b) : ObjectProperty.Small.{w}
      (transfiniteIterate (fun Q => Q.strictLimitsClosureStep J) c.1 P) := by
      have := H c.2.le
      exact hb' c.1 c.2
    infer_instance

end

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] (h : forall (a : α), HasCardinalLT (J a) κ)

include h

/--
lemma `strictLimitsClosureStep_strictLimitsClosureIter_eq_self` / 引理 `strictLimitsClosureStep_strictLimitsClosureIter_eq_self`

English:
lemma strictLimitsClosureStep_strictLimitsClosureIter_eq_self
  proof: by
  have hκ : κ.IsRegular := Fact.out
  have (a : α) := (h a).small
  refine le_antisymm (fun X hX => ?_) (le_strictLimitsClosureStep _ _)
  simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff] at hX
  obtain (hX | ⟨a, F, hF⟩) := hX
  · exact hX
  · simp only [strictLimitsClosureIter, t

中文:
引理 strictLimitsClosureStep_strictLimitsClosureIter_eq_self
  证明: by
  have hκ : κ.IsRegular := Fact.out
  have (a : α) := (h a).small
  refine le_antisymm (fun X hX => ?_) (le_strictLimitsClosureStep _ _)
  simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff] at hX
  obtain (hX | ⟨a, F, hF⟩) := hX
  · exact hX
  · simp only [strictLimitsClosureIter, t

Depends on / 依赖: Cardinal, Cardinal.isSuccLimit_ord, Fact.out, IsRegular, Ordinal, Set.mem_Iio, Subtype, Subtype.exists, aleph0_le, exists_prop, isSuccLimit_ord, le_antisymm, le_strictLimitsClosureStep, mem_Iio, prop_iSup_iff, prop_sup_iff, strictLimitsClosureIter, strictLimitsClosureStep, transfiniteIterate_limit
-/
lemma strictLimitsClosureStep_strictLimitsClosureIter_eq_self :
    (P.strictLimitsClosureIter J κ.ord).strictLimitsClosureStep J =
      (P.strictLimitsClosureIter J κ.ord) := by
  have hκ : κ.IsRegular := Fact.out
  have (a : α) := (h a).small
  refine le_antisymm (fun X hX => ?_) (le_strictLimitsClosureStep _ _)
  simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff] at hX
  obtain (hX | ⟨a, F, hF⟩) := hX
  · exact hX
  · simp only [strictLimitsClosureIter, transfiniteIterate_limit _ _ _
      (Cardinal.isSuccLimit_ord hκ.aleph0_le), prop_iSup_iff,
      Subtype.exists, Set.mem_Iio, exists_prop] at hF
    choose o ho ho' using hF
    obtain ⟨m, hm, hm'⟩ : exists (m : Ordinal.{w}) (hm : m < κ.ord), forall (j : J a), o j <= m := by
      refine ⟨⨆ j, o ((equivShrink.{w} (J a)).symm j),
        Ordinal.iSup_lt_of_lt_cof ?_ (fun _ => ho _), fun j => ?_⟩
      · rw [hκ.cof_ord, ← hasCardinalLT_iff_cardinal_mk_lt _ κ,
          ← hasCardinalLT_iff_of_equiv (equivShrink.{w} (J a))]
        exact h a
      · obtain ⟨j, rfl⟩ := (equivShrink.{w} (J a)).symm.surjective j
        exact le_ciSup Ordinal.bddAbove_of_small _
    refine monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) => Q.le_strictLimitsClosureStep J) (Order.succ_le_iff.2 hm) _ ?_
    dsimp
    rw [transfiniteIterate_succ _ _ _ (by simp)]
    simp only [strictLimitsClosureStep, prop_sup_iff, prop_iSup_iff]
    exact Or.inr ⟨a, ⟨_, fun j => monotone_transfiniteIterate _ _
      (fun (Q : ObjectProperty C) => Q.le_strictLimitsClosureStep J) (hm' j) _ (ho' j)⟩⟩

/--
lemma `isoClosure_strictLimitsClosureIter_eq_limitsClosure` / 引理 `isoClosure_strictLimitsClosureIter_eq_limitsClosure`

English:
lemma isoClosure_strictLimitsClosureIter_eq_limitsClosure
  proof: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictLimitsClosureIter_le_limitsClosure J κ.ord
  · have (a : α) :
        (P.strictLimitsClosureIter J κ.ord).isoClosure.IsClosedUnderLimitsOfShape (J a) := ⟨by
      conv_rhs => rw [← P.strictLimitsClosureStep_strictLimitsClosur

中文:
引理 isoClosure_strictLimitsClosureIter_eq_limitsClosure
  证明: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictLimitsClosureIter_le_limitsClosure J κ.ord
  · have (a : α) :
        (P.strictLimitsClosureIter J κ.ord).isoClosure.IsClosedUnderLimitsOfShape (J a) := ⟨by
      conv_rhs => rw [← P.strictLimitsClosureStep_strictLimitsClosur

Depends on / 依赖: IsClosedUnderLimitsOfShape, P.strictLimitsClosureIter, P.strictLimitsClosureIter_le_limitsClosure, P.strictLimitsClosureStep_strictLimitsClosureIter_eq_self, conv_rhs, isoClosure, isoClosure.IsClosedUnderLimitsOfShape, isoClosure_le_iff, isoClosure_strictLimitsOfShape, le_antisymm, le_iSup, le_sup_right, le_trans, limitsClosure_l, limitsOfShape_isoClosure, monotone_isoClosure, strictLimitsClosureIter, strictLimitsClosureIter_le_limitsClosure, strictLimitsClosureStep, strictLimitsClosureStep_strictLimitsClosureIter_eq_self
-/
lemma isoClosure_strictLimitsClosureIter_eq_limitsClosure :
    (P.strictLimitsClosureIter J κ.ord).isoClosure = P.limitsClosure J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    exact P.strictLimitsClosureIter_le_limitsClosure J κ.ord
  · have (a : α) :
        (P.strictLimitsClosureIter J κ.ord).isoClosure.IsClosedUnderLimitsOfShape (J a) := ⟨by
      conv_rhs => rw [← P.strictLimitsClosureStep_strictLimitsClosureIter_eq_self J κ h]
      rw [limitsOfShape_isoClosure]; rw [← isoClosure_strictLimitsOfShape]; rw [strictLimitsClosureStep]
      exact monotone_isoClosure ((le_trans (by rfl) (le_iSup _ a)).trans le_sup_right)⟩
    refine limitsClosure_le
      ((P.le_strictLimitsClosureIter J κ.ord).trans (le_isoClosure _))

/--
lemma `isEssentiallySmall_limitsClosure` / 引理 `isEssentiallySmall_limitsClosure`

English:
lemma isEssentiallySmall_limitsClosure
  proof: by
  obtain ⟨Q, hQ, hQ₁, hQ₂⟩ := EssentiallySmall.exists_small_le.{w} P
  have : ObjectProperty.EssentiallySmall.{w} (Q.isoClosure.limitsClosure J) := by
    rw [limitsClosure_isoClosure]; rw [← Q.isoClosure_strictLimitsClosureIter_eq_limitsClosure J κ h]
    infer_instance
  exact .of_le (limitsClo

中文:
引理 isEssentiallySmall_limitsClosure
  证明: by
  obtain ⟨Q, hQ, hQ₁, hQ₂⟩ := EssentiallySmall.exists_small_le.{w} P
  have : ObjectProperty.EssentiallySmall.{w} (Q.isoClosure.limitsClosure J) := by
    rw [limitsClosure_isoClosure]; rw [← Q.isoClosure_strictLimitsClosureIter_eq_limitsClosure J κ h]
    infer_instance
  exact .of_le (limitsClo

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, ObjectProperty, ObjectProperty.EssentiallySmall, Q.isoClosure.limitsClosure, Q.isoClosure_strictLimitsClosureIter_eq_limitsClosure, exists_small_le, infer_instance, isoClosure, isoClosure_strictLimitsClosureIter_eq_limitsClosure, limitsClosure, limitsClosure_isoClosure, limitsClosure_monotone, of_le
-/
lemma isEssentiallySmall_limitsClosure
    [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [forall a, Small.{w} (J a)] [forall a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsClosure J) := by
  obtain ⟨Q, hQ, hQ₁, hQ₂⟩ := EssentiallySmall.exists_small_le.{w} P
  have : ObjectProperty.EssentiallySmall.{w} (Q.isoClosure.limitsClosure J) := by
    rw [limitsClosure_isoClosure]; rw [← Q.isoClosure_strictLimitsClosureIter_eq_limitsClosure J κ h]
    infer_instance
  exact .of_le (limitsClosure_monotone J hQ₂)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.EssentiallySmall.{w}
  signature: P] [LocallySmall.{w} C] [Small.{w} α]
  body: by
  obtain ⟨κ, h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall J
  have : Fact κ.IsRegular := ⟨h₁⟩
  exact isEssentiallySmall_limitsClosure P J κ h₂

中文:
实例 [ObjectProperty.EssentiallySmall.{w}
  签名: P] [LocallySmall.{w} C] [Small.{w} α]
  定义体: by
  obtain ⟨κ, h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall J
  have : Fact κ.IsRegular := ⟨h₁⟩
  exact isEssentiallySmall_limitsClosure P J κ h₂

Depends on / 依赖: HasCardinalLT, HasCardinalLT.exists_regular_cardinal_forall, IsRegular, exists_regular_cardinal_forall, isEssentiallySmall_limitsClosure
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] [Small.{w} α]
    [forall a, Small.{w} (J a)] [forall a, LocallySmall.{w} (J a)] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsClosure J) := by
  obtain ⟨κ, h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall J
  have : Fact κ.IsRegular := ⟨h₁⟩
  exact isEssentiallySmall_limitsClosure P J κ h₂

end CategoryTheory.ObjectProperty
