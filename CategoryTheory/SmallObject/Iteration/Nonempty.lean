/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic
public import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
public import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone

/-!
# Existence of the iteration of a successor structure

Given `Φ : SuccStruct C`, we show by transfinite induction
that for any element `j` in a well-ordered set `J`,
the type `Φ.Iteration j` is nonempty.

-/

@[expose] public section

universe u

namespace CategoryTheory

namespace SmallObject

namespace SuccStruct

open Category Limits

variable {C : Type*} [Category* C] (Φ : SuccStruct C)
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

namespace Iteration

variable (J) in
/--
Definition of `mkOfBot` / `mkOfBot` 的定义

English:
definition mkOfBot
  signature: : Φ.Iteration (⊥ : J) where
  body: (Functor.const _).obj Φ.X₀
  obj_bot := rfl
  arrowSucc_eq _ h := by simp at h
  arrowMap_limit _ h₁ h₂ := (h₁.not_isMin (by simpa using h₂)).elim

中文:
定义 mkOfBot
  签名: : Φ.Iteration (⊥ : J) where
  定义体: (Functor.const _).obj Φ.X₀
  obj_bot := rfl
  arrowSucc_eq _ h := by simp at h
  arrowMap_limit _ h₁ h₂ := (h₁.not_isMin (by simpa using h₂)).elim

Depends on / 依赖: Functor, Functor.const
-/
def mkOfBot : Φ.Iteration (⊥ : J) where
  F := (Functor.const _).obj Φ.X₀
  obj_bot := rfl
  arrowSucc_eq _ h := by simp at h
  arrowMap_limit _ h₁ h₂ := (h₁.not_isMin (by simpa using h₂)).elim

variable {Φ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mkOfSucc` / `mkOfSucc` 的定义

English:
definition mkOfSucc
  signature: {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j)
  body: extendToSucc hj iter.F (Φ.toSucc _)
  obj_bot := by rw [extendToSucc_obj_eq _ _ _ _ bot_le, obj_bot]
  arrowSucc_eq i hi₁ := by
    rw [Order.lt_succ_iff_of_not_isMax hj] at hi₁
    obtain hi₁ | rfl := hi₁.lt_or_eq
    · rw [arrowSucc_def, arrowMap_extendToSucc _ _ _ _ _ _ (Order.succ_le_of_lt hi₁),

中文:
定义 mkOfSucc
  签名: {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j)
  定义体: extendToSucc hj iter.F (Φ.toSucc _)
  obj_bot := by rw [extendToSucc_obj_eq _ _ _ _ bot_le, obj_bot]
  arrowSucc_eq i hi₁ := by
    rw [Order.lt_succ_iff_of_not_isMax hj] at hi₁
    obtain hi₁ | rfl := hi₁.lt_or_eq
    · rw [arrowSucc_def, arrowMap_extendToSucc _ _ _ _ _ _ (Order.succ_le_of_lt hi₁),

Depends on / 依赖: extendToSucc, iter.F, toSucc
-/
noncomputable def mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j) :
    Φ.Iteration (Order.succ j) where
  F := extendToSucc hj iter.F (Φ.toSucc _)
  obj_bot := by rw [extendToSucc_obj_eq _ _ _ _ bot_le, obj_bot]
  arrowSucc_eq i hi₁ := by
    rw [Order.lt_succ_iff_of_not_isMax hj] at hi₁
    obtain hi₁ | rfl := hi₁.lt_or_eq
    · rw [arrowSucc_def, arrowMap_extendToSucc _ _ _ _ _ _ (Order.succ_le_of_lt hi₁),
        ← arrowSucc_def _ _ hi₁, iter.arrowSucc_eq i hi₁,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i hi₁.le]
    · rw [arrowSucc_extendToSucc, toSuccArrow,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i]
  arrowMap_limit i hi hij k hk := by
    have hij' := (Order.IsSuccLimit.le_succ_iff hi).1 hij
    rw [arrowMap_extendToSucc _ _ _ _ _ _ hij']; rw [arrowMap_limit _ _ hi _ _ hk]
    congr 1
    apply Arrow.functor_ext
    rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
    dsimp
    rw [← arrowMap]; rw [← arrowMap]; rw [arrowMap_extendToSucc]
    rfl

namespace mkOfLimit


variable {j : J} (hj : Order.IsSuccLimit j) (iter : forall (i : J), i < j -> Φ.Iteration i)

/-- Assuming `j : J` is a limit element and that we have `∀ (i : J), i < j → Φ.Iteration i`,
this is the inductive system `Set.Iio j ⥤ C` which sends `⟨i, _⟩` to
`(iter i _).F.obj ⟨i, _⟩`. -/
@[simps]
/--
Definition of `inductiveSystem` / `inductiveSystem` 的定义

English:
definition inductiveSystem
  signature: : Set.Iio j ⥤ C where
  body: (iter i.1 i.2).F.obj ⟨i.1, by simp⟩
  map {i₁ i₂} f := mapObj (iter i₁.1 i₁.2) (iter i₂.1 i₂.2) (leOfHom f)
    (by simp) (by simp) (leOfHom f)

中文:
定义 inductiveSystem
  签名: : Set.Iio j ⥤ C where
  定义体: (iter i.1 i.2).F.obj ⟨i.1, by simp⟩
  map {i₁ i₂} f := mapObj (iter i₁.1 i₁.2) (iter i₂.1 i₂.2) (leOfHom f)
    (by simp) (by simp) (leOfHom f)

Depends on / 依赖: F.obj
-/
noncomputable def inductiveSystem : Set.Iio j ⥤ C where
  obj i := (iter i.1 i.2).F.obj ⟨i.1, by simp⟩
  map {i₁ i₂} f := mapObj (iter i₁.1 i₁.2) (iter i₂.1 i₂.2) (leOfHom f)
    (by simp) (by simp) (leOfHom f)

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Set.Iic j ⥤ C
  body: letI := hasColimitsOfShape_of_isSuccLimit C j hj
  ofCocone (colimit.cocone (inductiveSystem iter))

中文:
定义 functor
  签名: : Set.Iic j ⥤ C
  定义体: letI := hasColimitsOfShape_of_isSuccLimit C j hj
  ofCocone (colimit.cocone (inductiveSystem iter))

Depends on / 依赖: cocone, colimit, colimit.cocone, hasColimitsOfShape_of_isSuccLimit, inductiveSystem, ofCocone
-/
noncomputable def functor : Set.Iic j ⥤ C :=
  letI := hasColimitsOfShape_of_isSuccLimit C j hj
  ofCocone (colimit.cocone (inductiveSystem iter))

/--
lemma `functor_obj` / 引理 `functor_obj`

English:
lemma functor_obj
  given: (i : J) (hi : i < j) {k : J} (iter' : Φ.Iteration k) (hk : i <= k)
  proof: by
  dsimp only [functor]
  rw [ofCocone_obj_eq _ _ hi]
  apply congr_obj

中文:
引理 functor_obj
  条件: (i : J) (hi : i < j) {k : J} (iter' : Φ.Iteration k) (hk : i <= k)
  证明: by
  dsimp only [functor]
  rw [ofCocone_obj_eq _ _ hi]
  apply congr_obj

Depends on / 依赖: congr_obj, functor, ofCocone_obj_eq
-/
lemma functor_obj (i : J) (hi : i < j) {k : J} (iter' : Φ.Iteration k) (hk : i <= k) :
    (functor hj iter).obj ⟨i, hi.le⟩ = iter'.F.obj ⟨i, hk⟩ := by
  dsimp only [functor]
  rw [ofCocone_obj_eq _ _ hi]
  apply congr_obj

/--
lemma `arrowMap_functor` / 引理 `arrowMap_functor`

English:
lemma arrowMap_functor
  given: (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j)
  proof: arrowMap_ofCocone _ _ _ _ h₂

中文:
引理 arrowMap_functor
  条件: (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j)
  证明: arrowMap_ofCocone _ _ _ _ h₂

Depends on / 依赖: arrowMap_ofCocone
-/
lemma arrowMap_functor (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j) :
    arrowMap (functor hj iter) i₁ i₂ h₁₂ h₂.le =
      Arrow.mk (mapObj (iter i₁ (lt_of_le_of_lt h₁₂ h₂)) (iter i₂ h₂) h₁₂
        (by simp) (by simp) h₁₂) :=
  arrowMap_ofCocone _ _ _ _ h₂

/--
lemma `arrowMap_functor_to_top` / 引理 `arrowMap_functor_to_top`

English:
lemma arrowMap_functor_to_top
  given: (i : J) (hi : i < j)
  proof: hasColimitsOfShape_of_isSuccLimit C j hj
    arrowMap (functor hj iter) i j hi.le (by simp) =
      Arrow.mk (colimit.ι (inductiveSystem iter) ⟨i, hi⟩) :=
  arrowMap_ofCocone_to_top _ _ _

中文:
引理 arrowMap_functor_to_top
  条件: (i : J) (hi : i < j)
  证明: hasColimitsOfShape_of_isSuccLimit C j hj
    arrowMap (functor hj iter) i j hi.le (by simp) =
      Arrow.mk (colimit.ι (inductiveSystem iter) ⟨i, hi⟩) :=
  arrowMap_ofCocone_to_top _ _ _

Depends on / 依赖: hasColimitsOfShape_of_isSuccLimit
-/
lemma arrowMap_functor_to_top (i : J) (hi : i < j) :
    letI := hasColimitsOfShape_of_isSuccLimit C j hj
    arrowMap (functor hj iter) i j hi.le (by simp) =
      Arrow.mk (colimit.ι (inductiveSystem iter) ⟨i, hi⟩) :=
  arrowMap_ofCocone_to_top _ _ _

end mkOfLimit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open mkOfLimit in
/--
Definition of `mkOfLimit` / `mkOfLimit` 的定义

English:
definition mkOfLimit
  signature: {j : J} (hj : Order.IsSuccLimit j)
  body: functor hj iter
  obj_bot := functor_obj hj iter ⊥ (Order.IsSuccLimit.bot_lt hj) (mkOfBot Φ J) (by rfl)
  arrowSucc_eq i hi := by
    rw [arrowSucc_def]; rw [arrowMap_functor _ _ _ _ (Order.le_succ i)
        ((Order.IsSuccLimit.succ_lt_iff hj).2 hi)]; rw [arrow_mk_mapObj]; rw [← arrowSucc_def _ _ (

中文:
定义 mkOfLimit
  签名: {j : J} (hj : Order.IsSuccLimit j)
  定义体: functor hj iter
  obj_bot := functor_obj hj iter ⊥ (Order.IsSuccLimit.bot_lt hj) (mkOfBot Φ J) (by rfl)
  arrowSucc_eq i hi := by
    rw [arrowSucc_def]; rw [arrowMap_functor _ _ _ _ (Order.le_succ i)
        ((Order.IsSuccLimit.succ_lt_iff hj).2 hi)]; rw [arrow_mk_mapObj]; rw [← arrowSucc_def _ _ (

Depends on / 依赖: functor
-/
noncomputable def mkOfLimit {j : J} (hj : Order.IsSuccLimit j)
    (iter : forall (i : J), i < j -> Φ.Iteration i) :
    Φ.Iteration j where
  F := functor hj iter
  obj_bot := functor_obj hj iter ⊥ (Order.IsSuccLimit.bot_lt hj) (mkOfBot Φ J) (by rfl)
  arrowSucc_eq i hi := by
    rw [arrowSucc_def]; rw [arrowMap_functor _ _ _ _ (Order.le_succ i)
        ((Order.IsSuccLimit.succ_lt_iff hj).2 hi)]; rw [arrow_mk_mapObj]; rw [← arrowSucc_def _ _ ((Order.lt_succ_of_le_of_not_isMax (by rfl) (not_isMax_of_lt hi)))]; rw [arrowSucc_eq]; rw [functor_obj _ _ _ hi]
  arrowMap_limit i hi hij k hk := by
    obtain hij | rfl := hij.lt_or_eq
    · rw [arrowMap_functor _ _ _ _ _ hij, arrow_mk_mapObj,
        arrowMap_limit _ _ hi _ _ hk]
      congr 1
      apply Arrow.functor_ext
      rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ f
      dsimp
      generalize_proofs
      rw [← arrowMap]; rw [← arrowMap]; rw [arrowMap_functor hj iter l₁ l₂ _ (hl₂.trans hij)]; rw [arrow_mk_mapObj]
      apply congr_arrowMap
    · rw [arrowMap_functor_to_top _ _ _ hk, ← arrowι_def _ hi]
      congr 1
      apply Arrow.functor_ext
      rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ f
      dsimp
      generalize_proofs
      rw [← arrowMap]; rw [arrow_mk_mapObj]; rw [arrowMap_functor _ _ _ _ _ hl₂]; rw [arrow_mk_mapObj]

variable (Φ)

/--
Instance `nonempty` / 实例 `nonempty`

English:
instance nonempty
  signature: (j : J)
  body: by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
      obtain rfl : i = ⊥ := by simpa using hi
      exact ⟨mkOfBot Φ J⟩
  | succ i hi hi' => exact ⟨mkOfSucc hi hi'.some⟩
  | isSuccLimit i hi hi' => exact ⟨mkOfLimit hi (fun a ha => (hi' a ha).some)⟩

中文:
实例 nonempty
  签名: (j : J)
  定义体: by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
      obtain rfl : i = ⊥ := by simpa using hi
      exact ⟨mkOfBot Φ J⟩
  | succ i hi hi' => exact ⟨mkOfSucc hi hi'.some⟩
  | isSuccLimit i hi hi' => exact ⟨mkOfLimit hi (fun a ha => (hi' a ha).some)⟩

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn, isSuccLimit, limitRecOn, mkOfBot, mkOfLimit, mkOfSucc
-/
instance nonempty (j : J) : Nonempty (Φ.Iteration j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
      obtain rfl : i = ⊥ := by simpa using hi
      exact ⟨mkOfBot Φ J⟩
  | succ i hi hi' => exact ⟨mkOfSucc hi hi'.some⟩
  | isSuccLimit i hi hi' => exact ⟨mkOfLimit hi (fun a ha => (hi' a ha).some)⟩

end Iteration

end SuccStruct

end SmallObject

end CategoryTheory
