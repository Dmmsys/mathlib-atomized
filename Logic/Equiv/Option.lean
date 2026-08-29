/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Control.EquivFunctor
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences for `Option α`


We define
* `Equiv.optionCongr`: the `Option α ≃ Option β` constructed from `e : α ≃ β` by sending `none` to
  `none`, and applying `e` elsewhere.
* `Equiv.removeNone`: the `α ≃ β` constructed from `Option α ≃ Option β` by removing `none` from
  both sides.
-/

@[expose] public section

universe u

namespace Equiv

open Option

variable {α β γ : Type*}

section OptionCongr

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv Option e`. -/
@[simps (attr := grind =) apply]
/--
Definition of `optionCongr` / `optionCongr` 的定义

English:
definition optionCongr
  signature: (e : α ≃ β)
  body: Option.map e
  invFun := Option.map e.symm
left_inv x := (Option.map_map _ _ _).trans e.symm_comp_self.symm ▸ congr_fun Option.map_id x
right_inv x := (Option.map_map _ _ _).trans e.self_comp_symm.symm ▸ congr_fun Option.map_id x

@[simp]

中文:
定义 optionCongr
  签名: (e : α ≃ β)
  定义体: Option.map e
  invFun := Option.map e.symm
left_inv x := (Option.map_map _ _ _).trans e.symm_comp_self.symm ▸ congr_fun Option.map_id x
right_inv x := (Option.map_map _ _ _).trans e.self_comp_symm.symm ▸ congr_fun Option.map_id x

@[simp]

Depends on / 依赖: Option.map
-/
def optionCongr (e : α ≃ β) : Option α ≃ Option β where
  toFun := Option.map e
  invFun := Option.map e.symm
left_inv x := (Option.map_map _ _ _).trans e.symm_comp_self.symm ▸ congr_fun Option.map_id x
right_inv x := (Option.map_map _ _ _).trans e.self_comp_symm.symm ▸ congr_fun Option.map_id x

@[simp]
/--
theorem `optionCongr_refl` / 定理 `optionCongr_refl`

English:
theorem optionCongr_refl
  statement: optionCongr (Equiv.refl α) = Equiv.refl _
  proof: ext congr_fun Option.map_id

@[simp, grind =]

中文:
定理 optionCongr_refl
  结论: optionCongr (等价.refl α) = 等价.refl _
  证明: ext congr_fun Option.map_id

@[simp, grind =]

Depends on / 依赖: Option.map_id, congr_fun, map_id
-/
theorem optionCongr_refl : optionCongr (Equiv.refl α) = Equiv.refl _ :=
ext congr_fun Option.map_id

@[simp, grind =]
/--
theorem `optionCongr_symm` / 定理 `optionCongr_symm`

English:
theorem optionCongr_symm
  given: (e : α ≃ β)
  statement: optionCongr e.symm = (optionCongr e).symm
  proof: rfl

@[simp]

中文:
定理 optionCongr_symm
  条件: (e : α ≃ β)
  结论: optionCongr e.symm = (optionCongr e).symm
  证明: rfl

@[simp]
-/
theorem optionCongr_symm (e : α ≃ β) : optionCongr e.symm = (optionCongr e).symm :=
  rfl

@[simp]
/--
theorem `optionCongr_trans` / 定理 `optionCongr_trans`

English:
theorem optionCongr_trans
  given: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  proof: by
  ext x : 1
  symm
  apply Option.map_map

中文:
定理 optionCongr_trans
  条件: (e₁ : α ≃ β) (e₂ : β ≃ γ)
  证明: by
  ext x : 1
  symm
  apply Option.map_map

Depends on / 依赖: Option.map_map, map_map
-/
theorem optionCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    optionCongr (e₁.trans e₂) = (optionCongr e₁).trans (optionCongr e₂) := by
  ext x : 1
  symm
  apply Option.map_map

/--
theorem `optionCongr_eq_equivFunctor_mapEquiv` / 定理 `optionCongr_eq_equivFunctor_mapEquiv`

English:
theorem optionCongr_eq_equivFunctor_mapEquiv
  given: {α β : Type u} (e : α ≃ β)
  proof: rfl

中文:
定理 optionCongr_eq_equivFunctor_mapEquiv
  条件: {α β : 类型u} (e : α ≃ β)
  证明: rfl
-/
theorem optionCongr_eq_equivFunctor_mapEquiv {α β : Type u} (e : α ≃ β) :
    optionCongr e = EquivFunctor.mapEquiv Option e :=
  rfl

end OptionCongr

section RemoveNone

variable (e : Option α ≃ Option β)

/--
Definition of `removeNoneAux` / `removeNoneAux` 的定义

English:
definition removeNoneAux
  signature: (x : α)
  body: if h : (e (some x)).isSome then Option.get _ h
  else
Option.get _
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none]; rw [← hn] at h
        exact Option.some_ne_none _ (e.injective h)

中文:
定义 removeNoneAux
  签名: (x : α)
  定义体: if h : (e (some x)).isSome then Option.get _ h
  else
Option.get _
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none]; rw [← hn] at h
        exact Option.some_ne_none _ (e.injective h)

Depends on / 依赖: Option.get, Option.ne_none_iff_isSome, Option.not_isSome_iff_eq_none, Option.some_ne_none, e.injective, injective, isSome, ne_none_iff_isSome, not_isSome_iff_eq_none, some_ne_none
-/
def removeNoneAux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
Option.get _
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none]; rw [← hn] at h
        exact Option.some_ne_none _ (e.injective h)

/--
theorem `removeNoneAux_some` / 定理 `removeNoneAux_some`

English:
theorem removeNoneAux_some
  given: {x : α} (h : exists x', e (some x) = some x')
  proof: by
  simp [removeNoneAux, Option.isSome_iff_exists.mpr h]

中文:
定理 removeNoneAux_some
  条件: {x : α} (h : 存在 x', e (some x) = some x')
  证明: by
  simp [removeNoneAux, Option.isSome_iff_exists.mpr h]

Depends on / 依赖: Option.isSome_iff_exists.mpr, isSome_iff_exists, removeNoneAux
-/
theorem removeNoneAux_some {x : α} (h : exists x', e (some x) = some x') :
    some (removeNoneAux e x) = e (some x) := by
  simp [removeNoneAux, Option.isSome_iff_exists.mpr h]

/--
theorem `removeNoneAux_none` / 定理 `removeNoneAux_none`

English:
theorem removeNoneAux_none
  given: {x : α} (h : e (some x) = none)
  proof: by
  simp [removeNoneAux, Option.not_isSome_iff_eq_none.mpr h]

中文:
定理 removeNoneAux_none
  条件: {x : α} (h : e (some x) = none)
  证明: by
  simp [removeNoneAux, Option.not_isSome_iff_eq_none.mpr h]

Depends on / 依赖: Option.not_isSome_iff_eq_none.mpr, not_isSome_iff_eq_none, removeNoneAux
-/
theorem removeNoneAux_none {x : α} (h : e (some x) = none) :
    some (removeNoneAux e x) = e none := by
  simp [removeNoneAux, Option.not_isSome_iff_eq_none.mpr h]

-- FIXME: This declaration is misnamed.
/--
theorem `removeNoneAux_inv` / 定理 `removeNoneAux_inv`

English:
theorem removeNoneAux_inv
  given: (x : α)
  statement: removeNoneAux e.symm (removeNoneAux e x) = x
  proof: Option.some_injective _
    (by
      cases h1 : e.symm (some (removeNoneAux e x)) <;> cases h2 : e (some x)
      · rw [removeNoneAux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm
      · rw [removeNoneAux_some _ ⟨_, h2⟩] at h1
        simp at h1
      · rw [removeNoneAux_none _ h2] at h1


中文:
定理 removeNoneAux_inv
  条件: (x : α)
  结论: removeNoneAux e.symm (removeNoneAux e x) = x
  证明: Option.some_injective _
    (by
      cases h1 : e.symm (some (removeNoneAux e x)) <;> cases h2 : e (some x)
      · rw [removeNoneAux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm
      · rw [removeNoneAux_some _ ⟨_, h2⟩] at h1
        simp at h1
      · rw [removeNoneAux_none _ h2] at h1


Depends on / 依赖: Option.some_injective, e.eq_symm_apply.mpr, e.symm, eq_symm_apply, removeNoneAux, removeNoneAux_none, removeNoneAux_some, some_injective
-/
theorem removeNoneAux_inv (x : α) : removeNoneAux e.symm (removeNoneAux e x) = x :=
  Option.some_injective _
    (by
      cases h1 : e.symm (some (removeNoneAux e x)) <;> cases h2 : e (some x)
      · rw [removeNoneAux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm
      · rw [removeNoneAux_some _ ⟨_, h2⟩] at h1
        simp at h1
      · rw [removeNoneAux_none _ h2] at h1
        simp at h1
      · rw [removeNoneAux_some _ ⟨_, h1⟩]
        rw [removeNoneAux_some _ ⟨_]; rw [h2⟩]
        simp)

@[deprecated (since := "2026-06-06")] alias removeNone_aux := removeNoneAux
@[deprecated (since := "2026-06-06")] alias removeNone_aux_none := removeNoneAux_none
@[deprecated (since := "2026-06-06")] alias removeNone_aux_some := removeNoneAux_some
@[deprecated (since := "2026-06-06")] alias removeNone_aux_inv := removeNoneAux_inv

/--
Definition of `removeNone` / `removeNone` 的定义

English:
definition removeNone
  signature: : α ≃ β where
  body: removeNoneAux e
  invFun := removeNoneAux e.symm
  left_inv := removeNoneAux_inv e
  right_inv := removeNoneAux_inv e.symm

@[simp]

中文:
定义 removeNone
  签名: : α ≃ β where
  定义体: removeNoneAux e
  invFun := removeNoneAux e.symm
  left_inv := removeNoneAux_inv e
  right_inv := removeNoneAux_inv e.symm

@[simp]

Depends on / 依赖: removeNoneAux
-/
def removeNone : α ≃ β where
  toFun := removeNoneAux e
  invFun := removeNoneAux e.symm
  left_inv := removeNoneAux_inv e
  right_inv := removeNoneAux_inv e.symm

@[simp]
/--
theorem `removeNone_symm` / 定理 `removeNone_symm`

English:
theorem removeNone_symm
  statement: (removeNone e).symm = removeNone e.symm
  proof: rfl

中文:
定理 removeNone_symm
  结论: (removeNone e).symm = removeNone e.symm
  证明: rfl
-/
theorem removeNone_symm : (removeNone e).symm = removeNone e.symm :=
  rfl

/--
theorem `removeNone_some` / 定理 `removeNone_some`

English:
theorem removeNone_some
  given: {x : α} (h : exists x', e (some x) = some x')
  proof: removeNoneAux_some e h

中文:
定理 removeNone_some
  条件: {x : α} (h : 存在 x', e (some x) = some x')
  证明: removeNoneAux_some e h

Depends on / 依赖: removeNoneAux_some
-/
theorem removeNone_some {x : α} (h : exists x', e (some x) = some x') :
    some (removeNone e x) = e (some x) :=
  removeNoneAux_some e h

/--
theorem `removeNone_none` / 定理 `removeNone_none`

English:
theorem removeNone_none
  given: {x : α} (h : e (some x) = none)
  statement: some (removeNone e x) = e none
  proof: removeNoneAux_none e h

@[simp]

中文:
定理 removeNone_none
  条件: {x : α} (h : e (some x) = none)
  结论: some (removeNone e x) = e none
  证明: removeNoneAux_none e h

@[simp]

Depends on / 依赖: removeNoneAux_none
-/
theorem removeNone_none {x : α} (h : e (some x) = none) : some (removeNone e x) = e none :=
  removeNoneAux_none e h

@[simp]
/--
theorem `option_symm_apply_none_iff` / 定理 `option_symm_apply_none_iff`

English:
theorem option_symm_apply_none_iff
  statement: e.symm none = none ↔ e none = none
  proof: ⟨fun h => by simpa using (congr_arg e h).symm, fun h => by simpa using (congr_arg e.symm h).symm⟩

中文:
定理 option_symm_apply_none_iff
  结论: e.symm none = none ↔ e none = none
  证明: ⟨fun h => by simpa using (congr_arg e h).symm, fun h => by simpa using (congr_arg e.symm h).symm⟩

Depends on / 依赖: congr_arg, e.symm
-/
theorem option_symm_apply_none_iff : e.symm none = none ↔ e none = none :=
  ⟨fun h => by simpa using (congr_arg e h).symm, fun h => by simpa using (congr_arg e.symm h).symm⟩

/--
theorem `some_removeNone_iff` / 定理 `some_removeNone_iff`

English:
theorem some_removeNone_iff
  given: {x : α}
  statement: some (removeNone e x) = e none ↔ e.symm none = some x
  proof: by
  rcases h : e (some x) with a | a
  · rw [removeNone_none _ h]
    simpa using (congr_arg e.symm h).symm
  · rw [removeNone_some _ ⟨a, h⟩]
    have h1 := congr_arg e.symm h
    rw [symm_apply_apply] at h1
    simp only [apply_eq_iff_eq, reduceCtorEq]
    simp [h1]

@[simp]

中文:
定理 some_removeNone_iff
  条件: {x : α}
  结论: some (removeNone e x) = e none ↔ e.symm none = some x
  证明: by
  rcases h : e (some x) with a | a
  · rw [removeNone_none _ h]
    simpa using (congr_arg e.symm h).symm
  · rw [removeNone_some _ ⟨a, h⟩]
    have h1 := congr_arg e.symm h
    rw [symm_apply_apply] at h1
    simp only [apply_eq_iff_eq, reduceCtorEq]
    simp [h1]

@[simp]

Depends on / 依赖: apply_eq_iff_eq, congr_arg, e.symm, reduceCtorEq, removeNone_none, removeNone_some, symm_apply_apply
-/
theorem some_removeNone_iff {x : α} : some (removeNone e x) = e none ↔ e.symm none = some x := by
  rcases h : e (some x) with a | a
  · rw [removeNone_none _ h]
    simpa using (congr_arg e.symm h).symm
  · rw [removeNone_some _ ⟨a, h⟩]
    have h1 := congr_arg e.symm h
    rw [symm_apply_apply] at h1
    simp only [apply_eq_iff_eq, reduceCtorEq]
    simp [h1]

@[simp]
/--
theorem `removeNone_optionCongr` / 定理 `removeNone_optionCongr`

English:
theorem removeNone_optionCongr
  given: (e : α ≃ β)
  statement: removeNone e.optionCongr = e
  proof: Equiv.ext fun x => Option.some_injective _ removeNone_some _ ⟨e x, by simp⟩

中文:
定理 removeNone_optionCongr
  条件: (e : α ≃ β)
  结论: removeNone e.optionCongr = e
  证明: Equiv.ext fun x => Option.some_injective _ removeNone_some _ ⟨e x, by simp⟩

Depends on / 依赖: Equiv.ext, Option.some_injective, removeNone_some, some_injective
-/
theorem removeNone_optionCongr (e : α ≃ β) : removeNone e.optionCongr = e :=
Equiv.ext fun x => Option.some_injective _ removeNone_some _ ⟨e x, by simp⟩

end RemoveNone

/--
theorem `optionCongr_injective` / 定理 `optionCongr_injective`

English:
theorem optionCongr_injective
  statement: Function.Injective (optionCongr : α ≃ β -> Option α ≃ Option β)
  proof: Function.LeftInverse.injective removeNone_optionCongr

中文:
定理 optionCongr_injective
  结论: 函数.单射 (optionCongr : α ≃ β -> 选项类型 α ≃ 选项类型 β)
  证明: Function.LeftInverse.injective removeNone_optionCongr

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, removeNone_optionCongr
-/
theorem optionCongr_injective : Function.Injective (optionCongr : α ≃ β -> Option α ≃ Option β) :=
  Function.LeftInverse.injective removeNone_optionCongr

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `optionSubtype` / `optionSubtype` 的定义

English:
definition optionSubtype
  signature: [DecidableEq β] (x : β)
  body: { toFun := fun a =>
        ⟨(e : Option α ≃ β) a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((eq_symm_apply _).2 e.property).symm).2 b.property)

中文:
定义 optionSubtype
  签名: [DecidableEq β] (x : β)
  定义体: { toFun := fun a =>
        ⟨(e : Option α ≃ β) a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((eq_symm_apply _).2 e.property).symm).2 b.property)

Depends on / 依赖: EquivLike, EquivLike.injective, Subtype, Subtype.val, b.property, casesOn, e.property, e.symm, eq_symm_apply, injective, invFun, left_inv, ne_iff, ne_none_iff_isSome, property, right_inv, some_get, some_inj, some_ne_none, symm_apply_apply
-/
def optionSubtype [DecidableEq β] (x : β) :
    { e : Option α ≃ β // e none = x } ≃ (α ≃ { y : β // y != x }) where
  toFun e :=
    { toFun := fun a =>
        ⟨(e : Option α ≃ β) a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((eq_symm_apply _).2 e.property).symm).2 b.property)),
      left_inv := fun a => by
        rw [← some_inj]; rw [some_get]
        exact symm_apply_apply (e : Option α ≃ β) a,
      right_inv := fun b => by
        ext
        simp }
  invFun e :=
    ⟨{ toFun := fun a => casesOn' a x (Subtype.val ∘ e),
        invFun := fun b => if h : b = x then none else e.symm ⟨b, h⟩,
        left_inv := fun a => by
          cases a with
          | none => simp
          | some a =>
            simp only [casesOn'_some, Function.comp_apply, Subtype.coe_eta,
              symm_apply_apply, dite_eq_ite]
            exact if_neg (e a).property,
        right_inv := fun b => by
          by_cases h : b = x <;> simp [h] },
      rfl⟩
  left_inv e := by
    ext a
    cases a
    · simpa using e.property.symm
    · simp
  right_inv e := by
    ext a
    rfl

@[simp]
/--
theorem `optionSubtype_apply_apply` / 定理 `optionSubtype_apply_apply`

English:
theorem optionSubtype_apply_apply
  proof: rfl

@[simp]

中文:
定理 optionSubtype_apply_apply
  证明: rfl

@[simp]
-/
theorem optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α)
    (h) : optionSubtype x e a = ⟨(e : Option α ≃ β) a, h⟩ := rfl

@[simp]
/--
theorem `coe_optionSubtype_apply_apply` / 定理 `coe_optionSubtype_apply_apply`

English:
theorem coe_optionSubtype_apply_apply
  proof: rfl

中文:
定理 coe_optionSubtype_apply_apply
  证明: rfl
-/
theorem coe_optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α) : ↑(optionSubtype x e a) = (e : Option α ≃ β) a := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `optionSubtype_apply_symm_apply` / 定理 `optionSubtype_apply_symm_apply`

English:
theorem optionSubtype_apply_symm_apply
  proof: by
  dsimp only [optionSubtype]
  simp

@[simp]

中文:
定理 optionSubtype_apply_symm_apply
  证明: by
  dsimp only [optionSubtype]
  simp

@[simp]

Depends on / 依赖: optionSubtype
-/
theorem optionSubtype_apply_symm_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (b : { y : β // y != x }) : ↑((optionSubtype x e).symm b) = (e : Option α ≃ β).symm b := by
  dsimp only [optionSubtype]
  simp

@[simp]
/--
theorem `optionSubtype_symm_apply_apply_coe` / 定理 `optionSubtype_symm_apply_apply_coe`

English:
theorem optionSubtype_symm_apply_apply_coe
  statement: [DecidableEq β] (x : β) (e : α ≃ { y : β // y != x })
  proof: rfl

@[simp]

中文:
定理 optionSubtype_symm_apply_apply_coe
  结论: [DecidableEq β] (x : β) (e : α ≃ { y : β // y != x })
  证明: rfl

@[simp]
-/
theorem optionSubtype_symm_apply_apply_coe [DecidableEq β] (x : β) (e : α ≃ { y : β // y != x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) a = e a :=
  rfl

@[simp]
/--
theorem `optionSubtype_symm_apply_apply_some` / 定理 `optionSubtype_symm_apply_apply_some`

English:
theorem optionSubtype_symm_apply_apply_some
  proof: rfl

@[simp]

中文:
定理 optionSubtype_symm_apply_apply_some
  证明: rfl

@[simp]
-/
theorem optionSubtype_symm_apply_apply_some
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y != x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) (some a) = e a :=
  rfl

@[simp]
/--
theorem `optionSubtype_symm_apply_apply_none` / 定理 `optionSubtype_symm_apply_apply_none`

English:
theorem optionSubtype_symm_apply_apply_none
  proof: rfl

中文:
定理 optionSubtype_symm_apply_apply_none
  证明: rfl
-/
theorem optionSubtype_symm_apply_apply_none
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y != x }) : ((optionSubtype x).symm e : Option α ≃ β) none = x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `optionSubtype_symm_apply_symm_apply` / 定理 `optionSubtype_symm_apply_symm_apply`

English:
theorem optionSubtype_symm_apply_symm_apply
  statement: [DecidableEq β] (x : β) (e : α ≃ { y : β // y != x })
  proof: by
  simp only [optionSubtype, coe_fn_symm_mk, Subtype.coe_mk,
             Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff]
  exact fun h => False.elim (b.property h)

中文:
定理 optionSubtype_symm_apply_symm_apply
  结论: [DecidableEq β] (x : β) (e : α ≃ { y : β // y != x })
  证明: by
  simp only [optionSubtype, coe_fn_symm_mk, Subtype.coe_mk,
             Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff]
  exact fun h => False.elim (b.property h)

Depends on / 依赖: False.elim, Subtype, Subtype.coe_eta, Subtype.coe_mk, b.property, coe_eta, coe_fn_symm_mk, coe_mk, dite_eq_ite, ite_eq_right_iff, optionSubtype, property
-/
theorem optionSubtype_symm_apply_symm_apply [DecidableEq β] (x : β) (e : α ≃ { y : β // y != x })
    (b : { y : β // y != x }) : ((optionSubtype x).symm e : Option α ≃ β).symm b = e.symm b := by
  simp only [optionSubtype, coe_fn_symm_mk, Subtype.coe_mk,
             Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff]
  exact fun h => False.elim (b.property h)

variable [DecidableEq α] {a b : α}

/-- Any type with a distinguished element is equivalent to an `Option` type on the subtype excluding
that element. -/
@[simps!]
.1 .symm (.refl _) def optionSubtypeNe (a : α) : Option {b // b != a} ≃ α := optionSubtype a

/--
lemma `optionSubtypeNe_symm_self` / 引理 `optionSubtypeNe_symm_self`

English:
lemma optionSubtypeNe_symm_self
  given: (a : α)
  statement: (optionSubtypeNe a).symm a = none
  proof: by simp

中文:
引理 optionSubtypeNe_symm_self
  条件: (a : α)
  结论: (optionSubtypeNe a).symm a = none
  证明: by simp
-/
lemma optionSubtypeNe_symm_self (a : α) : (optionSubtypeNe a).symm a = none := by simp
/--
lemma `optionSubtypeNe_symm_of_ne` / 引理 `optionSubtypeNe_symm_of_ne`

English:
lemma optionSubtypeNe_symm_of_ne
  given: (hba : b != a)
  statement: (optionSubtypeNe a).symm b = some ⟨b, hba⟩
  proof: by
  simp [hba]

中文:
引理 optionSubtypeNe_symm_of_ne
  条件: (hba : b != a)
  结论: (optionSubtypeNe a).symm b = some ⟨b, hba⟩
  证明: by
  simp [hba]
-/
lemma optionSubtypeNe_symm_of_ne (hba : b != a) : (optionSubtypeNe a).symm b = some ⟨b, hba⟩ := by
  simp [hba]

/--
lemma `optionSubtypeNe_none` / 引理 `optionSubtypeNe_none`

English:
lemma optionSubtypeNe_none
  given: (a : α)
  statement: optionSubtypeNe a none = a
  proof: rfl

中文:
引理 optionSubtypeNe_none
  条件: (a : α)
  结论: optionSubtypeNe a none = a
  证明: rfl
-/
@[simp] lemma optionSubtypeNe_none (a : α) : optionSubtypeNe a none = a := rfl
/--
lemma `optionSubtypeNe_some` / 引理 `optionSubtypeNe_some`

English:
lemma optionSubtypeNe_some
  given: (a : α) (b)
  statement: optionSubtypeNe a (some b) = b
  proof: rfl

中文:
引理 optionSubtypeNe_some
  条件: (a : α) (b)
  结论: optionSubtypeNe a (some b) = b
  证明: rfl
-/
@[simp] lemma optionSubtypeNe_some (a : α) (b) : optionSubtypeNe a (some b) = b := rfl

open Sum

/--
Definition of `optionEquivSumPUnit.` / `optionEquivSumPUnit.` 的定义

English:
definition optionEquivSumPUnit.{v,
  signature: w} (α
  body: ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none,
    fun o => by cases o <;> rfl,
    fun s => by rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩

@[simp]

中文:
定义 optionEquivSumPUnit.{v,
  签名: w} (α
  定义体: ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none,
    fun o => by cases o <;> rfl,
    fun s => by rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩

@[simp]

Depends on / 依赖: PUnit.unit, o.elim, s.elim
-/
def optionEquivSumPUnit.{v, w} (α : Type w) : Option α ≃ α oplus PUnit.{v + 1} :=
  ⟨fun o => o.elim (inr PUnit.unit) inl, fun s => s.elim some fun _ => none,
    fun o => by cases o <;> rfl,
    fun s => by rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩

@[simp]
/--
theorem `optionEquivSumPUnit_none` / 定理 `optionEquivSumPUnit_none`

English:
theorem optionEquivSumPUnit_none
  given: {α}
  statement: optionEquivSumPUnit α none = Sum.inr PUnit.unit
  proof: rfl

@[simp]

中文:
定理 optionEquivSumPUnit_none
  条件: {α}
  结论: optionEquivSumPUnit α none = 和.inr 命题单元.unit
  证明: rfl

@[simp]
-/
theorem optionEquivSumPUnit_none {α} : optionEquivSumPUnit α none = Sum.inr PUnit.unit :=
  rfl

@[simp]
/--
theorem `optionEquivSumPUnit_some` / 定理 `optionEquivSumPUnit_some`

English:
theorem optionEquivSumPUnit_some
  given: {α} (a)
  statement: optionEquivSumPUnit α (some a) = Sum.inl a
  proof: rfl

@[simp]

中文:
定理 optionEquivSumPUnit_some
  条件: {α} (a)
  结论: optionEquivSumPUnit α (some a) = 和.inl a
  证明: rfl

@[simp]
-/
theorem optionEquivSumPUnit_some {α} (a) : optionEquivSumPUnit α (some a) = Sum.inl a :=
  rfl

@[simp]
/--
theorem `optionEquivSumPUnit_coe` / 定理 `optionEquivSumPUnit_coe`

English:
theorem optionEquivSumPUnit_coe
  given: {α} (a : α)
  statement: optionEquivSumPUnit α a = Sum.inl a
  proof: rfl

@[simp]

中文:
定理 optionEquivSumPUnit_coe
  条件: {α} (a : α)
  结论: optionEquivSumPUnit α a = 和.inl a
  证明: rfl

@[simp]
-/
theorem optionEquivSumPUnit_coe {α} (a : α) : optionEquivSumPUnit α a = Sum.inl a :=
  rfl

@[simp]
/--
theorem `optionEquivSumPUnit_symm_inl` / 定理 `optionEquivSumPUnit_symm_inl`

English:
theorem optionEquivSumPUnit_symm_inl
  given: {α} (a)
  statement: (optionEquivSumPUnit α).symm (Sum.inl a) = a
  proof: rfl

@[simp]

中文:
定理 optionEquivSumPUnit_symm_inl
  条件: {α} (a)
  结论: (optionEquivSumPUnit α).symm (和.inl a) = a
  证明: rfl

@[simp]
-/
theorem optionEquivSumPUnit_symm_inl {α} (a) : (optionEquivSumPUnit α).symm (Sum.inl a) = a :=
  rfl

@[simp]
/--
theorem `optionEquivSumPUnit_symm_inr` / 定理 `optionEquivSumPUnit_symm_inr`

English:
theorem optionEquivSumPUnit_symm_inr
  given: {α} (a)
  statement: (optionEquivSumPUnit α).symm (Sum.inr a) = none
  proof: rfl

中文:
定理 optionEquivSumPUnit_symm_inr
  条件: {α} (a)
  结论: (optionEquivSumPUnit α).symm (和.inr a) = none
  证明: rfl
-/
theorem optionEquivSumPUnit_symm_inr {α} (a) : (optionEquivSumPUnit α).symm (Sum.inr a) = none :=
  rfl

/-- The set of `x : Option α` such that `isSome x` is equivalent to `α`. -/
@[simps]
/--
Definition of `optionIsSomeEquiv` / `optionIsSomeEquiv` 的定义

English:
definition optionIsSomeEquiv
  signature: (α)
  body: Option.get _ o.2
  invFun x := ⟨some x, rfl⟩
left_inv _ := Subtype.ext Option.some_get _
  right_inv _ := Option.get_some _ _

中文:
定义 optionIsSomeEquiv
  签名: (α)
  定义体: Option.get _ o.2
  invFun x := ⟨some x, rfl⟩
left_inv _ := Subtype.ext Option.some_get _
  right_inv _ := Option.get_some _ _

Depends on / 依赖: Option.get
-/
def optionIsSomeEquiv (α) : { x : Option α // x.isSome } ≃ α where
  toFun o := Option.get _ o.2
  invFun x := ⟨some x, rfl⟩
left_inv _ := Subtype.ext Option.some_get _
  right_inv _ := Option.get_some _ _

/--
Definition of `subtypeNeSumPUnit` / `subtypeNeSumPUnit` 的定义

English:
abbreviation subtypeNeSumPUnit
  signature: (i₀ : α)
  body: (Equiv.optionEquivSumPUnit.{u} _).symm.trans (Equiv.optionSubtypeNe i₀)

中文:
缩写 subtypeNeSumPUnit
  签名: (i₀ : α)
  定义体: (Equiv.optionEquivSumPUnit.{u} _).symm.trans (Equiv.optionSubtypeNe i₀)

Depends on / 依赖: Equiv.optionEquivSumPUnit, Equiv.optionSubtypeNe, optionEquivSumPUnit, optionSubtypeNe, symm.trans
-/
abbrev subtypeNeSumPUnit (i₀ : α) : { i // i != i₀ } oplus PUnit.{u + 1} ≃ α :=
  (Equiv.optionEquivSumPUnit.{u} _).symm.trans (Equiv.optionSubtypeNe i₀)

end Equiv
