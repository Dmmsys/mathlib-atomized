/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Control.ULift
public import Mathlib.Logic.Equiv.Basic

/-!
# Extra lemmas about `ULift` and `PLift`

In this file we provide `Subsingleton`, `Unique`, `DecidableEq`, and `isEmpty` instances for
`ULift α` and `PLift α`. We also prove `ULift.forall`, `ULift.exists`, `PLift.forall`, and
`PLift.exists`.
-/

public section

universe u v u' v'

open Function

namespace PLift

variable {α : Sort u} {β : Sort v} {f : α -> β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (PLift α)
  body: Equiv.plift.nonempty

中文:
实例 [非空
  签名: α] : 非空 (命题层提升 α)
  定义体: Equiv.plift.nonempty

Depends on / 依赖: Equiv.plift.nonempty, nonempty
-/
instance [Nonempty α] : Nonempty (PLift α) :=
  Equiv.plift.nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (PLift α)
  body: Equiv.plift.unique

中文:
实例 [唯一
  签名: α] : 唯一 (命题层提升 α)
  定义体: Equiv.plift.unique

Depends on / 依赖: Equiv.plift.unique, unique
-/
instance [Unique α] : Unique (PLift α) :=
  Equiv.plift.unique

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (PLift α)
  body: Equiv.plift.decidableEq

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (命题层提升 α)
  定义体: Equiv.plift.decidableEq

Depends on / 依赖: Equiv.plift.decidableEq, decidableEq
-/
instance [DecidableEq α] : DecidableEq (PLift α) :=
  Equiv.plift.decidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : IsEmpty (PLift α)
  body: Equiv.plift.isEmpty

中文:
实例 [是空
  签名: α] : 是空 (命题层提升 α)
  定义体: Equiv.plift.isEmpty

Depends on / 依赖: Equiv.plift.isEmpty, isEmpty
-/
instance [IsEmpty α] : IsEmpty (PLift α) :=
  Equiv.plift.isEmpty

/--
theorem `up_injective` / 定理 `up_injective`

English:
theorem up_injective
  statement: Injective (@up α)
  proof: Equiv.plift.symm.injective

中文:
定理 up_injective
  结论: 单射 (@up α)
  证明: Equiv.plift.symm.injective

Depends on / 依赖: Equiv.plift.symm.injective, injective
-/
theorem up_injective : Injective (@up α) :=
  Equiv.plift.symm.injective

/--
theorem `up_surjective` / 定理 `up_surjective`

English:
theorem up_surjective
  statement: Surjective (@up α)
  proof: Equiv.plift.symm.surjective

中文:
定理 up_surjective
  结论: 满射 (@up α)
  证明: Equiv.plift.symm.surjective

Depends on / 依赖: Equiv.plift.symm.surjective, surjective
-/
theorem up_surjective : Surjective (@up α) :=
  Equiv.plift.symm.surjective

/--
theorem `up_bijective` / 定理 `up_bijective`

English:
theorem up_bijective
  statement: Bijective (@up α)
  proof: Equiv.plift.symm.bijective

中文:
定理 up_bijective
  结论: 双射 (@up α)
  证明: Equiv.plift.symm.bijective

Depends on / 依赖: Equiv.plift.symm.bijective, bijective
-/
theorem up_bijective : Bijective (@up α) :=
  Equiv.plift.symm.bijective

/--
theorem `up_inj` / 定理 `up_inj`

English:
theorem up_inj
  given: {x y : α}
  statement: up x = up y ↔ x = y
  proof: by simp

中文:
定理 up_inj
  条件: {x y : α}
  结论: up x = up y ↔ x = y
  证明: by simp
-/
theorem up_inj {x y : α} : up x = up y ↔ x = y := by simp

/--
theorem `down_surjective` / 定理 `down_surjective`

English:
theorem down_surjective
  statement: Surjective (@down α)
  proof: Equiv.plift.surjective

中文:
定理 down_surjective
  结论: 满射 (@down α)
  证明: Equiv.plift.surjective

Depends on / 依赖: Equiv.plift.surjective, surjective
-/
theorem down_surjective : Surjective (@down α) :=
  Equiv.plift.surjective

/--
theorem `down_bijective` / 定理 `down_bijective`

English:
theorem down_bijective
  statement: Bijective (@down α)
  proof: Equiv.plift.bijective

中文:
定理 down_bijective
  结论: 双射 (@down α)
  证明: Equiv.plift.bijective

Depends on / 依赖: Equiv.plift.bijective, bijective
-/
theorem down_bijective : Bijective (@down α) :=
  Equiv.plift.bijective

-- This is not a good simp lemma, as its discrimination tree key is just an arrow.
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : PLift α -> Prop}
  statement: (forall x, p x) ↔ forall x : α, p (PLift.up x)
  proof: up_surjective.forall

@[simp]

中文:
定理 «对任意»
  条件: {p : 命题层提升 α -> 命题}
  结论: (对任意 x, p x) ↔ 对任意 x : α, p (命题层提升.up x)
  证明: up_surjective.forall

@[simp]
-/
theorem «forall» {p : PLift α -> Prop} : (forall x, p x) ↔ forall x : α, p (PLift.up x) :=
  up_surjective.forall

@[simp]
/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : PLift α -> Prop}
  statement: (exists x, p x) ↔ exists x : α, p (PLift.up x)
  proof: up_surjective.exists

中文:
定理 «存在»
  条件: {p : 命题层提升 α -> 命题}
  结论: (存在 x, p x) ↔ 存在 x : α, p (命题层提升.up x)
  证明: up_surjective.exists
-/
theorem «exists» {p : PLift α -> Prop} : (exists x, p x) ↔ exists x : α, p (PLift.up x) :=
  up_surjective.exists

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  statement: Injective (PLift.map f) ↔ Injective f
  proof: (Injective.of_comp_iff' _ down_bijective).trans up_injective.of_comp_iff _

中文:
引理 map_injective
  结论: 单射 (命题层提升.map f) ↔ 单射 f
  证明: (Injective.of_comp_iff' _ down_bijective).trans up_injective.of_comp_iff _
-/
@[simp] lemma map_injective : Injective (PLift.map f) ↔ Injective f :=
(Injective.of_comp_iff' _ down_bijective).trans up_injective.of_comp_iff _

/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  statement: Surjective (PLift.map f) ↔ Surjective f
  proof: (down_surjective.of_comp_iff _).trans Surjective.of_comp_iff' up_bijective _

中文:
引理 map_surjective
  结论: 满射 (命题层提升.map f) ↔ 满射 f
  证明: (down_surjective.of_comp_iff _).trans Surjective.of_comp_iff' up_bijective _
-/
@[simp] lemma map_surjective : Surjective (PLift.map f) ↔ Surjective f :=
(down_surjective.of_comp_iff _).trans Surjective.of_comp_iff' up_bijective _

/--
lemma `map_bijective` / 引理 `map_bijective`

English:
lemma map_bijective
  statement: Bijective (PLift.map f) ↔ Bijective f
  proof: (down_bijective.of_comp_iff _).trans Bijective.of_comp_iff' up_bijective _

中文:
引理 map_bijective
  结论: 双射 (命题层提升.map f) ↔ 双射 f
  证明: (down_bijective.of_comp_iff _).trans Bijective.of_comp_iff' up_bijective _
-/
@[simp] lemma map_bijective : Bijective (PLift.map f) ↔ Bijective f :=
(down_bijective.of_comp_iff _).trans Bijective.of_comp_iff' up_bijective _

end PLift

namespace ULift

variable {α : Type u} {β : Type v} {f : α -> β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (ULift α)
  body: Equiv.ulift.nonempty

中文:
实例 [非空
  签名: α] : 非空 (类型层提升 α)
  定义体: Equiv.ulift.nonempty

Depends on / 依赖: Equiv.ulift.nonempty, nonempty
-/
instance [Nonempty α] : Nonempty (ULift α) :=
  Equiv.ulift.nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (ULift α)
  body: Equiv.ulift.unique

中文:
实例 [唯一
  签名: α] : 唯一 (类型层提升 α)
  定义体: Equiv.ulift.unique

Depends on / 依赖: Equiv.ulift.unique, unique
-/
instance [Unique α] : Unique (ULift α) :=
  Equiv.ulift.unique

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (ULift α)
  body: Equiv.ulift.decidableEq

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (类型层提升 α)
  定义体: Equiv.ulift.decidableEq

Depends on / 依赖: Equiv.ulift.decidableEq, decidableEq
-/
instance [DecidableEq α] : DecidableEq (ULift α) :=
  Equiv.ulift.decidableEq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : IsEmpty (ULift α)
  body: Equiv.ulift.isEmpty

中文:
实例 [是空
  签名: α] : 是空 (类型层提升 α)
  定义体: Equiv.ulift.isEmpty

Depends on / 依赖: Equiv.ulift.isEmpty, isEmpty
-/
instance [IsEmpty α] : IsEmpty (ULift α) :=
  Equiv.ulift.isEmpty

/--
theorem `up_injective` / 定理 `up_injective`

English:
theorem up_injective
  statement: Injective (@up α)
  proof: Equiv.ulift.symm.injective

中文:
定理 up_injective
  结论: 单射 (@up α)
  证明: Equiv.ulift.symm.injective

Depends on / 依赖: Equiv.ulift.symm.injective, injective
-/
theorem up_injective : Injective (@up α) :=
  Equiv.ulift.symm.injective

/--
theorem `up_surjective` / 定理 `up_surjective`

English:
theorem up_surjective
  statement: Surjective (@up α)
  proof: Equiv.ulift.symm.surjective

中文:
定理 up_surjective
  结论: 满射 (@up α)
  证明: Equiv.ulift.symm.surjective

Depends on / 依赖: Equiv.ulift.symm.surjective, surjective
-/
theorem up_surjective : Surjective (@up α) :=
  Equiv.ulift.symm.surjective

/--
theorem `up_bijective` / 定理 `up_bijective`

English:
theorem up_bijective
  statement: Bijective (@up α)
  proof: Equiv.ulift.symm.bijective

中文:
定理 up_bijective
  结论: 双射 (@up α)
  证明: Equiv.ulift.symm.bijective

Depends on / 依赖: Equiv.ulift.symm.bijective, bijective
-/
theorem up_bijective : Bijective (@up α) :=
  Equiv.ulift.symm.bijective

/--
theorem `up_inj` / 定理 `up_inj`

English:
theorem up_inj
  given: {x y : α}
  statement: up x = up y ↔ x = y
  proof: by simp

中文:
定理 up_inj
  条件: {x y : α}
  结论: up x = up y ↔ x = y
  证明: by simp
-/
theorem up_inj {x y : α} : up x = up y ↔ x = y := by simp

/--
theorem `down_surjective` / 定理 `down_surjective`

English:
theorem down_surjective
  statement: Surjective (@down α)
  proof: Equiv.ulift.surjective

中文:
定理 down_surjective
  结论: 满射 (@down α)
  证明: Equiv.ulift.surjective

Depends on / 依赖: Equiv.ulift.surjective, surjective
-/
theorem down_surjective : Surjective (@down α) :=
  Equiv.ulift.surjective

/--
theorem `down_bijective` / 定理 `down_bijective`

English:
theorem down_bijective
  statement: Bijective (@down α)
  proof: Equiv.ulift.bijective

@[simp]

中文:
定理 down_bijective
  结论: 双射 (@down α)
  证明: Equiv.ulift.bijective

@[simp]

Depends on / 依赖: Equiv.ulift.bijective, bijective
-/
theorem down_bijective : Bijective (@down α) :=
  Equiv.ulift.bijective

@[simp]
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : ULift α -> Prop}
  statement: (forall x, p x) ↔ forall x : α, p (ULift.up x)
  proof: up_surjective.forall

@[simp]

中文:
定理 «对任意»
  条件: {p : 类型层提升 α -> 命题}
  结论: (对任意 x, p x) ↔ 对任意 x : α, p (类型层提升.up x)
  证明: up_surjective.forall

@[simp]
-/
theorem «forall» {p : ULift α -> Prop} : (forall x, p x) ↔ forall x : α, p (ULift.up x) :=
  up_surjective.forall

@[simp]
/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : ULift α -> Prop}
  statement: (exists x, p x) ↔ exists x : α, p (ULift.up x)
  proof: up_surjective.exists

中文:
定理 «存在»
  条件: {p : 类型层提升 α -> 命题}
  结论: (存在 x, p x) ↔ 存在 x : α, p (类型层提升.up x)
  证明: up_surjective.exists
-/
theorem «exists» {p : ULift α -> Prop} : (exists x, p x) ↔ exists x : α, p (ULift.up x) :=
  up_surjective.exists

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  statement: Injective (ULift.map f : ULift.{u'} α -> ULift.{v'} β) ↔ Injective f
  proof: (Injective.of_comp_iff' _ down_bijective).trans up_injective.of_comp_iff _

中文:
引理 map_injective
  结论: 单射 (类型层提升.map f : 类型层提升.{u'} α -> 类型层提升.{v'} β) ↔ 单射 f
  证明: (Injective.of_comp_iff' _ down_bijective).trans up_injective.of_comp_iff _
-/
@[simp] lemma map_injective : Injective (ULift.map f : ULift.{u'} α -> ULift.{v'} β) ↔ Injective f :=
(Injective.of_comp_iff' _ down_bijective).trans up_injective.of_comp_iff _

/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  proof: (down_surjective.of_comp_iff _).trans Surjective.of_comp_iff' up_bijective _

中文:
引理 map_surjective
  证明: (down_surjective.of_comp_iff _).trans Surjective.of_comp_iff' up_bijective _
-/
@[simp] lemma map_surjective :
    Surjective (ULift.map f : ULift.{u'} α -> ULift.{v'} β) ↔ Surjective f :=
(down_surjective.of_comp_iff _).trans Surjective.of_comp_iff' up_bijective _

/--
lemma `map_bijective` / 引理 `map_bijective`

English:
lemma map_bijective
  statement: Bijective (ULift.map f : ULift.{u'} α -> ULift.{v'} β) ↔ Bijective f
  proof: (down_bijective.of_comp_iff _).trans Bijective.of_comp_iff' up_bijective _

@[ext]

中文:
引理 map_bijective
  结论: 双射 (类型层提升.map f : 类型层提升.{u'} α -> 类型层提升.{v'} β) ↔ 双射 f
  证明: (down_bijective.of_comp_iff _).trans Bijective.of_comp_iff' up_bijective _

@[ext]
-/
@[simp] lemma map_bijective : Bijective (ULift.map f : ULift.{u'} α -> ULift.{v'} β) ↔ Bijective f :=
(down_bijective.of_comp_iff _).trans Bijective.of_comp_iff' up_bijective _

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (x y : ULift α) (h : x.down = y.down)
  statement: x = y
  proof: congrArg up h

@[simp]

中文:
定理 ext
  条件: (x y : 类型层提升 α) (h : x.down = y.down)
  结论: x = y
  证明: congrArg up h

@[simp]
-/
theorem ext (x y : ULift α) (h : x.down = y.down) : x = y :=
  congrArg up h

@[simp]
/--
lemma `rec_update` / 引理 `rec_update`

English:
lemma rec_update
  statement: {β : ULift α -> Type*} [DecidableEq α]
  proof: Function.rec_update up_injective (ULift.rec ·) (fun _ _ => rfl) (fun
    | _, _, .up _, h => (h _ rfl).elim) _ _ _

中文:
引理 rec_update
  结论: {β : 类型层提升 α -> 类型} [DecidableEq α]
  证明: Function.rec_update up_injective (ULift.rec ·) (fun _ _ => rfl) (fun
    | _, _, .up _, h => (h _ rfl).elim) _ _ _

Depends on / 依赖: Function, Function.rec_update, ULift.rec, rec_update, up_injective
-/
lemma rec_update {β : ULift α -> Type*} [DecidableEq α]
    (f : forall a, β (.up a)) (a : α) (x : β (.up a)) :
    ULift.rec (update f a x) = update (ULift.rec f) (.up a) x :=
  Function.rec_update up_injective (ULift.rec ·) (fun _ _ => rfl) (fun
    | _, _, .up _, h => (h _ rfl).elim) _ _ _

end ULift
