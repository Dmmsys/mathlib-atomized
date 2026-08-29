/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.PPWithUniv

/-!
# Small types

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `Shrink α : Type w`, and `equivShrink α : α ≃ Shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `Small.{w} α ↔ Small.{w} β`.

See `Mathlib/Logic/Small/Basic.lean` for further instances and theorems.
-/

@[expose] public section

universe u w v v'

/-- A type is `Small.{w}` if there exists an equivalence to some `S : Type w`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423: `v` is a true output (determined by `α`),
-- but we need the attribute to prevent `w` from also being treated as output.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params v, mk_iff, pp_with_univ]
/--
Definition of `Small` / `Small` 的定义

English:
class Small
  parameters: (α : Type v)
  axioms and operations (1):
    - equiv_small : exists S : Type w, Nonempty (α ≃ S)

中文:
类 Small
  参数: (α : 类型v)
  公理与运算 (1 个):
    - equiv_small : 存在 S : 类型 w, 非空 (α ≃ S)
-/
class Small (α : Type v) : Prop where
  /-- If a type is `Small.{w}`, then there exists an equivalence with some `S : Type w` -/
  equiv_small : exists S : Type w, Nonempty (α ≃ S)

/--
theorem `Small.mk'` / 定理 `Small.mk'`

English:
theorem Small.mk'
  given: {α : Type v} {S : Type w} (e : α ≃ S)
  statement: Small.{w} α
  proof: ⟨⟨S, ⟨e⟩⟩⟩

中文:
定理 Small.mk'
  条件: {α : 类型v} {S : 类型 w} (e : α ≃ S)
  结论: Small.{w} α
  证明: ⟨⟨S, ⟨e⟩⟩⟩
-/
theorem Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α :=
  ⟨⟨S, ⟨e⟩⟩⟩

/-- An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[pp_with_univ, no_expose]
/--
Definition of `Shrink` / `Shrink` 的定义

English:
definition Shrink
  signature: (α : Type v) [Small.{w} α]
  body: Classical.choose (@Small.equiv_small α _)

中文:
定义 Shrink
  签名: (α : 类型v) [Small.{w} α]
  定义体: Classical.choose (@Small.equiv_small α _)

Depends on / 依赖: Classical, Classical.choose, Small.equiv_small, equiv_small
-/
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.choose (@Small.equiv_small α _)

/-- The noncomputable equivalence between a `w`-small type and a model.
-/
@[no_expose]
/--
Definition of `equivShrink` / `equivShrink` 的定义

English:
definition equivShrink
  signature: (α : Type v) [Small.{w} α]
  body: Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))

@[ext]

中文:
定义 equivShrink
  签名: (α : 类型v) [Small.{w} α]
  定义体: Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))

@[ext]

Depends on / 依赖: Classical, Classical.choose_spec, Nonempty, Nonempty.some, Small.equiv_small, choose_spec, equiv_small
-/
noncomputable def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))

@[ext]
/--
theorem `Shrink.ext` / 定理 `Shrink.ext`

English:
theorem Shrink.ext
  statement: {α : Type v} [Small.{w} α] {x y : Shrink α}
  proof: by
  simpa using w

中文:
定理 Shrink.ext
  结论: {α : 类型v} [Small.{w} α] {x y : Shrink α}
  证明: by
  simpa using w
-/
theorem Shrink.ext {α : Type v} [Small.{w} α] {x y : Shrink α}
    (w : (equivShrink _).symm x = (equivShrink _).symm y) : x = y := by
  simpa using w

-- It would be nice to mark this as `aesop cases` if
-- https://github.com/leanprover-community/aesop/issues/59
-- is resolved.
@[induction_eliminator]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Shrink.rec {α : Type*} [Small.{w} α] {F : Shrink α -> Sort v}
  body: fun X => ((equivShrink _).apply_symm_apply X) ▸ (h _)

@[simp]

中文:
定义 noncomputable
  签名: def Shrink.rec {α : 类型} [Small.{w} α] {F : Shrink α -> 类型层 v}
  定义体: fun X => ((equivShrink _).apply_symm_apply X) ▸ (h _)

@[simp]
-/
protected noncomputable def Shrink.rec {α : Type*} [Small.{w} α] {F : Shrink α -> Sort v}
    (h : forall X, F (equivShrink _ X)) : forall X, F X :=
  fun X => ((equivShrink _).apply_symm_apply X) ▸ (h _)

@[simp]
/--
lemma `Shrink.rec_equivShrink` / 引理 `Shrink.rec_equivShrink`

English:
lemma Shrink.rec_equivShrink
  statement: {α : Type*} [Small.{w} α] {F : Shrink α -> Sort v}
  proof: by
  simp only [Shrink.rec, eqRec_eq_cast, cast_eq_iff_heq]
  rw [Equiv.symm_apply_apply]

中文:
引理 Shrink.rec_equivShrink
  结论: {α : 类型} [Small.{w} α] {F : Shrink α -> 类型层 v}
  证明: by
  simp only [Shrink.rec, eqRec_eq_cast, cast_eq_iff_heq]
  rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, Shrink, Shrink.rec, cast_eq_iff_heq, eqRec_eq_cast, symm_apply_apply
-/
lemma Shrink.rec_equivShrink {α : Type*} [Small.{w} α] {F : Shrink α -> Sort v}
    {f : (a : α) -> F (equivShrink α a)} (a : α) : Shrink.rec f (equivShrink _ a) = f a := by
  simp only [Shrink.rec, eqRec_eq_cast, cast_eq_iff_heq]
  rw [Equiv.symm_apply_apply]

/--
Instance `small_self` / 实例 `small_self`

English:
instance small_self
  signature: (α : Type v)
  body: Small.mk' Equiv.refl α

中文:
实例 small_self
  签名: (α : 类型v)
  定义体: Small.mk' Equiv.refl α

Depends on / 依赖: Equiv.refl, Small.mk
-/
instance small_self (α : Type v) : Small.{v} α :=
Small.mk' Equiv.refl α

/--
theorem `small_map` / 定理 `small_map`

English:
theorem small_map
  given: {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃ β)
  statement: Small.{w} α
  proof: let ⟨_, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)

中文:
定理 small_map
  条件: {α : 类型} {β : 类型} [hβ : Small.{w} β] (e : α ≃ β)
  结论: Small.{w} α
  证明: let ⟨_, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)

Depends on / 依赖: Small.mk, e.trans, equiv_small
-/
theorem small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃ β) : Small.{w} α :=
  let ⟨_, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)

/--
theorem `small_lift` / 定理 `small_lift`

English:
theorem small_lift
  given: (α : Type u) [hα : Small.{v} α]
  statement: Small.{max v w} α
  proof: let ⟨⟨_, ⟨f⟩⟩⟩ := hα
Small.mk' f.trans (Equiv.ulift.{w}).symm

中文:
定理 small_lift
  条件: (α : 类型u) [hα : Small.{v} α]
  结论: Small.{最大值 v w} α
  证明: let ⟨⟨_, ⟨f⟩⟩⟩ := hα
Small.mk' f.trans (Equiv.ulift.{w}).symm

Depends on / 依赖: Equiv.ulift, Small.mk, f.trans
-/
theorem small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w} α :=
  let ⟨⟨_, ⟨f⟩⟩⟩ := hα
Small.mk' f.trans (Equiv.ulift.{w}).symm

/--
lemma `small_max` / 引理 `small_max`

English:
lemma small_max
  given: (α : Type v)
  statement: Small.{max w v} α
  proof: small_lift.{v, w} α

中文:
引理 small_max
  条件: (α : 类型v)
  结论: Small.{最大值 w v} α
  证明: small_lift.{v, w} α

Depends on / 依赖: small_lift
-/
lemma small_max (α : Type v) : Small.{max w v} α :=
  small_lift.{v, w} α

/--
Instance `small_zero` / 实例 `small_zero`

English:
instance small_zero
  signature: (α : Type)
  body: small_max α

中文:
实例 small_zero
  签名: (α : 类型)
  定义体: small_max α

Depends on / 依赖: small_max
-/
instance small_zero (α : Type) : Small.{w} α := small_max α

instance (priority := 100) small_succ (α : Type v) : Small.{v + 1} α :=
  small_lift.{v, v + 1} α

/--
Instance `small_ulift` / 实例 `small_ulift`

English:
instance small_ulift
  signature: (α : Type u) [Small.{v} α]
  body: small_map Equiv.ulift

中文:
实例 small_ulift
  签名: (α : 类型u) [Small.{v} α]
  定义体: small_map Equiv.ulift

Depends on / 依赖: Equiv.ulift, small_map
-/
instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift.{w} α) :=
  small_map Equiv.ulift

/--
Instance `small_plift` / 实例 `small_plift`

English:
instance small_plift
  signature: (α : Type u) [Small.{v} α]
  body: small_map Equiv.plift

中文:
实例 small_plift
  签名: (α : 类型u) [Small.{v} α]
  定义体: small_map Equiv.plift

Depends on / 依赖: Equiv.plift, small_map
-/
instance small_plift (α : Type u) [Small.{v} α] : Small.{v} (PLift α) :=
  small_map Equiv.plift

/--
theorem `small_type` / 定理 `small_type`

English:
theorem small_type
  statement: Small.{max (u + 1) v} (Type u)
  proof: small_max.{max (u + 1) v} _

中文:
定理 small_type
  结论: Small.{最大值 (u + 1) v} (类型u)
  证明: small_max.{max (u + 1) v} _

Depends on / 依赖: small_max
-/
theorem small_type : Small.{max (u + 1) v} (Type u) :=
  small_max.{max (u + 1) v} _

instance {α : Type u} [Small.{v} α] [Nontrivial α] : Nontrivial (Shrink.{v} α) :=
  (equivShrink α).symm.nontrivial

section

/--
theorem `small_congr` / 定理 `small_congr`

English:
theorem small_congr
  given: {α : Type*} {β : Type*} (e : α ≃ β)
  statement: Small.{w} α ↔ Small.{w} β
  proof: ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩

中文:
定理 small_congr
  条件: {α : 类型} {β : 类型} (e : α ≃ β)
  结论: Small.{w} α ↔ Small.{w} β
  证明: ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩

Depends on / 依赖: e.symm, small_map
-/
theorem small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w} α ↔ Small.{w} β :=
  ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩

/--
Instance `small_sigma` / 实例 `small_sigma`

English:
instance small_sigma
  signature: {α} (β : α -> Type*) [Small.{w} α] [forall a, Small.{w} (β a)]
  body: ⟨⟨Σ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

中文:
实例 small_sigma
  签名: {α} (β : α -> 类型) [Small.{w} α] [对任意 a, Small.{w} (β a)]
  定义体: ⟨⟨Σ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

Depends on / 依赖: Equiv.sigmaCongr, Shrink, equivShrink, sigmaCongr
-/
instance small_sigma {α} (β : α -> Type*) [Small.{w} α] [forall a, Small.{w} (β a)] :
    Small.{w} (Σ a, β a) :=
  ⟨⟨Σ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `not_small_type` / 定理 `not_small_type`

English:
theorem not_small_type
  statement: ¬Small.{u} (Type max u v)

中文:
定理 not_small_type
  结论: ¬Small.{u} (类型 最大值 u v)
-/
theorem not_small_type : ¬Small.{u} (Type max u v)
  | ⟨⟨S, ⟨e⟩⟩⟩ =>
    @Function.cantor_injective (Σ α, e.symm α) (fun a => ⟨_, cast (e.3 _).symm a⟩) fun a b e => by
      dsimp at e
      injection e with h₁ h₂
      simpa using h₂

end
