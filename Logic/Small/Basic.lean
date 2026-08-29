/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.Logic.Equiv.Set

/-!
# Instances and theorems for `Small`.

In particular we prove `small_of_injective` and `small_of_surjective`.
-/

public section

assert_not_exists Countable

universe u w v v'

-- TODO(timotree3): lower the priority on this instance?
-- This instance applies to every synthesis problem of the form `Small ↥s` for some set `s`,
-- but we have lots of instances of `Small` for specific set constructions.
/--
Instance `small_subtype` / 实例 `small_subtype`

English:
instance small_subtype
  signature: (α : Type v) [Small.{w} α] (P : α -> Prop)
  body: small_map (equivShrink α).subtypeEquivOfSubtype'

中文:
实例 small_subtype
  签名: (α : 类型v) [Small.{w} α] (P : α -> 命题)
  定义体: small_map (equivShrink α).subtypeEquivOfSubtype'

Depends on / 依赖: equivShrink, small_map, subtypeEquivOfSubtype
-/
instance small_subtype (α : Type v) [Small.{w} α] (P : α -> Prop) : Small.{w} { x // P x } :=
  small_map (equivShrink α).subtypeEquivOfSubtype'

/--
theorem `small_of_injective` / 定理 `small_of_injective`

English:
theorem small_of_injective
  statement: {α : Type v} {β : Type w} [Small.{u} β] {f : α -> β}
  proof: small_map (Equiv.ofInjective f hf)

中文:
定理 small_of_injective
  结论: {α : 类型v} {β : Type w} [Small.{u} β] {f : α -> β}
  证明: small_map (Equiv.ofInjective f hf)

Depends on / 依赖: Equiv.ofInjective, ofInjective, small_map
-/
theorem small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α -> β}
    (hf : Function.Injective f) : Small.{u} α :=
  small_map (Equiv.ofInjective f hf)

/--
theorem `small_of_surjective` / 定理 `small_of_surjective`

English:
theorem small_of_surjective
  statement: {α : Type v} {β : Type w} [Small.{u} α] {f : α -> β}
  proof: small_of_injective (Function.injective_surjInv hf)

中文:
定理 small_of_surjective
  结论: {α : 类型v} {β : Type w} [Small.{u} α] {f : α -> β}
  证明: small_of_injective (Function.injective_surjInv hf)

Depends on / 依赖: Function, Function.injective_surjInv, injective_surjInv, small_of_injective
-/
theorem small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α -> β}
    (hf : Function.Surjective f) : Small.{u} β :=
  small_of_injective (Function.injective_surjInv hf)

instance (priority := 100) small_subsingleton (α : Type v) [Subsingleton α] : Small.{w} α := by
  rcases isEmpty_or_nonempty α with ⟨⟩
  · apply small_map (Equiv.equivPEmpty α)
  · apply small_map Equiv.punitOfNonemptyOfSubsingleton

/--
theorem `small_of_injective_of_exists` / 定理 `small_of_injective_of_exists`

English:
theorem small_of_injective_of_exists
  statement: {α : Type v} {β : Type w} {γ : Type v'} [Small.{u} α]
  proof: by
  by_cases hβ : Nonempty β
  · refine small_of_surjective (f := Function.invFun g ∘ f) (fun b => ?_)
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [Function.comp_apply, ha, Function.leftInverse_invFun hg]⟩
  · simp only [not_nonempty_iff] at hβ
    infer_instance

中文:
定理 small_of_injective_of_exists
  结论: {α : 类型v} {β : Type w} {γ : 类型v'} [Small.{u} α]
  证明: by
  by_cases hβ : Nonempty β
  · refine small_of_surjective (f := Function.invFun g ∘ f) (fun b => ?_)
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [Function.comp_apply, ha, Function.leftInverse_invFun hg]⟩
  · simp only [not_nonempty_iff] at hβ
    infer_instance

Depends on / 依赖: Function, Function.comp_apply, Function.invFun, Function.leftInverse_invFun, Nonempty, comp_apply, infer_instance, invFun, leftInverse_invFun, not_nonempty_iff, small_of_surjective
-/
theorem small_of_injective_of_exists {α : Type v} {β : Type w} {γ : Type v'} [Small.{u} α]
    (f : α -> γ) {g : β -> γ} (hg : Function.Injective g) (h : forall b : β, exists a : α, f a = g b) :
    Small.{u} β := by
  by_cases hβ : Nonempty β
  · refine small_of_surjective (f := Function.invFun g ∘ f) (fun b => ?_)
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [Function.comp_apply, ha, Function.leftInverse_invFun hg]⟩
  · simp only [not_nonempty_iff] at hβ
    infer_instance


/--
Instance `small_Pi` / 实例 `small_Pi`

English:
instance small_Pi
  signature: {α} (β : α -> Type*) [Small.{w} α] [forall a, Small.{w} (β a)]
  body: ⟨⟨forall a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

中文:
实例 small_Pi
  签名: {α} (β : α -> 类型) [Small.{w} α] [对任意 a, Small.{w} (β a)]
  定义体: ⟨⟨forall a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

Depends on / 依赖: Equiv.piCongr, Shrink, equivShrink, piCongr
-/
instance small_Pi {α} (β : α -> Type*) [Small.{w} α] [forall a, Small.{w} (β a)] :
    Small.{w} (forall a, β a) :=
  ⟨⟨forall a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.piCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩

/--
Instance `small_prod` / 实例 `small_prod`

English:
instance small_prod
  signature: {α β} [Small.{w} α] [Small.{w} β]
  body: ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩

中文:
实例 small_prod
  签名: {α β} [Small.{w} α] [Small.{w} β]
  定义体: ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩

Depends on / 依赖: Equiv.prodCongr, Shrink, equivShrink, prodCongr
-/
instance small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  ⟨⟨Shrink α × Shrink β, ⟨Equiv.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩

/--
Instance `small_sum` / 实例 `small_sum`

English:
instance small_sum
  signature: {α β} [Small.{w} α] [Small.{w} β]
  body: ⟨⟨Shrink α oplus Shrink β, ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩

中文:
实例 small_sum
  签名: {α β} [Small.{w} α] [Small.{w} β]
  定义体: ⟨⟨Shrink α oplus Shrink β, ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩

Depends on / 依赖: Equiv.sumCongr, Shrink, equivShrink, sumCongr
-/
instance small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α oplus β) :=
  ⟨⟨Shrink α oplus Shrink β, ⟨Equiv.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩

/--
Instance `small_set` / 实例 `small_set`

English:
instance small_set
  signature: {α} [Small.{w} α]
  body: ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩

中文:
实例 small_set
  签名: {α} [Small.{w} α]
  定义体: ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩

Depends on / 依赖: Equiv.Set.congr, Shrink, equivShrink
-/
instance small_set {α} [Small.{w} α] : Small.{w} (Set α) :=
  ⟨⟨Set (Shrink α), ⟨Equiv.Set.congr (equivShrink α)⟩⟩⟩

/--
Instance `small_quot` / 实例 `small_quot`

English:
instance small_quot
  signature: {α : Type u} [Small.{v} α] (r : α -> α -> Prop)
  body: small_of_surjective Quot.mk_surjective

中文:
实例 small_quot
  签名: {α : 类型u} [Small.{v} α] (r : α -> α -> 命题)
  定义体: small_of_surjective Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective, small_of_surjective
-/
instance small_quot {α : Type u} [Small.{v} α] (r : α -> α -> Prop) : Small.{v} (Quot r) :=
  small_of_surjective Quot.mk_surjective

/--
Instance `small_quotient` / 实例 `small_quotient`

English:
instance small_quotient
  signature: {α : Type u} [Small.{v} α] (s : Setoid α)
  body: small_of_surjective Quotient.mk_surjective

中文:
实例 small_quotient
  签名: {α : 类型u} [Small.{v} α] (s : Setoid α)
  定义体: small_of_surjective Quotient.mk_surjective

Depends on / 依赖: Quotient, Quotient.mk_surjective, mk_surjective, small_of_surjective
-/
instance small_quotient {α : Type u} [Small.{v} α] (s : Setoid α) : Small.{v} (Quotient s) :=
  small_of_surjective Quotient.mk_surjective

/--
Instance `small_orderDual` / 实例 `small_orderDual`

English:
instance small_orderDual
  signature: {α : Type*} [h : Small.{v} α]
  body: h

中文:
实例 small_orderDual
  签名: {α : 类型} [h : Small.{v} α]
  定义体: h
-/
instance small_orderDual {α : Type*} [h : Small.{v} α] : Small.{v} αᵒᵈ := h
