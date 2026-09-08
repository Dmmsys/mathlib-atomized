/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.WellPowered

/-!
# `Type u` is well-powered

By building a categorical equivalence `MonoOver α ≌ Set α` for any `α : Type u`,
we deduce that `Subobject α ≃o Set α` and that `Type u` is well-powered.

One would hope that for a particular concrete category `C` (`AddCommGroup`, etc)
it's viable to prove `[WellPowered C]` without explicitly aligning `Subobject X`
with the "hand-rolled" definition of subobjects.

This may be possible using Lawvere theories,
but it remains to be seen whether this just pushes lumps around in the carpet.
-/

@[expose] public section


universe u

open CategoryTheory ConcreteCategory

open CategoryTheory.Subobject

/-
**subtype_val_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subtype_val_mono {α : Type u} (s : Set α) : Mono (↾(Subtype.val : s -> α))
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem subtype_val_mono {α : Type u} (s : Set α) : Mono (↾(Subtype.val : s → α)) :=
  (mono_iff_injective _).mpr Subtype.val_injective

attribute [local instance] subtype_val_mono

/-- The category of `MonoOver α`, for `α : Type u`, is equivalent to the partial order `Set α`.
-/
@[simps]
/-
**Types.monoOverEquivalenceSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Types.monoOverEquivalenceSet (α : Type u) : MonoOver α ≌ Set α where funct
or
参数：α : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `subtype_val_mono`：subtype_val_mono {α : Type u} (s : Set α) : Mono (↾(Su
btype.val : s -> α))
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s

--- 原说明 ---
The category of `MonoOver α`, for `α : Type u`, is equivalent to the partial ord
er `Set α`.
-/
noncomputable def Types.monoOverEquivalenceSet (α : Type u) : MonoOver α ≌ Set α where
  functor :=
    { obj := fun f => Set.range f.1.hom
      map := fun {f g} t =>
        homOfLE
          (by
            rintro a ⟨x, rfl⟩
            exact ⟨t.hom.1 x, congr_hom t.hom.w x⟩) }
  inverse :=
    { obj := fun s => MonoOver.mk <| ↾(Subtype.val : s → α)
      map := fun {s t} b => MonoOver.homMk (↾
        fun w => ⟨w.1, Set.mem_of_mem_of_subset w.2 b.le⟩) }
  unitIso :=
    NatIso.ofComponents fun f =>
      MonoOver.isoMk (Equiv.ofInjective f.1.hom ((mono_iff_injective _).mp f.2)).toIso
  counitIso := NatIso.ofComponents fun _ => eqToIso Subtype.range_val
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellPowered.{u} (Type u) :=
  wellPowered_of_essentiallySmall_monoOver fun α =>
    EssentiallySmall.mk' (Types.monoOverEquivalenceSet α)

/-- For `α : Type u`, `Subobject α` is order isomorphic to `Set α`.
-/
/-
**Types.subobjectEquivSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Types.subobjectEquivSet (α : Type u) : Subobject α ≃o Set α
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `α : Type u`, `Subobject α` is order isomorphic to `Set α`.
-/
noncomputable def Types.subobjectEquivSet (α : Type u) : Subobject α ≃o Set α :=
  (Types.monoOverEquivalenceSet α).thinSkeletonOrderIso
