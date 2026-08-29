/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Countable and uncountable types

In this file we define a typeclass `Countable` saying that a given `Sort*` is countable
and a typeclass `Uncountable` saying that a given `Type*` is uncountable.

See also `Encodable` for a version that singles out
a specific encoding of elements of `α` by natural numbers.

This file also provides a few instances of these typeclasses.
More instances can be found in other files.
-/

public section

open Function

universe u v

variable {α : Sort u} {β : Sort v}

/-!
### Definition and basic properties
-/

/-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
@[mk_iff countable_iff_exists_injective, wikidata Q66707394]
/--
Definition of `Countable` / `Countable` 的定义

English:
class Countable
  parameters: (α : Sort u)
  axioms and operations (1):
    - exists_injective_nat' : exists f : α -> Nat, Injective f

中文:
类 Countable
  参数: (α : Sort u)
  公理与运算 (1 个):
    - exists_injective_nat' : 存在 f : α -> 自然数, Injective f
-/
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : exists f : α -> Nat, Injective f

/--
lemma `Countable.exists_injective_nat` / 引理 `Countable.exists_injective_nat`

English:
lemma Countable.exists_injective_nat
  given: (α : Sort u) [Countable α]
  statement: exists f : α -> Nat, Injective f
  proof: Countable.exists_injective_nat'

中文:
引理 Countable.exists_injective_nat
  条件: (α : Sort u) [Countable α]
  结论: 存在 f : α -> 自然数, Injective f
  证明: Countable.exists_injective_nat'

Depends on / 依赖: Countable, Countable.exists_injective_nat, exists_injective_nat
-/
lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : exists f : α -> Nat, Injective f :=
  Countable.exists_injective_nat'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable Nat
  body: ⟨⟨id, injective_id⟩⟩

中文:
实例 :
  签名: Countable 自然数
  定义体: ⟨⟨id, injective_id⟩⟩

Depends on / 依赖: injective_id
-/
instance : Countable Nat :=
  ⟨⟨id, injective_id⟩⟩

export Countable (exists_injective_nat)

/--
theorem `Function.Injective.countable` / 定理 `Function.Injective.countable`

English:
theorem Function.Injective.countable
  given: [Countable β] {f : α -> β} (hf : Injective f)
  proof: let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩

中文:
定理 Function.Injective.countable
  条件: [Countable β] {f : α -> β} (hf : Injective f)
  证明: let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩
-/
protected theorem Function.Injective.countable [Countable β] {f : α -> β} (hf : Injective f) :
    Countable α :=
  let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩

/--
theorem `Function.Surjective.countable` / 定理 `Function.Surjective.countable`

English:
theorem Function.Surjective.countable
  given: [Countable α] {f : α -> β} (hf : Surjective f)
  proof: (injective_surjInv hf).countable

中文:
定理 Function.Surjective.countable
  条件: [Countable α] {f : α -> β} (hf : Surjective f)
  证明: (injective_surjInv hf).countable
-/
protected theorem Function.Surjective.countable [Countable α] {f : α -> β} (hf : Surjective f) :
    Countable β :=
  (injective_surjInv hf).countable

/--
theorem `exists_surjective_nat` / 定理 `exists_surjective_nat`

English:
theorem exists_surjective_nat
  given: (α : Sort u) [Nonempty α] [Countable α]
  statement: exists f : Nat -> α, Surjective f
  proof: let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, invFun_surjective hf⟩

中文:
定理 exists_surjective_nat
  条件: (α : Sort u) [Nonempty α] [Countable α]
  结论: 存在 f : 自然数 -> α, Surjective f
  证明: let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, invFun_surjective hf⟩

Depends on / 依赖: exists_injective_nat, invFun, invFun_surjective
-/
theorem exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : exists f : Nat -> α, Surjective f :=
  let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, invFun_surjective hf⟩

/--
theorem `countable_iff_exists_surjective` / 定理 `countable_iff_exists_surjective`

English:
theorem countable_iff_exists_surjective
  given: [Nonempty α]
  statement: Countable α ↔ exists f : Nat -> α, Surjective f
  proof: ⟨@exists_surjective_nat _ _, fun ⟨_, hf⟩ => hf.countable⟩

中文:
定理 countable_iff_exists_surjective
  条件: [Nonempty α]
  结论: Countable α ↔ 存在 f : 自然数 -> α, Surjective f
  证明: ⟨@exists_surjective_nat _ _, fun ⟨_, hf⟩ => hf.countable⟩

Depends on / 依赖: countable, exists_surjective_nat, hf.countable
-/
theorem countable_iff_exists_surjective [Nonempty α] : Countable α ↔ exists f : Nat -> α, Surjective f :=
  ⟨@exists_surjective_nat _ _, fun ⟨_, hf⟩ => hf.countable⟩

/--
theorem `Countable.of_equiv` / 定理 `Countable.of_equiv`

English:
theorem Countable.of_equiv
  given: (α : Sort*) [Countable α] (e : α ≃ β)
  statement: Countable β
  proof: e.symm.injective.countable

中文:
定理 Countable.of_equiv
  条件: (α : Sort*) [Countable α] (e : α ≃ β)
  结论: Countable β
  证明: e.symm.injective.countable

Depends on / 依赖: countable, e.symm.injective.countable, injective
-/
theorem Countable.of_equiv (α : Sort*) [Countable α] (e : α ≃ β) : Countable β :=
  e.symm.injective.countable

/--
theorem `Equiv.countable_iff` / 定理 `Equiv.countable_iff`

English:
theorem Equiv.countable_iff
  given: (e : α ≃ β)
  statement: Countable α ↔ Countable β
  proof: ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩

中文:
定理 Equiv.countable_iff
  条件: (e : α ≃ β)
  结论: Countable α ↔ Countable β
  证明: ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩

Depends on / 依赖: Countable, Countable.of_equiv, e.symm, of_equiv
-/
theorem Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Countable β :=
  ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩

instance {β : Type v} [Countable β] : Countable (ULift.{u} β) :=
  Countable.of_equiv _ Equiv.ulift.symm



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] : Countable (PLift α)
  body: Equiv.plift.injective.countable

中文:
实例 [Countable
  签名: α] : Countable (PLift α)
  定义体: Equiv.plift.injective.countable

Depends on / 依赖: Equiv.plift.injective.countable, countable, injective
-/
instance [Countable α] : Countable (PLift α) :=
  Equiv.plift.injective.countable

instance (priority := 100) Subsingleton.to_countable [Subsingleton α] : Countable α :=
  ⟨⟨fun _ => 0, fun x y _ => Subsingleton.elim x y⟩⟩

instance (priority := 500) Subtype.countable [Countable α] {p : α -> Prop} :
    Countable { x // p x } :=
  Subtype.val_injective.countable

instance {n : Nat} : Countable (Fin n) :=
  Function.Injective.countable (@Fin.eq_of_val_eq n)

instance (priority := 100) Finite.to_countable [Finite α] : Countable α :=
  let ⟨_, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  Countable.of_equiv _ e.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable PUnit.{u}
  body: Subsingleton.to_countable

中文:
实例 :
  签名: Countable PUnit.{u}
  定义体: Subsingleton.to_countable

Depends on / 依赖: Subsingleton, Subsingleton.to_countable, to_countable
-/
instance : Countable PUnit.{u} :=
  Subsingleton.to_countable

instance (priority := 100) Prop.countable (p : Prop) : Countable p :=
  Subsingleton.to_countable

/--
Instance `Bool.countable` / 实例 `Bool.countable`

English:
instance Bool.countable
  signature: : Countable Bool
  body: ⟨⟨fun b => cond b 0 1, Bool.injective_iff.2 Nat.one_ne_zero⟩⟩

中文:
实例 Bool.countable
  签名: : Countable 布尔
  定义体: ⟨⟨fun b => cond b 0 1, Bool.injective_iff.2 Nat.one_ne_zero⟩⟩

Depends on / 依赖: Bool.injective_iff, Nat.one_ne_zero, injective_iff, one_ne_zero
-/
instance Bool.countable : Countable Bool :=
  ⟨⟨fun b => cond b 0 1, Bool.injective_iff.2 Nat.one_ne_zero⟩⟩

/--
Instance `Prop.countable'` / 实例 `Prop.countable'`

English:
instance Prop.countable'
  signature: : Countable Prop
  body: Countable.of_equiv Bool Equiv.propEquivBool.symm

中文:
实例 Prop.countable'
  签名: : Countable 命题
  定义体: Countable.of_equiv Bool Equiv.propEquivBool.symm

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.propEquivBool.symm, of_equiv, propEquivBool
-/
instance Prop.countable' : Countable Prop :=
  Countable.of_equiv Bool Equiv.propEquivBool.symm

instance (priority := 500) Quotient.countable [Countable α] {r : α -> α -> Prop} :
    Countable (Quot r) :=
  Quot.mk_surjective.countable

instance (priority := 500) [Countable α] {s : Setoid α} : Countable (Quotient s) :=
inferInstanceAs Countable (@Quot α _)

/-!
### Uncountable types
-/

/-- A type `α` is uncountable if it is not countable. -/
@[mk_iff uncountable_iff_not_countable]
/--
Definition of `Uncountable` / `Uncountable` 的定义

English:
class Uncountable
  parameters: (α : Sort*)
  axioms and operations (1):
    - not_countable : ¬Countable α

中文:
类 Uncountable
  参数: (α : Sort*)
  公理与运算 (1 个):
    - not_countable : ¬Countable α
-/
class Uncountable (α : Sort*) : Prop where
  /-- A type `α` is uncountable if it is not countable. -/
  not_countable : ¬Countable α

@[push]
/--
lemma `not_uncountable_iff` / 引理 `not_uncountable_iff`

English:
lemma not_uncountable_iff
  statement: ¬Uncountable α ↔ Countable α
  proof: by
  rw [uncountable_iff_not_countable]; rw [not_not]

@[push]

中文:
引理 not_uncountable_iff
  结论: ¬Uncountable α ↔ Countable α
  证明: by
  rw [uncountable_iff_not_countable]; rw [not_not]

@[push]

Depends on / 依赖: not_not, uncountable_iff_not_countable
-/
lemma not_uncountable_iff : ¬Uncountable α ↔ Countable α := by
  rw [uncountable_iff_not_countable]; rw [not_not]

@[push]
/--
lemma `not_countable_iff` / 引理 `not_countable_iff`

English:
lemma not_countable_iff
  statement: ¬Countable α ↔ Uncountable α
  proof: (uncountable_iff_not_countable α).symm

@[simp]

中文:
引理 not_countable_iff
  结论: ¬Countable α ↔ Uncountable α
  证明: (uncountable_iff_not_countable α).symm

@[simp]

Depends on / 依赖: uncountable_iff_not_countable
-/
lemma not_countable_iff : ¬Countable α ↔ Uncountable α := (uncountable_iff_not_countable α).symm

@[simp]
/--
lemma `not_uncountable` / 引理 `not_uncountable`

English:
lemma not_uncountable
  given: [Countable α]
  statement: ¬Uncountable α
  proof: not_uncountable_iff.2 ‹_›

@[simp]

中文:
引理 not_uncountable
  条件: [Countable α]
  结论: ¬Uncountable α
  证明: not_uncountable_iff.2 ‹_›

@[simp]

Depends on / 依赖: not_uncountable_iff
-/
lemma not_uncountable [Countable α] : ¬Uncountable α := not_uncountable_iff.2 ‹_›

@[simp]
/--
lemma `not_countable` / 引理 `not_countable`

English:
lemma not_countable
  given: [Uncountable α]
  statement: ¬Countable α
  proof: Uncountable.not_countable

中文:
引理 not_countable
  条件: [Uncountable α]
  结论: ¬Countable α
  证明: Uncountable.not_countable

Depends on / 依赖: Uncountable, Uncountable.not_countable, not_countable
-/
lemma not_countable [Uncountable α] : ¬Countable α := Uncountable.not_countable

/--
theorem `Function.Injective.uncountable` / 定理 `Function.Injective.uncountable`

English:
theorem Function.Injective.uncountable
  given: [Uncountable α] {f : α -> β} (hf : Injective f)
  proof: ⟨fun _ => not_countable hf.countable⟩

中文:
定理 Function.Injective.uncountable
  条件: [Uncountable α] {f : α -> β} (hf : Injective f)
  证明: ⟨fun _ => not_countable hf.countable⟩
-/
protected theorem Function.Injective.uncountable [Uncountable α] {f : α -> β} (hf : Injective f) :
    Uncountable β :=
  ⟨fun _ => not_countable hf.countable⟩

/--
theorem `Function.Surjective.uncountable` / 定理 `Function.Surjective.uncountable`

English:
theorem Function.Surjective.uncountable
  given: [Uncountable β] {f : α -> β} (hf : Surjective f)
  proof: (injective_surjInv hf).uncountable

中文:
定理 Function.Surjective.uncountable
  条件: [Uncountable β] {f : α -> β} (hf : Surjective f)
  证明: (injective_surjInv hf).uncountable
-/
protected theorem Function.Surjective.uncountable [Uncountable β] {f : α -> β} (hf : Surjective f) :
    Uncountable α := (injective_surjInv hf).uncountable

/--
lemma `not_injective_uncountable_countable` / 引理 `not_injective_uncountable_countable`

English:
lemma not_injective_uncountable_countable
  given: [Uncountable α] [Countable β] (f : α -> β)
  proof: fun hf => not_countable hf.countable

中文:
引理 not_injective_uncountable_countable
  条件: [Uncountable α] [Countable β] (f : α -> β)
  证明: fun hf => not_countable hf.countable

Depends on / 依赖: countable, hf.countable, not_countable
-/
lemma not_injective_uncountable_countable [Uncountable α] [Countable β] (f : α -> β) :
    ¬Injective f := fun hf => not_countable hf.countable

/--
lemma `not_surjective_countable_uncountable` / 引理 `not_surjective_countable_uncountable`

English:
lemma not_surjective_countable_uncountable
  given: [Countable α] [Uncountable β] (f : α -> β)
  proof: fun hf =>
  not_countable hf.countable

中文:
引理 not_surjective_countable_uncountable
  条件: [Countable α] [Uncountable β] (f : α -> β)
  证明: fun hf =>
  not_countable hf.countable
-/
lemma not_surjective_countable_uncountable [Countable α] [Uncountable β] (f : α -> β) :
    ¬Surjective f := fun hf =>
  not_countable hf.countable

/--
theorem `uncountable_iff_forall_not_surjective` / 定理 `uncountable_iff_forall_not_surjective`

English:
theorem uncountable_iff_forall_not_surjective
  given: [Nonempty α]
  proof: by
  rw [← not_countable_iff]; rw [countable_iff_exists_surjective]; rw [not_exists]

中文:
定理 uncountable_iff_forall_not_surjective
  条件: [Nonempty α]
  证明: by
  rw [← not_countable_iff]; rw [countable_iff_exists_surjective]; rw [not_exists]

Depends on / 依赖: countable_iff_exists_surjective, not_countable_iff, not_exists
-/
theorem uncountable_iff_forall_not_surjective [Nonempty α] :
    Uncountable α ↔ forall f : Nat -> α, ¬Surjective f := by
  rw [← not_countable_iff]; rw [countable_iff_exists_surjective]; rw [not_exists]

/--
theorem `Uncountable.of_equiv` / 定理 `Uncountable.of_equiv`

English:
theorem Uncountable.of_equiv
  given: (α : Sort*) [Uncountable α] (e : α ≃ β)
  statement: Uncountable β
  proof: e.injective.uncountable

中文:
定理 Uncountable.of_equiv
  条件: (α : Sort*) [Uncountable α] (e : α ≃ β)
  结论: Uncountable β
  证明: e.injective.uncountable

Depends on / 依赖: e.injective.uncountable, injective, uncountable
-/
theorem Uncountable.of_equiv (α : Sort*) [Uncountable α] (e : α ≃ β) : Uncountable β :=
  e.injective.uncountable

/--
theorem `Equiv.uncountable_iff` / 定理 `Equiv.uncountable_iff`

English:
theorem Equiv.uncountable_iff
  given: (e : α ≃ β)
  statement: Uncountable α ↔ Uncountable β
  proof: ⟨fun h => @Uncountable.of_equiv _ _ h e, fun h => @Uncountable.of_equiv _ _ h e.symm⟩

中文:
定理 Equiv.uncountable_iff
  条件: (e : α ≃ β)
  结论: Uncountable α ↔ Uncountable β
  证明: ⟨fun h => @Uncountable.of_equiv _ _ h e, fun h => @Uncountable.of_equiv _ _ h e.symm⟩

Depends on / 依赖: Uncountable, Uncountable.of_equiv, e.symm, of_equiv
-/
theorem Equiv.uncountable_iff (e : α ≃ β) : Uncountable α ↔ Uncountable β :=
  ⟨fun h => @Uncountable.of_equiv _ _ h e, fun h => @Uncountable.of_equiv _ _ h e.symm⟩

instance {β : Type v} [Uncountable β] : Uncountable (ULift.{u} β) :=
  .of_equiv _ Equiv.ulift.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Uncountable
  signature: α] : Uncountable (PLift α)
  body: .of_equiv _ Equiv.plift.symm

中文:
实例 [Uncountable
  签名: α] : Uncountable (PLift α)
  定义体: .of_equiv _ Equiv.plift.symm

Depends on / 依赖: Equiv.plift.symm, of_equiv
-/
instance [Uncountable α] : Uncountable (PLift α) :=
  .of_equiv _ Equiv.plift.symm

instance (priority := 100) [Uncountable α] : Infinite α :=
  ⟨fun _ => not_countable (α := α) inferInstance⟩
