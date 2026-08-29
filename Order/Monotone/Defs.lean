/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Coe

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `Monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `Antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `MonotoneOn f s`: Same as `Monotone f`, but for all `a, b ∈ s`.
* `AntitoneOn f s`: Same as `Antitone f`, but for all `a, b ∈ s`.
* `StrictMono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `StrictAnti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `StrictMonoOn f s`: Same as `StrictMono f`, but for all `a, b ∈ s`.
* `StrictAntiOn f s`: Same as `StrictAnti f`, but for all `a, b ∈ s`.

## Implementation notes

Some of these definitions used to only require `LE α` or `LT α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `Preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/

@[expose] public section

assert_not_exists Nat.instLinearOrder Int.instLinearOrder


open Function

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {π : ι -> Type*}

section MonotoneDef

variable [Preorder α] [Preorder β]

/--
Definition of `Monotone` / `Monotone` 的定义

English:
definition Monotone
  signature: (f : α -> β)
  body: forall ⦃a b⦄, a <= b -> f a <= f b

to_dual_insert_cast Monotone := forall_comm.eq

中文:
定义 Monotone
  签名: (f : α -> β)
  定义体: forall ⦃a b⦄, a <= b -> f a <= f b

to_dual_insert_cast Monotone := forall_comm.eq
-/
def Monotone (f : α -> β) : Prop :=
  forall ⦃a b⦄, a <= b -> f a <= f b

to_dual_insert_cast Monotone := forall_comm.eq

/--
Definition of `Antitone` / `Antitone` 的定义

English:
definition Antitone
  signature: (f : α -> β)
  body: forall ⦃a b⦄, a <= b -> f b <= f a

to_dual_insert_cast Antitone := forall_comm.eq

中文:
定义 Antitone
  签名: (f : α -> β)
  定义体: forall ⦃a b⦄, a <= b -> f b <= f a

to_dual_insert_cast Antitone := forall_comm.eq
-/
def Antitone (f : α -> β) : Prop :=
  forall ⦃a b⦄, a <= b -> f b <= f a

to_dual_insert_cast Antitone := forall_comm.eq

/--
Definition of `MonotoneOn` / `MonotoneOn` 的定义

English:
definition MonotoneOn
  signature: (f : α -> β) (s : Set α)
  body: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a <= b -> f a <= f b

to_dual_insert_cast MonotoneOn := by grind only

中文:
定义 MonotoneOn
  签名: (f : α -> β) (s : Set α)
  定义体: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a <= b -> f a <= f b

to_dual_insert_cast MonotoneOn := by grind only
-/
def MonotoneOn (f : α -> β) (s : Set α) : Prop :=
  forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a <= b -> f a <= f b

to_dual_insert_cast MonotoneOn := by grind only

/--
Definition of `AntitoneOn` / `AntitoneOn` 的定义

English:
definition AntitoneOn
  signature: (f : α -> β) (s : Set α)
  body: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a <= b -> f b <= f a

to_dual_insert_cast AntitoneOn := by grind only

中文:
定义 AntitoneOn
  签名: (f : α -> β) (s : Set α)
  定义体: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a <= b -> f b <= f a

to_dual_insert_cast AntitoneOn := by grind only
-/
def AntitoneOn (f : α -> β) (s : Set α) : Prop :=
  forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a <= b -> f b <= f a

to_dual_insert_cast AntitoneOn := by grind only

/--
Definition of `StrictMono` / `StrictMono` 的定义

English:
definition StrictMono
  signature: (f : α -> β)
  body: forall ⦃a b⦄, a < b -> f a < f b

to_dual_insert_cast StrictMono := forall_comm.eq

中文:
定义 StrictMono
  签名: (f : α -> β)
  定义体: forall ⦃a b⦄, a < b -> f a < f b

to_dual_insert_cast StrictMono := forall_comm.eq
-/
def StrictMono (f : α -> β) : Prop :=
  forall ⦃a b⦄, a < b -> f a < f b

to_dual_insert_cast StrictMono := forall_comm.eq

/--
Definition of `StrictAnti` / `StrictAnti` 的定义

English:
definition StrictAnti
  signature: (f : α -> β)
  body: forall ⦃a b⦄, a < b -> f b < f a

to_dual_insert_cast StrictAnti := forall_comm.eq

中文:
定义 StrictAnti
  签名: (f : α -> β)
  定义体: forall ⦃a b⦄, a < b -> f b < f a

to_dual_insert_cast StrictAnti := forall_comm.eq
-/
def StrictAnti (f : α -> β) : Prop :=
  forall ⦃a b⦄, a < b -> f b < f a

to_dual_insert_cast StrictAnti := forall_comm.eq

/--
Definition of `StrictMonoOn` / `StrictMonoOn` 的定义

English:
definition StrictMonoOn
  signature: (f : α -> β) (s : Set α)
  body: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a < f b

to_dual_insert_cast StrictMonoOn := by grind only

中文:
定义 StrictMonoOn
  签名: (f : α -> β) (s : Set α)
  定义体: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a < f b

to_dual_insert_cast StrictMonoOn := by grind only
-/
def StrictMonoOn (f : α -> β) (s : Set α) : Prop :=
  forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a < f b

to_dual_insert_cast StrictMonoOn := by grind only

/--
Definition of `StrictAntiOn` / `StrictAntiOn` 的定义

English:
definition StrictAntiOn
  signature: (f : α -> β) (s : Set α)
  body: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b < f a

to_dual_insert_cast StrictAntiOn := by grind only

中文:
定义 StrictAntiOn
  签名: (f : α -> β) (s : Set α)
  定义体: forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b < f a

to_dual_insert_cast StrictAntiOn := by grind only
-/
def StrictAntiOn (f : α -> β) (s : Set α) : Prop :=
  forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b < f a

to_dual_insert_cast StrictAntiOn := by grind only

end MonotoneDef

section Decidable

variable [Preorder α] [Preorder β] {f : α -> β} {s : Set α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a b, a <= b -> f a <= f b)] : Decidable (Monotone f)
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a b, a <= b -> f a <= f b)] : Decidable (Monotone f)
  定义体: i
-/
instance [i : Decidable (forall a b, a <= b -> f a <= f b)] : Decidable (Monotone f) := i
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a b, a <= b -> f b <= f a)] : Decidable (Antitone f)
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a b, a <= b -> f b <= f a)] : Decidable (Antitone f)
  定义体: i
-/
instance [i : Decidable (forall a b, a <= b -> f b <= f a)] : Decidable (Antitone f) := i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a in s, forall b in s, a <= b -> f a <= f b)] :
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a in s, 对任意 b in s, a <= b -> f a <= f b)] :
  定义体: i
-/
instance [i : Decidable (forall a in s, forall b in s, a <= b -> f a <= f b)] :
    Decidable (MonotoneOn f s) := i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a in s, forall b in s, a <= b -> f b <= f a)] :
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a in s, 对任意 b in s, a <= b -> f b <= f a)] :
  定义体: i
-/
instance [i : Decidable (forall a in s, forall b in s, a <= b -> f b <= f a)] :
    Decidable (AntitoneOn f s) := i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a b, a < b -> f a < f b)] : Decidable (StrictMono f)
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a b, a < b -> f a < f b)] : Decidable (StrictMono f)
  定义体: i
-/
instance [i : Decidable (forall a b, a < b -> f a < f b)] : Decidable (StrictMono f) := i
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a b, a < b -> f b < f a)] : Decidable (StrictAnti f)
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a b, a < b -> f b < f a)] : Decidable (StrictAnti f)
  定义体: i
-/
instance [i : Decidable (forall a b, a < b -> f b < f a)] : Decidable (StrictAnti f) := i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a in s, forall b in s, a < b -> f a < f b)] :
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a in s, 对任意 b in s, a < b -> f a < f b)] :
  定义体: i
-/
instance [i : Decidable (forall a in s, forall b in s, a < b -> f a < f b)] :
    Decidable (StrictMonoOn f s) := i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [i
  signature: : Decidable (forall a in s, forall b in s, a < b -> f b < f a)] :
  body: i

中文:
实例 [i
  签名: : Decidable (对任意 a in s, 对任意 b in s, a < b -> f b < f a)] :
  定义体: i
-/
instance [i : Decidable (forall a in s, forall b in s, a < b -> f b < f a)] :
    Decidable (StrictAntiOn f s) := i

end Decidable

/-! ### Monotonicity in function spaces -/


section Preorder

variable [Preorder α]

@[to_dual self]
/--
theorem `Monotone.comp_le_comp_left` / 定理 `Monotone.comp_le_comp_left`

English:
theorem Monotone.comp_le_comp_left
  proof: fun x => hf (le_gh x)

中文:
定理 Monotone.comp_le_comp_left
  证明: fun x => hf (le_gh x)

Depends on / 依赖: le_gh
-/
theorem Monotone.comp_le_comp_left
    [Preorder β] {f : β -> α} {g h : γ -> β} (hf : Monotone f) (le_gh : g <= h) :
    LE.le.{max w u} (f ∘ g) (f ∘ h) :=
  fun x => hf (le_gh x)

variable [Preorder γ]

/--
theorem `monotone_lam` / 定理 `monotone_lam`

English:
theorem monotone_lam
  given: {f : α -> β -> γ} (hf : forall b, Monotone fun a => f a b)
  statement: Monotone f
  proof: fun _ _ h b => hf b h

中文:
定理 monotone_lam
  条件: {f : α -> β -> γ} (hf : 对任意 b, Monotone fun a => f a b)
  结论: Monotone f
  证明: fun _ _ h b => hf b h
-/
theorem monotone_lam {f : α -> β -> γ} (hf : forall b, Monotone fun a => f a b) : Monotone f :=
  fun _ _ h b => hf b h

/--
theorem `monotone_app` / 定理 `monotone_app`

English:
theorem monotone_app
  given: (f : β -> α -> γ) (b : β) (hf : Monotone fun a b => f b a)
  statement: Monotone (f b)
  proof: fun _ _ h => hf h b

中文:
定理 monotone_app
  条件: (f : β -> α -> γ) (b : β) (hf : Monotone fun a b => f b a)
  结论: Monotone (f b)
  证明: fun _ _ h => hf h b
-/
theorem monotone_app (f : β -> α -> γ) (b : β) (hf : Monotone fun a b => f b a) : Monotone (f b) :=
  fun _ _ h => hf h b

/--
theorem `antitone_lam` / 定理 `antitone_lam`

English:
theorem antitone_lam
  given: {f : α -> β -> γ} (hf : forall b, Antitone fun a => f a b)
  statement: Antitone f
  proof: fun _ _ h b => hf b h

中文:
定理 antitone_lam
  条件: {f : α -> β -> γ} (hf : 对任意 b, Antitone fun a => f a b)
  结论: Antitone f
  证明: fun _ _ h b => hf b h
-/
theorem antitone_lam {f : α -> β -> γ} (hf : forall b, Antitone fun a => f a b) : Antitone f :=
  fun _ _ h b => hf b h

/--
theorem `antitone_app` / 定理 `antitone_app`

English:
theorem antitone_app
  given: (f : β -> α -> γ) (b : β) (hf : Antitone fun a b => f b a)
  statement: Antitone (f b)
  proof: fun _ _ h => hf h b

中文:
定理 antitone_app
  条件: (f : β -> α -> γ) (b : β) (hf : Antitone fun a b => f b a)
  结论: Antitone (f b)
  证明: fun _ _ h => hf h b
-/
theorem antitone_app (f : β -> α -> γ) (b : β) (hf : Antitone fun a b => f b a) : Antitone (f b) :=
  fun _ _ h => hf h b

end Preorder

/--
theorem `Function.monotone_eval` / 定理 `Function.monotone_eval`

English:
theorem Function.monotone_eval
  given: {ι : Type u} {α : ι -> Type v} [forall i, Preorder (α i)] (i : ι)
  proof: fun _ _ H => H i

中文:
定理 Function.monotone_eval
  条件: {ι : 类型u} {α : ι -> 类型v} [对任意 i, Preorder (α i)] (i : ι)
  证明: fun _ _ H => H i
-/
theorem Function.monotone_eval {ι : Type u} {α : ι -> Type v} [forall i, Preorder (α i)] (i : ι) :
    Monotone (Function.eval i : (forall i, α i) -> α i) := fun _ _ H => H i

/-! ### Monotonicity hierarchy -/


section Preorder

variable [Preorder α]

section Preorder

variable [Preorder β] {f : α -> β} {a b : α}

/-!
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`. This is useful
when you do not want to apply a `Monotone` assumption (i.e. your goal is `a ≤ b → f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `hf h` instead.
-/

@[to_dual self]
/--
theorem `Monotone.imp` / 定理 `Monotone.imp`

English:
theorem Monotone.imp
  given: (hf : Monotone f) (h : a <= b)
  statement: f a <= f b
  proof: hf h

@[to_dual self]

中文:
定理 Monotone.imp
  条件: (hf : Monotone f) (h : a <= b)
  结论: f a <= f b
  证明: hf h

@[to_dual self]
-/
theorem Monotone.imp (hf : Monotone f) (h : a <= b) : f a <= f b :=
  hf h

@[to_dual self]
/--
theorem `Antitone.imp` / 定理 `Antitone.imp`

English:
theorem Antitone.imp
  given: (hf : Antitone f) (h : a <= b)
  statement: f b <= f a
  proof: hf h

@[to_dual self]

中文:
定理 Antitone.imp
  条件: (hf : Antitone f) (h : a <= b)
  结论: f b <= f a
  证明: hf h

@[to_dual self]
-/
theorem Antitone.imp (hf : Antitone f) (h : a <= b) : f b <= f a :=
  hf h

@[to_dual self]
/--
theorem `StrictMono.imp` / 定理 `StrictMono.imp`

English:
theorem StrictMono.imp
  given: (hf : StrictMono f) (h : a < b)
  statement: f a < f b
  proof: hf h

@[to_dual self]

中文:
定理 StrictMono.imp
  条件: (hf : StrictMono f) (h : a < b)
  结论: f a < f b
  证明: hf h

@[to_dual self]
-/
theorem StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f b :=
  hf h

@[to_dual self]
/--
theorem `StrictAnti.imp` / 定理 `StrictAnti.imp`

English:
theorem StrictAnti.imp
  given: (hf : StrictAnti f) (h : a < b)
  statement: f b < f a
  proof: hf h

中文:
定理 StrictAnti.imp
  条件: (hf : StrictAnti f) (h : a < b)
  结论: f b < f a
  证明: hf h
-/
theorem StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f a :=
  hf h

/--
theorem `Monotone.monotoneOn` / 定理 `Monotone.monotoneOn`

English:
theorem Monotone.monotoneOn
  given: (hf : Monotone f) (s : Set α)
  statement: MonotoneOn f s
  proof: fun _ _ _ _ => hf.imp

中文:
定理 Monotone.monotoneOn
  条件: (hf : Monotone f) (s : Set α)
  结论: MonotoneOn f s
  证明: fun _ _ _ _ => hf.imp
-/
protected theorem Monotone.monotoneOn (hf : Monotone f) (s : Set α) : MonotoneOn f s :=
  fun _ _ _ _ => hf.imp

/--
theorem `Antitone.antitoneOn` / 定理 `Antitone.antitoneOn`

English:
theorem Antitone.antitoneOn
  given: (hf : Antitone f) (s : Set α)
  statement: AntitoneOn f s
  proof: fun _ _ _ _ => hf.imp

中文:
定理 Antitone.antitoneOn
  条件: (hf : Antitone f) (s : Set α)
  结论: AntitoneOn f s
  证明: fun _ _ _ _ => hf.imp
-/
protected theorem Antitone.antitoneOn (hf : Antitone f) (s : Set α) : AntitoneOn f s :=
  fun _ _ _ _ => hf.imp

/--
theorem `monotoneOn_univ` / 定理 `monotoneOn_univ`

English:
theorem monotoneOn_univ
  statement: MonotoneOn f Set.univ ↔ Monotone f
  proof: ⟨fun h _ _ => h trivial trivial, fun h => h.monotoneOn _⟩

中文:
定理 monotoneOn_univ
  结论: MonotoneOn f Set.univ ↔ Monotone f
  证明: ⟨fun h _ _ => h trivial trivial, fun h => h.monotoneOn _⟩
-/
@[simp] theorem monotoneOn_univ : MonotoneOn f Set.univ ↔ Monotone f :=
  ⟨fun h _ _ => h trivial trivial, fun h => h.monotoneOn _⟩

/--
theorem `antitoneOn_univ` / 定理 `antitoneOn_univ`

English:
theorem antitoneOn_univ
  statement: AntitoneOn f Set.univ ↔ Antitone f
  proof: ⟨fun h _ _ => h trivial trivial, fun h => h.antitoneOn _⟩

中文:
定理 antitoneOn_univ
  结论: AntitoneOn f Set.univ ↔ Antitone f
  证明: ⟨fun h _ _ => h trivial trivial, fun h => h.antitoneOn _⟩
-/
@[simp] theorem antitoneOn_univ : AntitoneOn f Set.univ ↔ Antitone f :=
  ⟨fun h _ _ => h trivial trivial, fun h => h.antitoneOn _⟩

/--
theorem `StrictMono.strictMonoOn` / 定理 `StrictMono.strictMonoOn`

English:
theorem StrictMono.strictMonoOn
  given: (hf : StrictMono f) (s : Set α)
  statement: StrictMonoOn f s
  proof: fun _ _ _ _ => hf.imp

中文:
定理 StrictMono.strictMonoOn
  条件: (hf : StrictMono f) (s : Set α)
  结论: StrictMonoOn f s
  证明: fun _ _ _ _ => hf.imp
-/
protected theorem StrictMono.strictMonoOn (hf : StrictMono f) (s : Set α) : StrictMonoOn f s :=
  fun _ _ _ _ => hf.imp

/--
theorem `StrictAnti.strictAntiOn` / 定理 `StrictAnti.strictAntiOn`

English:
theorem StrictAnti.strictAntiOn
  given: (hf : StrictAnti f) (s : Set α)
  statement: StrictAntiOn f s
  proof: fun _ _ _ _ => hf.imp

中文:
定理 StrictAnti.strictAntiOn
  条件: (hf : StrictAnti f) (s : Set α)
  结论: StrictAntiOn f s
  证明: fun _ _ _ _ => hf.imp
-/
protected theorem StrictAnti.strictAntiOn (hf : StrictAnti f) (s : Set α) : StrictAntiOn f s :=
  fun _ _ _ _ => hf.imp

/--
theorem `strictMonoOn_univ` / 定理 `strictMonoOn_univ`

English:
theorem strictMonoOn_univ
  statement: StrictMonoOn f Set.univ ↔ StrictMono f
  proof: ⟨fun h _ _ => h trivial trivial, fun h => h.strictMonoOn _⟩

中文:
定理 strictMonoOn_univ
  结论: StrictMonoOn f Set.univ ↔ StrictMono f
  证明: ⟨fun h _ _ => h trivial trivial, fun h => h.strictMonoOn _⟩
-/
@[simp] theorem strictMonoOn_univ : StrictMonoOn f Set.univ ↔ StrictMono f :=
  ⟨fun h _ _ => h trivial trivial, fun h => h.strictMonoOn _⟩

/--
theorem `strictAntiOn_univ` / 定理 `strictAntiOn_univ`

English:
theorem strictAntiOn_univ
  statement: StrictAntiOn f Set.univ ↔ StrictAnti f
  proof: ⟨fun h _ _ => h trivial trivial, fun h => h.strictAntiOn _⟩

中文:
定理 strictAntiOn_univ
  结论: StrictAntiOn f Set.univ ↔ StrictAnti f
  证明: ⟨fun h _ _ => h trivial trivial, fun h => h.strictAntiOn _⟩
-/
@[simp] theorem strictAntiOn_univ : StrictAntiOn f Set.univ ↔ StrictAnti f :=
  ⟨fun h _ _ => h trivial trivial, fun h => h.strictAntiOn _⟩

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α -> β}

/--
theorem `Monotone.strictMono_of_injective` / 定理 `Monotone.strictMono_of_injective`

English:
theorem Monotone.strictMono_of_injective
  given: (h₁ : Monotone f) (h₂ : Injective f)
  statement: StrictMono f
  proof: fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne h₂ H

中文:
定理 Monotone.strictMono_of_injective
  条件: (h₁ : Monotone f) (h₂ : Injective f)
  结论: StrictMono f
  证明: fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne h₂ H

Depends on / 依赖: h.le, h.ne, lt_of_ne
-/
theorem Monotone.strictMono_of_injective (h₁ : Monotone f) (h₂ : Injective f) : StrictMono f :=
fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne h₂ H

/--
theorem `Antitone.strictAnti_of_injective` / 定理 `Antitone.strictAnti_of_injective`

English:
theorem Antitone.strictAnti_of_injective
  given: (h₁ : Antitone f) (h₂ : Injective f)
  statement: StrictAnti f
  proof: fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne h₂ H.symm

中文:
定理 Antitone.strictAnti_of_injective
  条件: (h₁ : Antitone f) (h₂ : Injective f)
  结论: StrictAnti f
  证明: fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne h₂ H.symm

Depends on / 依赖: H.symm, h.le, h.ne, lt_of_ne
-/
theorem Antitone.strictAnti_of_injective (h₁ : Antitone f) (h₂ : Injective f) : StrictAnti f :=
fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne h₂ H.symm

end PartialOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {f : α -> β} {s : Set α}

@[to_dual none]
/--
theorem `monotone_iff_forall_lt` / 定理 `monotone_iff_forall_lt`

English:
theorem monotone_iff_forall_lt
  statement: Monotone f ↔ forall ⦃a b⦄, a < b -> f a <= f b
  proof: forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) hf⟩

@[to_dual none]

中文:
定理 monotone_iff_forall_lt
  结论: Monotone f ↔ 对任意 ⦃a b⦄, a < b -> f a <= f b
  证明: forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) hf⟩

@[to_dual none]

Depends on / 依赖: congr_arg, eq_or_lt, h.eq_or_lt.elim, h.le
-/
theorem monotone_iff_forall_lt : Monotone f ↔ forall ⦃a b⦄, a < b -> f a <= f b :=
  forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) hf⟩

@[to_dual none]
/--
theorem `antitone_iff_forall_lt` / 定理 `antitone_iff_forall_lt`

English:
theorem antitone_iff_forall_lt
  statement: Antitone f ↔ forall ⦃a b⦄, a < b -> f b <= f a
  proof: forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) hf⟩

@[to_dual none]

中文:
定理 antitone_iff_forall_lt
  结论: Antitone f ↔ 对任意 ⦃a b⦄, a < b -> f b <= f a
  证明: forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) hf⟩

@[to_dual none]

Depends on / 依赖: congr_arg, eq_or_lt, h.eq_or_lt.elim, h.le
-/
theorem antitone_iff_forall_lt : Antitone f ↔ forall ⦃a b⦄, a < b -> f b <= f a :=
  forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) hf⟩

@[to_dual none]
/--
theorem `monotoneOn_iff_forall_lt` / 定理 `monotoneOn_iff_forall_lt`

English:
theorem monotoneOn_iff_forall_lt
  proof: ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) (hf ha hb)⟩

@[to_dual none]

中文:
定理 monotoneOn_iff_forall_lt
  证明: ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) (hf ha hb)⟩

@[to_dual none]

Depends on / 依赖: congr_arg, eq_or_lt, h.eq_or_lt.elim, h.le
-/
theorem monotoneOn_iff_forall_lt :
    MonotoneOn f s ↔ forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a <= f b :=
  ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) (hf ha hb)⟩

@[to_dual none]
/--
theorem `antitoneOn_iff_forall_lt` / 定理 `antitoneOn_iff_forall_lt`

English:
theorem antitoneOn_iff_forall_lt
  proof: ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) (hf ha hb)⟩

中文:
定理 antitoneOn_iff_forall_lt
  证明: ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) (hf ha hb)⟩

Depends on / 依赖: congr_arg, eq_or_lt, h.eq_or_lt.elim, h.le
-/
theorem antitoneOn_iff_forall_lt :
    AntitoneOn f s ↔ forall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f b <= f a :=
  ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) (hf ha hb)⟩

-- `Preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `StrictMono f` is vacuously true.
/--
theorem `StrictMonoOn.monotoneOn` / 定理 `StrictMonoOn.monotoneOn`

English:
theorem StrictMonoOn.monotoneOn
  given: (hf : StrictMonoOn f s)
  statement: MonotoneOn f s
  proof: monotoneOn_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le

中文:
定理 StrictMonoOn.monotoneOn
  条件: (hf : StrictMonoOn f s)
  结论: MonotoneOn f s
  证明: monotoneOn_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le
-/
protected theorem StrictMonoOn.monotoneOn (hf : StrictMonoOn f s) : MonotoneOn f s :=
  monotoneOn_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le

/--
theorem `StrictAntiOn.antitoneOn` / 定理 `StrictAntiOn.antitoneOn`

English:
theorem StrictAntiOn.antitoneOn
  given: (hf : StrictAntiOn f s)
  statement: AntitoneOn f s
  proof: antitoneOn_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le

中文:
定理 StrictAntiOn.antitoneOn
  条件: (hf : StrictAntiOn f s)
  结论: AntitoneOn f s
  证明: antitoneOn_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le
-/
protected theorem StrictAntiOn.antitoneOn (hf : StrictAntiOn f s) : AntitoneOn f s :=
  antitoneOn_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le

/--
theorem `StrictMono.monotone` / 定理 `StrictMono.monotone`

English:
theorem StrictMono.monotone
  given: (hf : StrictMono f)
  statement: Monotone f
  proof: monotone_iff_forall_lt.2 fun _ _ h => (hf h).le

中文:
定理 StrictMono.monotone
  条件: (hf : StrictMono f)
  结论: Monotone f
  证明: monotone_iff_forall_lt.2 fun _ _ h => (hf h).le
-/
protected theorem StrictMono.monotone (hf : StrictMono f) : Monotone f :=
  monotone_iff_forall_lt.2 fun _ _ h => (hf h).le

/--
theorem `StrictAnti.antitone` / 定理 `StrictAnti.antitone`

English:
theorem StrictAnti.antitone
  given: (hf : StrictAnti f)
  statement: Antitone f
  proof: antitone_iff_forall_lt.2 fun _ _ h => (hf h).le

中文:
定理 StrictAnti.antitone
  条件: (hf : StrictAnti f)
  结论: Antitone f
  证明: antitone_iff_forall_lt.2 fun _ _ h => (hf h).le
-/
protected theorem StrictAnti.antitone (hf : StrictAnti f) : Antitone f :=
  antitone_iff_forall_lt.2 fun _ _ h => (hf h).le

end PartialOrder

/-! ### Monotonicity from and to subsingletons -/


namespace Subsingleton

variable [Preorder α] [Preorder β]

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: [Subsingleton α] (f : α -> β)
  statement: Monotone f
  proof: fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le

中文:
定理 monotone
  条件: [Subsingleton α] (f : α -> β)
  结论: Monotone f
  证明: fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le
-/
protected theorem monotone [Subsingleton α] (f : α -> β) : Monotone f :=
  fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le

/--
theorem `antitone` / 定理 `antitone`

English:
theorem antitone
  given: [Subsingleton α] (f : α -> β)
  statement: Antitone f
  proof: fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le

中文:
定理 antitone
  条件: [Subsingleton α] (f : α -> β)
  结论: Antitone f
  证明: fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le
-/
protected theorem antitone [Subsingleton α] (f : α -> β) : Antitone f :=
  fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le

/--
theorem `monotone'` / 定理 `monotone'`

English:
theorem monotone'
  given: [Subsingleton β] (f : α -> β)
  statement: Monotone f
  proof: fun _ _ _ => (Subsingleton.elim _ _).le

中文:
定理 monotone'
  条件: [Subsingleton β] (f : α -> β)
  结论: Monotone f
  证明: fun _ _ _ => (Subsingleton.elim _ _).le

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem monotone' [Subsingleton β] (f : α -> β) : Monotone f :=
  fun _ _ _ => (Subsingleton.elim _ _).le

/--
theorem `antitone'` / 定理 `antitone'`

English:
theorem antitone'
  given: [Subsingleton β] (f : α -> β)
  statement: Antitone f
  proof: fun _ _ _ => (Subsingleton.elim _ _).le

中文:
定理 antitone'
  条件: [Subsingleton β] (f : α -> β)
  结论: Antitone f
  证明: fun _ _ _ => (Subsingleton.elim _ _).le

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem antitone' [Subsingleton β] (f : α -> β) : Antitone f :=
  fun _ _ _ => (Subsingleton.elim _ _).le

/--
theorem `strictMono` / 定理 `strictMono`

English:
theorem strictMono
  given: [Subsingleton α] (f : α -> β)
  statement: StrictMono f
  proof: fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim

中文:
定理 strictMono
  条件: [Subsingleton α] (f : α -> β)
  结论: StrictMono f
  证明: fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim
-/
protected theorem strictMono [Subsingleton α] (f : α -> β) : StrictMono f :=
  fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim

/--
theorem `strictAnti` / 定理 `strictAnti`

English:
theorem strictAnti
  given: [Subsingleton α] (f : α -> β)
  statement: StrictAnti f
  proof: fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim

中文:
定理 strictAnti
  条件: [Subsingleton α] (f : α -> β)
  结论: StrictAnti f
  证明: fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim
-/
protected theorem strictAnti [Subsingleton α] (f : α -> β) : StrictAnti f :=
  fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim

end Subsingleton



/--
theorem `monotone_id` / 定理 `monotone_id`

English:
theorem monotone_id
  given: [Preorder α]
  statement: Monotone (id : α -> α)
  proof: fun _ _ => id

中文:
定理 monotone_id
  条件: [Preorder α]
  结论: Monotone (id : α -> α)
  证明: fun _ _ => id
-/
theorem monotone_id [Preorder α] : Monotone (id : α -> α) := fun _ _ => id

/--
theorem `monotoneOn_id` / 定理 `monotoneOn_id`

English:
theorem monotoneOn_id
  given: [Preorder α] {s : Set α}
  statement: MonotoneOn id s
  proof: fun _ _ _ _ => id

中文:
定理 monotoneOn_id
  条件: [Preorder α] {s : Set α}
  结论: MonotoneOn id s
  证明: fun _ _ _ _ => id
-/
theorem monotoneOn_id [Preorder α] {s : Set α} : MonotoneOn id s := fun _ _ _ _ => id

/--
theorem `strictMono_id` / 定理 `strictMono_id`

English:
theorem strictMono_id
  given: [Preorder α]
  statement: StrictMono (id : α -> α)
  proof: fun _ _ => id

中文:
定理 strictMono_id
  条件: [Preorder α]
  结论: StrictMono (id : α -> α)
  证明: fun _ _ => id
-/
theorem strictMono_id [Preorder α] : StrictMono (id : α -> α) := fun _ _ => id

/--
theorem `strictMonoOn_id` / 定理 `strictMonoOn_id`

English:
theorem strictMonoOn_id
  given: [Preorder α] {s : Set α}
  statement: StrictMonoOn id s
  proof: fun _ _ _ _ => id

中文:
定理 strictMonoOn_id
  条件: [Preorder α] {s : Set α}
  结论: StrictMonoOn id s
  证明: fun _ _ _ _ => id
-/
theorem strictMonoOn_id [Preorder α] {s : Set α} : StrictMonoOn id s := fun _ _ _ _ => id

/--
theorem `monotone_const` / 定理 `monotone_const`

English:
theorem monotone_const
  given: [Preorder α] [Preorder β] {c : β}
  statement: Monotone fun _ : α => c
  proof: fun _ _ _ => le_rfl

中文:
定理 monotone_const
  条件: [Preorder α] [Preorder β] {c : β}
  结论: Monotone fun _ : α => c
  证明: fun _ _ _ => le_rfl

Depends on / 依赖: le_rfl
-/
theorem monotone_const [Preorder α] [Preorder β] {c : β} : Monotone fun _ : α => c :=
  fun _ _ _ => le_rfl

/--
theorem `monotoneOn_const` / 定理 `monotoneOn_const`

English:
theorem monotoneOn_const
  given: [Preorder α] [Preorder β] {c : β} {s : Set α}
  proof: fun _ _ _ _ _ => le_rfl

中文:
定理 monotoneOn_const
  条件: [Preorder α] [Preorder β] {c : β} {s : Set α}
  证明: fun _ _ _ _ _ => le_rfl

Depends on / 依赖: le_rfl
-/
theorem monotoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    MonotoneOn (fun _ : α => c) s :=
  fun _ _ _ _ _ => le_rfl

/--
theorem `antitone_const` / 定理 `antitone_const`

English:
theorem antitone_const
  given: [Preorder α] [Preorder β] {c : β}
  statement: Antitone fun _ : α => c
  proof: fun _ _ _ => le_refl c

中文:
定理 antitone_const
  条件: [Preorder α] [Preorder β] {c : β}
  结论: Antitone fun _ : α => c
  证明: fun _ _ _ => le_refl c

Depends on / 依赖: le_refl
-/
theorem antitone_const [Preorder α] [Preorder β] {c : β} : Antitone fun _ : α => c :=
  fun _ _ _ => le_refl c

/--
theorem `antitoneOn_const` / 定理 `antitoneOn_const`

English:
theorem antitoneOn_const
  given: [Preorder α] [Preorder β] {c : β} {s : Set α}
  proof: fun _ _ _ _ _ => le_rfl

@[to_dual self]

中文:
定理 antitoneOn_const
  条件: [Preorder α] [Preorder β] {c : β} {s : Set α}
  证明: fun _ _ _ _ _ => le_rfl

@[to_dual self]

Depends on / 依赖: le_rfl
-/
theorem antitoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    AntitoneOn (fun _ : α => c) s :=
  fun _ _ _ _ _ => le_rfl

@[to_dual self]
/--
theorem `strictMono_of_le_iff_le` / 定理 `strictMono_of_le_iff_le`

English:
theorem strictMono_of_le_iff_le
  statement: [Preorder α] [Preorder β] {f : α -> β}
  proof: fun _ _ => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

中文:
定理 strictMono_of_le_iff_le
  结论: [Preorder α] [Preorder β] {f : α -> β}
  证明: fun _ _ => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

Depends on / 依赖: lt_iff_lt_of_le_iff_le
-/
theorem strictMono_of_le_iff_le [Preorder α] [Preorder β] {f : α -> β}
    (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f :=
  fun _ _ => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

/--
theorem `strictAnti_of_le_iff_le` / 定理 `strictAnti_of_le_iff_le`

English:
theorem strictAnti_of_le_iff_le
  statement: [Preorder α] [Preorder β] {f : α -> β}
  proof: fun _ _ => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

@[to_dual none]

中文:
定理 strictAnti_of_le_iff_le
  结论: [Preorder α] [Preorder β] {f : α -> β}
  证明: fun _ _ => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

@[to_dual none]

Depends on / 依赖: lt_iff_lt_of_le_iff_le
-/
theorem strictAnti_of_le_iff_le [Preorder α] [Preorder β] {f : α -> β}
    (h : forall x y, x <= y ↔ f y <= f x) : StrictAnti f :=
  fun _ _ => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

@[to_dual none]
/--
theorem `Function.Injective.of_lt_imp_ne` / 定理 `Function.Injective.of_lt_imp_ne`

English:
theorem Function.Injective.of_lt_imp_ne
  given: [LinearOrder α] {f : α -> β} (h : forall x y, x < y -> f x != f y)
  proof: by
  grind [Injective]

中文:
定理 Function.Injective.of_lt_imp_ne
  条件: [LinearOrder α] {f : α -> β} (h : 对任意 x y, x < y -> f x != f y)
  证明: by
  grind [Injective]

Depends on / 依赖: Injective
-/
theorem Function.Injective.of_lt_imp_ne [LinearOrder α] {f : α -> β} (h : forall x y, x < y -> f x != f y) :
    Injective f := by
  grind [Injective]

/--
theorem `Function.Injective.of_eq_imp_le` / 定理 `Function.Injective.of_eq_imp_le`

English:
theorem Function.Injective.of_eq_imp_le
  statement: [PartialOrder α] {f : α -> β}
  proof: .antisymm h hxy.symm fun _ _ hxy => h hxy

中文:
定理 Function.Injective.of_eq_imp_le
  结论: [PartialOrder α] {f : α -> β}
  证明: .antisymm h hxy.symm fun _ _ hxy => h hxy

Depends on / 依赖: antisymm, hxy.symm
-/
theorem Function.Injective.of_eq_imp_le [PartialOrder α] {f : α -> β}
    (h : forall {x y}, f x = f y -> x <= y) : f.Injective :=
.antisymm h hxy.symm fun _ _ hxy => h hxy

/-! ### Monotonicity under composition -/


section Composition

variable [Preorder α] [Preorder β] [Preorder γ] {g : β -> γ} {f : α -> β} {s : Set α} {t : Set β}

/--
theorem `Monotone.comp` / 定理 `Monotone.comp`

English:
theorem Monotone.comp
  given: (hg : Monotone g) (hf : Monotone f)
  statement: Monotone (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 Monotone.comp
  条件: (hg : Monotone g) (hf : Monotone f)
  结论: Monotone (g ∘ f)
  证明: fun _ _ h => hg (hf h)
-/
protected theorem Monotone.comp (hg : Monotone g) (hf : Monotone f) : Monotone (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `Monotone.comp_antitone` / 定理 `Monotone.comp_antitone`

English:
theorem Monotone.comp_antitone
  given: (hg : Monotone g) (hf : Antitone f)
  statement: Antitone (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 Monotone.comp_antitone
  条件: (hg : Monotone g) (hf : Antitone f)
  结论: Antitone (g ∘ f)
  证明: fun _ _ h => hg (hf h)
-/
theorem Monotone.comp_antitone (hg : Monotone g) (hf : Antitone f) : Antitone (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `Antitone.comp` / 定理 `Antitone.comp`

English:
theorem Antitone.comp
  given: (hg : Antitone g) (hf : Antitone f)
  statement: Monotone (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 Antitone.comp
  条件: (hg : Antitone g) (hf : Antitone f)
  结论: Monotone (g ∘ f)
  证明: fun _ _ h => hg (hf h)
-/
protected theorem Antitone.comp (hg : Antitone g) (hf : Antitone f) : Monotone (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `Antitone.comp_monotone` / 定理 `Antitone.comp_monotone`

English:
theorem Antitone.comp_monotone
  given: (hg : Antitone g) (hf : Monotone f)
  statement: Antitone (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 Antitone.comp_monotone
  条件: (hg : Antitone g) (hf : Monotone f)
  结论: Antitone (g ∘ f)
  证明: fun _ _ h => hg (hf h)
-/
theorem Antitone.comp_monotone (hg : Antitone g) (hf : Monotone f) : Antitone (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `Monotone.iterate` / 定理 `Monotone.iterate`

English:
theorem Monotone.iterate
  given: {f : α -> α} (hf : Monotone f) (n : Nat)
  statement: Monotone f^[n]
  proof: Nat.recOn n monotone_id fun _ h => h.comp hf

中文:
定理 Monotone.iterate
  条件: {f : α -> α} (hf : Monotone f) (n : 自然数)
  结论: Monotone f^[n]
  证明: Nat.recOn n monotone_id fun _ h => h.comp hf
-/
protected theorem Monotone.iterate {f : α -> α} (hf : Monotone f) (n : Nat) : Monotone f^[n] :=
  Nat.recOn n monotone_id fun _ h => h.comp hf

/--
theorem `Monotone.comp_monotoneOn` / 定理 `Monotone.comp_monotoneOn`

English:
theorem Monotone.comp_monotoneOn
  given: (hg : Monotone g) (hf : MonotoneOn f s)
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 Monotone.comp_monotoneOn
  条件: (hg : Monotone g) (hf : MonotoneOn f s)
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
protected theorem Monotone.comp_monotoneOn (hg : Monotone g) (hf : MonotoneOn f s) :
    MonotoneOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
theorem `Monotone.comp_antitoneOn` / 定理 `Monotone.comp_antitoneOn`

English:
theorem Monotone.comp_antitoneOn
  given: (hg : Monotone g) (hf : AntitoneOn f s)
  statement: AntitoneOn (g ∘ f) s
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 Monotone.comp_antitoneOn
  条件: (hg : Monotone g) (hf : AntitoneOn f s)
  结论: AntitoneOn (g ∘ f) s
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
theorem Monotone.comp_antitoneOn (hg : Monotone g) (hf : AntitoneOn f s) : AntitoneOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
theorem `Antitone.comp_antitoneOn` / 定理 `Antitone.comp_antitoneOn`

English:
theorem Antitone.comp_antitoneOn
  given: (hg : Antitone g) (hf : AntitoneOn f s)
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 Antitone.comp_antitoneOn
  条件: (hg : Antitone g) (hf : AntitoneOn f s)
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
protected theorem Antitone.comp_antitoneOn (hg : Antitone g) (hf : AntitoneOn f s) :
    MonotoneOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
theorem `Antitone.comp_monotoneOn` / 定理 `Antitone.comp_monotoneOn`

English:
theorem Antitone.comp_monotoneOn
  given: (hg : Antitone g) (hf : MonotoneOn f s)
  statement: AntitoneOn (g ∘ f) s
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 Antitone.comp_monotoneOn
  条件: (hg : Antitone g) (hf : MonotoneOn f s)
  结论: AntitoneOn (g ∘ f) s
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
theorem Antitone.comp_monotoneOn (hg : Antitone g) (hf : MonotoneOn f s) : AntitoneOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
theorem `StrictMono.comp` / 定理 `StrictMono.comp`

English:
theorem StrictMono.comp
  given: (hg : StrictMono g) (hf : StrictMono f)
  statement: StrictMono (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 StrictMono.comp
  条件: (hg : StrictMono g) (hf : StrictMono f)
  结论: StrictMono (g ∘ f)
  证明: fun _ _ h => hg (hf h)
-/
protected theorem StrictMono.comp (hg : StrictMono g) (hf : StrictMono f) : StrictMono (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `StrictMono.comp_strictAnti` / 定理 `StrictMono.comp_strictAnti`

English:
theorem StrictMono.comp_strictAnti
  given: (hg : StrictMono g) (hf : StrictAnti f)
  statement: StrictAnti (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 StrictMono.comp_strictAnti
  条件: (hg : StrictMono g) (hf : StrictAnti f)
  结论: StrictAnti (g ∘ f)
  证明: fun _ _ h => hg (hf h)
-/
theorem StrictMono.comp_strictAnti (hg : StrictMono g) (hf : StrictAnti f) : StrictAnti (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `StrictAnti.comp` / 定理 `StrictAnti.comp`

English:
theorem StrictAnti.comp
  given: (hg : StrictAnti g) (hf : StrictAnti f)
  statement: StrictMono (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 StrictAnti.comp
  条件: (hg : StrictAnti g) (hf : StrictAnti f)
  结论: StrictMono (g ∘ f)
  证明: fun _ _ h => hg (hf h)
-/
protected theorem StrictAnti.comp (hg : StrictAnti g) (hf : StrictAnti f) : StrictMono (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `StrictAnti.comp_strictMono` / 定理 `StrictAnti.comp_strictMono`

English:
theorem StrictAnti.comp_strictMono
  given: (hg : StrictAnti g) (hf : StrictMono f)
  statement: StrictAnti (g ∘ f)
  proof: fun _ _ h => hg (hf h)

中文:
定理 StrictAnti.comp_strictMono
  条件: (hg : StrictAnti g) (hf : StrictMono f)
  结论: StrictAnti (g ∘ f)
  证明: fun _ _ h => hg (hf h)

Depends on / 依赖: DecidablePred, Irreducible
-/
theorem StrictAnti.comp_strictMono (hg : StrictAnti g) (hf : StrictMono f) : StrictAnti (g ∘ f) :=
  fun _ _ h => hg (hf h)

/--
theorem `StrictMono.iterate` / 定理 `StrictMono.iterate`

English:
theorem StrictMono.iterate
  given: {f : α -> α} (hf : StrictMono f) (n : Nat)
  statement: StrictMono f^[n]
  proof: Nat.recOn n strictMono_id fun _ h => h.comp hf

中文:
定理 StrictMono.iterate
  条件: {f : α -> α} (hf : StrictMono f) (n : 自然数)
  结论: StrictMono f^[n]
  证明: Nat.recOn n strictMono_id fun _ h => h.comp hf
-/
protected theorem StrictMono.iterate {f : α -> α} (hf : StrictMono f) (n : Nat) : StrictMono f^[n] :=
  Nat.recOn n strictMono_id fun _ h => h.comp hf

/--
theorem `StrictMono.comp_strictMonoOn` / 定理 `StrictMono.comp_strictMonoOn`

English:
theorem StrictMono.comp_strictMonoOn
  given: (hg : StrictMono g) (hf : StrictMonoOn f s)
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 StrictMono.comp_strictMonoOn
  条件: (hg : StrictMono g) (hf : StrictMonoOn f s)
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
protected theorem StrictMono.comp_strictMonoOn (hg : StrictMono g) (hf : StrictMonoOn f s) :
    StrictMonoOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
theorem `StrictMono.comp_strictAntiOn` / 定理 `StrictMono.comp_strictAntiOn`

English:
theorem StrictMono.comp_strictAntiOn
  given: (hg : StrictMono g) (hf : StrictAntiOn f s)
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 StrictMono.comp_strictAntiOn
  条件: (hg : StrictMono g) (hf : StrictAntiOn f s)
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
theorem StrictMono.comp_strictAntiOn (hg : StrictMono g) (hf : StrictAntiOn f s) :
    StrictAntiOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
theorem `StrictAnti.comp_strictAntiOn` / 定理 `StrictAnti.comp_strictAntiOn`

English:
theorem StrictAnti.comp_strictAntiOn
  given: (hg : StrictAnti g) (hf : StrictAntiOn f s)
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 StrictAnti.comp_strictAntiOn
  条件: (hg : StrictAnti g) (hf : StrictAntiOn f s)
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
protected theorem StrictAnti.comp_strictAntiOn (hg : StrictAnti g) (hf : StrictAntiOn f s) :
    StrictMonoOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
theorem `StrictAnti.comp_strictMonoOn` / 定理 `StrictAnti.comp_strictMonoOn`

English:
theorem StrictAnti.comp_strictMonoOn
  given: (hg : StrictAnti g) (hf : StrictMonoOn f s)
  proof: fun _ ha _ hb h => hg (hf ha hb h)

中文:
定理 StrictAnti.comp_strictMonoOn
  条件: (hg : StrictAnti g) (hf : StrictMonoOn f s)
  证明: fun _ ha _ hb h => hg (hf ha hb h)
-/
theorem StrictAnti.comp_strictMonoOn (hg : StrictAnti g) (hf : StrictMonoOn f s) :
    StrictAntiOn (g ∘ f) s :=
  fun _ ha _ hb h => hg (hf ha hb h)

/--
lemma `MonotoneOn.comp` / 引理 `MonotoneOn.comp`

English:
lemma MonotoneOn.comp
  given: (hg : MonotoneOn g t) (hf : MonotoneOn f s) (hs : Set.MapsTo f s t)
  proof: fun _x hx _y hy hxy => hg (hs hx) (hs hy) hf hx hy hxy

中文:
引理 MonotoneOn.comp
  条件: (hg : MonotoneOn g t) (hf : MonotoneOn f s) (hs : Set.MapsTo f s t)
  证明: fun _x hx _y hy hxy => hg (hs hx) (hs hy) hf hx hy hxy
-/
lemma MonotoneOn.comp (hg : MonotoneOn g t) (hf : MonotoneOn f s) (hs : Set.MapsTo f s t) :
MonotoneOn (g ∘ f) s := fun _x hx _y hy hxy => hg (hs hx) (hs hy) hf hx hy hxy

/--
lemma `MonotoneOn.comp_AntitoneOn` / 引理 `MonotoneOn.comp_AntitoneOn`

English:
lemma MonotoneOn.comp_AntitoneOn
  statement: (hg : MonotoneOn g t) (hf : AntitoneOn f s)
  proof: fun _x hx _y hy hxy =>
hg (hs hy) (hs hx) hf hx hy hxy

中文:
引理 MonotoneOn.comp_AntitoneOn
  结论: (hg : MonotoneOn g t) (hf : AntitoneOn f s)
  证明: fun _x hx _y hy hxy =>
hg (hs hy) (hs hx) hf hx hy hxy
-/
lemma MonotoneOn.comp_AntitoneOn (hg : MonotoneOn g t) (hf : AntitoneOn f s)
    (hs : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s := fun _x hx _y hy hxy =>
hg (hs hy) (hs hx) hf hx hy hxy

/--
lemma `AntitoneOn.comp` / 引理 `AntitoneOn.comp`

English:
lemma AntitoneOn.comp
  given: (hg : AntitoneOn g t) (hf : AntitoneOn f s) (hs : Set.MapsTo f s t)
  proof: fun _x hx _y hy hxy => hg (hs hy) (hs hx) hf hx hy hxy

中文:
引理 AntitoneOn.comp
  条件: (hg : AntitoneOn g t) (hf : AntitoneOn f s) (hs : Set.MapsTo f s t)
  证明: fun _x hx _y hy hxy => hg (hs hy) (hs hx) hf hx hy hxy
-/
lemma AntitoneOn.comp (hg : AntitoneOn g t) (hf : AntitoneOn f s) (hs : Set.MapsTo f s t) :
MonotoneOn (g ∘ f) s := fun _x hx _y hy hxy => hg (hs hy) (hs hx) hf hx hy hxy

/--
lemma `AntitoneOn.comp_MonotoneOn` / 引理 `AntitoneOn.comp_MonotoneOn`

English:
lemma AntitoneOn.comp_MonotoneOn
  statement: (hg : AntitoneOn g t) (hf : MonotoneOn f s)
  proof: fun _x hx _y hy hxy =>
hg (hs hx) (hs hy) hf hx hy hxy

中文:
引理 AntitoneOn.comp_MonotoneOn
  结论: (hg : AntitoneOn g t) (hf : MonotoneOn f s)
  证明: fun _x hx _y hy hxy =>
hg (hs hx) (hs hy) hf hx hy hxy
-/
lemma AntitoneOn.comp_MonotoneOn (hg : AntitoneOn g t) (hf : MonotoneOn f s)
    (hs : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s := fun _x hx _y hy hxy =>
hg (hs hx) (hs hy) hf hx hy hxy

/--
lemma `StrictMonoOn.comp` / 引理 `StrictMonoOn.comp`

English:
lemma StrictMonoOn.comp
  given: (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t)
  proof: fun _x hx _y hy hxy => hg (hs hx) (hs hy) hf hx hy hxy

中文:
引理 StrictMonoOn.comp
  条件: (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t)
  证明: fun _x hx _y hy hxy => hg (hs hx) (hs hy) hf hx hy hxy
-/
lemma StrictMonoOn.comp (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy => hg (hs hx) (hs hy) hf hx hy hxy

/--
lemma `StrictMonoOn.comp_strictAntiOn` / 引理 `StrictMonoOn.comp_strictAntiOn`

English:
lemma StrictMonoOn.comp_strictAntiOn
  statement: (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
  proof: fun _x hx _y hy hxy =>
hg (hs hy) (hs hx) hf hx hy hxy

中文:
引理 StrictMonoOn.comp_strictAntiOn
  结论: (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
  证明: fun _x hx _y hy hxy =>
hg (hs hy) (hs hx) hf hx hy hxy

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.algebraMap_injective, algebraMap_injective
-/
lemma StrictMonoOn.comp_strictAntiOn (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy =>
hg (hs hy) (hs hx) hf hx hy hxy

/--
lemma `StrictAntiOn.comp` / 引理 `StrictAntiOn.comp`

English:
lemma StrictAntiOn.comp
  given: (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t)
  proof: fun _x hx _y hy hxy => hg (hs hy) (hs hx) hf hx hy hxy

中文:
引理 StrictAntiOn.comp
  条件: (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t)
  证明: fun _x hx _y hy hxy => hg (hs hy) (hs hx) hf hx hy hxy

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.equiv, Subalgebra, Subalgebra.algebraMap_eq, algebraMap_eq, galRestrict, injective, integralClosure, symm.injective
-/
lemma StrictAntiOn.comp (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy => hg (hs hy) (hs hx) hf hx hy hxy

/--
lemma `StrictAntiOn.comp_strictMonoOn` / 引理 `StrictAntiOn.comp_strictMonoOn`

English:
lemma StrictAntiOn.comp_strictMonoOn
  statement: (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
  proof: fun _x hx _y hy hxy =>
hg (hs hx) (hs hy) hf hx hy hxy

中文:
引理 StrictAntiOn.comp_strictMonoOn
  结论: (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
  证明: fun _x hx _y hy hxy =>
hg (hs hx) (hs hy) hf hx hy hxy
-/
lemma StrictAntiOn.comp_strictMonoOn (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy =>
hg (hs hx) (hs hy) hf hx hy hxy

end Composition

/-! ### Monotonicity in linear orders -/


section LinearOrder

variable [LinearOrder α]

section Preorder

variable [Preorder β] {f : α -> β} {s : Set α}

open Ordering

@[to_dual self]
/--
theorem `Monotone.reflect_lt` / 定理 `Monotone.reflect_lt`

English:
theorem Monotone.reflect_lt
  given: (hf : Monotone f) {a b : α} (h : f a < f b)
  statement: a < b
  proof: lt_of_not_ge fun h' => h.not_ge (hf h')

@[to_dual self]

中文:
定理 Monotone.reflect_lt
  条件: (hf : Monotone f) {a b : α} (h : f a < f b)
  结论: a < b
  证明: lt_of_not_ge fun h' => h.not_ge (hf h')

@[to_dual self]

Depends on / 依赖: h.not_ge, lt_of_not_ge, not_ge
-/
theorem Monotone.reflect_lt (hf : Monotone f) {a b : α} (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' => h.not_ge (hf h')

@[to_dual self]
/--
theorem `Antitone.reflect_lt` / 定理 `Antitone.reflect_lt`

English:
theorem Antitone.reflect_lt
  given: (hf : Antitone f) {a b : α} (h : f a < f b)
  statement: b < a
  proof: lt_of_not_ge fun h' => h.not_ge (hf h')

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 Antitone.reflect_lt
  条件: (hf : Antitone f) {a b : α} (h : f a < f b)
  结论: b < a
  证明: lt_of_not_ge fun h' => h.not_ge (hf h')

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: h.not_ge, lt_of_not_ge, not_ge
-/
theorem Antitone.reflect_lt (hf : Antitone f) {a b : α} (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' => h.not_ge (hf h')

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `MonotoneOn.reflect_lt` / 定理 `MonotoneOn.reflect_lt`

English:
theorem MonotoneOn.reflect_lt
  statement: (hf : MonotoneOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: lt_of_not_ge fun h' => h.not_ge hf hb ha h'

@[to_dual self (reorder := a b, ha hb)]

中文:
定理 MonotoneOn.reflect_lt
  结论: (hf : MonotoneOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: lt_of_not_ge fun h' => h.not_ge hf hb ha h'

@[to_dual self (reorder := a b, ha hb)]

Depends on / 依赖: h.not_ge, lt_of_not_ge, not_ge
-/
theorem MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b : α} (ha : a in s) (hb : b in s)
    (h : f a < f b) : a < b :=
lt_of_not_ge fun h' => h.not_ge hf hb ha h'

@[to_dual self (reorder := a b, ha hb)]
/--
theorem `AntitoneOn.reflect_lt` / 定理 `AntitoneOn.reflect_lt`

English:
theorem AntitoneOn.reflect_lt
  statement: (hf : AntitoneOn f s) {a b : α} (ha : a in s) (hb : b in s)
  proof: lt_of_not_ge fun h' => h.not_ge hf ha hb h'

中文:
定理 AntitoneOn.reflect_lt
  结论: (hf : AntitoneOn f s) {a b : α} (ha : a in s) (hb : b in s)
  证明: lt_of_not_ge fun h' => h.not_ge hf ha hb h'

Depends on / 依赖: h.not_ge, lt_of_not_ge, not_ge
-/
theorem AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b : α} (ha : a in s) (hb : b in s)
    (h : f a < f b) : b < a :=
lt_of_not_ge fun h' => h.not_ge hf ha hb h'

end Preorder

end LinearOrder

/--
theorem `Subtype.mono_coe` / 定理 `Subtype.mono_coe`

English:
theorem Subtype.mono_coe
  given: [Preorder α] (p : α -> Prop)
  statement: Monotone ((↑) : Subtype p -> α)
  proof: fun _ _ => id

中文:
定理 Subtype.mono_coe
  条件: [Preorder α] (p : α -> 命题)
  结论: Monotone ((↑) : Subtype p -> α)
  证明: fun _ _ => id

Depends on / 依赖: AlgHom, AlgHom.ext, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isLocalization, algebraMap_injective, injective, isDomain, isLocalization
-/
theorem Subtype.mono_coe [Preorder α] (p : α -> Prop) : Monotone ((↑) : Subtype p -> α) :=
  fun _ _ => id

/--
theorem `Subtype.strictMono_coe` / 定理 `Subtype.strictMono_coe`

English:
theorem Subtype.strictMono_coe
  given: [Preorder α] (p : α -> Prop)
  proof: fun _ _ => id

中文:
定理 Subtype.strictMono_coe
  条件: [Preorder α] (p : α -> 命题)
  证明: fun _ _ => id
-/
theorem Subtype.strictMono_coe [Preorder α] (p : α -> Prop) :
    StrictMono ((↑) : Subtype p -> α) :=
  fun _ _ => id

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {f : α -> γ} {g : β -> δ}

/--
theorem `monotone_fst` / 定理 `monotone_fst`

English:
theorem monotone_fst
  statement: Monotone (@Prod.fst α β)
  proof: fun _ _ => And.left

中文:
定理 monotone_fst
  结论: Monotone (@Prod.fst α β)
  证明: fun _ _ => And.left

Depends on / 依赖: And.left
-/
theorem monotone_fst : Monotone (@Prod.fst α β) := fun _ _ => And.left

/--
theorem `monotone_snd` / 定理 `monotone_snd`

English:
theorem monotone_snd
  statement: Monotone (@Prod.snd α β)
  proof: fun _ _ => And.right

中文:
定理 monotone_snd
  结论: Monotone (@Prod.snd α β)
  证明: fun _ _ => And.right

Depends on / 依赖: And.right
-/
theorem monotone_snd : Monotone (@Prod.snd α β) := fun _ _ => And.right

/--
theorem `monotone_prodMk_iff` / 定理 `monotone_prodMk_iff`

English:
theorem monotone_prodMk_iff
  given: {f : γ -> α} {g : γ -> β}
  proof: by
  simp_rw [Monotone, Prod.mk_le_mk, forall_and]

中文:
定理 monotone_prodMk_iff
  条件: {f : γ -> α} {g : γ -> β}
  证明: by
  simp_rw [Monotone, Prod.mk_le_mk, forall_and]

Depends on / 依赖: Monotone, Prod.mk_le_mk, forall_and, mk_le_mk, simp_rw
-/
theorem monotone_prodMk_iff {f : γ -> α} {g : γ -> β} :
    Monotone (fun x => (f x, g x)) ↔ Monotone f ∧ Monotone g := by
  simp_rw [Monotone, Prod.mk_le_mk, forall_and]

/--
theorem `Monotone.prodMk` / 定理 `Monotone.prodMk`

English:
theorem Monotone.prodMk
  given: {f : γ -> α} {g : γ -> β} (hf : Monotone f) (hg : Monotone g)
  proof: monotone_prodMk_iff.2 ⟨hf, hg⟩

中文:
定理 Monotone.prodMk
  条件: {f : γ -> α} {g : γ -> β} (hf : Monotone f) (hg : Monotone g)
  证明: monotone_prodMk_iff.2 ⟨hf, hg⟩

Depends on / 依赖: monotone_prodMk_iff
-/
theorem Monotone.prodMk {f : γ -> α} {g : γ -> β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x => (f x, g x)) :=
  monotone_prodMk_iff.2 ⟨hf, hg⟩

/--
theorem `Monotone.prodMap` / 定理 `Monotone.prodMap`

English:
theorem Monotone.prodMap
  given: (hf : Monotone f) (hg : Monotone g)
  statement: Monotone (Prod.map f g)
  proof: fun _ _ h => ⟨hf h.1, hg h.2⟩

中文:
定理 Monotone.prodMap
  条件: (hf : Monotone f) (hg : Monotone g)
  结论: Monotone (Prod.map f g)
  证明: fun _ _ h => ⟨hf h.1, hg h.2⟩
-/
theorem Monotone.prodMap (hf : Monotone f) (hg : Monotone g) : Monotone (Prod.map f g) :=
  fun _ _ h => ⟨hf h.1, hg h.2⟩

/--
theorem `Antitone.prodMap` / 定理 `Antitone.prodMap`

English:
theorem Antitone.prodMap
  given: (hf : Antitone f) (hg : Antitone g)
  statement: Antitone (Prod.map f g)
  proof: fun _ _ h => ⟨hf h.1, hg h.2⟩

中文:
定理 Antitone.prodMap
  条件: (hf : Antitone f) (hg : Antitone g)
  结论: Antitone (Prod.map f g)
  证明: fun _ _ h => ⟨hf h.1, hg h.2⟩
-/
theorem Antitone.prodMap (hf : Antitone f) (hg : Antitone g) : Antitone (Prod.map f g) :=
  fun _ _ h => ⟨hf h.1, hg h.2⟩

/--
lemma `monotone_prod_iff` / 引理 `monotone_prod_iff`

English:
lemma monotone_prod_iff
  given: {h : α × β -> γ}
  proof: ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

中文:
引理 monotone_prod_iff
  条件: {h : α × β -> γ}
  证明: ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

Depends on / 依赖: Prod.mk_le_mk_iff_right.mpr, mk_le_mk_iff_right
-/
lemma monotone_prod_iff {h : α × β -> γ} :
    Monotone h ↔ (forall a, Monotone (fun b => h (a, b))) ∧ (forall b, Monotone (fun a => h (a, b))) where
  mp h := ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

/--
lemma `antitone_prod_iff` / 引理 `antitone_prod_iff`

English:
lemma antitone_prod_iff
  given: {h : α × β -> γ}
  proof: ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

中文:
引理 antitone_prod_iff
  条件: {h : α × β -> γ}
  证明: ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

Depends on / 依赖: Prod.mk_le_mk_iff_right.mpr, mk_le_mk_iff_right
-/
lemma antitone_prod_iff {h : α × β -> γ} :
    Antitone h ↔ (forall a, Antitone (fun b => h (a, b))) ∧ (forall b, Antitone (fun a => h (a, b))) where
  mp h := ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] [Preorder γ] [Preorder δ] {f : α -> γ} {g : β -> δ}

/--
theorem `StrictMono.prodMap` / 定理 `StrictMono.prodMap`

English:
theorem StrictMono.prodMap
  given: (hf : StrictMono f) (hg : StrictMono g)
  statement: StrictMono (Prod.map f g)
  proof: fun a b => by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.monotone.imp) (And.imp hf.monotone.imp hg.imp)

中文:
定理 StrictMono.prodMap
  条件: (hf : StrictMono f) (hg : StrictMono g)
  结论: StrictMono (Prod.map f g)
  证明: fun a b => by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.monotone.imp) (And.imp hf.monotone.imp hg.imp)

Depends on / 依赖: And.imp, Or.imp, Prod.lt_iff, hf.imp, hf.monotone.imp, hg.imp, hg.monotone.imp, lt_iff, monotone
-/
theorem StrictMono.prodMap (hf : StrictMono f) (hg : StrictMono g) : StrictMono (Prod.map f g) :=
  fun a b => by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.monotone.imp) (And.imp hf.monotone.imp hg.imp)

/--
theorem `StrictAnti.prodMap` / 定理 `StrictAnti.prodMap`

English:
theorem StrictAnti.prodMap
  given: (hf : StrictAnti f) (hg : StrictAnti g)
  statement: StrictAnti (Prod.map f g)
  proof: fun a b => by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.antitone.imp) (And.imp hf.antitone.imp hg.imp)

中文:
定理 StrictAnti.prodMap
  条件: (hf : StrictAnti f) (hg : StrictAnti g)
  结论: StrictAnti (Prod.map f g)
  证明: fun a b => by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.antitone.imp) (And.imp hf.antitone.imp hg.imp)

Depends on / 依赖: And.imp, Or.imp, Prod.lt_iff, antitone, hf.antitone.imp, hf.imp, hg.antitone.imp, hg.imp, lt_iff
-/
theorem StrictAnti.prodMap (hf : StrictAnti f) (hg : StrictAnti g) : StrictAnti (Prod.map f g) :=
  fun a b => by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.antitone.imp) (And.imp hf.antitone.imp hg.imp)

end PartialOrder

/-! ### Pi types -/

namespace Function

variable [Preorder α] [DecidableEq ι] [forall i, Preorder (π i)] {f : forall i, π i} {i : ι}

-- Porting note: Dot notation breaks in `f.update i`
/--
theorem `update_mono` / 定理 `update_mono`

English:
theorem update_mono
  statement: Monotone (update f i)
  proof: fun _ _ => update_le_update_iff'.2

中文:
定理 update_mono
  结论: Monotone (update f i)
  证明: fun _ _ => update_le_update_iff'.2

Depends on / 依赖: IsDomain, IsIntegrallyClosed, update_le_update_iff
-/
theorem update_mono : Monotone (update f i) := fun _ _ => update_le_update_iff'.2

/--
theorem `update_strictMono` / 定理 `update_strictMono`

English:
theorem update_strictMono
  statement: StrictMono (update f i)
  proof: fun _ _ => update_lt_update_iff.2

中文:
定理 update_strictMono
  结论: StrictMono (update f i)
  证明: fun _ _ => update_lt_update_iff.2

Depends on / 依赖: update_lt_update_iff
-/
theorem update_strictMono : StrictMono (update f i) := fun _ _ => update_lt_update_iff.2

/--
theorem `const_mono` / 定理 `const_mono`

English:
theorem const_mono
  statement: Monotone (const β : α -> β -> α)
  proof: fun _ _ h _ => h

中文:
定理 const_mono
  结论: Monotone (const β : α -> β -> α)
  证明: fun _ _ h _ => h
-/
theorem const_mono : Monotone (const β : α -> β -> α) := fun _ _ h _ => h

/--
theorem `const_strictMono` / 定理 `const_strictMono`

English:
theorem const_strictMono
  given: [Nonempty β]
  statement: StrictMono (const β : α -> β -> α)
  proof: fun _ _ => const_lt_const.2

中文:
定理 const_strictMono
  条件: [Nonempty β]
  结论: StrictMono (const β : α -> β -> α)
  证明: fun _ _ => const_lt_const.2

Depends on / 依赖: const_lt_const
-/
theorem const_strictMono [Nonempty β] : StrictMono (const β : α -> β -> α) :=
  fun _ _ => const_lt_const.2

end Function

section apply
variable {β : ι -> Type*} [forall i, Preorder (β i)] [Preorder α] {f : α -> forall i, β i}

/--
lemma `monotone_iff_apply₂` / 引理 `monotone_iff_apply₂`

English:
lemma monotone_iff_apply₂
  statement: Monotone f ↔ forall i, Monotone (f · i)
  proof: by
  simp [Monotone, Pi.le_def, @forall_comm ι]

中文:
引理 monotone_iff_apply₂
  结论: Monotone f ↔ 对任意 i, Monotone (f · i)
  证明: by
  simp [Monotone, Pi.le_def, @forall_comm ι]

Depends on / 依赖: Monotone, Pi.le_def, forall_comm, le_def
-/
lemma monotone_iff_apply₂ : Monotone f ↔ forall i, Monotone (f · i) := by
  simp [Monotone, Pi.le_def, @forall_comm ι]

/--
lemma `antitone_iff_apply₂` / 引理 `antitone_iff_apply₂`

English:
lemma antitone_iff_apply₂
  statement: Antitone f ↔ forall i, Antitone (f · i)
  proof: by
  simp [Antitone, Pi.le_def, @forall_comm ι]

alias ⟨Monotone.apply₂, Monotone.of_apply₂⟩ := monotone_iff_apply₂
alias ⟨Antitone.apply₂, Antitone.of_apply₂⟩ := antitone_iff_apply₂

中文:
引理 antitone_iff_apply₂
  结论: Antitone f ↔ 对任意 i, Antitone (f · i)
  证明: by
  simp [Antitone, Pi.le_def, @forall_comm ι]

alias ⟨Monotone.apply₂, Monotone.of_apply₂⟩ := monotone_iff_apply₂
alias ⟨Antitone.apply₂, Antitone.of_apply₂⟩ := antitone_iff_apply₂

Depends on / 依赖: Antitone, Pi.le_def, forall_comm, le_def
-/
lemma antitone_iff_apply₂ : Antitone f ↔ forall i, Antitone (f · i) := by
  simp [Antitone, Pi.le_def, @forall_comm ι]

alias ⟨Monotone.apply₂, Monotone.of_apply₂⟩ := monotone_iff_apply₂
alias ⟨Antitone.apply₂, Antitone.of_apply₂⟩ := antitone_iff_apply₂

end apply
