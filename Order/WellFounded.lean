/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Bounds.Defs

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α, β x`.

The predicate `WellFounded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `WellFounded.min`, `WellFounded.sup`, and `WellFounded.succ`,
and an induction principle `WellFounded.induction_bot`.
-/

@[expose] public section

/-
**acc_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：acc_def {α} {r : α -> α -> Prop} {a : α} : Acc r a ↔ forall b, r b a -> Ac
c r b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y,
 r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, i
ncluding
construction of fixed points in the space of dependent functions `Π x : α, β x`.

The predicate `WellFounded` is defined in the core library. In this file we prov
e some extra lemmas
and provide a few new definitions: `WellFounded.min`, `WellFounded.sup`, and `We
llFounded.succ`,
and an induction principle `WellFounded.induction_bot`.
-/
theorem acc_def {α} {r : α → α → Prop} {a : α} : Acc r a ↔ ∀ b, r b a → Acc r b where
  mp h := h.rec fun _ h _ ↦ h
  mpr := .intro a
/-
**exists_not_acc_lt_of_not_acc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_not_acc_lt_of_not_acc {α} {a : α} {r} (h : ¬Acc r a) : exists b, ¬A
cc r b ∧ r b a
参数：h : ¬Acc r a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `acc_def`：acc_def {α} {r : α -> α -> Prop} {a : α} : Acc r a ↔ forall b, 
r b a -> Acc r b where mp h
-/
theorem exists_not_acc_lt_of_not_acc {α} {a : α} {r} (h : ¬Acc r a) : ∃ b, ¬Acc r b ∧ r b a := by
  rw [acc_def] at h
  push Not at h
  simpa only [and_comm]
/-
**not_acc_iff_exists_descending_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_acc_iff_exists_descending_chain {α} {r : α -> α -> Prop} {x : α} : ¬Ac
c r x ↔ exists f : Nat -> α, f 0 = x ∧ forall n, r (f (n + 1)) (f n) where mp hx
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_not_acc_lt_of_not_acc`：exists_not_acc_lt_of_not_acc {α} {a : α} {
r} (h : ¬Acc r a) : exists b, ¬Acc r b ∧ r b a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem not_acc_iff_exists_descending_chain {α} {r : α → α → Prop} {x : α} :
    ¬Acc r x ↔ ∃ f : ℕ → α, f 0 = x ∧ ∀ n, r (f (n + 1)) (f n) where
  mp hx := let f : ℕ → {a : α // ¬Acc r a} :=
      Nat.rec ⟨x, hx⟩ fun _ a ↦ ⟨_, (exists_not_acc_lt_of_not_acc a.2).choose_spec.1⟩
    ⟨(f · |>.1), rfl, fun n ↦ (exists_not_acc_lt_of_not_acc (f n).2).choose_spec.2⟩
  mpr h acc := acc.rec
    (fun _x _ ih ⟨f, hf⟩ ↦ ih (f 1) (hf.1 ▸ hf.2 0) ⟨(f <| · + 1), rfl, fun _ ↦ hf.2 _⟩) h
/-
**acc_iff_isEmpty_descending_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：acc_iff_isEmpty_descending_chain {α} {r : α -> α -> Prop} {x : α} : Acc r 
x ↔ IsEmpty { f : Nat -> α // f 0 = x ∧ forall n, r (f (n + 1)) (f n) }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `not_acc_iff_exists_descending_chain`：not_acc_iff_exists_descending_chain
 {α} {r : α -> α -> Prop} {x : α} : ¬Acc r x ↔ exists f : Nat -> α, f 0 = x ∧ fo
rall n, r (f (n + 1)) (f …
-/
theorem acc_iff_isEmpty_descending_chain {α} {r : α → α → Prop} {x : α} :
    Acc r x ↔ IsEmpty { f : ℕ → α // f 0 = x ∧ ∀ n, r (f (n + 1)) (f n) } := by
  contrapose!
  rw [nonempty_subtype]
  exact not_acc_iff_exists_descending_chain

/-- A relation is well-founded iff it doesn't have any infinite descending chain.

See `RelEmbedding.wellFounded_iff_isEmpty` for a version in terms of relation embeddings. -/
/-
**wellFounded_iff_isEmpty_descending_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_iff_isEmpty_descending_chain {α} {r : α -> α -> Prop} : WellFo
unded r ↔ IsEmpty { f : Nat -> α // forall n, r (f (n + 1)) (f n) } where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `acc_iff_isEmpty_descending_chain`：acc_iff_isEmpty_descending_chain {α} {
r : α -> α -> Prop} {x : α} : Acc r x ↔ IsEmpty { f : Nat -> α // f 0 = x ∧ fora
ll n, r (f (n + 1)) (f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A relation is well-founded iff it doesn't have any infinite descending chain.

See `RelEmbedding.wellFounded_iff_isEmpty` for a version in terms of relation em
beddings.
-/
theorem wellFounded_iff_isEmpty_descending_chain {α} {r : α → α → Prop} :
    WellFounded r ↔ IsEmpty { f : ℕ → α // ∀ n, r (f (n + 1)) (f n) } where
  mp := fun ⟨h⟩ ↦ ⟨fun ⟨f, hf⟩ ↦ (acc_iff_isEmpty_descending_chain.mp (h (f 0))).false ⟨f, rfl, hf⟩⟩
  mpr h := ⟨fun _ ↦ acc_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ ↦ h.false ⟨f, hf.2⟩⟩⟩

variable {α β γ : Type*}

namespace WellFounded

variable {r r' : α → α → Prop}

/-
**WellFounded.asymm** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, WellFounded r → Std.Asymm r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.asymmetric`：WellFounded.asymmetric {α : Sort*} {r : α -> α -
> Prop} (h : WellFounded r) (a b) : r a b -> ¬r b a
-/
protected theorem asymm (h : WellFounded r) : Std.Asymm r := ⟨h.asymmetric⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := WellFounded.asymm
/-
**WellFounded.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, WellFounded r → Std.Irrefl r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Asymm.irrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Asymm r], Std
.Irrefl r
· 使用定理 `WellFounded.asymm`：∀ {α : Type u_1} {r : α → α → Prop}, WellFounded r → 
Std.Asymm r
-/
protected theorem irrefl (h : WellFounded r) : Std.Irrefl r := @Std.Asymm.irrefl α r h.asymm

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := WellFounded.irrefl
/-
**WellFounded.** 是 Mathlib 中的一个实例，位于命名空间 `WellFounded`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedRelation α] : Std.Asymm (α := α) WellFoundedRelation.rel :=
  WellFoundedRelation.wf.asymm
/-
**WellFounded.mono** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：mono (hr : WellFounded r) (h : forall a b, r' a b -> r a b) : WellFounded 
r'
参数：hr : WellFounded r；h : forall a b, r' a b -> r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.wf`：∀ {α : Sort u} {r q : α → α → Prop}, Subrelation q r → W
ellFounded r → WellFounded q
-/
theorem mono (hr : WellFounded r) (h : ∀ a b, r' a b → r a b) : WellFounded r' :=
  Subrelation.wf (h _ _) hr

open scoped Function in -- required for scoped `on` notation
/-
**WellFounded.onFun** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：onFun {α β : Sort*} {r : β -> β -> Prop} {f : α -> β} : WellFounded r -> W
ellFounded (r on f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
-/
theorem onFun {α β : Sort*} {r : β → β → Prop} {f : α → β} :
    WellFounded r → WellFounded (r on f) :=
  InvImage.wf _
/-
**WellFounded.** 是 Mathlib 中的一个实例，位于命名空间 `WellFounded`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : β → β → Prop) (f : α → β) [IsWellFounded β r] :
    IsWellFounded α (r.onFun f) where
  wf := IsWellFounded.wf.onFun
/-
**WellFounded._root_.Function.Injective.isWellOrder** 是 Mathlib 中的一个定理，位于命名空间 `W
ellFounded`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.isWellOrder (r : β → β → Prop) {f : α → β} (hf : f.Injective)
    [IsWellOrder β r] : IsWellOrder α (r.onFun f) where
  __ := hf.trichotomous_onFun r

/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
/-
**WellFounded.has_min** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r → ∀ (s : Set α), s.None
mpty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a

--- 原说明 ---
If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`.
-/
theorem has_min {α} {r : α → α → Prop} (H : WellFounded r) (s : Set α) :
    s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
  | ⟨a, ha⟩ => show ∃ b ∈ s, ∀ x ∈ s, ¬r x b from
    Acc.recOn (H.apply a) (fun x _ IH =>
        not_imp_not.1 fun hne hx => hne <| ⟨x, hx, fun y hy hyx => hne <| IH y hyx hy⟩)
      ha
/-
**WellFounded.not_rightTotal** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：not_rightTotal (wf : WellFounded r) [Nonempty α] : ¬ Relator.RightTotal r
参数：wf : WellFounded r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem not_rightTotal (wf : WellFounded r) [Nonempty α] : ¬ Relator.RightTotal r := by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hba⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction
/-
**WellFounded.not_leftTotal** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：not_leftTotal (wf : WellFounded (Function.swap r)) [Nonempty α] : ¬ Relato
r.LeftTotal r
参数：wf : WellFounded (Function.swap r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem not_leftTotal (wf : WellFounded (Function.swap r)) [Nonempty α] :
    ¬ Relator.LeftTotal r := by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hab⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction

/-- A minimal element of a nonempty set in a well-founded order.

If you're working with a nonempty linear order, consider defining a
`ConditionallyCompleteLinearOrderBot` instance via
`WellFoundedLT.conditionallyCompleteLinearOrderBot` and using `Inf` instead. -/
/-
**WellFounded.min** 是 Mathlib 中的一个定义，位于命名空间 `WellFounded`。
形式化陈述：min {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) 
: α
参数：H : WellFounded r；s : Set α；h : s.Nonempty。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a

--- 原说明 ---
A minimal element of a nonempty set in a well-founded order.

If you're working with a nonempty linear order, consider defining a
`ConditionallyCompleteLinearOrderBot` instance via
`WellFoundedLT.conditionallyCompleteLinearOrderBot` and using `Inf` instead.
-/
noncomputable def min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=
  Classical.choose (H.has_min s h)
/-
**WellFounded.min_mem** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) (h : s.Nonemp
ty) : H.min s h in s
参数：H : WellFounded r；s : Set α；h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem min_mem {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) :
    H.min s h ∈ s :=
  let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h
/-
**WellFounded.prop_min** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：prop_min {r : α -> α -> Prop} (H : WellFounded r) {p : α -> Prop} (h : exi
sts a, p a) : p (H.min {a | p a} h)
参数：H : WellFounded r；h : exists a, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
-/
theorem prop_min {r : α → α → Prop} (H : WellFounded r) {p : α → Prop} (h : ∃ a, p a) :
    p (H.min {a | p a} h) :=
  H.min_mem {a | p a} h
/-
**WellFounded.not_lt_min** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：not_lt_min {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) {x} (hx : 
x in s) : ¬r x (H.min s ⟨x, hx⟩)
参数：H : WellFounded r；s : Set α；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem not_lt_min {r : α → α → Prop} (H : WellFounded r) (s : Set α) {x} (hx : x ∈ s) :
    ¬r x (H.min s ⟨x, hx⟩) :=
  let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s ⟨x, hx⟩)
  h' _ hx

/-- The minimal element of a trichotomous well-founded order is unique -/
/-
**WellFounded.min_eq_of_forall_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：min_eq_of_forall_not_lt [Std.Trichotomous r] (wf : WellFounded r) {s : Set
 α} {m : α} (hms : m in s) (hrm : forall x in s, ¬r x m) : wf.min s ⟨m, hms⟩ = m
参数：wf : WellFounded r；hms : m in s；hrm : forall x in s, ¬r x m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)

--- 原说明 ---
The minimal element of a trichotomous well-founded order is unique
-/
theorem min_eq_of_forall_not_lt [Std.Trichotomous r] (wf : WellFounded r) {s : Set α} {m : α}
    (hms : m ∈ s) (hrm : ∀ x ∈ s, ¬r x m) : wf.min s ⟨m, hms⟩ = m :=
  Std.Trichotomous.trichotomous _ m (hrm _ <| wf.min_mem s _) (wf.not_lt_min s hms)
/-
**WellFounded.notMem_of_lt_min** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：notMem_of_lt_min {wf : WellFounded r} {s : Set α} {hs : s.Nonempty} {x : α
} (hx : r x (wf.min s hs)) : x ∉ s
参数：hx : r x (wf.min s hs)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
-/
theorem notMem_of_lt_min {wf : WellFounded r} {s : Set α} {hs : s.Nonempty} {x : α}
    (hx : r x (wf.min s hs)) : x ∉ s :=
  (wf.not_lt_min s · hx)
/-
**WellFounded.mem_of_lt_min_compl** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：mem_of_lt_min_compl {wf : WellFounded r} {s : Set α} {hs : sᶜ.Nonempty} {x
 : α} (hx : r x (wf.min sᶜ hs)) : x in s
参数：hx : r x (wf.min sᶜ hs)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.notMem_compl_iff`：notMem_compl_iff {x : α} : x ∉ sᶜ ↔ x in s
· 使用定理 `WellFounded.notMem_of_lt_min`：notMem_of_lt_min {wf : WellFounded r} {s :
 Set α} {hs : s.Nonempty} {x : α} (hx : r x (wf.min s hs)) : x ∉ s
-/
theorem mem_of_lt_min_compl {wf : WellFounded r} {s : Set α} {hs : sᶜ.Nonempty} {x : α}
    (hx : r x (wf.min sᶜ hs)) : x ∈ s :=
  Set.notMem_compl_iff.mp <| notMem_of_lt_min hx
/-
**WellFounded.wellFounded_iff_has_min** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：wellFounded_iff_has_min {r : α -> α -> Prop} : WellFounded r ↔ forall s : 
Set α, s.Nonempty -> exists m in s, forall x in s, ¬r x m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
-/
theorem wellFounded_iff_has_min {r : α → α → Prop} :
    WellFounded r ↔ ∀ s : Set α, s.Nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬r x m := by
  refine ⟨fun h => h.has_min, fun h => ⟨fun x => ?_⟩⟩
  by_contra hx
  obtain ⟨m, hm, hm'⟩ := h {x | ¬Acc r x} ⟨x, hx⟩
  refine hm ⟨_, fun y hy => ?_⟩
  by_contra hy'
  exact hm' y hy' hy

@[to_dual]
/-
**WellFounded.wellFoundedLT_iff_exists_minimal** 是 Mathlib 中的一个定理，位于命名空间 `WellFo
unded`。
形式化陈述：wellFoundedLT_iff_exists_minimal [Preorder α] : WellFoundedLT α ↔ forall s
 : Set α, s.Nonempty -> exists m, Minimal (· in s) m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem wellFoundedLT_iff_exists_minimal [Preorder α] :
    WellFoundedLT α ↔ ∀ s : Set α, s.Nonempty → ∃ m, Minimal (· ∈ s) m := by
  simp only [isWellFounded_iff, wellFounded_iff_has_min, not_lt_iff_le_imp_ge, Minimal]

@[to_dual]
alias ⟨_root_.WellFoundedLT.exists_minimal, _⟩ := wellFoundedLT_iff_exists_minimal

@[to_dual]
/-
**WellFounded.minimal_wellFounded_lt_min** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`
。
形式化陈述：minimal_wellFounded_lt_min [Preorder α] [WellFoundedLT α] {s : Set α} (h :
 s.Nonempty) : Minimal (· in s) (wellFounded_lt.min s h)
参数：h : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem minimal_wellFounded_lt_min [Preorder α] [WellFoundedLT α] {s : Set α} (h : s.Nonempty) :
    Minimal (· ∈ s) (wellFounded_lt.min s h) := by
  grind [Minimal, lt_iff_le_not_ge, WellFounded.min]
/-
**WellFounded.isWellOrder_iff_exists_not_lt_and_eq_or_gt** 是 Mathlib 中的一个定理，位于命名
空间 `WellFounded`。
形式化陈述：isWellOrder_iff_exists_not_lt_and_eq_or_gt : IsWellOrder α r ↔ forall s : 
Set α, s.Nonempty -> exists m in s, forall x in s, ¬r x m ∧ (m = x ∨ r m x)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isWellOrder_iff_exists_not_lt_and_eq_or_gt :
    IsWellOrder α r ↔ ∀ s : Set α, s.Nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬r x m ∧ (m = x ∨ r m x) := by
  refine ⟨fun h s hs ↦ ?_, fun h ↦ { wf := ?_, trichotomous a b := ?_ }⟩
  · grind [h.wf.has_min, trichotomous_of r]
  · grind [wellFounded_iff_has_min]
  · grind [h {a, b} <| by simp]

/-- The minimum of `f '' s` is `f` applied to the minimum of `s`. -/
/-
**WellFounded.min_image** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：min_image {r : β -> β -> Prop} [Std.Trichotomous r] (wf : WellFounded r) (
f : α -> β) {s : Set α} (hne : s.Nonempty) : wf.min (f '' s) (hne.image f) = f (
wf.onFun (f
参数：wf : WellFounded r；f : α -> β；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.min_eq_of_forall_not_lt`：min_eq_of_forall_not_lt [Std.Tricho
tomous r] (wf : WellFounded r) {s : Set α} {m : α} (hms : m in s) (hrm : forall 
x in s, ¬r x m) : wf.min …
· 使用定理 `WellFounded.onFun`：onFun {α β : Sort*} {r : β -> β -> Prop} {f : α -> β}
 : WellFounded r -> WellFounded (r on f)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)

--- 原说明 ---
The minimum of `f '' s` is `f` applied to the minimum of `s`.
-/
theorem min_image {r : β → β → Prop} [Std.Trichotomous r] (wf : WellFounded r) (f : α → β)
    {s : Set α} (hne : s.Nonempty) :
    wf.min (f '' s) (hne.image f) = f (wf.onFun (f := f) |>.min s hne) := by
  apply min_eq_of_forall_not_lt wf <| Set.mem_image_of_mem f <| min_mem wf.onFun s hne
  rintro _ ⟨a, has, rfl⟩
  exact wf.onFun.not_lt_min s has
/-
**WellFounded.not_rel_apply_succ** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：not_rel_apply_succ [h : IsWellFounded α r] (f : Nat -> α) : exists n, ¬ r 
(f (n + 1)) (f n)
参数：f : Nat -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `wellFounded_iff_isEmpty_descending_chain`：wellFounded_iff_isEmpty_descen
ding_chain {α} {r : α -> α -> Prop} : WellFounded r ↔ IsEmpty { f : Nat -> α // 
forall n, r (f (n + 1)) (f n) …
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem not_rel_apply_succ [h : IsWellFounded α r] (f : ℕ → α) : ∃ n, ¬ r (f (n + 1)) (f n) := by
  by_contra! hf
  exact (wellFounded_iff_isEmpty_descending_chain.1 h.wf).elim ⟨f, hf⟩

open Set

/-- The supremum of a bounded, well-founded order -/
/-
**WellFounded.sup** 是 Mathlib 中的一个定义，位于命名空间 `WellFounded`。
形式化陈述：{α : Type u_1} → {r : α → α → Prop} → WellFounded r → (s : Set α) → Set.Bo
unded r s → α
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of a bounded, well-founded order
-/
protected noncomputable def sup {r : α → α → Prop} (wf : WellFounded r) (s : Set α)
    (h : Bounded r s) : α :=
  wf.min { x | ∀ a ∈ s, r a x } h
/-
**WellFounded.lt_sup** 是 Mathlib 中的一个定理，位于命名空间 `WellFounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : 
Set.Bounded r s) {x : α},   x ∈ s → r x (wf.sup s h)
参数：wf : WellFounded r；h : Set.Bounded r s；wf.sup s h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
-/
protected theorem lt_sup {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x}
    (hx : x ∈ s) : r x (wf.sup s h) :=
  min_mem wf { x | ∀ a ∈ s, r a x } h x hx

end WellFounded

section LinearOrder

variable [LinearOrder β] [Preorder γ]

-- TODO: the name `WellFounded.min` is incorrect when the assumption is that `>` is well-founded.
@[to_dual none]
/-
**WellFounded.min_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.min_le (h : WellFounded ((· < ·) : β -> β -> Prop)) {x : β} {s
 : Set β} (hx : x in s) : h.min s ⟨x, hx⟩ <= x
参数：h : WellFounded ((· < ·) : β -> β -> Prop)；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
-/
theorem WellFounded.min_le (h : WellFounded ((· < ·) : β → β → Prop))
    {x : β} {s : Set β} (hx : x ∈ s) : h.min s ⟨x, hx⟩ ≤ x :=
  not_lt.1 <| h.not_lt_min _ hx
/-
**Set.range_injOn_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.range_injOn_strictMono [WellFoundedLT β] : Set.InjOn Set.range { f : β
 -> γ | StrictMono f }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
-/
theorem Set.range_injOn_strictMono [WellFoundedLT β] :
    Set.InjOn Set.range { f : β → γ | StrictMono f } := by
  intro f hf g hg hfg
  ext a
  apply WellFoundedLT.induction a
  intro a IH
  obtain ⟨b, hb⟩ := hfg ▸ mem_range_self a
  obtain h | rfl | h := lt_trichotomy b a
  · rw [← IH b h] at hb
    cases (hf.injective hb).not_lt h
  · rw [hb]
  · obtain ⟨c, hc⟩ := hfg.symm ▸ mem_range_self a
    have := hg h
    rw [hb, ← hc, hf.lt_iff_lt] at this
    rw [IH c this] at hc
    cases (hg.injective hc).not_lt this
/-
**Set.range_injOn_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.range_injOn_strictAnti [WellFoundedGT β] : Set.InjOn Set.range { f : β
 -> γ | StrictAnti f }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_injOn_strictMono`：Set.range_injOn_strictMono [WellFoundedLT β]
 : Set.InjOn Set.range { f : β -> γ | StrictMono f }
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
· 使用定理 `StrictAnti.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictAnti f → StrictAnti (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…
-/
theorem Set.range_injOn_strictAnti [WellFoundedGT β] :
    Set.InjOn Set.range { f : β → γ | StrictAnti f } :=
  fun _ hf _ hg ↦ Set.range_injOn_strictMono (β := βᵒᵈ) hf.dual hg.dual
/-
**StrictMono.range_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.range_inj [WellFoundedLT β] {f g : β -> γ} (hf : StrictMono f) 
(hg : StrictMono g) : Set.range f = Set.range g ↔ f = g
参数：hf : StrictMono f；hg : StrictMono g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Set.range_injOn_strictMono`：Set.range_injOn_strictMono [WellFoundedLT β]
 : Set.InjOn Set.range { f : β -> γ | StrictMono f }
-/
theorem StrictMono.range_inj [WellFoundedLT β] {f g : β → γ}
    (hf : StrictMono f) (hg : StrictMono g) : Set.range f = Set.range g ↔ f = g :=
  Set.range_injOn_strictMono.eq_iff hf hg
/-
**StrictAnti.range_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.range_inj [WellFoundedGT β] {f g : β -> γ} (hf : StrictAnti f) 
(hg : StrictAnti g) : Set.range f = Set.range g ↔ f = g
参数：hf : StrictAnti f；hg : StrictAnti g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Set.range_injOn_strictAnti`：Set.range_injOn_strictAnti [WellFoundedGT β]
 : Set.InjOn Set.range { f : β -> γ | StrictAnti f }
-/
theorem StrictAnti.range_inj [WellFoundedGT β] {f g : β → γ}
    (hf : StrictAnti f) (hg : StrictAnti g) : Set.range f = Set.range g ↔ f = g :=
  Set.range_injOn_strictAnti.eq_iff hf hg

/-- A strictly monotone function `f` on a well-order satisfies `x ≤ f x` for all `x`. -/
/-
**StrictMono.id_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : StrictMono f) : id <
= f
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.le_def`：Pi.le_def {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] {
x y : forall i, π i} : x <= y ↔ forall i, x i <= y i
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A strictly monotone function `f` on a well-order satisfies `x ≤ f x` for all `x`
.
-/
theorem StrictMono.id_le [WellFoundedLT β] {f : β → β} (hf : StrictMono f) : id ≤ f := by
  rw [Pi.le_def]
  by_contra! H
  obtain ⟨m, hm, hm'⟩ := wellFounded_lt.has_min {i | f i < i} H
  exact hm' _ (hf hm) hm
/-
**StrictMono.le_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} (hf : StrictMono f) {x}
 : x <= f x
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
-/
theorem StrictMono.le_apply [WellFoundedLT β] {f : β → β} (hf : StrictMono f) {x} : x ≤ f x :=
  hf.id_le x

/-- A strictly monotone function `f` on a cowell-order satisfies `f x ≤ x` for all `x`. -/
/-
**StrictMono.le_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.le_id [WellFoundedGT β] {f : β -> β} (hf : StrictMono f) : f <=
 id
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
· 使用定理 `StrictMono.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictMono f → StrictMono (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…

--- 原说明 ---
A strictly monotone function `f` on a cowell-order satisfies `f x ≤ x` for all `
x`.
-/
theorem StrictMono.le_id [WellFoundedGT β] {f : β → β} (hf : StrictMono f) : f ≤ id :=
  StrictMono.id_le (β := βᵒᵈ) hf.dual
/-
**StrictMono.apply_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.apply_le [WellFoundedGT β] {f : β -> β} (hf : StrictMono f) {x}
 : f x <= x
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
· 使用定理 `StrictMono.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictMono f → StrictMono (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…
-/
theorem StrictMono.apply_le [WellFoundedGT β] {f : β → β} (hf : StrictMono f) {x} : f x ≤ x :=
  StrictMono.le_apply (β := βᵒᵈ) hf.dual
/-
**StrictMono.not_bddAbove_range_of_wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.not_bddAbove_range_of_wellFoundedLT {f : β -> β} [WellFoundedLT
 β] [NoMaxOrder β] (hf : StrictMono f) : ¬ BddAbove (Set.range f)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem StrictMono.not_bddAbove_range_of_wellFoundedLT {f : β → β} [WellFoundedLT β] [NoMaxOrder β]
    (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := exists_gt a
  exact ((hf.le_apply.trans_lt (hf hb)).trans_le <| ha (Set.mem_range_self _)).false
/-
**StrictMono.not_bddBelow_range_of_wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.not_bddBelow_range_of_wellFoundedGT {f : β -> β} [WellFoundedGT
 β] [NoMinOrder β] (hf : StrictMono f) : ¬ BddBelow (Set.range f)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.not_bddAbove_range_of_wellFoundedLT`：StrictMono.not_bddAbove_
range_of_wellFoundedLT {f : β -> β} [WellFoundedLT β] [NoMaxOrder β] (hf : Stric
tMono f) : ¬ BddAbove (Set.range f)
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
· 使用定理 `StrictMono.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β},   StrictMono f → StrictMono (⇑OrderDual.toDual ∘ f ∘
 ⇑Ord…
-/
theorem StrictMono.not_bddBelow_range_of_wellFoundedGT {f : β → β} [WellFoundedGT β] [NoMinOrder β]
    (hf : StrictMono f) : ¬ BddBelow (Set.range f) :=
  hf.dual.not_bddAbove_range_of_wellFoundedLT

end LinearOrder

namespace Function

variable (f : α → β)

section LT

variable [LT β] [WellFoundedLT β]

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `Function.not_lt_argmin`.

See also `Set.Finite.exists_minimalFor` and related lemmas for the case when `α` is finite. -/
/-
**Function.argmin** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：argmin [Nonempty α] : α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty

--- 原说明 ---
Given a function `f : α → β` where `β` carries a well-founded `<`, this is an el
ement of `α`
whose image under `f` is minimal in the sense of `Function.not_lt_argmin`.

See also `Set.Finite.exists_minimalFor` and related lemmas for the case when `α`
 is finite.
-/
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) Set.univ Set.univ_nonempty
/-
**Function.not_lt_argmin** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) _ (Set.mem_univ a)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`Function.not_lt_argminOn`.

See also `Set.Finite.exists_minimalFor` and related lemmas for the case when `α` or `s` is finite.

TODO Consider removing this definition in favour of `exists_minimalFor_of_wellFoundedLT`. -/
/-
**Function.argminOn** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：argminOn (s : Set α) (hs : s.Nonempty) : α
参数：s : Set α；hs : s.Nonempty。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-emp
ty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense 
of
`Function.not_lt_argminOn`.

See also `Set.Finite.exists_minimalFor` and related lemmas for the case when `α`
 or `s` is finite.

TODO Consider removing this definition in favour of `exists_minimalFor_of_wellFo
undedLT`.
-/
noncomputable def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) s hs

@[simp]
/-
**Function.argminOn_mem** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f s hs in s
参数：s : Set α；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
-/
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f s hs ∈ s :=
  WellFounded.min_mem _ _ _
/-
**Function.not_lt_argminOn** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：not_lt_argminOn (s : Set α) {a : α} (ha : a in s) : ¬f a < f (argminOn f s
 ⟨a, ha⟩)
参数：s : Set α；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
-/
theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s) : ¬f a < f (argminOn f s ⟨a, ha⟩) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) s ha

end LT

section LinearOrder

variable [LinearOrder β] [WellFoundedLT β]

/-
**Function.argmin_le** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：argmin_le (a : α) [Nonempty α] : f (argmin f) <= f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Function.not_lt_argmin`：not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (a
rgmin f)
-/
theorem argmin_le (a : α) [Nonempty α] : f (argmin f) ≤ f a :=
  not_lt.mp <| not_lt_argmin f a
/-
**Function.isMinimalFor_argmin** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：isMinimalFor_argmin [Nonempty α] : MinimalFor (fun _ => True) f (argmin f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Function.argmin_le`：argmin_le (a : α) [Nonempty α] : f (argmin f) <= f a
-/
theorem isMinimalFor_argmin [Nonempty α] :
    MinimalFor (fun _ ↦ True) f (argmin f) :=
  ⟨trivial, fun a _ _ ↦ argmin_le f a⟩
/-
**Function.argminOn_le** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：argminOn_le (s : Set α) {a : α} (ha : a in s) : f (argminOn f s ⟨a, ha⟩) <
= f a
参数：s : Set α；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Function.not_lt_argminOn`：not_lt_argminOn (s : Set α) {a : α} (ha : a in
 s) : ¬f a < f (argminOn f s ⟨a, ha⟩)
-/
theorem argminOn_le (s : Set α) {a : α} (ha : a ∈ s) :
    f (argminOn f s ⟨a, ha⟩) ≤ f a :=
  not_lt.mp <| not_lt_argminOn f s ha
/-
**Function.isMinimalFor_argminOn** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：isMinimalFor_argminOn (s : Set α) (hs : s.Nonempty) : MinimalFor (· in s) 
f (argminOn f s hs)
参数：s : Set α；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.argminOn_mem`：argminOn_mem (s : Set α) (hs : s.Nonempty) : argm
inOn f s hs in s
· 使用定理 `Function.argminOn_le`：argminOn_le (s : Set α) {a : α} (ha : a in s) : f 
(argminOn f s ⟨a, ha⟩) <= f a
-/
theorem isMinimalFor_argminOn (s : Set α) (hs : s.Nonempty) :
    MinimalFor (· ∈ s) f (argminOn f s hs) :=
  ⟨argminOn_mem f s hs, fun _ h _ ↦ argminOn_le f s h⟩

end LinearOrder

end Function

section Induction

/-- Let `r` be a relation on `α`, let `f : α → β` be a function, let `C : β → Prop`, and
let `bot : α`. This induction principle shows that `C (f bot)` holds, given that
* some `a` that is accessible by `r` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
/-
**Acc.induction_bot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Acc.induction_bot' {α β} {r : α -> α -> Prop} {a bot : α} (ha : Acc r a) {
C : β -> Prop} {f : α -> β} (ih : forall b, f b != f bot -> C (f b) -> exists c,
 r c b ∧ C (f c)) : C (f a) -> C (f bot)
参数：ha : Acc r a；ih : forall b, f b != f bot -> C (f b) -> exists c, r c b ∧ C (f
 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y

--- 原说明 ---
Let `r` be a relation on `α`, let `f : α → β` be a function, let `C : β → Prop`,
 and
let `bot : α`. This induction principle shows that `C (f bot)` holds, given that
* some `a` that is accessible by `r` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`.
-/
theorem Acc.induction_bot' {α β} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : β → Prop}
    {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) : C (f a) → C (f bot) :=
  (@Acc.recOn _ _ (fun x _ => C (f x) → C (f bot)) _ ha) fun x _ ih' hC =>
    (eq_or_ne (f x) (f bot)).elim (fun h => h ▸ hC) (fun h =>
      let ⟨y, hy₁, hy₂⟩ := ih x h hC
      ih' y hy₁ hy₂)

/-- Let `r` be a relation on `α`, let `C : α → Prop` and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` that is accessible by `r` satisfies `C a`, and
* for each `b ≠ bot` such that `C b` holds, there is `c` satisfying `r c b` and `C c`. -/
/-
**Acc.induction_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Acc.induction_bot {α} {r : α -> α -> Prop} {a bot : α} (ha : Acc r a) {C :
 α -> Prop} (ih : forall b, b != bot -> C b -> exists c, r c b ∧ C c) : C a -> C
 bot
参数：ha : Acc r a；ih : forall b, b != bot -> C b -> exists c, r c b ∧ C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.induction_bot'`：Acc.induction_bot' {α β} {r : α -> α -> Prop} {a bot
 : α} (ha : Acc r a) {C : β -> Prop} {f : α -> β} (ih : forall b, f b != f bot -
> C (f b…

--- 原说明 ---
Let `r` be a relation on `α`, let `C : α → Prop` and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` that is accessible by `r` satisfies `C a`, and
* for each `b ≠ bot` such that `C b` holds, there is `c` satisfying `r c b` and 
`C c`.
-/
theorem Acc.induction_bot {α} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : α → Prop}
    (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  ha.induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `f : α → β` be a function,
let `C : β → Prop`, and let `bot : α`.
This induction principle shows that `C (f bot)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
/-
**WellFounded.induction_bot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.induction_bot' {α β} {r : α -> α -> Prop} (hwf : WellFounded r
) {a bot : α} {C : β -> Prop} {f : α -> β} (ih : forall b, f b != f bot -> C (f 
b) -> exists c, r c b ∧ C (f c)) : C (f a) -> C (f bot)
参数：hwf : WellFounded r；ih : forall b, f b != f bot -> C (f b) -> exists c, r c b
 ∧ C (f c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.induction_bot'`：Acc.induction_bot' {α β} {r : α -> α -> Prop} {a bot
 : α} (ha : Acc r a) {C : β -> Prop} {f : α -> β} (ih : forall b, f b != f bot -
> C (f b…
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a

--- 原说明 ---
Let `r` be a well-founded relation on `α`, let `f : α → β` be a function,
let `C : β → Prop`, and let `bot : α`.
This induction principle shows that `C (f bot)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`.
-/
theorem WellFounded.induction_bot' {α β} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : β → Prop} {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) :
    C (f a) → C (f bot) :=
  (hwf.apply a).induction_bot' ih

/-- Let `r` be a well-founded relation on `α`, let `C : α → Prop`, and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` satisfies `C a`, and
* for each `b` that satisfies `C b`, there is `c` satisfying `r c b` and `C c`.

The naming is inspired by the fact that when `r` is transitive, it follows that `bot` is
the smallest element w.r.t. `r` that satisfies `C`. -/
/-
**WellFounded.induction_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.induction_bot {α} {r : α -> α -> Prop} (hwf : WellFounded r) {
a bot : α} {C : α -> Prop} (ih : forall b, b != bot -> C b -> exists c, r c b ∧ 
C c) : C a -> C bot
参数：hwf : WellFounded r；ih : forall b, b != bot -> C b -> exists c, r c b ∧ C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction_bot'`：WellFounded.induction_bot' {α β} {r : α -> α
 -> Prop} (hwf : WellFounded r) {a bot : α} {C : β -> Prop} {f : α -> β} (ih : f
orall b, f b != …

--- 原说明 ---
Let `r` be a well-founded relation on `α`, let `C : α → Prop`, and let `bot : α`
.
This induction principle shows that `C bot` holds, given that
* some `a` satisfies `C a`, and
* for each `b` that satisfies `C b`, there is `c` satisfying `r c b` and `C c`.

The naming is inspired by the fact that when `r` is transitive, it follows that 
`bot` is
the smallest element w.r.t. `r` that satisfies `C`.
-/
theorem WellFounded.induction_bot {α} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : α → Prop} (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  hwf.induction_bot' ih

end Induction

/-- A nonempty linear order with well-founded `<` has a bottom element. -/
@[to_dual (attr := instance_reducible)
/-- A nonempty linear order with well-founded `>` has a top element. -/]
/-
**WellFoundedLT.toOrderBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WellFoundedLT.toOrderBot (α) [LinearOrder α] [Nonempty α] [h : WellFounded
LT α] : OrderBot α where bot
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
-/
noncomputable def WellFoundedLT.toOrderBot (α) [LinearOrder α] [Nonempty α] [h : WellFoundedLT α] :
    OrderBot α where
  bot := h.wf.min _ Set.univ_nonempty
  bot_le a := h.wf.min_le (Set.mem_univ a)

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [h : WellFoundedLT α] : WellFoundedLT (ULift α) where
  wf := InvImage.wf ULift.down h.wf
