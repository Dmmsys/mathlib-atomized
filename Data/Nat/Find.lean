/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Push
public import Batteries.Tactic.Init

/-!
# `Nat.find` and `Nat.findGreatest`
-/

@[expose] public section

variable {m n k : ℕ} {p q : ℕ → Prop}

namespace Nat

section Find

/-! ### `Nat.find` -/

set_option backward.privateInPublic true in
/-
**Nat.lbp** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `Nat.find`
-/
private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

set_option linter.defProp false in
set_option backward.privateInPublic true in
/-
**Nat.wf_lbp** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def wf_lbp : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc lbp k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Find the smallest `n` satisfying `p n`. Returns a subtype. -/
/-
**Nat.findX** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{p : ℕ → Prop} → [DecidablePred p] → (∃ n, p n) → { n // p n ∧ ∀ m < n, ¬p
 m }
参数：∃ n, p n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find the smallest `n` satisfying `p n`. Returns a subtype.
-/
protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0 fun _ h => absurd h (Nat.not_lt_zero _)

/-- If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisfy `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ m`.
-/
/-
**Nat.find** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{p : ℕ → Prop} → [DecidablePred p] → (∃ n, p n) → ℕ
参数：∃ n, p n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof th
at
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisf
y `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ 
m`.
-/
protected def find : ℕ :=
  (Nat.findX H).1
/-
**Nat.find_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n), p (Nat.find H)
参数：H : ∃ n, p n；Nat.find H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left

grind_pattern Nat.find_spec => Nat.find H
/-
**Nat.find_min** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {m : ℕ}, m < Nat.
find H → ¬p m
参数：H : ∃ n, p n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem find_min : ∀ {m : ℕ}, m < Nat.find H → ¬p m :=
  @(Nat.findX H).2.right
/-
**Nat.find_min'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {m : ℕ}, p m → Na
t.find H ≤ m
参数：H : ∃ n, p n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_not_gt`：∀ {a b : ℕ}, ¬b > a → b ≤ a
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
-/
protected theorem find_min' {m : ℕ} (h : p m) : Nat.find H ≤ m :=
  Nat.le_of_not_gt fun l => Nat.find_min H l h
/-
**Nat.find_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_eq_iff (h : exists n : Nat, p n) : Nat.find h = m ↔ p m ∧ forall n < 
m, ¬p n
参数：h : exists n : Nat, p n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
lemma find_eq_iff (h : ∃ n : ℕ, p n) : Nat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  · grind [Nat.find_min]
  · rintro ⟨hm, hlt⟩
    have := Nat.find_min' h hm
    grind
/-
**Nat.find_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n) (n : ℕ), Nat.find
 h < n ↔ ∃ m < n, p m
参数：h : ∃ n, p n；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
@[simp] lemma find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 ↦ ⟨Nat.find h, h2, Nat.find_spec h⟩,
    fun ⟨_, hmn, hm⟩ ↦ Nat.lt_of_le_of_lt (Nat.find_min' h hm) hmn⟩
/-
**Nat.find_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n) (n : ℕ), Nat.find
 h ≤ n ↔ ∃ m ≤ n, p m
参数：h : ∃ n, p n；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [← Nat.lt_succ_iff, find_lt_iff]
/-
**Nat.le_find_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n) (n : ℕ), n ≤ Nat.
find h ↔ ∀ m < n, ¬p m
参数：h : ∃ n, p n；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma le_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n ≤ Nat.find h ↔ ∀ m < n, ¬p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]
/-
**Nat.lt_find_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n) (n : ℕ), n < Nat.
find h ↔ ∀ m ≤ n, ¬p m
参数：h : ∃ n, p n；n : ℕ。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < Nat.find h ↔ ∀ m ≤ n, ¬p m := by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]
/-
**Nat.find_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n), Nat.find h = 0 ↔
 p 0
参数：h : ∃ n, p n。
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
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma find_eq_zero (h : ∃ n : ℕ, p n) : Nat.find h = 0 ↔ p 0 := by simp [find_eq_iff]

/-- If a predicate `q` holds at some `x` and implies `p` up to that `x`, then
the earliest `xq` such that `q xq` is at least the smallest `xp` where `p xp`.
The stronger version of `Nat.find_mono`, since this one needs
implication only up to `Nat.find _` while the other requires `q` implying `p` everywhere. -/
/-
**Nat.find_mono_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_mono_of_le [DecidablePred q] {x : Nat} (hx : q x) (hpq : forall n <= 
x, q n -> p n) : Nat.find ⟨x, show p x from hpq _ le_rfl hx⟩ <= Nat.find ⟨x, hx⟩
参数：hx : q x；hpq : forall n <= x, q n -> p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)

--- 原说明 ---
If a predicate `q` holds at some `x` and implies `p` up to that `x`, then
the earliest `xq` such that `q xq` is at least the smallest `xp` where `p xp`.
The stronger version of `Nat.find_mono`, since this one needs
implication only up to `Nat.find _` while the other requires `q` implying `p` ev
erywhere.
-/
lemma find_mono_of_le [DecidablePred q] {x : ℕ} (hx : q x) (hpq : ∀ n ≤ x, q n → p n) :
    Nat.find ⟨x, show p x from hpq _ le_rfl hx⟩ ≤ Nat.find ⟨x, hx⟩ :=
  Nat.find_min' _ (hpq _ (Nat.find_min' _ hx) (Nat.find_spec ⟨x, hx⟩))

/-- A weak version of `Nat.find_mono_of_le`, requiring `q` implies `p` everywhere.
-/
/-
**Nat.find_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_mono [DecidablePred q] (h : forall n, q n -> p n) {hp : exists n, p n
} {hq : exists n, q n} : Nat.find hp <= Nat.find hq
参数：h : forall n, q n -> p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.find_mono_of_le`：find_mono_of_le [DecidablePred q] {x : Nat} (hx : q
 x) (hpq : forall n <= x, q n -> p n) : Nat.find ⟨x, show p x from hpq _ le_rfl 
hx⟩ <= Na…

--- 原说明 ---
A weak version of `Nat.find_mono_of_le`, requiring `q` implies `p` everywhere.
-/
lemma find_mono [DecidablePred q] (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
    Nat.find hp ≤ Nat.find hq :=
  let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ ↦ h _

/-- If a predicate `p` holds at some `x` and agrees with `q` up to that `x`, then
their `Nat.find` agree. The stronger version of `Nat.find_congr'`, since this one needs
agreement only up to `Nat.find _` while the other requires `p = q`.
Usage of this lemma will likely be via `obtain ⟨x, hx⟩ := hp; apply Nat.find_congr hx` to unify `q`,
or provide it explicitly with `rw [Nat.find_congr (q := q) hx]`.
-/
/-
**Nat.find_congr** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_congr [DecidablePred q] {x : Nat} (hx : p x) (hpq : forall n <= x, p 
n ↔ q n) : .1 hx⟩
参数：hx : p x；hpq : forall n <= x, p n ↔ q n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Nat.find_mono_of_le`：find_mono_of_le [DecidablePred q] {x : Nat} (hx : q
 x) (hpq : forall n <= x, q n -> p n) : Nat.find ⟨x, show p x from hpq _ le_rfl 
hx⟩ <= Na…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If a predicate `p` holds at some `x` and agrees with `q` up to that `x`, then
their `Nat.find` agree. The stronger version of `Nat.find_congr'`, since this on
e needs
agreement only up to `Nat.find _` while the other requires `p = q`.
Usage of this lemma will likely be via `obtain ⟨x, hx⟩ := hp; apply Nat.find_con
gr hx` to unify `q`,
or provide it explicitly with `rw [Nat.find_congr (q := q) hx]`.
-/
lemma find_congr [DecidablePred q] {x : ℕ} (hx : p x) (hpq : ∀ n ≤ x, p n ↔ q n) :
    Nat.find ⟨x, hx⟩ = Nat.find ⟨x, show q x from hpq _ le_rfl |>.1 hx⟩ :=
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hx) fun _ h ↦ (hpq _ h).mpr)
    (find_mono_of_le hx fun _ h ↦ (hpq _ h).mp)

/-- A weak version of `Nat.find_congr`, requiring `p = q` everywhere. -/
/-
**Nat.find_congr'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_congr' [DecidablePred q] {hp : exists n, p n} {hq : exists n, q n} (h
pq : forall {n}, p n ↔ q n) : Nat.find hp = Nat.find hq
参数：hpq : forall {n}, p n ↔ q n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.find_congr`：find_congr [DecidablePred q] {x : Nat} (hx : p x) (hpq :
 forall n <= x, p n ↔ q n) : .1 hx⟩

--- 原说明 ---
A weak version of `Nat.find_congr`, requiring `p = q` everywhere.
-/
lemma find_congr' [DecidablePred q] {hp : ∃ n, p n} {hq : ∃ n, q n} (hpq : ∀ {n}, p n ↔ q n) :
    Nat.find hp = Nat.find hq :=
  let ⟨_, hp⟩ := hp; find_congr hp fun _ _ ↦ hpq
/-
**Nat.find_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n
参数：hn : p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.find_le_iff`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
) (n : ℕ), Nat.find h ≤ n ↔ ∃ m ≤ n, p m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma find_le {h : ∃ n, p n} (hn : p n) : Nat.find h ≤ n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩
/-
**Nat.find_comp_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_comp_succ (h₁ : exists n, p n) (h₂ : exists n, p (n + 1)) (h0 : ¬p 0)
 : Nat.find h₁ = Nat.find h₂ + 1
参数：h₁ : exists n, p n；h₂ : exists n, p (n + 1)；h0 : ¬p 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.find_eq_iff`：find_eq_iff (h : exists n : Nat, p n) : Nat.find h = m 
↔ p m ∧ forall n < m, ¬p n
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
-/
lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬p 0) :
    Nat.find h₁ = Nat.find h₂ + 1 := by
  refine (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn ↦ ?_⟩
  cases n
  exacts [h0, @Nat.find_min (fun n ↦ p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]
/-
**Nat.find_pos** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_pos (h : exists n : Nat, p n) : 0 < Nat.find h ↔ ¬p 0
参数：h : exists n : Nat, p n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.find_eq_zero`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p 
n), Nat.find h = 0 ↔ p 0
-/
lemma find_pos (h : ∃ n : ℕ, p n) : 0 < Nat.find h ↔ ¬p 0 :=
  Nat.pos_iff_ne_zero.trans (Nat.find_eq_zero _).not
/-
**Nat.find_add** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：find_add {hₘ : exists m, p (m + n)} {hₙ : exists n, p n} (hn : n <= Nat.fi
nd hₙ) : Nat.find hₘ + n = Nat.find hₙ
参数：m + n；hn : n <= Nat.find hₙ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.le_find_iff`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
) (n : ℕ), n ≤ Nat.find h ↔ ∀ m < n, ¬p m
· 使用定理 `Nat.not_le`：∀ {a b : ℕ}, ¬a ≤ b ↔ b < a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Nat.find_le`：find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n
· 使用定理 `Nat.add_le_of_le_sub`：∀ {a b c : ℕ}, b ≤ c → a ≤ c - b → a + b ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
-/
lemma find_add {hₘ : ∃ m, p (m + n)} {hₙ : ∃ n, p n} (hn : n ≤ Nat.find hₙ) :
    Nat.find hₘ + n = Nat.find hₙ := by
  refine le_antisymm ((le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_) ?_
  · have hnm : n ≤ m := le_trans hn (find_le hpm)
    refine Nat.add_le_of_le_sub hnm (find_le ?_)
    rwa [Nat.sub_add_cancel hnm]
  · rw [← Nat.sub_le_iff_le_add]
    refine (le_find_iff _ _).2 fun m hm hpm => Nat.not_le.2 hm ?_
    rw [Nat.sub_le_iff_le_add]
    exact find_le hpm

end Find

/-! ### `Nat.findGreatest` -/

section FindGreatest

/-- `Nat.findGreatest P n` is the largest `i ≤ n` such that `P i` holds, or `0` if no such `i`
exists -/
/-
**Nat.findGreatest** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：(P : ℕ → Prop) → [DecidablePred P] → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.findGreatest P n` is the largest `i ≤ n` such that `P i` holds, or `0` if n
o such `i`
exists
-/
def findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else Nat.findGreatest P n

variable {P Q : ℕ → Prop} [DecidablePred P] {n : ℕ}
/-
**Nat.findGreatest_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {P : ℕ → Prop} [inst : DecidablePred P], Nat.findGreatest P 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma findGreatest_zero : Nat.findGreatest P 0 = 0 := (rfl)
/-
**Nat.findGreatest_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_succ (n : Nat) : Nat.findGreatest P (n + 1) = if P (n + 1) th
en n + 1 else Nat.findGreatest P n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma findGreatest_succ (n : ℕ) :
    Nat.findGreatest P (n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n := (rfl)
/-
**Nat.findGreatest_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, P n → Nat.findGreatest 
P n = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma findGreatest_eq : ∀ {n}, P n → Nat.findGreatest P n = n
  | 0, _ => rfl
  | n + 1, h => by simp [Nat.findGreatest, h]

@[simp]
/-
**Nat.findGreatest_of_not** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_of_not (h : ¬ P (n + 1)) : findGreatest P (n + 1) = findGreat
est P n
参数：h : ¬ P (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma findGreatest_of_not (h : ¬ P (n + 1)) : findGreatest P (n + 1) = findGreatest P n := by
  simp [Nat.findGreatest, h]
/-
**Nat.findGreatest_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_eq_iff : Nat.findGreatest P k = m ↔ m <= k ∧ (m != 0 -> P m) 
∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.findGreatest_zero`：∀ {P : ℕ → Prop} [inst : DecidablePred P], Nat.fi
ndGreatest P 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.findGreatest_eq`：∀ {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, 
P n → Nat.findGreatest P n = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Decidable.lt_or_eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b 
: α} [DecidableLE α], a ≤ b → a < b ∨ a = b
· 使用引理 `Nat.findGreatest_of_not`：findGreatest_of_not (h : ¬ P (n + 1)) : findGre
atest P (n + 1) = findGreatest P n
-/
lemma findGreatest_eq_iff :
    Nat.findGreatest P k = m ↔ m ≤ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n⦄, m < n → n ≤ k → ¬P n := by
  induction k generalizing m with
  | zero =>
    rw [eq_comm, Iff.comm]
    simp only [Nat.le_zero, ne_eq, findGreatest_zero, and_iff_left_iff_imp]
    rintro rfl
    exact ⟨fun h ↦ (h rfl).elim, fun n hlt heq ↦ by lia⟩
  | succ k ihk =>
    by_cases hk : P (k + 1)
    · rw [findGreatest_eq hk]
      constructor
      · rintro rfl
        exact ⟨le_refl _, fun _ ↦ hk, fun n hlt hle ↦ by lia⟩
      · rintro ⟨hle, h0, hm⟩
        rcases Decidable.lt_or_eq_of_le hle with hlt | rfl
        exacts [(hm hlt (le_refl _) hk).elim, rfl]
    · rw [findGreatest_of_not hk, ihk]
      grind
/-
**Nat.findGreatest_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_eq_zero_iff : Nat.findGreatest P k = 0 ↔ forall ⦃n⦄, 0 < n ->
 n <= k -> ¬P n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma findGreatest_eq_zero_iff : Nat.findGreatest P k = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ k → ¬P n := by
  simp [findGreatest_eq_iff]
/-
**Nat.findGreatest_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {k : ℕ} {P : ℕ → Prop} [inst : DecidablePred P], 0 < Nat.findGreatest P 
k ↔ ∃ n, 0 < n ∧ n ≤ k ∧ P n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Nat.findGreatest_eq_zero_iff`：findGreatest_eq_zero_iff : Nat.findGreates
t P k = 0 ↔ forall ⦃n⦄, 0 < n -> n <= k -> ¬P n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma findGreatest_pos : 0 < Nat.findGreatest P k ↔ ∃ n, 0 < n ∧ n ≤ k ∧ P n := by
  rw [Nat.pos_iff_ne_zero, Ne, findGreatest_eq_zero_iff]; push Not; rfl
/-
**Nat.findGreatest_spec** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_spec (hmb : m <= n) (hm : P m) : P (Nat.findGreatest P n)
参数：hmb : m <= n；hm : P m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.findGreatest_eq_zero_iff`：findGreatest_eq_zero_iff : Nat.findGreates
t P k = 0 ↔ forall ⦃n⦄, 0 < n -> n <= k -> ¬P n
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Nat.findGreatest_eq_iff`：findGreatest_eq_iff : Nat.findGreatest P k = m 
↔ m <= k ∧ (m != 0 -> P m) ∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n
-/
lemma findGreatest_spec (hmb : m ≤ n) (hm : P m) : P (Nat.findGreatest P n) := by
  by_cases h : Nat.findGreatest P n = 0
  · cases m
    · rwa [h]
    exact ((findGreatest_eq_zero_iff.1 h) (zero_lt_succ _) hmb hm).elim
  · exact (findGreatest_eq_iff.1 rfl).2.1 h
/-
**Nat.findGreatest_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_le (n : Nat) : Nat.findGreatest P n <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.findGreatest_eq_iff`：findGreatest_eq_iff : Nat.findGreatest P k = m 
↔ m <= k ∧ (m != 0 -> P m) ∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n
-/
lemma findGreatest_le (n : ℕ) : Nat.findGreatest P n ≤ n :=
  (findGreatest_eq_iff.1 rfl).1
/-
**Nat.le_findGreatest** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_findGreatest (hmb : m <= n) (hm : P m) : m <= Nat.findGreatest P n
参数：hmb : m <= n；hm : P m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.findGreatest_eq_iff`：findGreatest_eq_iff : Nat.findGreatest P k = m 
↔ m <= k ∧ (m != 0 -> P m) ∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n
-/
lemma le_findGreatest (hmb : m ≤ n) (hm : P m) : m ≤ Nat.findGreatest P n :=
  le_of_not_gt fun hlt => (findGreatest_eq_iff.1 rfl).2.2 hlt hmb hm
/-
**Nat.findGreatest_mono_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_mono_right (P : Nat -> Prop) [DecidablePred P] {m n} (hmn : m
 <= n) : Nat.findGreatest P m <= Nat.findGreatest P n
参数：P : Nat -> Prop；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.findGreatest_succ`：findGreatest_succ (n : Nat) : Nat.findGreatest P 
(n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Nat.findGreatest_le`：findGreatest_le (n : Nat) : Nat.findGreatest P n <=
 n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma findGreatest_mono_right (P : ℕ → Prop) [DecidablePred P] {m n} (hmn : m ≤ n) :
    Nat.findGreatest P m ≤ Nat.findGreatest P n := by
  induction hmn with
  | refl => simp
  | step hmk ih =>
    rw [findGreatest_succ]
    split_ifs
    · exact le_trans ih <| le_trans (findGreatest_le _) (le_succ _)
    · exact ih
/-
**Nat.findGreatest_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_mono_left [DecidablePred Q] (hPQ : forall n, P n -> Q n) (n :
 Nat) : Nat.findGreatest P n <= Nat.findGreatest Q n
参数：hPQ : forall n, P n -> Q n；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.findGreatest_eq`：∀ {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, 
P n → Nat.findGreatest P n = n
· 使用引理 `Nat.findGreatest_of_not`：findGreatest_of_not (h : ¬ P (n + 1)) : findGre
atest P (n + 1) = findGreatest P n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Nat.findGreatest_mono_right`：findGreatest_mono_right (P : Nat -> Prop) [
DecidablePred P] {m n} (hmn : m <= n) : Nat.findGreatest P m <= Nat.findGreatest
 P n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
lemma findGreatest_mono_left [DecidablePred Q] (hPQ : ∀ n, P n → Q n) (n : ℕ) :
    Nat.findGreatest P n ≤ Nat.findGreatest Q n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    by_cases h : P (n + 1)
    · rw [findGreatest_eq h, findGreatest_eq (hPQ _ h)]
    · rw [findGreatest_of_not h]
      exact le_trans hn (Nat.findGreatest_mono_right _ <| le_succ _)
/-
**Nat.findGreatest_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：findGreatest_mono [DecidablePred Q] (hPQ : forall n, P n -> Q n) (hmn : m 
<= n) : Nat.findGreatest P m <= Nat.findGreatest Q n
参数：hPQ : forall n, P n -> Q n；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Nat.findGreatest_mono_right`：findGreatest_mono_right (P : Nat -> Prop) [
DecidablePred P] {m n} (hmn : m <= n) : Nat.findGreatest P m <= Nat.findGreatest
 P n
· 使用引理 `Nat.findGreatest_mono_left`：findGreatest_mono_left [DecidablePred Q] (hP
Q : forall n, P n -> Q n) (n : Nat) : Nat.findGreatest P n <= Nat.findGreatest Q
 n
-/
lemma findGreatest_mono [DecidablePred Q] (hPQ : ∀ n, P n → Q n) (hmn : m ≤ n) :
    Nat.findGreatest P m ≤ Nat.findGreatest Q n :=
  le_trans (Nat.findGreatest_mono_right _ hmn) (findGreatest_mono_left hPQ _)
/-
**Nat.findGreatest_is_greatest** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：findGreatest_is_greatest (hk : Nat.findGreatest P n < k) (hkb : k <= n) : 
¬P k
参数：hk : Nat.findGreatest P n < k；hkb : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.findGreatest_eq_iff`：findGreatest_eq_iff : Nat.findGreatest P k = m 
↔ m <= k ∧ (m != 0 -> P m) ∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n
-/
theorem findGreatest_is_greatest (hk : Nat.findGreatest P n < k) (hkb : k ≤ n) : ¬P k :=
  (findGreatest_eq_iff.1 rfl).2.2 hk hkb
/-
**Nat.findGreatest_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：findGreatest_of_ne_zero (h : Nat.findGreatest P n = m) (h0 : m != 0) : P m
参数：h : Nat.findGreatest P n = m；h0 : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.findGreatest_eq_iff`：findGreatest_eq_iff : Nat.findGreatest P k = m 
↔ m <= k ∧ (m != 0 -> P m) ∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n
-/
theorem findGreatest_of_ne_zero (h : Nat.findGreatest P n = m) (h0 : m ≠ 0) : P m :=
  (findGreatest_eq_iff.1 h).2.1 h0

end FindGreatest

end Nat

