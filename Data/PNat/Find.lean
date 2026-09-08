/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.PNat.Basic

/-!
# Explicit least witnesses to existentials on positive natural numbers

Implemented via calling out to `Nat.find`.

-/

@[expose] public section


namespace PNat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.decidablePredExistsNat** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：decidablePredExistsNat : DecidablePred fun n' : Nat => exists (n : Nat+) (
_ : n' = n), p n
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidablePredExistsNat : DecidablePred fun n' : ℕ => ∃ (n : ℕ+) (_ : n' = n), p n :=
  fun n' =>
  decidable_of_iff' (∃ h : 0 < n', p ⟨n', h⟩) <|
    Subtype.exists.trans <| by
      simp_rw [mk_coe, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']

/-- The `PNat` version of `Nat.findX` -/
/-
**PNat.findX** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：{p : ℕ+ → Prop} → [DecidablePred p] → (∃ n, p n) → { n // p n ∧ ∀ m < n, ¬
p m }
参数：∃ n, p n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PNat` version of `Nat.findX`
-/
protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } := by
  have : ∃ (n' : ℕ) (n : ℕ+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine ⟨⟨n, ?_⟩, ?_, fun m hm pm => ?_⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using! pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩

/-- If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `PNat.find hp` is the
smallest positive natural number satisfying `p`. Note that `PNat.find` is protected,
meaning that you can't just write `find`, even if the `PNat` namespace is open.

The API for `PNat.find` is:

* `PNat.find_spec` is the proof that `PNat.find hp` satisfies `p`.
* `PNat.find_min` is the proof that if `m < PNat.find hp` then `m` does not satisfy `p`.
* `PNat.find_min'` is the proof that if `m` does satisfy `p` then `PNat.find hp ≤ m`.
-/
/-
**PNat.find** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：{p : ℕ+ → Prop} → [DecidablePred p] → (∃ n, p n) → ℕ+
参数：∃ n, p n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof 
that
there exists some positive natural number satisfying `p`, then `PNat.find hp` is
 the
smallest positive natural number satisfying `p`. Note that `PNat.find` is protec
ted,
meaning that you can't just write `find`, even if the `PNat` namespace is open.

The API for `PNat.find` is:

* `PNat.find_spec` is the proof that `PNat.find hp` satisfies `p`.
* `PNat.find_min` is the proof that if `m < PNat.find hp` then `m` does not sati
sfy `p`.
* `PNat.find_min'` is the proof that if `m` does satisfy `p` then `PNat.find hp 
≤ m`.
-/
protected def find : ℕ+ :=
  PNat.findX h
/-
**PNat.find_spec** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n), p (PNat.find h)
参数：h : ∃ n, p n；PNat.find h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
protected theorem find_spec : p (PNat.find h) :=
  (PNat.findX h).prop.left
/-
**PNat.find_min** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n) {m : ℕ+}, m < PN
at.find h → ¬p m
参数：h : ∃ n, p n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
protected theorem find_min : ∀ {m : ℕ+}, m < PNat.find h → ¬p m :=
  @(PNat.findX h).prop.right
/-
**PNat.find_min'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n) {m : ℕ+}, p m → 
PNat.find h ≤ m
参数：h : ∃ n, p n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `PNat.find_min`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n)
 {m : ℕ+}, m < PNat.find h → ¬p m
-/
protected theorem find_min' {m : ℕ+} (hm : p m) : PNat.find h ≤ m :=
  le_of_not_gt fun l => PNat.find_min h l hm

variable {n m : ℕ+}
/-
**PNat.find_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：find_eq_iff : PNat.find h = m ↔ p m ∧ forall n < m, ¬p n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.find_spec`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
), p (PNat.find h)
· 使用定理 `PNat.find_min`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n)
 {m : ℕ+}, m < PNat.find h → ¬p m
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `PNat.find_min'`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
) {m : ℕ+}, p m → PNat.find h ≤ m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
-/
theorem find_eq_iff : PNat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)

@[simp]
/-
**PNat.find_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：find_lt_iff (n : Nat+) : PNat.find h < n ↔ exists m < n, p m
参数：n : Nat+。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.find_spec`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
), p (PNat.find h)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `PNat.find_min'`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
) {m : ℕ+}, p m → PNat.find h ≤ m
-/
theorem find_lt_iff (n : ℕ+) : PNat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨_, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩

@[simp]
/-
**PNat.find_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：find_le_iff (n : Nat+) : PNat.find h <= n ↔ exists m <= n, p m
参数：n : Nat+。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
theorem find_le_iff (n : ℕ+) : PNat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [← lt_add_one_iff, find_lt_iff]

@[simp]
/-
**PNat.le_find_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：le_find_iff (n : Nat+) : n <= PNat.find h ↔ forall m < n, ¬p m
参数：n : Nat+。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_find_iff (n : ℕ+) : n ≤ PNat.find h ↔ ∀ m < n, ¬p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]

@[simp]
/-
**PNat.lt_find_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：lt_find_iff (n : Nat+) : n < PNat.find h ↔ forall m <= n, ¬p m
参数：n : Nat+。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `instAddLeftMonoPNat`：AddLeftMono ℕ+
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `instAddLeftReflectLTPNat`：AddLeftReflectLT ℕ+
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_find_iff (n : ℕ+) : n < PNat.find h ↔ ∀ m ≤ n, ¬p m := by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]

@[simp]
/-
**PNat.find_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：find_eq_one : PNat.find h = 1 ↔ p 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PNat.instIsBotOneClass`：IsBotOneClass ℕ+
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem find_eq_one : PNat.find h = 1 ↔ p 1 := by simp [find_eq_iff]
/-
**PNat.one_le_find** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：one_le_find : 1 < PNat.find h ↔ ¬p 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PNat.instIsBotOneClass`：IsBotOneClass ℕ+
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_le_find : 1 < PNat.find h ↔ ¬p 1 := by simp
/-
**PNat.find_mono** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：find_mono (h : forall n, q n -> p n) {hp : exists n, p n} {hq : exists n, 
q n} : PNat.find hp <= PNat.find hq
参数：h : forall n, q n -> p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.find_min'`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
) {m : ℕ+}, p m → PNat.find h ≤ m
· 使用定理 `PNat.find_spec`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
), p (PNat.find h)
-/
theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
    PNat.find hp ≤ PNat.find hq :=
  PNat.find_min' _ (h _ (PNat.find_spec hq))
/-
**PNat.find_le** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：find_le {h : exists n, p n} (hn : p n) : PNat.find h <= n
参数：hn : p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.find_le_iff`：find_le_iff (n : Nat+) : PNat.find h <= n ↔ exists m <
= n, p m
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem find_le {h : ∃ n, p n} (hn : p n) : PNat.find h ≤ n :=
  (PNat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩
/-
**PNat.find_comp_succ** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：find_comp_succ (h : exists n, p n) (h₂ : exists n, p (n + 1)) (h1 : ¬p 1) 
: PNat.find h = PNat.find h₂ + 1
参数：h : exists n, p n；h₂ : exists n, p (n + 1)；h1 : ¬p 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.find_eq_iff`：find_eq_iff : PNat.find h = m ↔ p m ∧ forall n < m, ¬p
 n
· 使用定理 `PNat.find_spec`：∀ {p : ℕ+ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
), p (PNat.find h)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `instAddLeftReflectLEPNat`：AddLeftReflectLE ℕ+
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `instAddLeftMonoPNat`：AddLeftMono ℕ+
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `instAddLeftReflectLTPNat`：AddLeftReflectLT ℕ+
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem find_comp_succ (h : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬p 1) :
    PNat.find h = PNat.find h₂ + 1 := by
  refine (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n ↦ ?_⟩
  induction n with
  | one => simp [h1]
  | succ m _ =>
    intro hm
    simp only [add_lt_add_iff_right, lt_find_iff] at hm
    exact hm _ le_rfl

end PNat

