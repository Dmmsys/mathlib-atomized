/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Nat.PSub
public import Mathlib.Data.PFun

/-!
# The partial recursive functions

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `Part` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization: `μ f` returns the
least natural number `n` for which `f n = 0`, or diverges if such `n` doesn't exist.

## Main definitions

- `Nat.Partrec f`: `f` is partial recursive, for functions `f : ℕ →. ℕ`
- `Partrec f`: `f` is partial recursive, for partial functions between `Primcodable` types
- `Computable f`: `f` is partial recursive, for total functions between `Primcodable` types

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

@[expose] public section

open List (Vector)
open Encodable Denumerable Part

attribute [-simp] not_forall

namespace Nat

section Rfind

variable (p : ℕ →. Bool)

set_option backward.privateInPublic true in
/-
**Nat.lbp** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, false ∈ p k

set_option linter.defProp false in
set_option backward.privateInPublic true in
/-
**Nat.wf_lbp** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def wf_lbp (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom) : WellFounded (lbp p) :=
  ⟨by
    let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (lbp p) k by exact fun a => this _ _ (Nat.le_add_left _ _)
    intro m k kn
    induction m generalizing k with (refine ⟨_, fun y r => ?_⟩; rcases r with ⟨rfl, a⟩)
    | zero => injection mem_unique pn.1 (a _ kn)
    | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)⟩

variable (H : ∃ n, true ∈ p n ∧ ∀ k < n, (p k).Dom)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined as false.
Returns a subtype. -/
/-
**Nat.rfindX** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：rfindX : { n // true in p n ∧ forall m < n, false in p m }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined 
as false.
Returns a subtype.
-/
def rfindX : { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } :=
  suffices ∀ k, (∀ n < k, false ∈ p n) → { n // true ∈ p n ∧ ∀ m < n, false ∈ p m } from
    this 0 fun _ => (Nat.not_lt_zero _).elim
  @WellFounded.fix _ _ (lbp p) (wf_lbp p H)
    (by
      intro m IH al
      have pm : (p m).Dom := by
        rcases H with ⟨n, h₁, h₂⟩
        rcases lt_trichotomy m n with (h₃ | h₃ | h₃)
        · exact h₂ _ h₃
        · rw [h₃]
          exact h₁.fst
        · injection mem_unique h₁ (al _ h₃)
      cases e : (p m).get pm
      · suffices ∀ᵉ k ≤ m, false ∈ p k from IH _ ⟨rfl, this⟩ fun n h => this _ (le_of_lt_succ h)
        intro n h
        rcases h.lt_or_eq_dec with h | h
        · exact al _ h
        · rw [h]
          exact ⟨_, e⟩
      · exact ⟨m, ⟨_, e⟩, al⟩)

end Rfind

/-- Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined as false.
Returns a `Part`. -/
/-
**Nat.rfind** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：rfind (p : Nat ->. Bool) : Part Nat
参数：p : Nat ->. Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find the smallest `n` satisfying `p n`, where all `p k` for `k < n` are defined 
as false.
Returns a `Part`.
-/
def rfind (p : ℕ →. Bool) : Part ℕ :=
  ⟨_, fun h => (rfindX p h).1⟩
/-
**Nat.rfind_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfind_spec {p : Nat ->. Bool} {n : Nat} (h : n in rfind p) : true in p n
参数：h : n in rfind p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
-/
theorem rfind_spec {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : true ∈ p n :=
  h.snd ▸ (rfindX p h.fst).2.1
/-
**Nat.rfind_min** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfind_min {p : Nat ->. Bool} {n : Nat} (h : n in rfind p) : forall {m : Na
t}, m < n -> false in p m
参数：h : n in rfind p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
-/
theorem rfind_min {p : ℕ →. Bool} {n : ℕ} (h : n ∈ rfind p) : ∀ {m : ℕ}, m < n → false ∈ p m :=
  @(h.snd ▸ @((rfindX p h.fst).2.2))

@[simp]
/-
**Nat.rfind_dom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfind_dom {p : Nat ->. Bool} : (rfind p).Dom ↔ exists n, true in p n ∧ for
all {m : Nat}, m < n -> (p m).Dom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rfind_dom {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).Dom :=
  Iff.rfl
/-
**Nat.rfind_dom'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfind_dom' {p : Nat ->. Bool} : (rfind p).Dom ↔ exists n, true in p n ∧ fo
rall {m : Nat}, m <= n -> (p m).Dom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Decidable.eq_or_lt_of_le`：∀ {α : Type u_2} [inst : PartialOrder α] {a b 
: α} [DecidableLE α], a ≤ b → a = b ∨ a < b
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem rfind_dom' {p : ℕ →. Bool} :
    (rfind p).Dom ↔ ∃ n, true ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).Dom :=
  exists_congr fun _ =>
    and_congr_right fun pn =>
      ⟨fun H _ h => (Decidable.eq_or_lt_of_le h).elim (fun e => e.symm ▸ pn.fst) (H _), fun H _ h =>
        H (le_of_lt h)⟩

@[simp]
/-
**Nat.mem_rfind** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_rfind {p : Nat ->. Bool} {n : Nat} : n in rfind p ↔ true in p n ∧ fora
ll {m : Nat}, m < n -> false in p m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rfind_spec`：rfind_spec {p : Nat ->. Bool} {n : Nat} (h : n in rfind 
p) : true in p n
· 使用定理 `Nat.rfind_min`：rfind_min {p : Nat ->. Bool} {n : Nat} (h : n in rfind p)
 : forall {m : Nat}, m < n -> false in p m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.dom_iff_mem`：∀ {α : Type u_1} {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.rfind_dom`：rfind_dom {p : Nat ->. Bool} : (rfind p).Dom ↔ exists n, 
true in p n ∧ forall {m : Nat}, m < n -> (p m).Dom
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_rfind {p : ℕ →. Bool} {n : ℕ} :
    n ∈ rfind p ↔ true ∈ p n ∧ ∀ {m : ℕ}, m < n → false ∈ p m :=
  ⟨fun h => ⟨rfind_spec h, @rfind_min _ _ h⟩, fun ⟨h₁, h₂⟩ => by
    let ⟨m, hm⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨_, h₁, fun {m} mn => (h₂ mn).fst⟩
    rcases lt_trichotomy m n with (h | h | h)
    · injection mem_unique (h₂ h) (rfind_spec hm)
    · rwa [← h]
    · injection mem_unique h₁ (rfind_min hm h)⟩
/-
**Nat.rfind_min'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfind_min' {p : Nat -> Bool} {m : Nat} (pm : p m) : exists n in rfind p, n
 <= m
参数：pm : p m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.dom_iff_mem`：∀ {α : Type u_1} {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.rfind_dom`：rfind_dom {p : Nat ->. Bool} : (rfind p).Dom ↔ exists n, 
true in p n ∧ forall {m : Nat}, m < n -> (p m).Dom
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `Nat.rfind_min`：rfind_min {p : Nat ->. Bool} {n : Nat} (h : n in rfind p)
 : forall {m : Nat}, m < n -> false in p m
-/
theorem rfind_min' {p : ℕ → Bool} {m : ℕ} (pm : p m) : ∃ n ∈ rfind p, n ≤ m :=
  have : true ∈ (p : ℕ →. Bool) m := ⟨trivial, pm⟩
  let ⟨n, hn⟩ := dom_iff_mem.1 <| (@rfind_dom p).2 ⟨m, this, fun {_} _ => ⟨⟩⟩
  ⟨n, hn, not_lt.1 fun h => by injection mem_unique this (rfind_min hn h)⟩
/-
**Nat.rfind_zero_none** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfind_zero_none (p : Nat ->. Bool) (p0 : p 0 = Part.none) : rfind p = Part
.none
参数：p : Nat ->. Bool；p0 : p 0 = Part.none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_none_iff`：eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.rfind_dom'`：rfind_dom' {p : Nat ->. Bool} : (rfind p).Dom ↔ exists n
, true in p n ∧ forall {m : Nat}, m <= n -> (p m).Dom
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem rfind_zero_none (p : ℕ →. Bool) (p0 : p 0 = Part.none) : rfind p = Part.none :=
  eq_none_iff.2 fun _ h =>
    let ⟨_, _, h₂⟩ := rfind_dom'.1 h.fst
    (p0 ▸ h₂ (zero_le _) : (@Part.none Bool).Dom)

/-- Find the smallest `n` satisfying `f n`, where all `f k` for `k < n` are defined as false.
Returns a `Part`. -/
/-
**Nat.rfindOpt** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：rfindOpt {α} (f : Nat -> Option α) : Part α
参数：f : Nat -> Option α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find the smallest `n` satisfying `f n`, where all `f k` for `k < n` are defined 
as false.
Returns a `Part`.
-/
def rfindOpt {α} (f : ℕ → Option α) : Part α :=
  (rfind fun n => (f n).isSome).bind fun n => f n
/-
**Nat.rfindOpt_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfindOpt_spec {α} {f : Nat -> Option α} {a} (h : a in rfindOpt f) : exists
 n, a in f n
参数：h : a in rfindOpt f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.mem_bind_iff`：mem_bind_iff {f : Part α} {g : α -> Part β} {b} : b i
n f.bind g ↔ exists a in f, b in g a
· 使用定理 `Part.mem_coe`：mem_coe {a : α} {o : Option α} : a in (o : Part α) ↔ a in 
o
-/
theorem rfindOpt_spec {α} {f : ℕ → Option α} {a} (h : a ∈ rfindOpt f) : ∃ n, a ∈ f n :=
  let ⟨n, _, h₂⟩ := mem_bind_iff.1 h
  ⟨n, mem_coe.1 h₂⟩
/-
**Nat.rfindOpt_dom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfindOpt_dom {α} {f : Nat -> Option α} : (rfindOpt f).Dom ↔ exists n a, a 
in f n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Nat.rfindOpt_spec`：rfindOpt_spec {α} {f : Nat -> Option α} {a} (h : a in
 rfindOpt f) : exists n, a in f n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.isSome_iff_exists`：∀ {α : Type u_1} {x : Option α}, x.isSome = tr
ue ↔ ∃ a, x = some a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.true_eq`：∀ (b : Bool), (true = b) = (b = true)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `trivial`：True
· 使用定理 `Nat.rfind_spec`：rfind_spec {p : Nat ->. Bool} {n : Nat} (h : n in rfind 
p) : true in p n
· 使用定理 `Part.get_mem`：get_mem {o : Part α} (h) : get o h in o
-/
theorem rfindOpt_dom {α} {f : ℕ → Option α} : (rfindOpt f).Dom ↔ ∃ n a, a ∈ f n :=
  ⟨fun h => (rfindOpt_spec ⟨h, rfl⟩).imp fun _ h => ⟨_, h⟩, fun h => by
    have h' : ∃ n, (f n).isSome := h.imp fun n => Option.isSome_iff_exists.2
    have s := Nat.find_spec h'
    have fd : (rfind fun n => (f n).isSome).Dom :=
      ⟨Nat.find h', by simpa using s.symm, fun _ _ => trivial⟩
    refine ⟨fd, ?_⟩
    have := rfind_spec (get_mem fd)
    simpa using this⟩
/-
**Nat.rfindOpt_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：rfindOpt_mono {α} {f : Nat -> Option α} (H : forall {a m n}, m <= n -> a i
n f m -> a in f n) {a} : a in rfindOpt f ↔ exists n, a in f n
参数：H : forall {a m n}, m <= n -> a in f m -> a in f n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.rfindOpt_spec`：rfindOpt_spec {α} {f : Nat -> Option α} {a} (h : a in
 rfindOpt f) : exists n, a in f n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.rfindOpt_dom`：rfindOpt_dom {α} {f : Nat -> Option α} : (rfindOpt f).
Dom ↔ exists n a, a in f n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem rfindOpt_mono {α} {f : ℕ → Option α} (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n) {a} :
    a ∈ rfindOpt f ↔ ∃ n, a ∈ f n :=
  ⟨rfindOpt_spec, fun ⟨n, h⟩ => by
    have h' := rfindOpt_dom.2 ⟨_, _, h⟩
    obtain ⟨k, hk⟩ := rfindOpt_spec ⟨h', rfl⟩
    have := (H (le_max_left _ _) h).symm.trans (H (le_max_right _ _) hk)
    simp at this; simp [this, get_mem]⟩

/-- `Nat.Partrec f` means that the partial function `f : ℕ →. ℕ` is partially recursive. -/
/-
**Nat.Partrec** 是 Mathlib 中的一个归纳类型，位于命名空间 `Nat`。
形式化陈述：(ℕ →. ℕ) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.Partrec f` means that the partial function `f : ℕ →. ℕ` is partially recurs
ive.
-/
protected inductive Partrec : (ℕ →. ℕ) → Prop
  | zero : Nat.Partrec (pure 0)
  | succ : Nat.Partrec succ
  | left : Nat.Partrec ↑fun n : ℕ => n.unpair.1
  | right : Nat.Partrec ↑fun n : ℕ => n.unpair.2
  | pair {f g} : Nat.Partrec f → Nat.Partrec g → Nat.Partrec fun n => pair <$> f n <*> g n
  | comp {f g} : Nat.Partrec f → Nat.Partrec g → Nat.Partrec fun n => g n >>= f
  | prec {f g} : Nat.Partrec f → Nat.Partrec g → Nat.Partrec (unpaired fun a n =>
      n.rec (f a) fun y IH => do let i ← IH; g (pair a (pair y i)))
  | rfind {f} : Nat.Partrec f →
    Nat.Partrec fun a => rfind fun n => (fun m => m = 0) <$> f (pair a n)

namespace Partrec

/-
**Nat.Partrec.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : forall n, f n = g n) :
 Nat.Partrec g
参数：hf : Nat.Partrec f；H : forall n, f n = g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {f g : ℕ →. ℕ} (hf : Nat.Partrec f) (H : ∀ n, f n = g n) : Nat.Partrec g :=
  (funext H : f = g) ▸ hf
/-
**Nat.Partrec.of_eq_tot** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：of_eq_tot {f : Nat ->. Nat} {g : Nat -> Nat} (hf : Nat.Partrec f) (H : for
all n, g n in f n) : Nat.Partrec g
参数：hf : Nat.Partrec f；H : forall n, g n in f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
-/
theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : Nat.Partrec f) (H : ∀ n, g n ∈ f n) :
    Nat.Partrec g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.Partrec.of_primrec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f) : Nat.Partrec f
参数：hf : Nat.Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq_tot`：of_eq_tot {f : Nat ->. Nat} {g : Nat -> Nat} (hf 
: Nat.Partrec f) (H : forall n, g n in f n) : Nat.Partrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Partrec f := by
  induction hf with
  | zero => exact zero
  | succ => exact succ
  | left => exact left
  | right => exact right
  | pair _ _ pf pg =>
    refine (pf.pair pg).of_eq_tot fun n => ?_
    simp [Seq.seq]
  | comp _ _ pf pg =>
    refine (pf.comp pg).of_eq_tot fun n => (by simp)
  | prec _ _ pf pg =>
    refine (pf.prec pg).of_eq_tot fun n => ?_
    simp only [unpaired, PFun.coe_val, bind_eq_bind]
    induction n.unpair.2 with
    | zero => simp
    | succ m IH =>
      simp only [mem_bind_iff, mem_some_iff]
      exact ⟨_, IH, rfl⟩
/-
**Nat.Partrec.some** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：Nat.Partrec Part.some
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_primrec`：of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f)
 : Nat.Partrec f
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
-/
protected theorem some : Nat.Partrec some :=
  of_primrec Primrec.id

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.Partrec.none** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：none : Nat.Partrec fun _ => none
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.of_primrec`：of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f)
 : Nat.Partrec f
· 使用定理 `Nat.Primrec.const`：const : forall n : Nat, Nat.Primrec fun _ => n | 0 =>
 zero | n + 1 => Primrec.succ.comp (const n)  protected theorem id : Nat.Primrec
 id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_none_iff`：eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem none : Nat.Partrec fun _ => none :=
  (of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h
/-
**Nat.Partrec.prec'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：prec' {f g h} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hh : Nat.Partrec 
h) : Nat.Partrec fun a => (f a).bind fun n => n.rec (g a) fun y IH => do {let i 
← IH; h (Nat.pair a (Nat.pair y i))}
参数：hf : Nat.Partrec f；hg : Nat.Partrec g；hh : Nat.Partrec h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.some`：Nat.Partrec Part.some
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Part.bind_map`：bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) : (map f 
x).bind g = x.bind fun y => g (f y)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prec' {f g h} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hh : Nat.Partrec h) :
    Nat.Partrec fun a => (f a).bind fun n => n.rec (g a)
      fun y IH => do {let i ← IH; h (Nat.pair a (Nat.pair y i))} :=
  ((prec hg hh).comp (pair Partrec.some hf)).of_eq fun a =>
    ext fun s => by simp [Seq.seq]

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.Partrec.ppred** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partrec`。
形式化陈述：ppred : Nat.Partrec fun n => ppred n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.of_primrec`：of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f)
 : Nat.Partrec f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec₂.unpaired'`：unpaired' {f : Nat -> Nat -> Nat} : Nat.Primrec (Nat
.unpaired f) ↔ Primrec₂ f
· 使用定理 `Part.eq_none_iff`：eq_none_iff {o : Part α} : o = none ↔ forall a, a ∉ o
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 39 条，此处仅展示前 30 条）
-/
theorem ppred : Nat.Partrec fun n => ppred n :=
  have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
      (@PrimrecRel.comp _ _ _ _ _ _ _ _ _
        Primrec.eq Primrec.fst (_root_.Primrec.succ.comp Primrec.snd))
      (_root_.Primrec.const 0) (_root_.Primrec.const 1)).to₂
  (of_primrec (Primrec₂.unpaired'.2 this)).rfind.of_eq fun n => by
    cases n
    · exact eq_none_iff.2 (by simp)
    · exact eq_some_iff.2 (by simp; lia)

end Partrec

end Nat

/-- Partially recursive partial functions `α → σ` between `Primcodable` types -/
/-
**Partrec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α ->. σ)
参数：f : α ->. σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partially recursive partial functions `α → σ` between `Primcodable` types
-/
def Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) :=
  Nat.Partrec fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

/-- Partially recursive partial functions `α → β → σ` between `Primcodable` types -/
/-
**Partrec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Partrec {α σ} [Primcodable α] [Primcodable σ] (f : α ->. σ)
参数：f : α ->. σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partially recursive partial functions `α → β → σ` between `Primcodable` types
-/
def Partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β →. σ) :=
  Partrec fun p : α × β => f p.1 p.2

/-- Computable functions `α → σ` between `Primcodable` types:
  a function is computable if and only if it is partially recursive (as a partial function) -/
@[wikidata Q1148456]
/-
**Computable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Computable {α σ} [Primcodable α] [Primcodable σ] (f : α -> σ)
参数：f : α -> σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computable functions `α → σ` between `Primcodable` types:
  a function is computable if and only if it is partially recursive (as a partia
l function)
-/
def Computable {α σ} [Primcodable α] [Primcodable σ] (f : α → σ) :=
  Partrec (f : α →. σ)

/-- Computable functions `α → β → σ` between `Primcodable` types -/
/-
**Computable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Computable {α σ} [Primcodable α] [Primcodable σ] (f : α -> σ)
参数：f : α -> σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computable functions `α → β → σ` between `Primcodable` types
-/
def Computable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Computable fun p : α × β => f p.1 p.2
/-
**Primrec.to_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α -> σ} (hf : P
rimrec f) : Computable f
参数：hf : Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.ppred`：ppred : Nat.Partrec fun n => ppred n
· 使用定理 `Nat.Partrec.of_primrec`：of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f)
 : Nat.Partrec f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Part.bind_none`：bind_none (f : α -> Part β) : none.bind f = none
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {f : α → σ} (hf : Primrec f) :
    Computable f :=
  (Nat.Partrec.ppred.comp (Nat.Partrec.of_primrec hf)).of_eq fun n => by
    simp; cases decode (α := α) n <;> simp

nonrec theorem Primrec₂.to_comp {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Primrec₂ f) : Computable₂ f :=
  hf.to_comp
/-
**Computable.partrec** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le σ] {f : α → σ}, Computable f → Partrec ↑f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Computable.partrec {α σ} [Primcodable α] [Primcodable σ] {f : α → σ}
    (hf : Computable f) : Partrec (f : α →. σ) :=
  hf
/-
**Computable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Computable {α σ} [Primcodable α] [Primcodable σ] (f : α -> σ)
参数：f : α -> σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Computable₂.partrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Computable₂ f) : Partrec₂ fun a => (f a : β →. σ) :=
  hf

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/-
**Computable.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n, f n = g n) : Compu
table g
参数：hf : Computable f；H : forall n, f n = g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {f g : α → σ} (hf : Computable f) (H : ∀ n, f n = g n) : Computable g :=
  (funext H : f = g) ▸ hf
/-
**Computable.const** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：const (s : σ) : Computable fun _ : α => s
参数：s : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem const (s : σ) : Computable fun _ : α => s :=
  (Primrec.const _).to_comp
/-
**Computable.ofOption** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：ofOption {f : α -> Option β} (hf : Computable f) : Partrec fun a => (f a :
 Part β)
参数：hf : Computable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.ppred`：ppred : Nat.Partrec fun n => ppred n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_none`：bind_none (f : α -> Part β) : none.bind f = none
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Part.map_none`：map_none (f : α -> β) : map f none = none
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ofOption {f : α → Option β} (hf : Computable f) : Partrec fun a => (f a : Part β) :=
  (Nat.Partrec.ppred.comp hf).of_eq fun n => by
    rcases decode (α := α) n with - | a <;> simp
    cases f a <;> simp
/-
**Computable.to** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to₂ {f : α × β → σ} (hf : Computable f) : Computable₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl
/-
**Computable.id** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Computable id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
protected theorem id : Computable (@id α) :=
  Primrec.id.to_comp
/-
**Computable.fst** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：fst : Computable (@Prod.fst α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
-/
theorem fst : Computable (@Prod.fst α β) :=
  Primrec.fst.to_comp
/-
**Computable.snd** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：snd : Computable (@Prod.snd α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
-/
theorem snd : Computable (@Prod.snd α β) :=
  Primrec.snd.to_comp

nonrec theorem pair {f : α → β} {g : α → γ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode (α := α) n <;> simp [Seq.seq]
/-
**Computable.unpair** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：unpair : Computable Nat.unpair
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.unpair`：unpair : Primrec Nat.unpair
-/
theorem unpair : Computable Nat.unpair :=
  Primrec.unpair.to_comp
/-
**Computable.succ** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：succ : Computable Nat.succ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
-/
theorem succ : Computable Nat.succ :=
  Primrec.succ.to_comp
/-
**Computable.pred** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：pred : Computable Nat.pred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.pred`：pred : Primrec Nat.pred
-/
theorem pred : Computable Nat.pred :=
  Primrec.pred.to_comp
/-
**Computable.nat_bodd** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：nat_bodd : Computable Nat.bodd
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.nat_bodd`：nat_bodd : Primrec Nat.bodd
-/
theorem nat_bodd : Computable Nat.bodd :=
  Primrec.nat_bodd.to_comp
/-
**Computable.nat_div2** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：nat_div2 : Computable Nat.div2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.nat_div2`：nat_div2 : Primrec Nat.div2
-/
theorem nat_div2 : Computable Nat.div2 :=
  Primrec.nat_div2.to_comp
/-
**Computable.sumInl** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：sumInl : Computable (@Sum.inl α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.sumInl`：sumInl : Primrec (@Sum.inl α β)
-/
theorem sumInl : Computable (@Sum.inl α β) :=
  Primrec.sumInl.to_comp
/-
**Computable.sumInr** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：sumInr : Computable (@Sum.inr α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.sumInr`：sumInr : Primrec (@Sum.inr α β)
-/
theorem sumInr : Computable (@Sum.inr α β) :=
  Primrec.sumInr.to_comp
/-
**Computable.list_cons** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：list_cons : Computable₂ (@List.cons α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.list_cons`：list_cons : Primrec₂ (@List.cons α)
-/
theorem list_cons : Computable₂ (@List.cons α) :=
  Primrec.list_cons.to_comp
/-
**Computable.list_reverse** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：list_reverse : Computable (@List.reverse α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.list_reverse`：list_reverse : Primrec (@List.reverse α)
-/
theorem list_reverse : Computable (@List.reverse α) :=
  Primrec.list_reverse.to_comp
/-
**Computable.list_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：list_getElem? : Computable₂ ((·[·]? : List α -> Nat -> Option α))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem list_getElem? : Computable₂ ((·[·]? : List α → ℕ → Option α)) :=
  Primrec.list_getElem?.to_comp
/-
**Computable.list_append** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：list_append : Computable₂ ((· ++ ·) : List α -> List α -> List α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.list_append`：list_append : Primrec₂ ((· ++ ·) : List α -> List α
 -> List α)
-/
theorem list_append : Computable₂ ((· ++ ·) : List α → List α → List α) :=
  Primrec.list_append.to_comp
/-
**Computable.list_concat** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：list_concat : Computable₂ fun l (a : α) => l ++ [a]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.list_concat`：list_concat : Primrec₂ fun l (a : α) => l ++ [a]
-/
theorem list_concat : Computable₂ fun l (a : α) => l ++ [a] :=
  Primrec.list_concat.to_comp
/-
**Computable.list_length** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：list_length : Computable (@List.length α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.list_length`：list_length : Primrec (@List.length α)
-/
theorem list_length : Computable (@List.length α) :=
  Primrec.list_length.to_comp
/-
**Computable.vector_cons** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_cons {n} : Computable₂ (@List.Vector.cons α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.vector_cons`：vector_cons {n} : Primrec₂ (@List.Vector.cons α n)
-/
theorem vector_cons {n} : Computable₂ (@List.Vector.cons α n) :=
  Primrec.vector_cons.to_comp
/-
**Computable.vector_toList** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_toList {n} : Computable (@List.Vector.toList α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.vector_toList`：vector_toList {n} : Primrec (@List.Vector.toList 
α n)
-/
theorem vector_toList {n} : Computable (@List.Vector.toList α n) :=
  Primrec.vector_toList.to_comp
/-
**Computable.vector_length** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_length {n} : Computable (@List.Vector.length α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.vector_length`：vector_length {n} : Primrec (@List.Vector.length 
α n)
-/
theorem vector_length {n} : Computable (@List.Vector.length α n) :=
  Primrec.vector_length.to_comp
/-
**Computable.vector_head** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_head {n} : Computable (@List.Vector.head α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.vector_head`：vector_head {n} : Primrec (@List.Vector.head α n)
-/
theorem vector_head {n} : Computable (@List.Vector.head α n) :=
  Primrec.vector_head.to_comp
/-
**Computable.vector_tail** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_tail {n} : Computable (@List.Vector.tail α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.vector_tail`：vector_tail {n} : Primrec (@List.Vector.tail α n)
-/
theorem vector_tail {n} : Computable (@List.Vector.tail α n) :=
  Primrec.vector_tail.to_comp
/-
**Computable.vector_get** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_get {n} : Computable₂ (@List.Vector.get α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.vector_get`：vector_get {n} : Primrec₂ (@List.Vector.get α n)
-/
theorem vector_get {n} : Computable₂ (@List.Vector.get α n) :=
  Primrec.vector_get.to_comp
/-
**Computable.vector_ofFn'** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_ofFn' {n} : Computable (@List.Vector.ofFn α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.vector_ofFn'`：vector_ofFn' {n} : Primrec (@List.Vector.ofFn α n)
-/
theorem vector_ofFn' {n} : Computable (@List.Vector.ofFn α n) :=
  Primrec.vector_ofFn'.to_comp
/-
**Computable.fin_app** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：fin_app {n} : Computable₂ (@id (Fin n -> σ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.fin_app`：fin_app {n} : Primrec₂ (@id (Fin n -> σ))
-/
theorem fin_app {n} : Computable₂ (@id (Fin n → σ)) :=
  Primrec.fin_app.to_comp
/-
**Computable.encode** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Computable Encodable.encode
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
-/
protected theorem encode : Computable (@encode α _) :=
  Primrec.encode.to_comp
/-
**Computable.decode** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Computable Encodable.decode
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.decode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.decode
-/
protected theorem decode : Computable (decode (α := α)) :=
  Primrec.decode.to_comp
/-
**Computable.ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：∀ (α : Type u_5) [inst : Denumerable α], Computable (Denumerable.ofNat α)
参数：α : Type u_5；Denumerable.ofNat α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.ofNat`：∀ (α : Type u_4) [inst : Denumerable α], Primrec (Denumer
able.ofNat α)
-/
protected theorem ofNat (α) [Denumerable α] : Computable (ofNat α) :=
  (Primrec.ofNat _).to_comp
/-
**Computable.encode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：encode_iff {f : α -> σ} : (Computable fun a => encode (f a)) ↔ Computable 
f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem encode_iff {f : α → σ} : (Computable fun a => encode (f a)) ↔ Computable f :=
  Iff.rfl
/-
**Computable.option_some** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：option_some : Computable (@Option.some α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.option_some`：option_some : Primrec (@some α)
-/
theorem option_some : Computable (@Option.some α) :=
  Primrec.option_some.to_comp

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

/-
**Partrec.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n = g n) : Partrec
 g
参数：hf : Partrec f；H : forall n, f n = g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {f g : α →. σ} (hf : Partrec f) (H : ∀ n, f n = g n) : Partrec g :=
  (funext H : f = g) ▸ hf
/-
**Partrec.of_eq_tot** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：of_eq_tot {f : α ->. σ} {g : α -> σ} (hf : Partrec f) (H : forall n, g n i
n f n) : Computable g
参数：hf : Partrec f；H : forall n, g n in f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
-/
theorem of_eq_tot {f : α →. σ} {g : α → σ} (hf : Partrec f) (H : ∀ n, g n ∈ f n) : Computable g :=
  hf.of_eq fun a => eq_some_iff.2 (H a)
/-
**Partrec.none** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：none : Partrec fun _ : α => @Part.none σ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.none`：none : Nat.Partrec fun _ => none
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_none`：map_none (f : α -> β) : map f none = none
· 使用定理 `Part.bind_none`：bind_none (f : α -> Part β) : none.bind f = none
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
-/
theorem none : Partrec fun _ : α => @Part.none σ :=
  Nat.Partrec.none.of_eq fun n => by cases decode (α := α) n <;> simp
/-
**Partrec.some** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Partrec Part.some
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.id`：∀ {α : Type u_1} [inst : Primcodable α], Computable id
-/
protected theorem some : Partrec (@Part.some α) :=
  Computable.id
/-
**Partrec._root_.Decidable.Partrec.const'** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Decidable.Partrec.const' (s : Part σ) [Decidable s.Dom] : Partrec fun _ : α => s :=
  (Computable.ofOption (const (toOption s))).of_eq fun _ => of_toOption s
/-
**Partrec.const'** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：const' (s : Part σ) : Partrec fun _ : α => s
参数：s : Part σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.Partrec.const'`：∀ {α : Type u_1} {σ : Type u_3} [inst : Primco
dable α] [inst_1 : Primcodable σ] (s : Part σ) [Decidable s.Dom],   Partrec fun 
x => s
-/
theorem const' (s : Part σ) : Partrec fun _ : α => s :=
  haveI := Classical.dec s.Dom
  Decidable.Partrec.const' s

set_option backward.isDefEq.respectTransparency false in
/-
**Partrec.bind** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g : α → β →. σ}, P
artrec f → Partrec₂ g → Partrec fun a => (f a).bind (g a)
参数：f a；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.some`：Nat.Partrec Part.some
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_none`：bind_none (f : α -> Part β) : none.bind f = none
· 使用定理 `Part.map_none`：map_none (f : α -> β) : map f none = none
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `Part.map_bind`：map_bind {γ} (f : α -> Part β) (x : Part α) (g : β -> γ) 
: map g (x.bind f) = x.bind fun y => map g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Part.bind_map`：bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) : (map f 
x).bind g = x.bind fun y => g (f y)
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
-/
protected theorem bind {f : α →. β} {g : α → β →. σ} (hf : Partrec f) (hg : Partrec₂ g) :
    Partrec fun a => (f a).bind (g a) :=
  (hg.comp (Nat.Partrec.some.pair hf)).of_eq fun n => by
    rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]
/-
**Partrec.map** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : Computable₂ g) 
: Partrec fun a => (f a).map (g a)
参数：hf : Partrec f；hg : Computable₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_some_eq_map`：bind_some_eq_map (f : α -> β) (x : Part α) : x.bi
nd (fun y => some (f y)) = map f x
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
-/
theorem map {f : α →. β} {g : α → β → σ} (hf : Partrec f) (hg : Computable₂ g) :
    Partrec fun a => (f a).map (g a) := by
  simpa [bind_some_eq_map] using Partrec.bind (g := fun a x => some (g a x)) hf hg
/-
**Partrec.to** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to₂ {f : α × β →. σ} (hf : Partrec f) : Partrec₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl
/-
**Partrec.nat_rec** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：nat_rec {f : α -> Nat} {g : α ->. σ} {h : α -> Nat × σ ->. σ} (hf : Comput
able f) (hg : Partrec g) (hh : Partrec₂ h) : Partrec fun a => (f a).rec (g a) fu
n y IH => IH.bind fun i => h a (y, i)
参数：hf : Computable f；hg : Partrec g；hh : Partrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.prec'`：prec' {f g h} (hf : Nat.Partrec f) (hg : Nat.Partrec 
g) (hh : Nat.Partrec h) : Nat.Partrec fun a => (f a).bind fun n => n.rec (g a) f
un y IH…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `Part.bind_none`：bind_none (f : α -> Part β) : none.bind f = none
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Part.bind_map`：bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) : (map f 
x).bind g = x.bind fun y => g (f y)
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `Part.map_bind`：map_bind {γ} (f : α -> Part β) (x : Part α) (g : β -> γ) 
: map g (x.bind f) = x.bind fun y => map g (f y)
-/
theorem nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ} (hf : Computable f) (hg : Partrec g)
    (hh : Partrec₂ h) : Partrec fun a => (f a).rec (g a) fun y IH => IH.bind fun i => h a (y, i) :=
  (Nat.Partrec.prec' hf hg hh).of_eq fun n => by
    rcases e : decode (α := α) n with - | a
    · simp
    · simp only [coe_some, PFun.coe_val, bind_some]
      induction f a <;> simp_all

nonrec theorem comp {f : β →. σ} {g : α → β} (hf : Partrec f) (hg : Computable g) :
    Partrec fun a => f (g a) :=
  (hf.comp hg).of_eq fun n => by
    simp only [PFun.coe_val, map_some, bind_eq_bind]
    rcases e : decode (α := α) n with - | a <;> simp [encodek]
/-
**Partrec.nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.map_id'`：map_id' {f : α -> α} (H : forall x : α, f x = x) (o) : map
 f o = o
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nat_iff {f : ℕ →. ℕ} : Partrec f ↔ Nat.Partrec f := by simp [Partrec, map_id']
/-
**Partrec.map_encode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：map_encode_iff {f : α ->. σ} : (Partrec fun a => (f a).map encode) ↔ Partr
ec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_encode_iff {f : α →. σ} : (Partrec fun a => (f a).map encode) ↔ Partrec f :=
  Iff.rfl

end Partrec

namespace Partrec₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/-
**Partrec₂.unpaired** 是 Mathlib 中的一个定理，位于命名空间 `Partrec₂`。
形式化陈述：unpaired {f : Nat -> Nat ->. α} : Partrec (Nat.unpaired f) ↔ Partrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec₂.pair`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [i
nst_1 : Primcodable β], Primrec₂ Prod.mk
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.unpair`：unpair : Primrec Nat.unpair
-/
theorem unpaired {f : ℕ → ℕ →. α} : Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  ⟨fun h => by simpa using! Partrec.comp (g := fun p : ℕ × ℕ => (p.1, p.2)) h Primrec₂.pair.to_comp,
    fun h => h.comp Primrec.unpair.to_comp⟩
/-
**Partrec₂.unpaired'** 是 Mathlib 中的一个定理，位于命名空间 `Partrec₂`。
形式化陈述：unpaired' {f : Nat -> Nat ->. Nat} : Nat.Partrec (Nat.unpaired f) ↔ Partre
c₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Partrec.nat_iff`：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
· 使用定理 `Partrec₂.unpaired`：unpaired {f : Nat -> Nat ->. α} : Partrec (Nat.unpair
ed f) ↔ Partrec₂ f
-/
theorem unpaired' {f : ℕ → ℕ →. ℕ} : Nat.Partrec (Nat.unpaired f) ↔ Partrec₂ f :=
  Partrec.nat_iff.symm.trans unpaired

nonrec theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ} (hf : Partrec₂ f) (hg : Computable g)
    (hh : Computable h) : Partrec fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
/-
**Partrec₂.comp** 是 Mathlib 中的一个定理，位于命名空间 `Partrec₂`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_5} [inst : Prim
codable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] [inst_3 : Primcod
able σ] {f : β → γ →. σ} {g : α → β} {h : α → γ},   Partrec₂ f → Computable g → 
Computable h → Partrec fun a => f (g a) (h a)
参数：g a；h a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Computable.pair`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {f : α → β} {
g : α…
-/
theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} (hf : Partrec₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Partrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

end Partrec₂

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

nonrec theorem comp {f : β → σ} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f (g a) :=
  hf.comp hg

/-
**Computable.comp** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {g : α → β}, Computa
ble f → Computable g → Computable fun a => f (g a)
参数：g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
-/
theorem comp₂ {f : γ → σ} {g : α → β → γ} (hf : Computable f) (hg : Computable₂ g) :
    Computable₂ fun a b => f (g a b) :=
  hf.comp hg

end Computable

namespace Computable₂

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/-
**Computable₂.mk** 是 Mathlib 中的一个定理，位于命名空间 `Computable₂`。
形式化陈述：mk {f : α -> β -> σ} (hf : Computable fun p : α × β => f p.1 p.2) : Comput
able₂ f
参数：hf : Computable fun p : α × β => f p.1 p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk {f : α → β → σ} (hf : Computable fun p : α × β => f p.1 p.2) : Computable₂ f := hf

nonrec theorem comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Computable₂ f)
    (hg : Computable g) (hh : Computable h) : Computable fun a => f (g a) (h a) :=
  hf.comp (hg.pair hh)
/-
**Computable₂.comp** 是 Mathlib 中的一个定理，位于命名空间 `Computable₂`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type u_5} [inst : Prim
codable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] [inst_3 : Primcod
able σ] {f : β → γ → σ} {g : α → β} {h : α → γ},   Computable₂ f → Computable g 
→ Computable h → Computable fun a => f (g a) (h a)
参数：g a；h a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.pair`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable γ]   {f : α → β} {
g : α…
-/
theorem comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Computable₂ f)
    (hg : Computable₂ g) (hh : Computable₂ h) : Computable₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

end Computable₂

namespace Partrec

variable {α : Type*} {σ : Type*} [Primcodable α] [Primcodable σ]

open Computable

set_option backward.isDefEq.respectTransparency false in
/-
**Partrec.rfind** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：rfind {p : α -> Nat ->. Bool} (hp : Partrec₂ p) : Partrec fun a => Nat.rfi
nd (p a)
参数：hp : Partrec₂ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Partrec.map`：map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : 
Computable₂ g) : Partrec fun a => (f a).map (g a)
· 使用定理 `Primrec₂.to_comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst :
 Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β →
 σ}, P…
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.dom_bool`：dom_bool (f : Bool -> α) : Primrec f
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Part.map_id'`：map_id' {f : α -> α} (H : forall x : α, f x = x) (o) : map
 f o = o
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Part.bind_none`：bind_none (f : α -> Part β) : none.bind f = none
· 使用定理 `Part.map_none`：map_none (f : α -> β) : map f none = none
· 使用定理 `Nat.rfind_zero_none`：rfind_zero_none (p : Nat ->. Bool) (p0 : p 0 = Part
.none) : rfind p = Part.none
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Part.map_map`：map_map (g : β -> γ) (f : α -> β) (o : Part α) : map g (ma
p f o) = map (g ∘ f) o
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem rfind {p : α → ℕ →. Bool} (hp : Partrec₂ p) : Partrec fun a => Nat.rfind (p a) :=
  (Nat.Partrec.rfind <|
        hp.map ((Primrec.dom_bool fun b => cond b 0 1).comp Primrec.snd).to₂.to_comp).of_eq
    fun n => by
    rcases e : decode (α := α) n <;> simp [e, Nat.rfind_zero_none, map_map, map_id']
/-
**Partrec.rfindOpt** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：rfindOpt {f : α -> Nat -> Option σ} (hf : Computable₂ f) : Partrec fun a =
> Nat.rfindOpt (f a)
参数：hf : Computable₂ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Partrec.rfind`：rfind {p : α -> Nat ->. Bool} (hp : Partrec₂ p) : Partrec
 fun a => Nat.rfind (p a)
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Computable.partrec`：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodable 
α] [inst_1 : Primcodable σ] {f : α → σ}, Computable f → Partrec ↑f
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.option_isSome`：option_isSome : Primrec (@Option.isSome α)
· 使用定理 `Computable.ofOption`：ofOption {f : α -> Option β} (hf : Computable f) : 
Partrec fun a => (f a : Part β)
-/
theorem rfindOpt {f : α → ℕ → Option σ} (hf : Computable₂ f) :
    Partrec fun a => Nat.rfindOpt (f a) :=
  (rfind (Primrec.option_isSome.to_comp.comp hf).partrec.to₂).bind (ofOption hf)
/-
**Partrec.nat_casesOn_right** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：nat_casesOn_right {f : α -> Nat} {g : α -> σ} {h : α -> Nat ->. σ} (hf : C
omputable f) (hg : Computable g) (hh : Partrec₂ h) : Partrec fun a => (f a).case
sOn (some (g a)) (h a)
参数：hf : Computable f；hg : Computable g；hh : Partrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.nat_rec`：nat_rec {f : α -> Nat} {g : α ->. σ} {h : α -> Nat × σ 
->. σ} (hf : Computable f) (hg : Partrec g) (hh : Partrec₂ h) : Partrec fun a =>
 (f a…
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Partrec₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type 
u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] 
[in…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.pred`：pred : Computable Nat.pred
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.mem_bind_iff`：mem_bind_iff {f : Part α} {g : α -> Part β} {b} : b i
n f.bind g ↔ exists a in f, b in g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
-/
theorem nat_casesOn_right {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ} (hf : Computable f)
    (hg : Computable g) (hh : Partrec₂ h) : Partrec fun a => (f a).casesOn (some (g a)) (h a) :=
  (nat_rec hf hg (hh.comp fst (pred.comp <| hf.comp fst)).to₂).of_eq fun a => by
    simp only [PFun.coe_val, Nat.pred_eq_sub_one]
    rcases f a with - | n
    · simp
    · refine ext fun b => ⟨fun H => ?_, fun H => ?_⟩
      · rcases mem_bind_iff.1 H with ⟨c, _, h₂⟩
        exact h₂
      · have : ∀ m, (Nat.rec (motive := fun _ => Part σ)
            (Part.some (g a)) (fun y IH => IH.bind fun _ => h a n) m).Dom := by
          intro m
          induction m <;> simp [*, H.fst]
        exact ⟨⟨this n, H.fst⟩, H.snd⟩
/-
**Partrec.bind_decode** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_decode₂_iff {f : α →. σ} :
    Partrec f ↔ Nat.Partrec fun n => Part.bind (decode₂ α n) fun a => (f a).map encode :=
  ⟨fun hf =>
    nat_iff.1 <|
      (Computable.ofOption Primrec.decode₂.to_comp).bind <|
        (map hf (Computable.encode.comp snd).to₂).comp snd,
    fun h =>
    map_encode_iff.1 <| by simpa [encodek₂] using (nat_iff.2 h).comp (@Computable.encode α _)⟩
/-
**Partrec.vector_mOfFn** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le σ] {n : ℕ} {f : Fin n → α →. σ},   (∀ (i : Fin n), Partrec (f i)) → Partrec f
un a => List.Vector.mOfFn fun i => f i a
参数：∀ (i : Fin n), Partrec (f i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vector_mOfFn :
    ∀ {n} {f : Fin n → α →. σ},
      (∀ i, Partrec (f i)) → Partrec fun a : α => Vector.mOfFn fun i => f i a
  | 0, _, _ => const _
  | n + 1, f, hf => by
    simp only [Vector.mOfFn, pure_eq_some, bind_eq_bind]
    exact
      (hf 0).bind
        (Partrec.bind ((vector_mOfFn fun i => hf i.succ).comp fst)
          (Primrec.vector_cons.to_comp.comp (snd.comp fst) snd))

end Partrec

@[simp]
/-
**Vector.mOfFn_part_some** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Vector.mOfFn_part_some {α n} : forall f : Fin n -> α, (List.Vector.mOfFn f
un i => Part.some (f i)) = Part.some (List.Vector.ofFn f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.mOfFn_pure`：∀ {m : Type u_6 → Type u_7} [inst : Monad m] [La
wfulMonad m] {α : Type u_6} {n : ℕ} (f : Fin n → α),   (List.Vector.mOfFn fun i 
=> pure (f i…
· 使用定理 `Part.instLawfulMonad`：LawfulMonad Part
-/
theorem Vector.mOfFn_part_some {α n} :
    ∀ f : Fin n → α,
      (List.Vector.mOfFn fun i => Part.some (f i)) = Part.some (List.Vector.ofFn f) :=
  Vector.mOfFn_pure

namespace Computable

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

/-
**Computable.option_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：option_some_iff {f : α -> σ} : (Computable fun a => Option.some (f a)) ↔ C
omputable f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computable.encode_iff`：encode_iff {f : α -> σ} : (Computable fun a => en
code (f a)) ↔ Computable f
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.pred`：pred : Primrec Nat.pred
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computable.option_some`：option_some : Computable (@Option.some α)
-/
theorem option_some_iff {f : α → σ} : (Computable fun a => Option.some (f a)) ↔ Computable f :=
  ⟨fun h => encode_iff.1 <| Primrec.pred.to_comp.comp <| encode_iff.2 h, option_some.comp⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Computable.bind_decode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：bind_decode_iff {f : α -> β -> Option σ} : (Computable₂ fun a n => (decode
 (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Partrec.nat_iff`：nat_iff {f : Nat ->. Nat} : Partrec f ↔ Nat.Partrec f
· 使用定理 `Nat.Partrec.ppred`：ppred : Nat.Partrec fun n => ppred n
· 使用定理 `Nat.Partrec.of_primrec`：of_primrec {f : Nat -> Nat} (hf : Nat.Primrec f)
 : Nat.Partrec f
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Computable₂.partrec₂`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [in
st : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →
 β → σ}, C…
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
· 使用定理 `Part.map_bind`：map_bind {γ} (f : α -> Part β) (x : Part α) (g : β -> γ) 
: map g (x.bind f) = x.bind fun y => map g (f y)
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Part.bind_none`：bind_none (f : α -> Part β) : none.bind f = none
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Partrec.nat_casesOn_right`：nat_casesOn_right {f : α -> Nat} {g : α -> σ}
 {h : α -> Nat ->. σ} (hf : Computable f) (hg : Computable g) (hh : Partrec₂ h) 
: Partrec fun a…
· 使用定理 `Primrec.to_comp`：Primrec.to_comp {α σ} [Primcodable α] [Primcodable σ] {
f : α -> σ} (hf : Primrec f) : Computable f
· 使用定理 `Primrec.encdec`：encdec : Primrec fun n => encode (@decode α _ n)
（共 37 条，此处仅展示前 30 条）
-/
theorem bind_decode_iff {f : α → β → Option σ} :
    (Computable₂ fun a n => (decode (α := β) n).bind (f a)) ↔ Computable₂ f :=
  ⟨fun hf =>
    Nat.Partrec.of_eq
      (((Partrec.nat_iff.2
        (Nat.Partrec.ppred.comp <| Nat.Partrec.of_primrec <| Primcodable.prim (α := β))).comp
            snd).bind
        (Computable.comp hf fst).to₂.partrec₂)
      fun n => by
        simp only [decode_prod_val, decode_nat, Option.map_some, PFun.coe_val, bind_eq_bind,
          bind_some, Part.map_bind, map_some]
        cases decode (α := α) n.unpair.1 <;> simp
        cases decode (α := β) n.unpair.2 <;> simp,
    fun hf => by
    have :
      Partrec fun a : α × ℕ =>
        (encode (decode (α := β) a.2)).casesOn (some Option.none)
          fun n => Part.map (f a.1) (decode (α := β) n) :=
      Partrec.nat_casesOn_right
        (h := fun (a : α × ℕ) (n : ℕ) ↦ map (fun b ↦ f a.1 b) (Part.ofOption (decode n)))
        (Primrec.encdec.to_comp.comp snd) (const Option.none)
        ((ofOption (Computable.decode.comp snd)).map (hf.comp (fst.comp <| fst.comp fst) snd).to₂)
    refine this.of_eq fun a => ?_
    simp; cases decode (α := β) a.2 <;> simp [encodek]⟩
/-
**Computable.map_decode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：map_decode_iff {f : α -> β -> σ} : (Computable₂ fun a n => (decode (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.map_eq_bind`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {x :
 Option α}, Option.map f x = x.bind (some ∘ f)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Computable.bind_decode_iff`：bind_decode_iff {f : α -> β -> Option σ} : (
Computable₂ fun a n => (decode (α
· 使用定理 `Computable.option_some_iff`：option_some_iff {f : α -> σ} : (Computable f
un a => Option.some (f a)) ↔ Computable f
-/
theorem map_decode_iff {f : α → β → σ} :
    (Computable₂ fun a n => (decode (α := β) n).map (f a)) ↔ Computable₂ f := by
  convert! (bind_decode_iff (f := fun a => Option.some ∘ f a)).trans option_some_iff
  apply Option.map_eq_bind
/-
**Computable.nat_rec** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：nat_rec {f : α -> Nat} {g : α -> σ} {h : α -> Nat × σ -> σ} (hf : Computab
le f) (hg : Computable g) (hh : Computable₂ h) : Computable fun a => Nat.rec (mo
tive
参数：hf : Computable f；hg : Computable g；hh : Computable₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.nat_rec`：nat_rec {f : α -> Nat} {g : α ->. σ} {h : α -> Nat × σ 
->. σ} (hf : Computable f) (hg : Partrec g) (hh : Partrec₂ h) : Partrec fun a =>
 (f a…
· 使用定理 `Computable₂.partrec₂`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [in
st : Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →
 β → σ}, C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
-/
theorem nat_rec {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.rec (motive := fun _ => σ) (g a) (fun y IH => h a (y, IH)) (f a) :=
  (Partrec.nat_rec hf hg hh.partrec₂).of_eq fun a => by simp; induction f a <;> simp [*]
/-
**Computable.nat_casesOn** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：nat_casesOn {f : α -> Nat} {g : α -> σ} {h : α -> Nat -> σ} (hf : Computab
le f) (hg : Computable g) (hh : Computable₂ h) : Computable fun a => Nat.casesOn
 (motive
参数：hf : Computable f；hg : Computable g；hh : Computable₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.nat_rec`：nat_rec {f : α -> Nat} {g : α -> σ} {h : α -> Nat × 
σ -> σ} (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) : Computabl
e fun a …
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Ty
pe u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable 
γ] [in…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
-/
theorem nat_casesOn {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) :
    Computable fun a => Nat.casesOn (motive := fun _ => σ) (f a) (g a) (h a) :=
  nat_rec hf hg (hh.comp fst <| fst.comp snd).to₂
/-
**Computable.cond** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Computable c) (hf : C
omputable f) (hg : Computable g) : Computable fun a => cond (c a) (f a) (g a)
参数：hc : Computable c；hf : Computable f；hg : Computable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.nat_casesOn`：nat_casesOn {f : α -> Nat} {g : α -> σ} {h : α -
> Nat -> σ} (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) : Compu
table fun a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computable.encode_iff`：encode_iff {f : α -> σ} : (Computable fun a => en
code (f a)) ↔ Computable f
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Computable c) (hf : Computable f)
    (hg : Computable g) : Computable fun a => cond (c a) (f a) (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl
/-
**Computable.option_casesOn** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：option_casesOn {o : α -> Option β} {f : α -> σ} {g : α -> β -> σ} (ho : Co
mputable o) (hf : Computable f) (hg : Computable₂ g) : @Computable _ σ _ _ fun a
 => Option.casesOn (o a) (f a) (g a)
参数：ho : Computable o；hf : Computable f；hg : Computable₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computable.option_some_iff`：option_some_iff {f : α -> σ} : (Computable f
un a => Option.some (f a)) ↔ Computable f
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.nat_casesOn`：nat_casesOn {f : α -> Nat} {g : α -> σ} {h : α -
> Nat -> σ} (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) : Compu
table fun a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computable.encode_iff`：encode_iff {f : α -> σ} : (Computable fun a => en
code (f a)) ↔ Computable f
· 使用定理 `Computable.map_decode_iff`：map_decode_iff {f : α -> β -> σ} : (Computabl
e₂ fun a n => (decode (α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
-/
theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Computable o)
    (hf : Computable f) (hg : Computable₂ g) :
    @Computable _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  option_some_iff.1 <|
    (nat_casesOn (encode_iff.2 ho) (option_some_iff.2 hf) (map_decode_iff.2 hg)).of_eq fun a => by
      cases o a <;> simp [encodek]
/-
**Computable.option_bind** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：option_bind {f : α -> Option β} {g : α -> β -> Option σ} (hf : Computable 
f) (hg : Computable₂ g) : Computable fun a => (f a).bind (g a)
参数：hf : Computable f；hg : Computable₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> 
σ} {g : α -> β -> σ} (ho : Computable o) (hf : Computable f) (hg : Computable₂ g
) : @Computable…
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).bind (g a) :=
  (option_casesOn hf (const Option.none) hg).of_eq fun a => by cases f a <;> rfl
/-
**Computable.option_map** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：option_map {f : α -> Option β} {g : α -> β -> σ} (hf : Computable f) (hg :
 Computable₂ g) : Computable fun a => (f a).map (g a)
参数：hf : Computable f；hg : Computable₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.map_eq_bind`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {x :
 Option α}, Option.map f x = x.bind (some ∘ f)
· 使用定理 `Computable.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> O
ption σ} (hf : Computable f) (hg : Computable₂ g) : Computable fun a => (f a).bi
nd (g a)
· 使用定理 `Computable.comp₂`：comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Computable 
f) (hg : Computable₂ g) : Computable₂ fun a b => f (g a b)
· 使用定理 `Computable.option_some`：option_some : Computable (@Option.some α)
-/
theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Computable f) (hg : Computable₂ g) :
    Computable fun a => (f a).map (g a) := by
  convert! option_bind hf (option_some.comp₂ hg)
  apply Option.map_eq_bind
/-
**Computable.option_getD** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：option_getD {f : α -> Option β} {g : α -> β} (hf : Computable f) (hg : Com
putable g) : Computable fun a => (f a).getD (g a)
参数：hf : Computable f；hg : Computable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> 
σ} {g : α -> β -> σ} (ho : Computable o) (hf : Computable f) (hg : Computable₂ g
) : @Computable…
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_getD {f : α → Option β} {g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a => (f a).getD (g a) :=
  (Computable.option_casesOn hf hg (show Computable₂ fun _ b => b from Computable.snd)).of_eq
    fun a => by cases f a <;> rfl
/-
**Computable.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：subtype_mk {f : α -> β} {p : β -> Prop} [DecidablePred p] {h : forall a, p
 (f a)} (hp : PrimrecPred p) (hf : Computable f) : @Computable _ _ _ (Primcodabl
e.subtype hp) fun a => (⟨f a, h a⟩ : Subtype p)
参数：f a；hp : PrimrecPred p；hf : Computable f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_mk {f : α → β} {p : β → Prop} [DecidablePred p] {h : ∀ a, p (f a)}
    (hp : PrimrecPred p) (hf : Computable f) :
    @Computable _ _ _ (Primcodable.subtype hp) fun a => (⟨f a, h a⟩ : Subtype p) :=
  hf
/-
**Computable.sumCasesOn** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : 
Computable f) (hg : Computable₂ g) (hh : Computable₂ h) : @Computable _ σ _ _ fu
n a => Sum.casesOn (f a) (g a) (h a)
参数：hf : Computable f；hg : Computable₂ g；hh : Computable₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computable.option_some_iff`：option_some_iff {f : α -> σ} : (Computable f
un a => Option.some (f a)) ↔ Computable f
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Co
mputable c) (hf : Computable f) (hg : Computable g) : Computable fun a => cond (
c a) …
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.nat_bodd`：nat_bodd : Computable Nat.bodd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computable.encode_iff`：encode_iff {f : α -> σ} : (Computable fun a => en
code (f a)) ↔ Computable f
· 使用定理 `Computable.option_map`：option_map {f : α -> Option β} {g : α -> β -> σ} 
(hf : Computable f) (hg : Computable₂ g) : Computable fun a => (f a).map (g a)
· 使用定理 `Computable.decode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.decode
· 使用定理 `Computable.nat_div2`：nat_div2 : Computable Nat.div2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_mul`：bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n)
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.false_and`：∀ (b : Bool), (false && b) = false
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.div2_succ`：div2_succ (n : Nat) : div2 (n + 1) = cond (bodd n) (succ 
(div2 n)) (div2 n)
-/
theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Computable₂ h) :
    @Computable _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Computable.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by
        rcases f a with b | c <;> simp [Nat.div2_val]
/-
**Computable.nat_strong_rec** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：nat_strong_rec (f : α -> Nat -> σ) {g : α -> List σ -> Option σ} (hg : Com
putable₂ g) (H : forall a n, g a ((List.range n).map (f a)) = Option.some (f a n
)) : Computable₂ f
参数：f : α -> Nat -> σ；hg : Computable₂ g；H : forall a n, g a ((List.range n).map 
(f a)) = Option.some (f a n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Computable.option_some_iff`：option_some_iff {f : α -> σ} : (Computable f
un a => Option.some (f a)) ↔ Computable f
· 使用定理 `Computable.of_eq`：of_eq {f g : α -> σ} (hf : Computable f) (H : forall n
, f n = g n) : Computable g
· 使用定理 `Computable.nat_rec`：nat_rec {f : α -> Nat} {g : α -> σ} {h : α -> Nat × 
σ -> σ} (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) : Computabl
e fun a …
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> O
ption σ} (hf : Computable f) (hg : Computable₂ g) : Computable fun a => (f a).bi
nd (g a)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.option_map`：option_map {f : α -> Option β} {g : α -> β -> σ} 
(hf : Computable f) (hg : Computable₂ g) : Computable fun a => (f a).map (g a)
· 使用定理 `Computable₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Ty
pe u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable 
γ] [in…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Computable.list_concat`：list_concat : Computable₂ fun l (a : α) => l ++ 
[a]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Computable.list_getElem?`：∀ {α : Type u_1} [inst : Primcodable α], Compu
table₂ fun x1 x2 => x1[x2]?
· 使用定理 `Computable.succ`：succ : Computable Nat.succ
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 38 条，此处仅展示前 30 条）
-/
theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : Computable₂ g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = Option.some (f a n)) : Computable₂ f :=
  suffices Computable₂ fun a n => (List.range n).map (f a) from
    option_some_iff.1 <|
      (list_getElem?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a => by
        simp
  option_some_iff.1 <|
    (nat_rec snd (const (Option.some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp <| fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a => by
      induction a.2 with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]
/-
**Computable.list_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：∀ {α : Type u_1} {σ : Type u_4} [inst : Primcodable α] [inst_1 : Primcodab
le σ] {n : ℕ} {f : Fin n → α → σ},   (∀ (i : Fin n), Computable (f i)) → Computa
ble fun a => List.ofFn fun i => f i a
参数：∀ (i : Fin n), Computable (f i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem list_ofFn :
    ∀ {n} {f : Fin n → α → σ},
      (∀ i, Computable (f i)) → Computable fun a => List.ofFn fun i => f i a
  | 0, _, _ => by
    simp only [List.ofFn_zero]
    exact const []
  | n + 1, f, hf => by
    simp only [List.ofFn_succ]
    exact list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)
/-
**Computable.vector_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Computable`。
形式化陈述：vector_ofFn {n} {f : Fin n -> α -> σ} (hf : forall i, Computable (f i)) : 
Computable fun a => List.Vector.ofFn fun i => f i a
参数：hf : forall i, Computable (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.vector_mOfFn`：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodabl
e α] [inst_1 : Primcodable σ] {n : ℕ} {f : Fin n → α →. σ},   (∀ (i : Fin n), Pa
rtrec (f i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Vector.mOfFn_part_some`：Vector.mOfFn_part_some {α n} : forall f : Fin n 
-> α, (List.Vector.mOfFn fun i => Part.some (f i)) = Part.some (List.Vector.ofFn
 f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, Computable (f i)) :
    Computable fun a => List.Vector.ofFn fun i => f i a :=
  (Partrec.vector_mOfFn hf).of_eq fun a => by simp

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

open Computable

/-
**Partrec.option_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：option_some_iff {f : α ->. σ} : (Partrec fun a => (f a).map Option.some) ↔
 Partrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partrec.of_eq`：of_eq {f g : Nat ->. Nat} (hf : Nat.Partrec f) (H : f
orall n, f n = g n) : Nat.Partrec g
· 使用定理 `Nat.Partrec.ppred`：ppred : Nat.Partrec fun n => ppred n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.bind_assoc`：bind_assoc {γ} (f : Part α) (g : α -> Part β) (k : β ->
 Part γ) : (f.bind g).bind k = f.bind fun x => (g x).bind k
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.bind_map`：bind_map {γ} (f : α -> β) (x) (g : β -> Part γ) : (map f 
x).bind g = x.bind fun y => g (f y)
· 使用定理 `Part.bind_some_eq_map`：bind_some_eq_map (f : α -> β) (x : Part α) : x.bi
nd (fun y => some (f y)) = map f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Partrec.map`：map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : 
Computable₂ g) : Partrec fun a => (f a).map (g a)
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.option_some`：option_some : Computable (@Option.some α)
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
-/
theorem option_some_iff {f : α →. σ} : (Partrec fun a => (f a).map Option.some) ↔ Partrec f :=
  ⟨fun h => (Nat.Partrec.ppred.comp h).of_eq fun n => by simp [Part.bind_assoc, bind_some_eq_map],
    fun hf => hf.map (option_some.comp snd).to₂⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Partrec.optionCasesOn_right** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：optionCasesOn_right {o : α -> Option β} {f : α -> σ} {g : α -> β ->. σ} (h
o : Computable o) (hf : Computable f) (hg : Partrec₂ g) : @Partrec _ σ _ _ fun a
 => Option.casesOn (o a) (Part.some (f a)) (g a)
参数：ho : Computable o；hf : Computable f；hg : Partrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.nat_casesOn_right`：nat_casesOn_right {f : α -> Nat} {g : α -> σ}
 {h : α -> Nat ->. σ} (hf : Computable f) (hg : Computable g) (hh : Partrec₂ h) 
: Partrec fun a…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Computable.encode_iff`：encode_iff {f : α -> σ} : (Computable fun a => en
code (f a)) ↔ Computable f
· 使用定理 `Computable.partrec`：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodable 
α] [inst_1 : Primcodable σ] {f : α → σ}, Computable f → Partrec ↑f
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Computable.ofOption`：ofOption {f : α -> Option β} (hf : Computable f) : 
Partrec fun a => (f a : Part β)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.decode`：∀ {α : Type u_1} [inst : Primcodable α], Computable E
ncodable.decode
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Partrec₂.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {σ : Type 
u_5} [inst : Primcodable α] [inst_1 : Primcodable β]   [inst_2 : Primcodable γ] 
[in…
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `Part.bind_some`：bind_some (a : α) (f : α -> Part β) : (some a).bind f = 
f a
-/
theorem optionCasesOn_right {o : α → Option β} {f : α → σ} {g : α → β →. σ} (ho : Computable o)
    (hf : Computable f) (hg : Partrec₂ g) :
    @Partrec _ σ _ _ fun a => Option.casesOn (o a) (Part.some (f a)) (g a) :=
  have :
    Partrec fun a : α =>
      Nat.casesOn (encode (o a)) (Part.some (f a)) (fun n => Part.bind (decode (α := β) n) (g a)) :=
    nat_casesOn_right (h := fun a n ↦ Part.bind (ofOption (decode n)) fun b ↦ g a b)
      (encode_iff.2 ho) hf.partrec <|
        ((@Computable.decode β _).comp snd).ofOption.bind (hg.comp (fst.comp fst) snd).to₂
  this.of_eq fun a => by rcases o a with - | b <;> simp [encodek]
/-
**Partrec.sumCasesOn_right** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：sumCasesOn_right {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ ->. σ}
 (hf : Computable f) (hg : Computable₂ g) (hh : Partrec₂ h) : @Partrec _ σ _ _ f
un a => Sum.casesOn (f a) (fun b => Part.some (g a b)) (h a)
参数：hf : Computable f；hg : Computable₂ g；hh : Partrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.optionCasesOn_right`：optionCasesOn_right {o : α -> Option β} {f 
: α -> σ} {g : α -> β ->. σ} (ho : Computable o) (hf : Computable f) (hg : Partr
ec₂ g) : @Partrec…
· 使用定理 `Computable.sumCasesOn`：sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ}
 {h : α -> γ -> σ} (hf : Computable f) (hg : Computable₂ g) (hh : Computable₂ h)
 : @Computa…
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.option_some`：option_some : Computable (@Option.some α)
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Partrec.option_some_iff`：option_some_iff {f : α ->. σ} : (Partrec fun a 
=> (f a).map Option.some) ↔ Partrec f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.map_some`：map_some (f : α -> β) (a : α) : map f (some a) = some (f 
a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sumCasesOn_right {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ →. σ} (hf : Computable f)
    (hg : Computable₂ g) (hh : Partrec₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (fun b => Part.some (g a b)) (h a) :=
  have :
    Partrec fun a =>
      (Option.casesOn (Sum.casesOn (f a) (fun _ => Option.none) Option.some : Option γ)
          (some (Sum.casesOn (f a) (fun b => some (g a b)) fun _ => Option.none)) fun c =>
          (h a c).map Option.some :
        Part (Option σ)) :=
    optionCasesOn_right (g := fun a n => Part.map Option.some (h a n))
      (sumCasesOn hf (const Option.none).to₂ (option_some.comp snd).to₂)
      (sumCasesOn (g := fun a n => Option.some (g a n)) hf (option_some.comp hg)
        (const Option.none).to₂)
      (option_some_iff.2 hh)
  option_some_iff.1 <| this.of_eq fun a => by cases f a <;> simp
/-
**Partrec.sumCasesOn_left** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：sumCasesOn_left {f : α -> β oplus γ} {g : α -> β ->. σ} {h : α -> γ -> σ} 
(hf : Computable f) (hg : Partrec₂ g) (hh : Computable₂ h) : @Partrec _ σ _ _ fu
n a => Sum.casesOn (f a) (g a) fun c => Part.some (h a c)
参数：hf : Computable f；hg : Partrec₂ g；hh : Computable₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.sumCasesOn_right`：sumCasesOn_right {f : α -> β oplus γ} {g : α -
> β -> σ} {h : α -> γ ->. σ} (hf : Computable f) (hg : Computable₂ g) (hh : Part
rec₂ h) : @Par…
· 使用定理 `Computable.sumCasesOn`：sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ}
 {h : α -> γ -> σ} (hf : Computable f) (hg : Computable₂ g) (hh : Computable₂ h)
 : @Computa…
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.sumInr`：sumInr : Computable (@Sum.inr α β)
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Computable.sumInl`：sumInl : Computable (@Sum.inl α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sumCasesOn_left {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ → σ} (hf : Computable f)
    (hg : Partrec₂ g) (hh : Computable₂ h) :
    @Partrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) fun c => Part.some (h a c) :=
  (sumCasesOn_right (sumCasesOn hf (sumInr.comp snd).to₂ (sumInl.comp snd).to₂) hh hg).of_eq
    fun a => by cases f a <;> simp
/-
**Partrec.fix_aux** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：fix_aux {α σ} (f : α ->. σ oplus α) (a : α) (b : σ) : let F : α -> Nat ->.
 σ oplus α
参数：f : α ->. σ oplus α；a : α；b : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PFun.mem_fix_iff`：mem_fix_iff {f : α ->. β oplus α} {a : α} {b : β} : b 
in f.fix a ↔ Sum.inl b in f a ∨ exists a', Sum.inr a' in f a ∧ b in f.fix a'
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem fix_aux {α σ} (f : α →. σ ⊕ α) (a : α) (b : σ) :
    let F : α → ℕ →. σ ⊕ α := fun a n =>
      n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
    (∃ n : ℕ,
        ((∃ b' : σ, Sum.inl b' ∈ F a n) ∧ ∀ {m : ℕ}, m < n → ∃ b : α, Sum.inr b ∈ F a m) ∧
          Sum.inl b ∈ F a n) ↔
      b ∈ PFun.fix f a := by
  intro F; refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨n, ⟨_x, h₁⟩, h₂⟩
    have : ∀ m a', Sum.inr a' ∈ F a m → b ∈ PFun.fix f a' → b ∈ PFun.fix f a := by
      intro m a' am ba
      induction m generalizing a' with simp [F] at am
      | zero => rwa [← am]
      | succ m IH =>
        rcases am with ⟨a₂, am₂, fa₂⟩
        exact IH _ am₂ (PFun.mem_fix_iff.2 (Or.inr ⟨_, fa₂, ba⟩))
    cases n <;> simp [F] at h₂
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `obtain`/`specialize`. It is not yet clear whether this is due to defeq abuse
    in Mathlib or a problem in the new canonicalizer; a minimization would help. The original
    proof was:
    ```
    have := h₁ (Nat.lt_succ_self _)
    grind [mem_unique, PFun.mem_fix_iff]
    ```
    -/
    obtain ⟨c, hc⟩ := h₁ (Nat.lt_succ_self _)
    specialize this _ _ hc
    grind [mem_unique, PFun.mem_fix_iff]
  · suffices ∀ a', b ∈ PFun.fix f a' → ∀ k, Sum.inr a' ∈ F a k →
        ∃ n, Sum.inl b ∈ F a n ∧ ∀ m < n, k ≤ m → ∃ a₂, Sum.inr a₂ ∈ F a m by
      rcases this _ h 0 (by simp [F]) with ⟨n, hn₁, hn₂⟩
      exact ⟨_, ⟨⟨_, hn₁⟩, fun {m} mn => hn₂ m mn (Nat.zero_le _)⟩, hn₁⟩
    intro a₁ h₁
    apply @PFun.fixInduction _ _ _ _ _ _ h₁
    intro a₂ h₂ IH k hk
    rcases PFun.mem_fix_iff.1 h₂ with (h₂ | ⟨a₃, am₃, _⟩)
    · refine ⟨k.succ, ?_, fun m mk km => ⟨a₂, ?_⟩⟩
      · simpa [F] using Or.inr ⟨_, hk, h₂⟩
      · rwa [le_antisymm (Nat.le_of_lt_succ mk) km]
    · rcases IH _ am₃ k.succ (by simpa [F] using ⟨_, hk, am₃⟩) with ⟨n, hn₁, hn₂⟩
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer),
      the `clear_value F` was not required here. -/
      clear_value F
      grind

set_option backward.isDefEq.respectTransparency false in
/-
**Partrec.fix** 是 Mathlib 中的一个定理，位于命名空间 `Partrec`。
形式化陈述：fix {f : α ->. σ oplus α} (hf : Partrec f) : Partrec (PFun.fix f)
参数：hf : Partrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Partrec.nat_rec`：nat_rec {f : α -> Nat} {g : α ->. σ} {h : α -> Nat × σ 
->. σ} (hf : Computable f) (hg : Partrec g) (hh : Partrec₂ h) : Partrec fun a =>
 (f a…
· 使用定理 `Computable.snd`：snd : Computable (@Prod.snd α β)
· 使用定理 `Computable.partrec`：∀ {α : Type u_1} {σ : Type u_2} [inst : Primcodable 
α] [inst_1 : Primcodable σ] {f : α → σ}, Computable f → Partrec ↑f
· 使用定理 `Computable.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} [inst : 
Primcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β → σ} {
g : α…
· 使用定理 `Computable.sumInr`：sumInr : Computable (@Sum.inr α β)
· 使用定理 `Computable.fst`：fst : Computable (@Prod.fst α β)
· 使用定理 `Partrec.to₂`：to₂ {f : α × β ->. σ} (hf : Partrec f) : Partrec₂ fun a b =
> f (a, b)
· 使用定理 `Partrec.sumCasesOn_right`：sumCasesOn_right {f : α -> β oplus γ} {g : α -
> β -> σ} {h : α -> γ ->. σ} (hf : Computable f) (hg : Computable₂ g) (hh : Part
rec₂ h) : @Par…
· 使用定理 `Computable.to₂`：to₂ {f : α × β -> σ} (hf : Computable f) : Computable₂ f
un a b => f (a, b)
· 使用定理 `Partrec.comp`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : β →. σ} {g 
: …
· 使用定理 `Partrec.map`：map {f : α ->. β} {g : α -> β -> σ} (hf : Partrec f) (hg : 
Computable₂ g) : Partrec fun a => (f a).map (g a)
· 使用定理 `Computable.sumCasesOn`：sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ}
 {h : α -> γ -> σ} (hf : Computable f) (hg : Computable₂ g) (hh : Computable₂ h)
 : @Computa…
· 使用定理 `Computable.id`：∀ {α : Type u_1} [inst : Primcodable α], Computable id
· 使用定理 `Computable.const`：const (s : σ) : Computable fun _ : α => s
· 使用定理 `Partrec.of_eq`：of_eq {f g : α ->. σ} (hf : Partrec f) (H : forall n, f n
 = g n) : Partrec g
· 使用定理 `Partrec.bind`：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Pri
mcodable α] [inst_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α →. β} {g 
: …
· 使用定理 `Partrec.rfind`：rfind {p : α -> Nat ->. Bool} (hp : Partrec₂ p) : Partrec
 fun a => Nat.rfind (p a)
· 使用定理 `Partrec.none`：none : Partrec fun _ : α => @Part.none σ
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 34 条，此处仅展示前 30 条）
-/
theorem fix {f : α →. σ ⊕ α} (hf : Partrec f) : Partrec (PFun.fix f) := by
  let F : α → ℕ →. σ ⊕ α := fun a n =>
    n.rec (some (Sum.inr a)) fun _ IH => IH.bind fun s => Sum.casesOn s (fun _ => Part.some s) f
  have hF : Partrec₂ F :=
    Partrec.nat_rec snd (sumInr.comp fst).partrec
      (sumCasesOn_right (snd.comp snd) (snd.comp <| snd.comp fst).to₂ (hf.comp snd).to₂).to₂
  let p a n := @Part.map _ Bool (fun s => Sum.casesOn s (fun _ => true) fun _ => false) (F a n)
  have hp : Partrec₂ p :=
    hF.map ((sumCasesOn Computable.id (const true).to₂ (const false).to₂).comp snd).to₂
  exact ((Partrec.rfind hp).bind (hF.bind (sumCasesOn_right snd snd.to₂ none.to₂).to₂).to₂).of_eq
    fun a => ext fun b => by simpa [p] using fix_aux f _ _

end Partrec

