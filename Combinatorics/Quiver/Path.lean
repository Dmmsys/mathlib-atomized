/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison, Matteo Cipollina, Runtian Zhou
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor
public import Mathlib.Logic.Lemmas
public import Batteries.Data.List.Basic

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.

We also define `Quiver.Reachable a b`, the existence of a directed path from `a` to `b`.
-/

@[expose] public section

open Function

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace Quiver

/-- `Path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
/-
**Quiver.Path** 是 Mathlib 中的一个归纳类型，位于命名空间 `Quiver`。
形式化陈述：{V : Type u} → [Quiver V] → V → V → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Path a b` is the type of paths from `a` to `b` through the arrows of `G`.
-/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Type max u v
  | nil : Path a a
  | cons : ∀ {b c : V}, Path a b → (b ⟶ c) → Path a c

-- See issue https://github.com/leanprover/lean4/issues/2049
compile_inductive% Path

/-- An arrow viewed as a path of length one. -/
/-
**Quiver.Hom.toPath** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u_1} → [inst : Quiver V] → {a b : V} → (a ⟶ b) → Quiver.Path a b
参数：a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow viewed as a path of length one.
-/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

namespace Path

variable {V : Type u} [Quiver V] {a b c d : V}

/-
**Quiver.Path.nil_ne_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：nil_ne_cons (p : Path a b) (e : b ⟶ a) : Path.nil != p.cons e
参数：p : Path a b；e : b ⟶ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma nil_ne_cons (p : Path a b) (e : b ⟶ a) : Path.nil ≠ p.cons e :=
  fun h => by injection h
/-
**Quiver.Path.cons_ne_nil** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons e != Path.nil
参数：p : Path a b；e : b ⟶ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons e ≠ Path.nil :=
  fun h => by injection h
/-
**Quiver.Path.obj_eq_of_cons_eq_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：obj_eq_of_cons_eq_cons {p : Path a b} {p' : Path a c} {e : b ⟶ d} {e' : c 
⟶ d} (h : p.cons e = p'.cons e') : b = c
参数：h : p.cons e = p'.cons e'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma obj_eq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c := by injection h
/-
**Quiver.Path.heq_of_cons_eq_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：heq_of_cons_eq_cons {p : Path a b} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d
} (h : p.cons e = p'.cons e') : p ≍ p'
参数：h : p.cons e = p'.cons e'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
lemma heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : p ≍ p' := by injection h
/-
**Quiver.Path.hom_heq_of_cons_eq_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：hom_heq_of_cons_eq_cons {p : Path a b} {p' : Path a c} {e : b ⟶ d} {e' : c
 ⟶ d} (h : p.cons e = p'.cons e') : e ≍ e'
参数：h : p.cons e = p'.cons e'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
lemma hom_heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : e ≍ e' := by injection h

/-- The length of a path is the number of arrows it uses. -/
/-
**Quiver.Path.length** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{V : Type u} → [inst : Quiver V] → {a b : V} → Quiver.Path a b → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of a path is the number of arrows it uses.
-/
def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, nil => 0
  | _, cons p _ => p.length + 1
/-
**Quiver.Path.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : V} : Inhabited (Path a a) :=
  ⟨nil⟩

@[simp]
/-
**Quiver.Path.length_nil** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：length_nil {a : V} : (nil : Path a a).length = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_nil {a : V} : (nil : Path a a).length = 0 :=
  rfl

@[simp]
/-
**Quiver.Path.length_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p
.length + 1
参数：a b c : V；p : Path a b；e : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl
/-
**Quiver.Path.eq_of_length_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b
参数：p : Path a b；hzero : p.length = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b := by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero
/-
**Quiver.Path.eq_nil_of_length_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：eq_nil_of_length_zero (p : Path a a) (hzero : p.length = 0) : p = nil
参数：p : Path a a；hzero : p.length = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem eq_nil_of_length_zero (p : Path a a) (hzero : p.length = 0) : p = nil := by
  cases p
  · rfl
  · simp at hzero

@[simp]
/-
**Quiver.Path.length_toPath** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：length_toPath {a b : V} (e : a ⟶ b) : e.toPath.length = 1
参数：e : a ⟶ b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma length_toPath {a b : V} (e : a ⟶ b) : e.toPath.length = 1 := rfl

/-- Composition of paths. -/
/-
**Quiver.Path.comp** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{V : Type u} → [inst : Quiver V] → {a b c : V} → Quiver.Path a b → Quiver.
Path b c → Quiver.Path a c
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of paths.
-/
def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
  | _, p, nil => p
  | _, p, cons q e => (p.comp q).cons e

@[simp]
/-
**Quiver.Path.comp_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) : p.comp
 (q.cons e) = (p.comp q).cons e
参数：p : Path a b；q : Path b c；e : c ⟶ d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) :
    p.comp (q.cons e) = (p.comp q).cons e :=
  rfl

@[simp]
/-
**Quiver.Path.comp_nil** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p
参数：p : Path a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl

@[simp]
/-
**Quiver.Path.nil_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Quiver.Path a b), Quiver.P
ath.nil.comp p = p
参数：p : Quiver.Path a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil_comp {a : V} : ∀ {b} (p : Path a b), Path.nil.comp p = p
  | _, nil => rfl
  | _, cons p _ => by rw [comp_cons, nil_comp p]

@[simp]
/-
**Quiver.Path.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b c d : V} (p : Quiver.Path a b) (q : 
Quiver.Path b c) (r : Quiver.Path c d),   (p.comp q).comp r = p.comp (q.comp r)
参数：p : Quiver.Path a b；q : Quiver.Path b c；r : Quiver.Path c d；p.comp q；q.comp r
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {a b c : V} :
    ∀ {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, nil => rfl
  | _, p, q, cons r _ => by rw [comp_cons, comp_cons, comp_cons, comp_assoc p q r]

@[simp]
/-
**Quiver.Path.length_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Quiver.Path a b) {c : V} (
q : Quiver.Path b c),   (p.comp q).length = p.length + q.length
参数：p : Quiver.Path a b；q : Quiver.Path b c；p.comp q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).length = p.length + q.length
  | _, nil => rfl
  | _, cons _ _ => congr_arg Nat.succ (length_comp _ _)
/-
**Quiver.Path.comp_inj** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length
) : p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂
参数：hq : q₁.length = q₂.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n
· 使用定理 `HEq.eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.cons.injEq`：∀ {V : Type u} [inst : Quiver V] {a b c : V} (a_
1 : Quiver.Path a b) (a_2 : b ⟶ c) (b_1 : V) (a_3 : Quiver.Path a b_1)   (a_4 : 
b_1 ⟶ c), (a…
-/
theorem comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  induction q₁ with
  | nil =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · exact ⟨h, rfl⟩
    · cases hq
  | cons q₁ f₁ ih =>
    rcases q₂ with _ | ⟨q₂, f₂⟩
    · cases hq
    · simp only [comp_cons, cons.injEq] at h
      obtain rfl := h.1
      obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.eq
      rw [h.2.2.eq]
      exact ⟨rfl, rfl⟩
/-
**Quiver.Path.comp_inj'** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length
) : p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂
参数：h : p₁.length = p₂.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quiver.Path.comp_inj`：comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq
 : q₁.length = q₂.length) : p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂
· 使用定理 `Nat.add_left_cancel`：∀ {n m k : ℕ}, n + m = n + k → m = k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.length_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p :
 Quiver.Path a b) {c : V} (q : Quiver.Path b c),   (p.comp q).length = p.length 
+ q.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel (n := p₂.length) <|
    by simpa [h] using congr_arg length h_eq).1 h_eq,
   by rintro ⟨rfl, rfl⟩; rfl⟩
/-
**Quiver.Path.comp_injective_left** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp 
q
参数：q : Path b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quiver.Path.comp_inj`：comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq
 : q₁.length = q₂.length) : p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂
-/
theorem comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp q :=
  fun _ _ h => ((comp_inj rfl).1 h).1
/-
**Quiver.Path.comp_injective_right** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_injective_right (p : Path a b) : Injective (p.comp : Path b c -> Path
 a c)
参数：p : Path a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quiver.Path.comp_inj'`：comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (
h : p₁.length = p₂.length) : p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂
-/
theorem comp_injective_right (p : Path a b) : Injective (p.comp : Path b c → Path a c) :=
  fun _ _ h => ((comp_inj' rfl).1 h).2

@[simp]
/-
**Quiver.Path.comp_inj_left** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ 
p₁ = p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Quiver.Path.comp_injective_left`：comp_injective_left (q : Path b c) : In
jective fun p : Path a b => p.comp q
-/
theorem comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
  q.comp_injective_left.eq_iff

@[simp]
/-
**Quiver.Path.comp_inj_right** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔
 q₁ = q₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Quiver.Path.comp_injective_right`：comp_injective_right (p : Path a b) : 
Injective (p.comp : Path b c -> Path a c)
-/
theorem comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
  p.comp_injective_right.eq_iff
/-
**Quiver.Path.eq_toPath_comp_of_length_eq_succ** 是 Mathlib 中的一个引理，位于命名空间 `Quiver
.Path`。
形式化陈述：eq_toPath_comp_of_length_eq_succ (p : Path a b) {n : Nat} (hp : p.length =
 n + 1) : exists (c : V) (f : a ⟶ c) (q : Quiver.Path c b) (_ : q.length = n), p
 = f.toPath.comp q
参数：p : Path a b；hp : p.length = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quiver.Path.eq_nil_of_length_zero`：eq_nil_of_length_zero (p : Path a a) 
(hzero : p.length = 0) : p = nil
· 使用定理 `Quiver.Path.eq_of_length_zero`：eq_of_length_zero (p : Path a b) (hzero :
 p.length = 0) : a = b
· 使用定理 `Nat.add_eq_right`：∀ {a b : ℕ}, a + b = b ↔ a = 0
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Quiver.Path.length_cons`：length_cons (a b c : V) (p : Path a b) (e : b ⟶
 c) : (p.cons e).length = p.length + 1
· 使用定理 `Nat.add_right_cancel_iff`：∀ {m k n : ℕ}, m + n = k + n ↔ m = k
-/
lemma eq_toPath_comp_of_length_eq_succ (p : Path a b) {n : ℕ}
    (hp : p.length = n + 1) :
    ∃ (c : V) (f : a ⟶ c) (q : Quiver.Path c b) (_ : q.length = n),
      p = f.toPath.comp q := by
  induction p generalizing n with
  | nil => simp at hp
  | @cons c d p q h =>
    cases n
    · rw [length_cons, Nat.zero_add, Nat.add_eq_right] at hp
      obtain rfl := eq_of_length_zero p hp
      obtain rfl := eq_nil_of_length_zero p hp
      exact ⟨d, q, nil, rfl, rfl⟩
    · rw [length_cons, Nat.add_right_cancel_iff] at hp
      obtain ⟨x, q'', p'', hl, rfl⟩ := h hp
      exact ⟨x, q'', p''.cons q, by simpa, rfl⟩

section Decomposition

variable {V R : Type*} [Quiver V] {a b : V} (p : Path a b)

/-
**Quiver.Path.length_ne_zero_iff_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`
。
形式化陈述：length_ne_zero_iff_eq_comp (p : Path a b) : p.length != 0 ↔ exists (c : V)
 (e : a ⟶ c) (p' : Path c b), p = e.toPath.comp p' ∧ p.length = p'.length + 1
参数：p : Path a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.Path.eq_toPath_comp_of_length_eq_succ`：eq_toPath_comp_of_length_e
q_succ (p : Path a b) {n : Nat} (hp : p.length = n + 1) : exists (c : V) (f : a 
⟶ c) (q : Quiver.Path c b) (_ : q.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma length_ne_zero_iff_eq_comp (p : Path a b) :
    p.length ≠ 0 ↔ ∃ (c : V) (e : a ⟶ c) (p' : Path c b),
      p = e.toPath.comp p' ∧ p.length = p'.length + 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h_len : p.length = (p.length - 1) + 1 := by lia
    obtain ⟨c, e, p', hp', rfl⟩ := Path.eq_toPath_comp_of_length_eq_succ p h_len
    exact ⟨c, e, p', rfl, by lia⟩
  · rintro ⟨c, p', e, rfl, h⟩
    simp [h]

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
/-
**Quiver.Path.length_ne_zero_iff_eq_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`
。
形式化陈述：length_ne_zero_iff_eq_cons : p.length != 0 ↔ exists (c : V) (p' : Path a c
) (e : c ⟶ b), p = p'.cons e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Every non-empty path can be decomposed as an initial path plus a final edge.
-/
lemma length_ne_zero_iff_eq_cons :
    p.length ≠ 0 ↔ ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases p with
    | nil => simp at h
    | cons p' e => exact ⟨_, p', e, rfl⟩
  · rintro ⟨c, p', e, rfl⟩
    simp
/-
**Quiver.Path.comp_toPath_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u_1} [inst : Quiver V] {a b c : V} (p : Quiver.Path a b) (e : 
b ⟶ c), p.comp e.toPath = p.cons e
参数：p : Quiver.Path a b；e : b ⟶ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_toPath_eq_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.comp e.toPath = p.cons e :=
  rfl

end Decomposition

/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp]
/-
**Quiver.Path.toList** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{V : Type u} → [inst : Quiver V] → {a b : V} → Quiver.Path a b → List V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a path into a list. The list contains `a` at its head, but not `b` a priori
.
-/
def toList : ∀ {b : V}, Path a b → List V
  | _, nil => []
  | _, @cons _ _ _ c _ p _ => c :: p.toList

/-- `Quiver.Path.toList` is a contravariant functor. The inversion comes from `Quiver.Path` and
`List` having different preferred directions for adding elements. -/
@[simp]
/-
**Quiver.Path.toList_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Quiver.Path a b) {c : V} (
q : Quiver.Path b c),   (p.comp q).toList = q.toList ++ p.toList
参数：p : Quiver.Path a b；q : Quiver.Path b c；p.comp q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Quiver.Path.toList` is a contravariant functor. The inversion comes from `Quive
r.Path` and
`List` having different preferred directions for adding elements.
-/
theorem toList_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList
  | _, nil => by simp
  | _, @cons _ _ _ d _ q _ => by simp [toList_comp]
/-
**Quiver.Path.isChain_toList_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Quiver.Path a b), List.IsC
hain (fun x y => Nonempty (y ⟶ x)) p.toList
参数：p : Quiver.Path a b；fun x y => Nonempty (y ⟶ x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_toList_nonempty :
    ∀ {b} (p : Path a b), (p.toList).IsChain (fun x y => Nonempty (y ⟶ x))
  | _, nil => .nil
  | _, cons nil _ => .singleton _
  | _, cons (cons p g) _ => List.IsChain.cons_cons ⟨g⟩ (isChain_toList_nonempty (cons p g))
/-
**Quiver.Path.isChain_cons_toList_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Pat
h`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Quiver.Path a b),   List.I
sChain (fun x y => Nonempty (y ⟶ x)) (b :: p.toList)
参数：p : Quiver.Path a b；fun x y => Nonempty (y ⟶ x)；b :: p.toList。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_cons_toList_nonempty :
    ∀ {b} (p : Path a b), (b :: p.toList).IsChain (fun x y => Nonempty (y ⟶ x))
  | _, nil => .singleton _
  | _, cons p f => p.isChain_cons_toList_nonempty.cons_cons ⟨f⟩

variable [∀ a b : V, Subsingleton (a ⟶ b)]
/-
**Quiver.Path.toList_injective** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：toList_injective (a : V) : forall b, Injective (toList : Path a b -> List 
V) | _, nil, nil, _ => rfl | _, nil, @cons _ _ _ c _ p f, h => by cases h | _, @
cons _ _ _ c _ p f, nil, h => by cases h | _, @cons _ _ _ c _ p f, @cons _ _ _ t
 _ C D, h => by simp only [toList, List.cons.injEq] at h obtain ⟨rfl, hAC⟩
参数：a : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toList_injective (a : V) : ∀ b, Injective (toList : Path a b → List V)
  | _, nil, nil, _ => rfl
  | _, nil, @cons _ _ _ c _ p f, h => by cases h
  | _, @cons _ _ _ c _ p f, nil, h => by cases h
  | _, @cons _ _ _ c _ p f, @cons _ _ _ t _ C D, h => by
    simp only [toList, List.cons.injEq] at h
    obtain ⟨rfl, hAC⟩ := h
    simp [toList_injective _ _ hAC, eq_iff_true_of_subsingleton]

@[simp]
/-
**Quiver.Path.toList_inj** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：toList_inj {p q : Path a b} : p.toList = q.toList ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Quiver.Path.toList_injective`：toList_injective (a : V) : forall b, Injec
tive (toList : Path a b -> List V) | _, nil, nil, _ => rfl | _, nil, @cons _ _ _
 c _ p f, h => by …
-/
theorem toList_inj {p q : Path a b} : p.toList = q.toList ↔ p = q :=
  (toList_injective _ _).eq_iff


section BoundedPath

variable {V : Type*} [Quiver V]

/-- A bounded path is a path with a uniform bound on its length. -/
/-
**Quiver.Path.BoundedPaths** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：BoundedPaths (v w : V) (n : Nat) : Sort _
参数：v w : V；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded path is a path with a uniform bound on its length.
-/
def BoundedPaths (v w : V) (n : ℕ) : Sort _ :=
  { p : Path v w // p.length ≤ n }

/-- Bounded paths of length zero between two vertices form a subsingleton. -/
/-
**Quiver.Path.instSubsingletonBddPaths** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.Path`。
形式化陈述：instSubsingletonBddPaths (v w : V) : Subsingleton (BoundedPaths v w 0) whe
re allEq
参数：v w : V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False

--- 原说明 ---
Bounded paths of length zero between two vertices form a subsingleton.
-/
instance instSubsingletonBddPaths (v w : V) : Subsingleton (BoundedPaths v w 0) where
  allEq := fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => rfl
    | _, _, .cons _ _, _ => by simp [Quiver.Path.length] at hp
    | _, _, _, .cons _ _ => by simp [Quiver.Path.length] at hq

/-- Bounded paths of length zero between two vertices have decidable equality. -/
/-
**Quiver.Path.decidableEqBddPathsZero** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：decidableEqBddPathsZero (v w : V) : DecidableEq (BoundedPaths v w 0)
参数：v w : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bounded paths of length zero between two vertices have decidable equality.
-/
def decidableEqBddPathsZero (v w : V) : DecidableEq (BoundedPaths v w 0) :=
  fun _ _ => isTrue <| Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Given decidable equality on paths of length up to `n`, we can construct
decidable equality on paths of length up to `n + 1`. -/
/-
**Quiver.Path.decidableEqBddPathsOfDecidableEq** 是 Mathlib 中的一个定义，位于命名空间 `Quiver
.Path`。
形式化陈述：decidableEqBddPathsOfDecidableEq (n : Nat) (h₁ : DecidableEq V) (h₂ : fora
ll (v w : V), DecidableEq (v ⟶ w)) (h₃ : forall (v w : V), DecidableEq (BoundedP
aths v w n)) (v w : V) : DecidableEq (BoundedPaths v w (n + 1))
参数：n : Nat；h₁ : DecidableEq V；h₂ : forall (v w : V), DecidableEq (v ⟶ w)；h₃ : fo
rall (v w : V), DecidableEq (BoundedPaths v w n)；v w : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given decidable equality on paths of length up to `n`, we can construct
decidable equality on paths of length up to `n + 1`.
-/
def decidableEqBddPathsOfDecidableEq (n : ℕ) (h₁ : DecidableEq V)
    (h₂ : ∀ (v w : V), DecidableEq (v ⟶ w)) (h₃ : ∀ (v w : V), DecidableEq (BoundedPaths v w n))
    (v w : V) : DecidableEq (BoundedPaths v w (n + 1)) :=
  fun ⟨p, hp⟩ ⟨q, hq⟩ =>
    match v, w, p, q with
    | _, _, .nil, .nil => isTrue rfl
    | _, _, .nil, .cons _ _
    | _, _, .cons _ _, .nil =>
      isFalse fun h => Quiver.Path.noConfusion rfl .rfl .rfl .rfl (heq_of_eq (Subtype.mk.inj h))
    | _, _, .cons (b := v') p' α, .cons (b := v'') q' β =>
      match v', v'', h₁ v' v'' with
      | _, _, isTrue (Eq.refl _) =>
        if h : α = β then
          have hp' : p'.length ≤ n := by simp [Quiver.Path.length] at hp; lia
          have hq' : q'.length ≤ n := by simp [Quiver.Path.length] at hq; lia
          if h'' : (⟨p', hp'⟩ : BoundedPaths _ _ n) = ⟨q', hq'⟩ then
            isTrue <| by
              apply Subtype.ext
              dsimp
              rw [h, show p' = q' from Subtype.mk.inj h'']
          else
            isFalse fun h =>
              h'' <| Subtype.ext <| eq_of_heq <| (Quiver.Path.cons.inj <| Subtype.mk.inj h).2.1
        else
          isFalse fun h' =>
            h <| eq_of_heq (Quiver.Path.cons.inj <| Subtype.mk.inj h').2.2
      | _, _, isFalse h => isFalse fun h' =>
        h (Quiver.Path.cons.inj <| Subtype.mk.inj h').1

/-- Equality is decidable on all uniformly bounded paths given decidable
equality on the vertices and the arrows. -/
/-
**Quiver.Path.decidableEqBoundedPaths** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.Path`。
形式化陈述：decidableEqBoundedPaths [DecidableEq V] [forall (v w : V), DecidableEq (v 
⟶ w)] (n : Nat) : (v w : V) -> DecidableEq (BoundedPaths v w n)
参数：v w : V；v ⟶ w；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equality is decidable on all uniformly bounded paths given decidable
equality on the vertices and the arrows.
-/
instance decidableEqBoundedPaths [DecidableEq V] [∀ (v w : V), DecidableEq (v ⟶ w)]
    (n : ℕ) : (v w : V) → DecidableEq (BoundedPaths v w n) :=
  n.rec decidableEqBddPathsZero
    fun n decEq => decidableEqBddPathsOfDecidableEq n inferInstance inferInstance decEq

/-- Equality is decidable on paths in a quiver given decidable equality on the vertices and
arrows. -/
/-
**Quiver.Path.instDecidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.Path`。
形式化陈述：instDecidableEq [DecidableEq V] [forall (v w : V), DecidableEq (v ⟶ w)] : 
(v w : V) -> DecidableEq (Path v w)
参数：v w : V；v ⟶ w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equality is decidable on paths in a quiver given decidable equality on the verti
ces and
arrows.
-/
instance instDecidableEq [DecidableEq V] [∀ (v w : V), DecidableEq (v ⟶ w)] :
    (v w : V) → DecidableEq (Path v w) := fun v w p q =>
  let m := max p.length q.length
  let p' : BoundedPaths v w m := ⟨p, Nat.le_max_left ..⟩
  let q' : BoundedPaths v w m := ⟨q, Nat.le_max_right ..⟩
  decidable_of_iff (p' = q') Subtype.ext_iff

end BoundedPath

end Path

section Reachable

variable {V : Type u} [Quiver V]

/-- `Reachable a b` holds when there is a directed path from `a` to `b`.

This is a preorder rather than an equivalence, since quiver paths are directed (compare the
symmetric `SimpleGraph.Reachable`). -/
/-
**Quiver.Reachable** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：Reachable (a b : V) : Prop
参数：a b : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Reachable a b` holds when there is a directed path from `a` to `b`.

This is a preorder rather than an equivalence, since quiver paths are directed (
compare the
symmetric `SimpleGraph.Reachable`).
-/
def Reachable (a b : V) : Prop := Nonempty (Path a b)

variable {a b c : V}
/-
**Quiver.Reachable.elim** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Reachable`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} {p : Prop}, Quiver.Reachable a 
b → (∀ (a : Quiver.Path a b), p) → p
参数：∀ (a : Quiver.Path a b), p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
protected theorem Reachable.elim {p : Prop} (h : Reachable a b) (hp : Path a b → p) : p :=
  Nonempty.elim h hp

@[refl]
/-
**Quiver.Reachable.refl** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Reachable`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] (a : V), Quiver.Reachable a a
参数：a : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Reachable.refl (a : V) : Reachable a a := ⟨.nil⟩

@[simp]
/-
**Quiver.Reachable.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Reachable`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a : V}, Quiver.Reachable a a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Reachable.refl`：∀ {V : Type u} [inst : Quiver V] (a : V), Quiver.
Reachable a a
-/
protected theorem Reachable.rfl : Reachable a a := .refl _

@[trans]
/-
**Quiver.Reachable.trans** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Reachable`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b c : V}, Quiver.Reachable a b → Quive
r.Reachable b c → Quiver.Reachable a c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Reachable.elim`：∀ {V : Type u} [inst : Quiver V] {a b : V} {p : P
rop}, Quiver.Reachable a b → (∀ (a : Quiver.Path a b), p) → p
-/
protected theorem Reachable.trans (hab : Reachable a b) (hbc : Reachable b c) : Reachable a c :=
  hab.elim fun p => hbc.elim fun q => ⟨p.comp q⟩
/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreorder V Reachable where
  refl := .refl
  trans _ _ _ := .trans

/-- A path witnesses that its target is reachable from its source. -/
/-
**Quiver.Path.reachable** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Quiver.Path a b), Quiver.R
eachable a b
参数：p : Quiver.Path a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path witnesses that its target is reachable from its source.
-/
protected theorem Path.reachable (p : Path a b) : Reachable a b := ⟨p⟩

/-- An arrow witnesses that its target is reachable from its source. -/
/-
**Quiver.Hom.reachable** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Hom`。
形式化陈述：∀ {V : Type u} [inst : Quiver V] {a b : V} (e : a ⟶ b), Quiver.Reachable a
 b
参数：e : a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow witnesses that its target is reachable from its source.
-/
protected theorem Hom.reachable (e : a ⟶ b) : Reachable a b := ⟨e.toPath⟩

end Reachable

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : V ⥤q W)

/-- The image of a path under a prefunctor. -/
/-
**Prefunctor.mapPath** 是 Mathlib 中的一个定义，位于命名空间 `Prefunctor`。
形式化陈述：{V : Type u₁} →   [inst : Quiver V] →     {W : Type u₂} → [inst_1 : Quiver
 W] → (F : V ⥤q W) → {a b : V} → Quiver.Path a b → Quiver.Path (F.obj a) (F.obj 
b)
参数：F : V ⥤q W；F.obj a；F.obj b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a path under a prefunctor.
-/
def mapPath {a : V} : ∀ {b : V}, Path a b → Path (F.obj a) (F.obj b)
  | _, Path.nil => Path.nil
  | _, Path.cons p e => Path.cons (mapPath p) (F.map e)

@[simp]
/-
**Prefunctor.mapPath_nil** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：mapPath_nil (a : V) : F.mapPath (Path.nil : Path a a) = Path.nil
参数：a : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPath_nil (a : V) : F.mapPath (Path.nil : Path a a) = Path.nil :=
  rfl

@[simp]
/-
**Prefunctor.mapPath_cons** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：mapPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : F.mapPath (Path.cons
 p e) = Path.cons (F.mapPath p) (F.map e)
参数：p : Path a b；e : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl

@[simp]
/-
**Prefunctor.mapPath_comp** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：∀ {V : Type u₁} [inst : Quiver V] {W : Type u₂} [inst_1 : Quiver W] (F : V
 ⥤q W) {a b : V} (p : Quiver.Path a b) {c : V}   (q : Quiver.Path b c), F.mapPat
h (p.comp q) = (F.mapPath p).comp (F.mapPath q)
参数：F : V ⥤q W；p : Quiver.Path a b；q : Quiver.Path b c；p.comp q；F.mapPath p；F.map
Path q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPath_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, Path.nil => rfl
  | c, Path.cons q e => by dsimp; rw [mapPath_comp p q]

@[simp]
/-
**Prefunctor.mapPath_toPath** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：mapPath_toPath {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPa
th
参数：f : a ⟶ b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPath_toPath {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPath :=
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**Prefunctor.mapPath_id** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：∀ {V : Type u₁} [inst : Quiver V] {a b : V} (p : Quiver.Path a b), (𝟭q V).
mapPath p = p
参数：p : Quiver.Path a b；𝟭q V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPath_id {a b : V} : (p : Path a b) → (𝟭q V).mapPath p = p
  | Path.nil => rfl
  | Path.cons q e => by dsimp; rw [mapPath_id q]

variable {U : Type u₃} [Quiver.{v₃} U] (G : W ⥤q U)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**Prefunctor.mapPath_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Prefunctor`。
形式化陈述：mapPath_comp_apply {a b : V} (p : Path a b) : (F ⋙q G).mapPath p = G.mapPa
th (F.mapPath p)
参数：p : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapPath_comp_apply {a b : V} (p : Path a b) :
    (F ⋙q G).mapPath p = G.mapPath (F.mapPath p) := by
  induction p with
  | nil => rfl
  | cons x y h => simp [h]

end Prefunctor

