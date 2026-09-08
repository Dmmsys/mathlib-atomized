/-
Copyright (c) 2025 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Subwalks

We define a relation on walks stating that one walk is the subwalk of another.

## Main definitions

* `SimpleGraph.Walk.IsSubwalk`: A relation on walks stating that the first walk is a contiguous
  subwalk of the second walk.

## Tags
walks, subwalks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G G' : SimpleGraph V} {u v u' v' : V}

/-- `p.IsSubwalk q` means that the walk `p` is a contiguous subwalk of the walk `q`. -/
/-
**SimpleGraph.Walk.IsSubwalk** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：IsSubwalk {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop
参数：p : G.Walk u₁ v₁；q : G.Walk u₂ v₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p.IsSubwalk q` means that the walk `p` is a contiguous subwalk of the walk `q`.
-/
def IsSubwalk {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[refl, simp]
/-
**SimpleGraph.Walk.isSubwalk_rfl** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isSubwalk_rfl {u v} (p : G.Walk u v) : p.IsSubwalk p
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSubwalk_rfl {u v} (p : G.Walk u v) : p.IsSubwalk p :=
  ⟨nil, nil, by simp⟩

@[simp]
/-
**SimpleGraph.Walk.isSubwalk_nil_start** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：isSubwalk_nil_start {u v} (q : G.Walk u v) : (Walk.nil : G.Walk u u).IsSub
walk q
参数：q : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSubwalk_nil_start {u v} (q : G.Walk u v) : (Walk.nil : G.Walk u u).IsSubwalk q :=
  ⟨nil, q, by simp⟩

@[deprecated (since := "2026-07-11")] alias nil_isSubwalk := isSubwalk_nil_start

@[simp]
/-
**SimpleGraph.Walk.isSubwalk_nil_end** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：isSubwalk_nil_end {u v} (q : G.Walk u v) : (nil : G.Walk v v).IsSubwalk q
参数：q : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSubwalk_nil_end {u v} (q : G.Walk u v) : (nil : G.Walk v v).IsSubwalk q :=
  ⟨q, nil, by simp⟩
/-
**SimpleGraph.Walk.IsSubwalk.cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Is
Subwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' w : V} {p : G.Walk u v} {q
 : G.Walk u' v'},   p.IsSubwalk q → ∀ (h : G.Adj w u'), p.IsSubwalk (SimpleGraph
.Walk.cons h q)
参数：h : G.Adj w u'；SimpleGraph.Walk.cons h q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma IsSubwalk.cons {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) (h : G.Adj w u') : p.IsSubwalk (q.cons h) := by
  obtain ⟨r1, r2, rfl⟩ := hpq
  use r1.cons h, r2
  simp

@[simp]
/-
**SimpleGraph.Walk.isSubwalk_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isSubwalk_cons {u v w} (p : G.Walk u v) (h : G.Adj w u) : p.IsSubwalk (p.c
ons h)
参数：p : G.Walk u v；h : G.Adj w u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsSubwalk.cons`：∀ {V : Type u_1} {G : SimpleGraph V} {u
 v u' v' w : V} {p : G.Walk u v} {q : G.Walk u' v'},   p.IsSubwalk q → ∀ (h : G.
Adj w u'), p.IsSubwal…
· 使用引理 `SimpleGraph.Walk.isSubwalk_rfl`：isSubwalk_rfl {u v} (p : G.Walk u v) : p
.IsSubwalk p
-/
lemma isSubwalk_cons {u v w} (p : G.Walk u v) (h : G.Adj w u) : p.IsSubwalk (p.cons h) :=
  (isSubwalk_rfl p).cons h
/-
**SimpleGraph.Walk.IsSubwalk.concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.
IsSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' w : V} {p : G.Walk u v} {q
 : G.Walk u' v'},   p.IsSubwalk q → ∀ (h : G.Adj v' w), p.IsSubwalk (q.concat h)
参数：h : G.Adj v' w；q.concat h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.append_concat`：append_concat {u v w x : V} (p : G.Walk 
u v) (q : G.Walk v w) (h : G.Adj w x) : p.append (q.concat h) = (p.append q).con
cat h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma IsSubwalk.concat {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) (h : G.Adj v' w) : p.IsSubwalk (q.concat h) := by
  obtain ⟨r₁, r₂, rfl⟩ := hpq
  exact ⟨r₁, r₂.concat h, by rw [append_concat]⟩

@[simp]
/-
**SimpleGraph.Walk.isSubwalk_concat** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：isSubwalk_concat {u v w} (p : G.Walk u v) (h : G.Adj v w) : p.IsSubwalk (p
.concat h)
参数：p : G.Walk u v；h : G.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsSubwalk.concat`：∀ {V : Type u_1} {G : SimpleGraph V} 
{u v u' v' w : V} {p : G.Walk u v} {q : G.Walk u' v'},   p.IsSubwalk q → ∀ (h : 
G.Adj v' w), p.IsSubwal…
· 使用引理 `SimpleGraph.Walk.isSubwalk_rfl`：isSubwalk_rfl {u v} (p : G.Walk u v) : p
.IsSubwalk p
-/
lemma isSubwalk_concat {u v w} (p : G.Walk u v) (h : G.Adj v w) : p.IsSubwalk (p.concat h) :=
  (isSubwalk_rfl p).concat h
/-
**SimpleGraph.Walk.IsSubwalk.trans** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.I
sSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk 
u₁ v₁} {p₂ : G.Walk u₂ v₂}   {p₃ : G.Walk u₃ v₃}, p₁.IsSubwalk p₂ → p₂.IsSubwalk
 p₃ → p₁.IsSubwalk p₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.append_assoc`：append_assoc {u v w x : V} (p : G.Walk u 
v) (q : G.Walk v w) (r : G.Walk w x) : p.append (q.append r) = (p.append q).appe
nd r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsSubwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
    {p₃ : G.Walk u₃ v₃} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₃) :
    p₁.IsSubwalk p₃ := by
  obtain ⟨q₁, r₁, rfl⟩ := h₁
  obtain ⟨q₂, r₂, rfl⟩ := h₂
  use q₂.append q₁, r₁.append r₂
  simp [append_assoc]
/-
**SimpleGraph.Walk.isSubwalk_nil_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：isSubwalk_nil_iff {u v u'} (p : G.Walk u v) : p.IsSubwalk (nil : G.Walk u'
 u') ↔ exists (hu : u' = u) (hv : u' = v), p = nil.copy hu hv
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
-/
lemma isSubwalk_nil_iff {u v u'} (p : G.Walk u v) :
    p.IsSubwalk (nil : G.Walk u' u') ↔ ∃ (hu : u' = u) (hv : u' = v), p = nil.copy hu hv := by
  cases p with
  | nil =>
    constructor
    · rintro ⟨_ | _, _, ⟨⟩⟩
      simp
    · rintro ⟨rfl, _, _⟩
      simp
  | cons h p =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · rintro ⟨rfl, rfl, ⟨⟩⟩
/-
**SimpleGraph.Walk.nil_isSubwalk_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：nil_isSubwalk_iff_exists {u' u v} (q : G.Walk u v) : (Walk.nil : G.Walk u'
 u').IsSubwalk q ↔ exists (ru : G.Walk u u') (rv : G.Walk u' v), q = ru.append r
v
参数：q : G.Walk u v。
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
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nil_isSubwalk_iff_exists {u' u v} (q : G.Walk u v) :
    (Walk.nil : G.Walk u' u').IsSubwalk q ↔
      ∃ (ru : G.Walk u u') (rv : G.Walk u' v), q = ru.append rv := by
  simp [IsSubwalk]
/-
**SimpleGraph.Walk.length_le_of_isSubwalk** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
.Walk`。
形式化陈述：length_le_of_isSubwalk {u₁ v₁ u₂ v₂} {q : G.Walk u₁ v₁} {p : G.Walk u₂ v₂}
 (h : p.IsSubwalk q) : p.length <= q.length
参数：h : p.IsSubwalk q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma length_le_of_isSubwalk {u₁ v₁ u₂ v₂} {q : G.Walk u₁ v₁} {p : G.Walk u₂ v₂}
    (h : p.IsSubwalk q) : p.length ≤ q.length := by
  grind [IsSubwalk, length_append]
/-
**SimpleGraph.Walk.isSubwalk_of_append_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：isSubwalk_of_append_left {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {
p₃ : G.Walk v u} (h : p₃ = p₁.append p₂) : p₁.IsSubwalk p₃
参数：h : p₃ = p₁.append p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isSubwalk_of_append_left {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₁.IsSubwalk p₃ :=
  ⟨nil, p₂, h⟩
/-
**SimpleGraph.Walk.isSubwalk_of_append_right** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：isSubwalk_of_append_right {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} 
{p₃ : G.Walk v u} (h : p₃ = p₁.append p₂) : p₂.IsSubwalk p₃
参数：h : p₃ = p₁.append p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
-/
lemma isSubwalk_of_append_right {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₂.IsSubwalk p₃ :=
  ⟨p₁, nil, append_nil _ ▸ h⟩
/-
**SimpleGraph.Walk.isSubwalk_take** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isSubwalk_take {u v : V} (p : G.Walk u v) (n : Nat) : (p.take n).IsSubwalk
 p
参数：p : G.Walk u v；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.append_take_drop_eq`：append_take_drop_eq (p : G.Walk u 
v) (n : Nat) : (p.take n).append (p.drop n) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSubwalk_take {u v : V} (p : G.Walk u v) (n : ℕ) : (p.take n).IsSubwalk p :=
  ⟨nil, p.drop n, by simp⟩
/-
**SimpleGraph.Walk.isSubwalk_drop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isSubwalk_drop {u v : V} (p : G.Walk u v) (n : Nat) : (p.drop n).IsSubwalk
 p
参数：p : G.Walk u v；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.append_take_drop_eq`：append_take_drop_eq (p : G.Walk u 
v) (n : Nat) : (p.take n).append (p.drop n) = p
· 使用定理 `SimpleGraph.Walk.append_nil`：append_nil {u v : V} (p : G.Walk u v) : p.a
ppend nil = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isSubwalk_drop {u v : V} (p : G.Walk u v) (n : ℕ) : (p.drop n).IsSubwalk p :=
  ⟨p.take n, nil, by simp⟩
/-
**SimpleGraph.Walk.isSubwalk_iff_support_isInfix** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：isSubwalk_iff_support_isInfix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Wa
lk v' w'} : p₁.IsSubwalk p₂ ↔ p₁.support <:+: p₂.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_add_one_of_le`：∀ {n m : ℕ}, n ≤ m → n < m + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用引理 `SimpleGraph.Walk.getVert_eq_support_getElem`：getVert_eq_support_getElem 
{u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length) : p.getVert n = p.suppo
rt[n]'(p.length_support ▸ Nat.lt_…
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_append_right`：∀ {α : Type u_1} {as bs : List α} {i : ℕ} (h₁
 : as.length ≤ i) {h₂ : i < (as ++ bs).length},   (as ++ bs)[i] = bs[i - as.leng
th]
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `List.getElem_zero`：∀ {α : Type u_1} {l : List α} (h : 0 < l.length), l[0
] = l.head ⋯
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.head_append_of_ne_nil`：∀ {α : Type u_1} {l' l : List α} {w₁ : l ++ 
l' ≠ []} (w₂ : l ≠ []), (l ++ l').head w₁ = l.head w₂
· 使用定理 `SimpleGraph.Walk.head_support`：head_support {G : SimpleGraph V} {a b : V
} (p : G.Walk a b) : p.support.head (by simp) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `List.getElem_append_left`：∀ {α : Type u_1} {i : ℕ} {as bs : List α} (h :
 i < as.length) {h' : i < (as ++ bs).length}, (as ++ bs)[i] = as[i]
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用引理 `SimpleGraph.Walk.support_take`：support_take {u v} (p : G.Walk u v) (n : 
Nat) : (p.take n).support = p.support.take (n + 1)
· 使用定理 `List.take_append`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, List.take i
 (l₁ ++ l₂) = List.take i l₁ ++ List.take (i - l₁.length) l₂
（共 43 条，此处仅展示前 30 条）
-/
theorem isSubwalk_iff_support_isInfix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} :
    p₁.IsSubwalk p₂ ↔ p₁.support <:+: p₂.support := by
  refine ⟨fun ⟨ru, rv, h⟩ ↦ ?_, fun ⟨s, t, h⟩ ↦ ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) ≤ p₂.length := by grind [_=_ length_support]
    refine ⟨p₂.take s.length |>.copy rfl ?_, p₂.drop (s.length + p₁.length) |>.copy ?_ rfl, ?_⟩
    · simp [p₂.getVert_eq_support_getElem (by lia : s.length ≤ p₂.length), ← h,
        List.getElem_zero]
    · simp [p₂.getVert_eq_support_getElem this, ← h, ← p₁.getVert_eq_support_getElem le_rfl]
    apply ext_support
    simp only [← h, support_append, support_copy, support_take,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind), List.drop_append, List.drop_append,
      List.drop_eq_nil_of_le (by lia), List.drop_eq_nil_of_le (by grind), ← p₁.cons_tail_support]
    simp +arith [-cons_tail_support]
/-
**SimpleGraph.Walk.isSubwalk_iff_darts_isInfix** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：isSubwalk_iff_darts_isInfix {p₁ : G.Walk u v} {p₂ : G.Walk u' v'} (hnil : 
¬p₁.Nil) : p₁.IsSubwalk p₂ ↔ p₁.darts <:+: p₂.darts
参数：hnil : ¬p₁.Nil。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isSubwalk_iff_support_isInfix`：isSubwalk_iff_support_is
Infix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} : p₁.IsSubwalk p₂ ↔ 
p₁.support <:+: p₂.support
· 使用定理 `List.infix_iff_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁ <:+: l₂
 ↔ ∃ k, l₁.length + k ≤ l₂.length ∧ ∀ (i : ℕ) (h : i < l₁.length), l₂[i + k]? = 
some l₁[i]
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
· 使用定理 `SimpleGraph.Dart.ext`：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : G.Da
rt), d₁.toProd = d₂.toProd → d₁ = d₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem isSubwalk_iff_darts_isInfix {p₁ : G.Walk u v} {p₂ : G.Walk u' v'} (hnil : ¬p₁.Nil) :
    p₁.IsSubwalk p₂ ↔ p₁.darts <:+: p₂.darts := by
  rw [isSubwalk_iff_support_isInfix, List.infix_iff_getElem?, List.infix_iff_getElem?]
  refine ⟨fun ⟨k, hk, h⟩ ↦ ⟨k, by grind, fun i hi ↦ ?_⟩,
    fun ⟨k, hk, h⟩ ↦ ⟨k, by grind, fun i hi ↦ ?_⟩⟩
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    ext <;> grind [fst_darts_getElem, snd_darts_getElem]
  · rw [getElem?_pos _ _ <| by grind, Option.some_inj]
    by_cases hi' : i = p₁.length
    · have := h <| i - 1
      grind [not_nil_iff_lt_length, snd_darts_getElem]
    have := h i
    grind [fst_darts_getElem]

@[simp]
/-
**SimpleGraph.Walk.isSubwalk_nil_iff_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：isSubwalk_nil_iff_mem_support (p : G.Walk u v) : (nil : G.Walk v' v').IsSu
bwalk p ↔ v' in p.support
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SimpleGraph.Walk.isSubwalk_iff_support_isInfix`：isSubwalk_iff_support_is
Infix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} : p₁.IsSubwalk p₂ ↔ 
p₁.support <:+: p₂.support
· 使用定理 `List.singleton_infix_iff`：singleton_infix_iff (x : α) (xs : List α) : [x
] <:+: xs ↔ x in xs
-/
theorem isSubwalk_nil_iff_mem_support (p : G.Walk u v) :
    (nil : G.Walk v' v').IsSubwalk p ↔ v' ∈ p.support :=
  isSubwalk_iff_support_isInfix.trans <| p.support.singleton_infix_iff _
/-
**SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_darts** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：isSubwalk_toWalk_iff_mem_darts (p : G.Walk u v) (h : G.Adj u' v') : h.toWa
lk.IsSubwalk p ↔ ⟨⟨u', v'⟩, h⟩ in p.darts
参数：p : G.Walk u v；h : G.Adj u' v'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSubwalk_toWalk_iff_mem_darts (p : G.Walk u v) (h : G.Adj u' v') :
    h.toWalk.IsSubwalk p ↔ ⟨⟨u', v'⟩, h⟩ ∈ p.darts := by
  simp [isSubwalk_iff_darts_isInfix, List.singleton_infix_iff]
/-
**SimpleGraph.Walk.isSubwalk_toWalk_adj_iff_mem_darts** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk`。
形式化陈述：isSubwalk_toWalk_adj_iff_mem_darts {d : G.Dart} (p : G.Walk u v) : d.adj.t
oWalk.IsSubwalk p ↔ d in p.darts
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_darts`：isSubwalk_toWalk_iff_me
m_darts (p : G.Walk u v) (h : G.Adj u' v') : h.toWalk.IsSubwalk p ↔ ⟨⟨u', v'⟩, h
⟩ in p.darts
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
-/
theorem isSubwalk_toWalk_adj_iff_mem_darts {d : G.Dart} (p : G.Walk u v) :
    d.adj.toWalk.IsSubwalk p ↔ d ∈ p.darts :=
  isSubwalk_toWalk_iff_mem_darts ..
/-
**SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：isSubwalk_toWalk_iff_mem_edges {p : G.Walk u v} (h : G.Adj u' v') : h.toWa
lk.IsSubwalk p ∨ h.symm.toWalk.IsSubwalk p ↔ s(u', v') in p.edges
参数：h : G.Adj u' v'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_darts`：isSubwalk_toWalk_iff_me
m_darts (p : G.Walk u v) (h : G.Adj u' v') : h.toWalk.IsSubwalk p ↔ ⟨⟨u', v'⟩, h
⟩ in p.darts
· 使用定理 `SimpleGraph.Walk.edges.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u v : V
} (p : G.Walk u v), p.edges = List.map SimpleGraph.Dart.edge p.darts
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
· 使用定理 `Sym2.rel_iff'`：rel_iff' {p q : α × α} : Rel α p q ↔ p = q ∨ p = q.swap
· 使用定理 `Sym2.eq`：∀ {α : Type u_1} {a b c d : α}, s(a, b) = s(c, d) ↔ Sym2.Rel α 
(a, b) (c, d)
· 使用定理 `SimpleGraph.Dart.edge.eq_1`：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.
Dart), d.edge = s(d.toProd.1, d.toProd.2)
-/
theorem isSubwalk_toWalk_iff_mem_edges {p : G.Walk u v} (h : G.Adj u' v') :
    h.toWalk.IsSubwalk p ∨ h.symm.toWalk.IsSubwalk p ↔ s(u', v') ∈ p.edges := by
  rw [isSubwalk_toWalk_iff_mem_darts, isSubwalk_toWalk_iff_mem_darts, edges, List.mem_map]
  refine ⟨fun h ↦ by grind [Dart.edge], fun h ↦ ?_⟩
  have ⟨d, hd, h⟩ := h
  rw [Dart.edge, Sym2.eq, Sym2.rel_iff'] at h
  refine h.imp (fun h ↦ ?_) (fun h ↦ ?_)
    <;> convert! hd using 2
    <;> exact h.symm
/-
**SimpleGraph.Walk.infix_support_iff_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：infix_support_iff_mem_edges {p : G.Walk u v} : [u', v'] <:+: p.support ∨ [
v', u'] <:+: p.support ↔ s(u', v') in p.edges
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `SimpleGraph.Walk.adj_of_infix_support`：adj_of_infix_support {u v u' v'} 
{p : G.Walk u v} (h : [u', v'] <:+: p.support) : G.Adj u' v'
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_edges`：isSubwalk_toWalk_iff_me
m_edges {p : G.Walk u v} (h : G.Adj u' v') : h.toWalk.IsSubwalk p ∨ h.symm.toWal
k.IsSubwalk p ↔ s(u', v') in p.edges
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.adj_of_mem_edges`：adj_of_mem_edges {u v x y : V} (p : G
.Walk u v) (h : s(x, y) in p.edges) : G.Adj x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem infix_support_iff_mem_edges {p : G.Walk u v} :
    [u', v'] <:+: p.support ∨ [v', u'] <:+: p.support ↔ s(u', v') ∈ p.edges := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h.elim adj_of_infix_support (adj_of_infix_support · |>.symm)
    simpa [← isSubwalk_toWalk_iff_mem_edges this, isSubwalk_iff_support_isInfix]
  · have := (isSubwalk_toWalk_iff_mem_edges <| p.adj_of_mem_edges h).mpr h
    simpa [isSubwalk_iff_support_isInfix]
/-
**SimpleGraph.Walk.isSubwalk_antisymm** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：isSubwalk_antisymm {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ :
 p₂.IsSubwalk p₁) : p₁ = p₂
参数：h₁ : p₁.IsSubwalk p₂；h₂ : p₂.IsSubwalk p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用引理 `List.infix_antisymm`：infix_antisymm {l₁ l₂ : List α} (h₁ : l₁ <:+: l₂) (
h₂ : l₂ <:+: l₁) : l₁ = l₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isSubwalk_iff_support_isInfix`：isSubwalk_iff_support_is
Infix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} : p₁.IsSubwalk p₂ ↔ 
p₁.support <:+: p₂.support
-/
lemma isSubwalk_antisymm {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁) :
    p₁ = p₂ := by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
  exact ext_support <| List.infix_antisymm h₁ h₂

@[simp]
/-
**SimpleGraph.Walk.IsSubwalk.support_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk.IsSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂
 : G.Walk u' v'},   p₂.IsSubwalk p₁ → p₂.support ⊆ p₁.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsInfix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁ 
⊆ l₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isSubwalk_iff_support_isInfix`：isSubwalk_iff_support_is
Infix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} : p₁.IsSubwalk p₂ ↔ 
p₁.support <:+: p₂.support
-/
theorem IsSubwalk.support_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.support ⊆ p₁.support :=
  (isSubwalk_iff_support_isInfix.mp h).subset
/-
**SimpleGraph.Walk.IsSubwalk.edges_isInfix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk.IsSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂
 : G.Walk u' v'},   p₁.IsSubwalk p₂ → p₁.edges <:+: p₂.edges
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSubwalk.edges_isInfix {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₁.IsSubwalk p₂) : p₁.edges <:+: p₂.edges := by
  grind [edges_append, IsSubwalk]

@[simp]
/-
**SimpleGraph.Walk.IsSubwalk.edges_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk.IsSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂
 : G.Walk u' v'},   p₂.IsSubwalk p₁ → p₂.edges ⊆ p₁.edges
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsInfix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.IsSubwalk.edges_isInfix`：∀ {V : Type u_1} {G : SimpleGr
aph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'},   p₁.IsSubwalk p₂ 
→ p₁.edges <:+: p₂.edges
-/
theorem IsSubwalk.edges_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.edges ⊆ p₁.edges :=
  h.edges_isInfix.subset
/-
**SimpleGraph.Walk.IsSubwalk.darts_isInfix** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk.IsSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂
 : G.Walk u' v'},   p₁.IsSubwalk p₂ → p₁.darts <:+: p₂.darts
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSubwalk.darts_isInfix {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₁.IsSubwalk p₂) : p₁.darts <:+: p₂.darts := by
  grind [darts_append, IsSubwalk]

@[simp]
/-
**SimpleGraph.Walk.IsSubwalk.darts_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk.IsSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂
 : G.Walk u' v'},   p₂.IsSubwalk p₁ → p₂.darts ⊆ p₁.darts
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsInfix.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁ 
⊆ l₂
· 使用定理 `SimpleGraph.Walk.IsSubwalk.darts_isInfix`：∀ {V : Type u_1} {G : SimpleGr
aph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'},   p₁.IsSubwalk p₂ 
→ p₁.darts <:+: p₂.darts
-/
theorem IsSubwalk.darts_subset {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) : p₂.darts ⊆ p₁.darts :=
  h.darts_isInfix.subset
/-
**SimpleGraph.Walk.IsSubwalk.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsS
ubwalk`。
形式化陈述：∀ {V : Type u_1} {G G' : SimpleGraph V} {u v u' v' : V} {p₁ : G.Walk u v} 
{p₂ : G.Walk u' v'},   p₂.IsSubwalk p₁ → ∀ (f : G →g G'), (SimpleGraph.Walk.map 
f p₂).IsSubwalk (SimpleGraph.Walk.map f p₁)
参数：f : G →g G'；SimpleGraph.Walk.map f p₂；SimpleGraph.Walk.map f p₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isSubwalk_iff_support_isInfix`：isSubwalk_iff_support_is
Infix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} : p₁.IsSubwalk p₂ ↔ 
p₁.support <:+: p₂.support
-/
protected lemma IsSubwalk.map {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h : p₂.IsSubwalk p₁) (f : G →g G') : (p₂.map f).IsSubwalk (p₁.map f) := by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h, List.IsInfix.map]
/-
**SimpleGraph.Walk.IsSubwalk.copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Is
Subwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' x y x' y' : V} {p : G.Walk
 x y} {q : G.Walk u v},   p.IsSubwalk q → ∀ (hx : x = x') (hy : y = y') (hu : u 
= u') (hv : v = v'), (p.copy hx hy).IsSubwalk (q.copy hu hv)
参数：hx : x = x'；hy : y = y'；hu : u = u'；hv : v = v'；p.copy hx hy；q.copy hu hv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isSubwalk_iff_support_isInfix`：isSubwalk_iff_support_is
Infix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} : p₁.IsSubwalk p₂ ↔ 
p₁.support <:+: p₂.support
-/
protected lemma IsSubwalk.copy {u v u' v' x y x' y'} {p : G.Walk x y} {q : G.Walk u v}
    (h : p.IsSubwalk q) (hx : x = x') (hy : y = y') (hu : u = u') (hv : v = v') :
    (p.copy hx hy).IsSubwalk (q.copy hu hv) := by
  simp [isSubwalk_iff_support_isInfix, isSubwalk_iff_support_isInfix.mp h]
/-
**SimpleGraph.Walk.IsSubwalk.dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k.IsSubwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p : G.Walk u v} {q :
 G.Walk u' v'},   p.IsSubwalk q → p.dropLast.IsSubwalk q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsSubwalk.trans`：∀ {V : Type u_1} {G : SimpleGraph V} {
u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}   {p₃ : G.Walk u₃
 v₃}, p₁.IsSubwalk p₂ …
· 使用定理 `SimpleGraph.Walk.isSubwalk_take`：isSubwalk_take {u v : V} (p : G.Walk u 
v) (n : Nat) : (p.take n).IsSubwalk p
-/
protected lemma IsSubwalk.dropLast {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) : p.dropLast.IsSubwalk q :=
  (isSubwalk_take _ _).trans hpq
/-
**SimpleGraph.Walk.IsSubwalk.tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Is
Subwalk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v u' v' : V} {p : G.Walk u v} {q :
 G.Walk u' v'},   p.IsSubwalk q → p.tail.IsSubwalk q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsSubwalk.trans`：∀ {V : Type u_1} {G : SimpleGraph V} {
u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}   {p₃ : G.Walk u₃
 v₃}, p₁.IsSubwalk p₂ …
· 使用定理 `SimpleGraph.Walk.isSubwalk_drop`：isSubwalk_drop {u v : V} (p : G.Walk u 
v) (n : Nat) : (p.drop n).IsSubwalk p
-/
protected lemma IsSubwalk.tail {u v u' v'} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) : p.tail.IsSubwalk q :=
  (isSubwalk_drop _ _).trans hpq

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Walk.take_isSubwalk_take** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：take_isSubwalk_take {u v n k} (p : G.Walk u v) (h : n <= k) : (p.take n).I
sSubwalk (p.take k)
参数：p : G.Walk u v；h : n <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用引理 `SimpleGraph.Walk.isSubwalk_rfl`：isSubwalk_rfl {u v} (p : G.Walk u v) : p
.IsSubwalk p
· 使用定理 `SimpleGraph.Walk.IsSubwalk.trans`：∀ {V : Type u_1} {G : SimpleGraph V} {
u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}   {p₃ : G.Walk u₃
 v₃}, p₁.IsSubwalk p₂ …
· 使用定理 `SimpleGraph.Walk.isSubwalk_take`：isSubwalk_take {u v : V} (p : G.Walk u 
v) (n : Nat) : (p.take n).IsSubwalk p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `SimpleGraph.Walk.isSubwalk_of_append_left`：isSubwalk_of_append_left {v w
 u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u} (h : p₃ = p₁.appen
d p₂) : p₁.IsSubwalk p₃
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.support_take`：support_take {u v} (p : G.Walk u v) (n : 
Nat) : (p.take n).support = p.support.take (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem take_isSubwalk_take {u v n k} (p : G.Walk u v) (h : n ≤ k) :
    (p.take n).IsSubwalk (p.take k) := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply ih.trans
    cases p
    · exact isSubwalk_take _ _
    · cases k
      · exact isSubwalk_of_append_left rfl
      simp [isSubwalk_iff_support_isInfix, support_take, List.IsPrefix.isInfix]
/-
**SimpleGraph.Walk.drop_isSubwalk_drop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：drop_isSubwalk_drop {u v n k} (p : G.Walk u v) (h : n <= k) : (p.drop k).I
sSubwalk (p.drop n)
参数：p : G.Walk u v；h : n <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用引理 `SimpleGraph.Walk.isSubwalk_rfl`：isSubwalk_rfl {u v} (p : G.Walk u v) : p
.IsSubwalk p
· 使用定理 `SimpleGraph.Walk.IsSubwalk.trans`：∀ {V : Type u_1} {G : SimpleGraph V} {
u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}   {p₃ : G.Walk u₃
 v₃}, p₁.IsSubwalk p₂ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `SimpleGraph.Walk.IsSubwalk.tail`：∀ {V : Type u_1} {G : SimpleGraph V} {u
 v u' v' : V} {p : G.Walk u v} {q : G.Walk u' v'},   p.IsSubwalk q → p.tail.IsSu
bwalk q
· 使用定理 `SimpleGraph.Walk.IsSubwalk.copy`：∀ {V : Type u_1} {G : SimpleGraph V} {u
 v u' v' x y x' y' : V} {p : G.Walk x y} {q : G.Walk u v},   p.IsSubwalk q → ∀ (
hx : x = x') (hy : y …
· 使用引理 `SimpleGraph.Walk.drop_zero`：drop_zero {u v} (p : G.Walk u v) : p.drop 0 
= p.copy (getVert_zero p).symm rfl
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem drop_isSubwalk_drop {u v n k} (p : G.Walk u v) (h : n ≤ k) :
    (p.drop k).IsSubwalk (p.drop n) := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k h ih =>
    apply IsSubwalk.trans ?_ ih
    clear h ih
    induction k generalizing p u with
    | zero => exact p.drop_zero ▸ (p.isSubwalk_rfl.copy rfl rfl p.getVert_zero.symm rfl).tail
    | succ _ ih => cases p <;> simp [drop, ih]

end Walk

end SimpleGraph

