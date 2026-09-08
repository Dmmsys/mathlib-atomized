/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.List.Nodup
public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Batteries.Data.Fin.Lemmas
public import Mathlib.Data.Fin.SuccPred

/-!
# Additional theorems and definitions about the `Vector` type

This file introduces the infix notation `::ᵥ` for `Vector.cons`.
-/

@[expose] public section

universe u

variable {α β γ σ φ : Type*} {m n : ℕ}

namespace List.Vector

@[inherit_doc]
infixr:67 " ::ᵥ " => Vector.cons

/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩
/-
**List.Vector.toList_injective** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_injective : Function.Injective (@toList α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem toList_injective : Function.Injective (@toList α n) :=
  Subtype.val_injective

/-- Two `v w : Vector α n` are equal iff they are equal at every single index. -/
@[ext]
/-
**List.Vector.ext** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {v w : List.Vector α n}, (∀ (m : Fin n), v.get m 
= w.get m) → v = w
参数：∀ (m : Fin n), v.get m = w.get m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two `v w : Vector α n` are equal iff they are equal at every single index.
-/
theorem ext : ∀ {v w : Vector α n} (_ : ∀ m : Fin n, Vector.get v m = Vector.get w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.ext (List.ext_get (by rw [hv, hw]) fun m hm _ => h ⟨m, hv ▸ hm⟩)

/-- The empty `Vector` is a `Subsingleton`. -/
/-
**List.Vector.zero_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
形式化陈述：zero_subsingleton : Subsingleton (Vector α 0)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.ext`：∀ {α : Type u_1} {n : ℕ} {v w : List.Vector α n}, (∀ (m
 : Fin n), v.get m = w.get m) → v = w

--- 原说明 ---
The empty `Vector` is a `Subsingleton`.
-/
instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩

@[simp]
/-
**List.Vector.cons_val** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector α n), ↑(a ::ᵥ v) = a :: 
↑v
参数：a : α；v : List.Vector α n；a ::ᵥ v。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_val (a : α) : ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.eq_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) : v = a ::ᵥ v'
 ↔ v.head = a ∧ v.tail = v'
参数：a : α；v : Vector α n.succ；v' : Vector α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `List.Vector.tail_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).tail = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `List.Vector.cons_head_tail`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α 
n.succ), v.head ::ᵥ v.tail = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩
/-
**List.Vector.ne_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) : v != a ::ᵥ v
' ↔ v.head != a ∨ v.tail != v'
参数：a : α；v : Vector α n.succ；v' : Vector α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `List.Vector.eq_cons_iff`：eq_cons_iff (a : α) (v : Vector α n.succ) (v' :
 Vector α n) : v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v'
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v' := by rw [Ne, eq_cons_iff a v v', not_and_or]
/-
**List.Vector.exists_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：exists_eq_cons (v : Vector α n.succ) : exists (a : α) (as : Vector α n), v
 = a ::ᵥ as
参数：v : Vector α n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Vector.eq_cons_iff`：eq_cons_iff (a : α) (v : Vector α n.succ) (v' :
 Vector α n) : v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v'
-/
theorem exists_eq_cons (v : Vector α n.succ) : ∃ (a : α) (as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩

@[simp]
/-
**List.Vector.toList_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), (List.Vector.ofFn f).toList = Li
st.ofFn f
参数：f : Fin n → α；List.Vector.ofFn f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toList_ofFn : ∀ {n} (f : Fin n → α), toList (ofFn f) = List.ofFn f
  | 0, f => by rw [ofFn, List.ofFn_zero, toList, nil]
  | n + 1, f => by rw [ofFn, List.ofFn_succ, toList_cons, toList_ofFn]

@[simp]
/-
**List.Vector.mk_toList** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n) (h : v.toList.length = n), 
⟨v.toList, h⟩ = v
参数：v : List.Vector α n；h : v.toList.length = n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_toList : ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨_, _⟩, _ => rfl
/-
**List.Vector.length_val** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n), (↑v).length = n
参数：v : List.Vector α n；↑v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[simp] theorem length_val (v : Vector α n) : v.val.length = n := v.2

@[simp]
/-
**List.Vector.pmap_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：pmap_cons {p : α -> Prop} (f : (a : α) -> p a -> β) (a : α) (v : Vector α 
n) (hp : forall x in (cons a v).toList, p x) : (cons a v).pmap f hp = cons (f a 
(by simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp
] at hp exact hp.1)) (v.pmap f (by simp only [Nat.succ_eq_add_one, toList_cons, 
List.mem_cons, forall_eq_or_imp] at hp exact hp.2))
参数：f : (a : α) -> p a -> β；a : α；v : Vector α n；hp : forall x in (cons a v).toLi
st, p x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pmap_cons {p : α → Prop} (f : (a : α) → p a → β) (a : α) (v : Vector α n)
    (hp : ∀ x ∈ (cons a v).toList, p x) :
    (cons a v).pmap f hp = cons (f a (by
      simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp] at hp
      exact hp.1))
      (v.pmap f (by
        simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp] at hp
        exact hp.2)) := rfl

/-- Opposite direction of `Vector.pmap_cons` -/
/-
**List.Vector.pmap_cons'** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：pmap_cons' {p : α -> Prop} (f : (a : α) -> p a -> β) (a : α) (v : Vector α
 n) (ha : p a) (hp : forall x in v.toList, p x) : cons (f a ha) (v.pmap f hp) = 
(cons a v).pmap f (by simpa [ha])
参数：f : (a : α) -> p a -> β；a : α；v : Vector α n；ha : p a；hp : forall x in v.toLi
st, p x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Opposite direction of `Vector.pmap_cons`
-/
theorem pmap_cons' {p : α → Prop} (f : (a : α) → p a → β) (a : α) (v : Vector α n)
    (ha : p a) (hp : ∀ x ∈ v.toList, p x) :
    cons (f a ha) (v.pmap f hp) = (cons a v).pmap f (by simpa [ha]) := rfl

@[simp]
/-
**List.Vector.toList_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_map {β : Type*} (v : Vector α n) (f : α -> β) : (v.map f).toList = 
v.toList.map f
参数：v : Vector α n；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toList_map {β : Type*} (v : Vector α n) (f : α → β) :
    (v.map f).toList = v.toList.map f := by cases v; rfl

@[simp]
/-
**List.Vector.head_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：head_map {β : Type*} (v : Vector α (n + 1)) (f : α -> β) : (v.map f).head 
= f v.head
参数：v : Vector α (n + 1)；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.exists_eq_cons`：exists_eq_cons (v : Vector α n.succ) : exist
s (a : α) (as : Vector α n), v = a ::ᵥ as
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.map_cons`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β
) (a : α) (v : List.Vector α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Ve
ctor.map f…
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
-/
theorem head_map {β : Type*} (v : Vector α (n + 1)) (f : α → β) : (v.map f).head = f v.head := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, head_cons, head_cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.tail_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：tail_map {β : Type*} (v : Vector α (n + 1)) (f : α -> β) : (v.map f).tail 
= v.tail.map f
参数：v : Vector α (n + 1)；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.exists_eq_cons`：exists_eq_cons (v : Vector α n.succ) : exist
s (a : α) (as : Vector α n), v = a ::ᵥ as
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.map_cons`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} (f : α → β
) (a : α) (v : List.Vector α n),   List.Vector.map f (a ::ᵥ v) = f a ::ᵥ List.Ve
ctor.map f…
· 使用定理 `List.Vector.tail_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).tail = v
-/
theorem tail_map {β : Type*} (v : Vector α (n + 1)) (f : α → β) :
    (v.map f).tail = v.tail.map f := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, tail_cons, tail_cons]

@[simp]
/-
**List.Vector.getElem_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：getElem_map {β : Type*} (v : Vector α n) (f : α -> β) {i : Nat} (hi : i < 
n) : (v.map f)[i] = f v[i]
参数：v : Vector α n；f : α -> β；hi : i < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.toList_map`：toList_map {β : Type*} (v : Vector α n) (f : α -
> β) : (v.map f).toList = v.toList.map f
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getElem_map {β : Type*} (v : Vector α n) (f : α → β) {i : ℕ} (hi : i < n) :
    (v.map f)[i] = f v[i] := by
  simp only [getElem_def, toList_map, List.getElem_map]

@[simp]
/-
**List.Vector.toList_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α n) (hp
 : forall x in v.toList, p x) : (v.pmap f hp).toList = v.toList.pmap f hp
参数：f : (a : α) -> p a -> β；v : Vector α n；hp : forall x in v.toList, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toList_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α n)
    (hp : ∀ x ∈ v.toList, p x) :
    (v.pmap f hp).toList = v.toList.pmap f hp := by cases v; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.head_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：head_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
 (hp : forall x in v.toList, p x) : (v.pmap f hp).head = f v.head (hp _ <| by rw
 [← cons_head_tail v]; rw [toList_cons]; rw [head_cons]; rw [List.mem_cons]; exa
ct .inl rfl)
参数：f : (a : α) -> p a -> β；v : Vector α (n + 1)；hp : forall x in v.toList, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.exists_eq_cons`：exists_eq_cons (v : Vector α n.succ) : exist
s (a : α) (as : Vector α n), v = a ::ᵥ as
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.Vector.pmap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} {p 
: α → Prop} (f f_1 : (a : α) → p a → β),   f = f_1 →     ∀ (v v_1 : List.Vector 
α n) (e_v : v = v…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem head_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α (n + 1))
    (hp : ∀ x ∈ v.toList, p x) :
    (v.pmap f hp).head = f v.head (hp _ <| by
      rw [← cons_head_tail v, toList_cons, head_cons, List.mem_cons]; exact .inl rfl) := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, head_cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.tail_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：tail_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α (n + 1))
 (hp : forall x in v.toList, p x) : (v.pmap f hp).tail = v.tail.pmap f (fun x hx
 => hp _ <| by rw [← cons_head_tail v]; rw [toList_cons]; rw [List.mem_cons]; ex
act .inr hx)
参数：f : (a : α) -> p a -> β；v : Vector α (n + 1)；hp : forall x in v.toList, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.exists_eq_cons`：exists_eq_cons (v : Vector α n.succ) : exist
s (a : α) (as : Vector α n), v = a ::ᵥ as
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.Vector.pmap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {n : ℕ} {p 
: α → Prop} (f f_1 : (a : α) → p a → β),   f = f_1 →     ∀ (v v_1 : List.Vector 
α n) (e_v : v = v…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.tail_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).tail = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α (n + 1))
    (hp : ∀ x ∈ v.toList, p x) :
    (v.pmap f hp).tail = v.tail.pmap f (fun x hx ↦ hp _ <| by
      rw [← cons_head_tail v, toList_cons, List.mem_cons]; exact .inr hx) := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, tail_cons]

@[simp]
/-
**List.Vector.getElem_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：getElem_pmap {p : α -> Prop} (f : (a : α) -> p a -> β) (v : Vector α n) (h
p : forall x in v.toList, p x) {i : Nat} (hi : i < n) : (v.pmap f hp)[i] = f v[i
] (hp _ (by simp [getElem_def, List.getElem_mem]))
参数：f : (a : α) -> p a -> β；v : Vector α n；hp : forall x in v.toList, p x；hi : i 
< n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.toList_pmap`：toList_pmap {p : α -> Prop} (f : (a : α) -> p a
 -> β) (v : Vector α n) (hp : forall x in v.toList, p x) : (v.pmap f hp).toList 
= v.toList.pm…
· 使用定理 `List.length_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a
 : α) → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (List.pmap f l H).length = l
.lengt…
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_pmap`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (
a : α) → p a → β) {l : List α} (h : ∀ a ∈ l, p a) {i : ℕ}   (hn : i < (List.pmap
 f l h)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getElem_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α n)
    (hp : ∀ x ∈ v.toList, p x) {i : ℕ} (hi : i < n) :
    (v.pmap f hp)[i] = f v[i] (hp _ (by simp [getElem_def, List.getElem_mem])) := by
  simp only [getElem_def, toList_pmap, List.getElem_pmap]
/-
**List.Vector.get_eq_get_toList** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_eq_get_toList (v : Vector α n) (i : Fin n) : v.get i = v.toList.get (F
in.cast v.toList_length.symm i)
参数：v : Vector α n；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_eq_get_toList (v : Vector α n) (i : Fin n) :
    v.get i = v.toList.get (Fin.cast v.toList_length.symm i) :=
  rfl

@[simp]
/-
**List.Vector.get_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_replicate (a : α) (i : Fin n) : (Vector.replicate n a).get i = a
参数：a : α；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getElem_replicate`：∀ {α : Type u_1} {a : α} {n i : ℕ} (h : i < (Lis
t.replicate n a).length), (List.replicate n a)[i] = a
-/
theorem get_replicate (a : α) (i : Fin n) : (Vector.replicate n a).get i = a := by
  apply List.getElem_replicate

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.get_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_map {β : Type*} (v : Vector α n) (f : α -> β) (i : Fin n) : (v.map f).
get i = f (v.get i)
参数：v : Vector α n；f : α -> β；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_map {β : Type*} (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by
  cases v; simp [Vector.map, get_eq_get_toList]

@[simp]
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_nil (f : α → β → γ) : Vector.map₂ f nil nil = nil :=
  rfl

@[simp]
/-
**List.Vector.map** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {n : ℕ} → (α → β) → List.Vector α n → Li
st.Vector β n
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_cons (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α → β → γ) :
    Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂) = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂) :=
  rfl

@[simp]
/-
**List.Vector.get_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f i
参数：f : Fin n -> α；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.Vector.toList_ofFn`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), (List
.Vector.ofFn f).toList = List.ofFn f
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f i := by
  simp [get_eq_get_toList]

@[simp]
/-
**List.Vector.ofFn_get** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：ofFn_get (v : Vector α n) : ofFn (get v) = v
参数：v : Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.ext`：∀ {α : Type u_1} {n : ℕ} {v w : List.Vector α n}, (∀ (m
 : Fin n), v.get m = w.get m) → v = w
· 使用定理 `List.Vector.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i
 = f i
-/
theorem ofFn_get (v : Vector α n) : ofFn (get v) = v := by
  ext
  apply List.Vector.get_ofFn

/-- The natural equivalence between length-`n` vectors and functions from `Fin n`. -/
/-
**List.Vector._root_.Equiv.vectorEquivFin** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between length-`n` vectors and functions from `Fin n`.
-/
def _root_.Equiv.vectorEquivFin (α : Type*) (n : ℕ) : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩
/-
**List.Vector.get_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_tail (x : Vector α n) (i) : x.tail.get i = x.get ⟨i.1 + 1, by lia⟩
参数：x : Vector α n；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length.eq_1`：∀ {α : Type u_1}, [].length = 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem get_tail (x : Vector α n) (i) : x.tail.get i = x.get ⟨i.1 + 1, by lia⟩ := by
  obtain ⟨i, ih⟩ := i; dsimp
  rcases x with ⟨_ | _, h⟩ <;> try rfl
  rw [List.length] at h
  rw [← h] at ih
  contradiction

@[simp]
/-
**List.Vector.get_tail_succ** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ) (i : Fin n), v.tail.ge
t i = v.get i.succ
参数：v : List.Vector α n.succ；i : Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
-/
theorem get_tail_succ : ∀ (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [get_eq_get_toList]; rfl

@[simp]
/-
**List.Vector.tail_val** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ), ↑v.tail = (↑v).tail
参数：v : List.Vector α n.succ；↑v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_val : ∀ v : Vector α n.succ, v.tail.val = v.val.tail
  | ⟨_ :: _, _⟩ => rfl

/-- The `tail` of a `nil` vector is `nil`. -/
@[simp]
/-
**List.Vector.tail_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：tail_nil : (@nil α).tail = nil
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `tail` of a `nil` vector is `nil`.
-/
theorem tail_nil : (@nil α).tail = nil :=
  rfl

/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp]
/-
**List.Vector.singleton_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} (v : List.Vector α 1), v.tail = List.Vector.nil
参数：v : List.Vector α 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `tail` of a vector made up of one element is `nil`.
-/
theorem singleton_tail : ∀ (v : Vector α 1), v.tail = Vector.nil
  | ⟨[_], _⟩ => rfl

@[simp]
/-
**List.Vector.tail_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：tail_ofFn {n : Nat} (f : Fin n.succ -> α) : tail (ofFn f) = ofFn fun i => 
f i.succ
参数：f : Fin n.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.ofFn_get`：ofFn_get (v : Vector α n) : ofFn (get v) = v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.get_tail`：get_tail (x : Vector α n) (i) : x.tail.get i = x.g
et ⟨i.1 + 1, by lia⟩
· 使用定理 `List.Vector.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i
 = f i
-/
theorem tail_ofFn {n : ℕ} (f : Fin n.succ → α) : tail (ofFn f) = ofFn fun i => f i.succ :=
  (ofFn_get _).symm.trans <| by
    congr
    funext i
    rw [get_tail, get_ofFn]
    rfl
/-
**List.Vector.toList_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n), v.tail.toList = v.toList.t
ail
参数：v : List.Vector α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toList_tail : ∀ (v : Vector α n), v.tail.toList = v.toList.tail
  | ⟨[], _⟩     => by rfl
  | ⟨_ :: _, _⟩ => by rfl

@[simp]
/-
**List.Vector.toList_empty** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_empty (v : Vector α 0) : v.toList = []
参数：v : Vector α 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem toList_empty (v : Vector α 0) : v.toList = [] :=
  List.length_eq_zero_iff.mp v.2

/-- The list that makes up a `Vector` made up of a single element,
retrieved via `toList`, is equal to the list of that single element. -/
@[simp]
/-
**List.Vector.toList_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_singleton (v : Vector α 1) : v.toList = [v.head]
参数：v : Vector α 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.cons_head_tail`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α 
n.succ), v.head ::ᵥ v.tail = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.Vector.singleton_tail`：∀ {α : Type u_1} (v : List.Vector α 1), v.ta
il = List.Vector.nil
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The list that makes up a `Vector` made up of a single element,
retrieved via `toList`, is equal to the list of that single element.
-/
theorem toList_singleton (v : Vector α 1) : v.toList = [v.head] := by
  rw [← v.cons_head_tail]
  simp only [toList_cons, toList_nil, head_cons, singleton_tail]

@[simp]
/-
**List.Vector.empty_toList_eq_ff** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：empty_toList_eq_ff (v : Vector α (n + 1)) : v.toList.isEmpty = false
参数：v : Vector α (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_toList_eq_ff (v : Vector α (n + 1)) : v.toList.isEmpty = false :=
  match v with
  | ⟨_ :: _, _⟩ => rfl
/-
**List.Vector.not_empty_toList** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：not_empty_toList (v : Vector α (n + 1)) : ¬v.toList.isEmpty
参数：v : Vector α (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.empty_toList_eq_ff`：empty_toList_eq_ff (v : Vector α (n + 1)
) : v.toList.isEmpty = false
· 使用定理 `Bool.coe_sort_false`：coe_sort_false : (false : Prop) = False
-/
theorem not_empty_toList (v : Vector α (n + 1)) : ¬v.toList.isEmpty := by
  simp only [empty_toList_eq_ff, Bool.coe_sort_false, not_false_iff]

/-- Mapping under `id` does not change a vector. -/
@[simp]
/-
**List.Vector.map_id** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：map_id {n : Nat} (v : Vector α n) : Vector.map id v = v
参数：v : Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.eq`：∀ {α : Type u_1} {n : ℕ} (a1 a2 : List.Vector α n), a1.t
oList = a2.toList → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.toList_map`：toList_map {β : Type*} (v : Vector α n) (f : α -
> β) : (v.map f).toList = v.toList.map f
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping under `id` does not change a vector.
-/
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])
/-
**List.Vector.nodup_iff_injective_get** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：nodup_iff_injective_get {v : Vector α n} : v.toList.Nodup ↔ Function.Injec
tive v.get
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
-/
theorem nodup_iff_injective_get {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.get := by
  obtain ⟨l, rfl⟩ := v
  exact List.nodup_iff_injective_get
/-
**List.Vector.head** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → List.Vector α n.succ → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head?_toList : ∀ v : Vector α n.succ, (toList v).head? = some (head v)
  | ⟨_ :: _, _⟩ => rfl

/-- Reverse a vector. -/
/-
**List.Vector.reverse** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：reverse (v : Vector α n) : Vector α n
参数：v : Vector α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reverse a vector.
-/
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by simp⟩

/-- The `List` of a vector after a `reverse`, retrieved by `toList` is equal
to the `List.reverse` after retrieving a vector's `toList`. -/
/-
**List.Vector.toList_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `List` of a vector after a `reverse`, retrieved by `toList` is equal
to the `List.reverse` after retrieving a vector's `toList`.
-/
theorem toList_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.reverse_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：reverse_reverse {v : Vector α n} : v.reverse.reverse = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reverse_reverse {v : Vector α n} : v.reverse.reverse = v := by
  cases v
  simp [Vector.reverse]

@[simp]
/-
**List.Vector.get_zero** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ), v.get 0 = v.head
参数：v : List.Vector α n.succ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem get_zero : ∀ v : Vector α n.succ, get v 0 = head v
  | ⟨_ :: _, _⟩ => rfl

@[simp]
/-
**List.Vector.head_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：head_ofFn {n : Nat} (f : Fin n.succ -> α) : head (ofFn f) = f 0
参数：f : Fin n.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.get_zero`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ
), v.get 0 = v.head
· 使用定理 `List.Vector.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i
 = f i
-/
theorem head_ofFn {n : ℕ} (f : Fin n.succ → α) : head (ofFn f) = f 0 := by
  rw [← get_zero, get_ofFn]
/-
**List.Vector.get_cons_zero** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_cons_zero (a : α) (v : Vector α n) : get (a ::ᵥ v) 0 = a
参数：a : α；v : Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.get_zero`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ
), v.get 0 = v.head
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_cons_zero (a : α) (v : Vector α n) : get (a ::ᵥ v) 0 = a := by simp [get_zero]

/-- Accessing the nth element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
/-
**List.Vector.get_cons_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {ix : Fin 1} (x : α), (x ::ᵥ List.Vector.nil).get ix = x
参数：x : α；x ::ᵥ List.Vector.nil。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Accessing the nth element of a vector made up
of one element `x : α` is `x` itself.
-/
theorem get_cons_nil : ∀ {ix : Fin 1} (x : α), get (x ::ᵥ nil) ix = x
  | ⟨0, _⟩, _ => rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.get_cons_succ** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_cons_succ (a : α) (v : Vector α n) (i : Fin n) : get (a ::ᵥ v) i.succ 
= get v i
参数：a : α；v : Vector α n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.get_tail_succ`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n
.succ) (i : Fin n), v.tail.get i = v.get i.succ
· 使用定理 `List.Vector.tail_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).tail = v
-/
theorem get_cons_succ (a : α) (v : Vector α n) (i : Fin n) : get (a ::ᵥ v) i.succ = get v i := by
  rw [← get_tail_succ, tail_cons]

/-- The last element of a `Vector`, given that the vector is at least one element. -/
/-
**List.Vector.last** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：last (v : Vector α (n + 1)) : α
参数：v : Vector α (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The last element of a `Vector`, given that the vector is at least one element.
-/
def last (v : Vector α (n + 1)) : α :=
  v.get (Fin.last n)

/-- The last element of a `Vector`, given that the vector is at least one element. -/
/-
**List.Vector.last_def** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：last_def {v : Vector α (n + 1)} : v.last = v.get (Fin.last n)
参数：n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The last element of a `Vector`, given that the vector is at least one element.
-/
theorem last_def {v : Vector α (n + 1)} : v.last = v.get (Fin.last n) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
/-
**List.Vector.reverse_get_zero** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：reverse_get_zero {v : Vector α (n + 1)} : v.reverse.head = v.last
参数：n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.get_zero`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ
), v.get 0 = v.head
· 使用定理 `List.Vector.last_def`：last_def {v : Vector α (n + 1)} : v.last = v.get (
Fin.last n)
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `List.Vector.get_eq_get_toList`：get_eq_get_toList (v : Vector α n) (i : F
in n) : v.get i = v.toList.get (Fin.cast v.toList_length.symm i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_one_sub_lt_of_lt`：∀ {a b : ℕ}, a < b → b - 1 - a < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem_reverse`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i < l.r
everse.length), l.reverse[i] = l[l.length - 1 - i]
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `last` element of a vector is the `head` of the `reverse` vector.
-/
theorem reverse_get_zero {v : Vector α (n + 1)} : v.reverse.head = v.last := by
  rw [← get_zero, last_def, get_eq_get_toList, get_eq_get_toList]
  simp_rw [toList_reverse]
  simp

section Scan

variable {β : Type*}
variable (f : β → α → β) (b : β)
variable (v : Vector α n)

/-- Construct a `Vector β (n + 1)` from a `Vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `Fin.last n`, using `b : β` as the starting value.
-/
/-
**List.Vector.scanl** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：scanl : Vector β (n + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `Vector β (n + 1)` from a `Vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `Fin.last n`, using `b : β` as the starting 
value.
-/
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, toList_length]⟩

/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp]
/-
**List.Vector.scanl_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：scanl_nil : scanl f b nil = b ::ᵥ nil
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.ext`：∀ {α : Type u_1} {n : ℕ} {v w : List.Vector α n}, (∀ (m
 : Fin n), v.get m = w.get m) → v = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.scanl_nil`：∀ {β : Type u_1} {α : Type u_2} {init : β} {f : β → α → 
β}, List.scanl f init [] = [init]
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_singleton`：∀ {α : Type u_1} {a : α} {i : ℕ} (h : i < 1), [a
][i] = a
· 使用定理 `List.Vector.cons_val`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector 
α n), ↑(a ::ᵥ v) = a :: ↑v
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Providing an empty vector to `scanl` gives the starting value `b : β`.
-/
theorem scanl_nil : scanl f b nil = b ::ᵥ nil := by
  ext; simp [scanl, get]

set_option backward.isDefEq.respectTransparency false in
/-- The recursive step of `scanl` splits a vector `x ::ᵥ v : Vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_get`.
-/
@[simp]
/-
**List.Vector.scanl_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.eq`：∀ {α : Type u_1} {n : ℕ} (a1 a2 : List.Vector α n), a1.t
oList = a2.toList → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `List.scanl_cons`：∀ {β : Type u_1} {α : Type u_2} {b : β} {a : α} {l : Li
st α} {f : β → α → β},   List.scanl f b (a :: l) = b :: List.scanl f (f b a) l
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The recursive step of `scanl` splits a vector `x ::ᵥ v : Vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_get`.
-/
theorem scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v := by
  apply Vector.eq; simp [scanl]

/-- The underlying `List` of a `Vector` after a `scanl` is the `List.scanl`
of the underlying `List` of the original `Vector`.
-/
@[simp]
/-
**List.Vector.scanl_val** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {β : Type u_6} (f : β → α → β) (b : β) {v : List.
Vector α n},   ↑(List.Vector.scanl f b v) = List.scanl f b ↑v
参数：f : β → α → β；b : β；List.Vector.scanl f b v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying `List` of a `Vector` after a `scanl` is the `List.scanl`
of the underlying `List` of the original `Vector`.
-/
theorem scanl_val : ∀ {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val
  | _ => rfl

/-- The `toList` of a `Vector` after a `scanl` is the `List.scanl`
of the `toList` of the original `Vector`.
-/
@[simp]
/-
**List.Vector.toList_scanl** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_scanl : (scanl f b v).toList = List.scanl f b v.toList
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `toList` of a `Vector` after a `scanl` is the `List.scanl`
of the `toList` of the original `Vector`.
-/
theorem toList_scanl : (scanl f b v).toList = List.scanl f b v.toList :=
  rfl

/-- The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : Vector α 1` into a `Vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp]
/-
**List.Vector.scanl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil
参数：v : Vector α 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.cons_head_tail`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α 
n.succ), v.head ::ᵥ v.tail = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.Vector.singleton_tail`：∀ {α : Type u_1} (v : List.Vector α 1), v.ta
il = List.Vector.nil
· 使用定理 `List.Vector.scanl_cons`：scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ
 scanl f (f b x) v
· 使用定理 `List.Vector.scanl_nil`：scanl_nil : scanl f b nil = b ::ᵥ nil
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : Vector α 1` into a `Vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil := by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, head_cons, singleton_tail]

/-- The first element of `scanl` of a vector `v : Vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
/-
**List.Vector.scanl_head** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：scanl_head : (scanl f b v).head = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.scanl_nil`：scanl_nil : scanl f b nil = b ::ᵥ nil
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.cons_head_tail`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α 
n.succ), v.head ::ᵥ v.tail = v
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `List.Vector.scanl_cons`：scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ
 scanl f (f b x) v
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…

--- 原说明 ---
The first element of `scanl` of a vector `v : Vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
theorem scanl_head : (scanl f b v).head = b := by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, head_cons]
  · rw [← cons_head_tail v]
    simp [← get_zero, get_eq_get_toList]

set_option backward.isDefEq.respectTransparency false in
/-- For an index `i : Fin n`, the nth element of `scanl` of a
vector `v : Vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `castSucc i` element of
`scanl f b v` and `get v i`.

This lemma is the `get` version of `scanl_cons`.
-/
@[simp]
/-
**List.Vector.scanl_get** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：scanl_get (i : Fin n) : (scanl f b v).get i.succ = f ((scanl f b v).get (F
in.castSucc i)) (v.get i)
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.eq_zero`：eq_zero (n : Fin 1) : n = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.scanl_singleton`：scanl_singleton (v : Vector α 1) : scanl f 
b v = b ::ᵥ f b v.head ::ᵥ nil
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.Vector.get_zero`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n.succ
), v.get 0 = v.head
· 使用定理 `List.Vector.head_cons`：∀ {α : Type u_1} {n : ℕ} (a : α) (v : List.Vector
 α n), (a ::ᵥ v).head = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.Vector.toList_cons`：toList_cons (a : α) (v : Vector α n) : toList (
cons a v) = a :: toList v
· 使用定理 `List.Vector.toList_singleton`：toList_singleton (v : Vector α 1) : v.toLi
st = [v.head]
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.cons_head_tail`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α 
n.succ), v.head ::ᵥ v.tail = v
· 使用定理 `List.Vector.scanl_cons`：scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ
 scanl f (f b x) v
· 使用定理 `List.Vector.get_cons_succ`：get_cons_succ (a : α) (v : Vector α n) (i : F
in n) : get (a ::ᵥ v) i.succ = get v i
· 使用定理 `List.Vector.scanl_head`：scanl_head : (scanl f b v).head = b

--- 原说明 ---
For an index `i : Fin n`, the nth element of `scanl` of a
vector `v : Vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `castSucc i` element of
`scanl f b v` and `get v i`.

This lemma is the `get` version of `scanl_cons`.
-/
theorem scanl_get (i : Fin n) :
    (scanl f b v).get i.succ = f ((scanl f b v).get (Fin.castSucc i)) (v.get i) := by
  rcases n with - | n
  · exact i.elim0
  induction n generalizing b with
  | zero =>
    have i0 : i = 0 := Fin.eq_zero _
    simp [scanl_singleton, i0, get_zero]; simp [get_eq_get_toList]
  | succ n hn =>
    rw [← cons_head_tail v, scanl_cons, get_cons_succ]
    refine Fin.cases ?_ ?_ i
    · simp
    · intro i'
      simp only [hn, Fin.castSucc_succ, get_cons_succ]

end Scan

/-- Monadic analog of `Vector.ofFn`.
Given a monadic function on `Fin n`, return a `Vector α n` inside the monad. -/
/-
**List.Vector.mOfFn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{m : Type u → Type u_6} → [Monad m] → {α : Type u} → {n : ℕ} → (Fin n → m 
α) → m (List.Vector α n)
参数：Fin n → m α；List.Vector α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic analog of `Vector.ofFn`.
Given a monadic function on `Fin n`, return a `Vector α n` inside the monad.
-/
def mOfFn {m} [Monad m] {α : Type u} : ∀ {n}, (Fin n → m α) → m (Vector α n)
  | 0, _ => pure nil
  | _ + 1, f => do
    let a ← f 0
    let v ← mOfFn fun i => f i.succ
    pure (a ::ᵥ v)
/-
**List.Vector.mOfFn_pure** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {m : Type u_6 → Type u_7} [inst : Monad m] [LawfulMonad m] {α : Type u_6
} {n : ℕ} (f : Fin n → α),   (List.Vector.mOfFn fun i => pure (f i)) = pure (Lis
t.Vector.ofFn f)
参数：f : Fin n → α；List.Vector.mOfFn fun i => pure (f i)；List.Vector.ofFn f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mOfFn_pure {m} [Monad m] [LawfulMonad m] {α} :
    ∀ {n} (f : Fin n → α), (@mOfFn m _ _ _ fun i => pure (f i)) = pure (ofFn f)
  | 0, _ => rfl
  | n + 1, f => by
    rw [mOfFn, @mOfFn_pure m _ _ _ n _, ofFn]
    simp

/-- Apply a monadic function to each component of a vector,
returning a vector inside the monad. -/
/-
**List.Vector.mmap** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{m : Type u → Type u_6} →   [Monad m] → {α : Type u_7} → {β : Type u} → (α
 → m β) → {n : ℕ} → List.Vector α n → m (List.Vector β n)
参数：α → m β；List.Vector β n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a monadic function to each component of a vector,
returning a vector inside the monad.
-/
def mmap {m} [Monad m] {α} {β : Type u} (f : α → m β) : ∀ {n}, Vector α n → m (Vector β n)
  | 0, _ => pure nil
  | _ + 1, xs => do
    let h' ← f xs.head
    let t' ← mmap f xs.tail
    pure (h' ::ᵥ t')

@[simp]
/-
**List.Vector.mmap_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：mmap_nil {m} [Monad m] {α β} (f : α -> m β) : mmap f nil = pure nil
参数：f : α -> m β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mmap_nil {m} [Monad m] {α β} (f : α → m β) : mmap f nil = pure nil :=
  rfl

@[simp]
/-
**List.Vector.mmap_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {m : Type u_6 → Type u_7} [inst : Monad m] {α : Type u_8} {β : Type u_6}
 (f : α → m β) (a : α) {n : ℕ}   (v : List.Vector α n),   List.Vector.mmap f (a 
::ᵥ v) = do     let h' ← f a     let t' ← List.Vector.mmap f v     pure (h' ::ᵥ 
t')
参数：f : α → m β；a : α；v : List.Vector α n；a ::ᵥ v；h' ::ᵥ t'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mmap_cons {m} [Monad m] {α β} (f : α → m β) (a) :
    ∀ {n} (v : Vector α n),
      mmap f (a ::ᵥ v) = do
        let h' ← f a
        let t' ← mmap f v
        pure (h' ::ᵥ t')
  | _, ⟨_, rfl⟩ => rfl

/--
Define `C v` by induction on `v : Vector α n`.

This function has two arguments: `nil` handles the base case on `C nil`,
and `cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

It is used as the default induction principle for the `induction` tactic.
-/
@[elab_as_elim, induction_eliminator]
/-
**List.Vector.inductionOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：inductionOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vec
tor α n) (nil : C nil) (cons : forall {n : Nat} {x : α} {w : Vector α n}, C w ->
 C (x ::ᵥ w)) : C v
参数：v : Vector α n；nil : C nil；cons : forall {n : Nat} {x : α} {w : Vector α n}, 
C w -> C (x ::ᵥ w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `C v` by induction on `v : Vector α n`.

This function has two arguments: `nil` handles the base case on `C nil`,
and `cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

It is used as the default induction principle for the `induction` tactic.
-/
def inductionOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil) (cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) : C v := by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    exact cons (ih ⟨v, (add_left_inj 1).mp v_property⟩)

@[simp]
/-
**List.Vector.inductionOn_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：inductionOn_nil {C : forall {n : Nat}, Vector α n -> Sort*} (nil : C nil) 
(cons : forall {n : Nat} {x : α} {w : Vector α n}, C w -> C (x ::ᵥ w)) : Vector.
nil.inductionOn nil cons = nil
参数：nil : C nil；cons : forall {n : Nat} {x : α} {w : Vector α n}, C w -> C (x ::ᵥ
 w)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inductionOn_nil {C : ∀ {n : ℕ}, Vector α n → Sort*}
    (nil : C nil) (cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) :
    Vector.nil.inductionOn nil cons = nil :=
  rfl

@[simp]
/-
**List.Vector.inductionOn_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：inductionOn_cons {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (x 
: α) (v : Vector α n) (nil : C nil) (cons : forall {n : Nat} {x : α} {w : Vector
 α n}, C w -> C (x ::ᵥ w)) : (x ::ᵥ v).inductionOn nil cons = cons (v.inductionO
n nil cons : C v)
参数：x : α；v : Vector α n；nil : C nil；cons : forall {n : Nat} {x : α} {w : Vector 
α n}, C w -> C (x ::ᵥ w)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inductionOn_cons {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (x : α) (v : Vector α n)
    (nil : C nil) (cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) :
    (x ::ᵥ v).inductionOn nil cons = cons (v.inductionOn nil cons : C v) :=
  rfl

variable {β γ : Type*}

/-- Define `C v w` by induction on a pair of vectors `v : Vector α n` and `w : Vector β n`. -/
@[elab_as_elim]
/-
**List.Vector.inductionOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：inductionOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vec
tor α n) (nil : C nil) (cons : forall {n : Nat} {x : α} {w : Vector α n}, C w ->
 C (x ::ᵥ w)) : C v
参数：v : Vector α n；nil : C nil；cons : forall {n : Nat} {x : α} {w : Vector α n}, 
C w -> C (x ::ᵥ w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `C v w` by induction on a pair of vectors `v : Vector α n` and `w : Vecto
r β n`.
-/
def inductionOn₂ {C : ∀ {n}, Vector α n → Vector β n → Sort*}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil) (cons : ∀ {n a b} {x : Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) :
    C v w := by
  induction n with
  | zero =>
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, w_property⟩
    cases w_property
    apply @cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih

/-- Define `C u v w` by induction on a triplet of vectors
`u : Vector α n`, `v : Vector β n`, and `w : Vector γ b`. -/
@[elab_as_elim]
/-
**List.Vector.inductionOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：inductionOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vec
tor α n) (nil : C nil) (cons : forall {n : Nat} {x : α} {w : Vector α n}, C w ->
 C (x ::ᵥ w)) : C v
参数：v : Vector α n；nil : C nil；cons : forall {n : Nat} {x : α} {w : Vector α n}, 
C w -> C (x ::ᵥ w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `C u v w` by induction on a triplet of vectors
`u : Vector α n`, `v : Vector β n`, and `w : Vector γ b`.
-/
def inductionOn₃ {C : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort*}
    (u : Vector α n) (v : Vector β n) (w : Vector γ n) (nil : C nil nil nil)
    (cons : ∀ {n a b c} {x : Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  induction n with
  | zero =>
    rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  | succ n ih =>
    rcases u with ⟨_ | ⟨a, u⟩, u_property⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨c, w⟩, w_property⟩
    cases w_property
    apply
      @cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
        ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih

/-- Define `motive v` by case-analysis on `v : Vector α n`. -/
/-
**List.Vector.casesOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：casesOn {motive : forall {n}, Vector α n -> Sort*} (v : Vector α m) (nil :
 motive nil) (cons : forall {n}, (hd : α) -> (tl : Vector α n) -> motive (Vector
.cons hd tl)) : motive v
参数：v : Vector α m；nil : motive nil；cons : forall {n}, (hd : α) -> (tl : Vector α
 n) -> motive (Vector.cons hd tl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `motive v` by case-analysis on `v : Vector α n`.
-/
def casesOn {motive : ∀ {n}, Vector α n → Sort*} (v : Vector α m)
    (nil : motive nil)
    (cons : ∀ {n}, (hd : α) → (tl : Vector α n) → motive (Vector.cons hd tl)) :
    motive v :=
  inductionOn (C := motive) v nil @fun _ hd tl _ => cons hd tl

/-- Define `motive v₁ v₂` by case-analysis on `v₁ : Vector α n` and `v₂ : Vector β n`. -/
/-
**List.Vector.casesOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：casesOn {motive : forall {n}, Vector α n -> Sort*} (v : Vector α m) (nil :
 motive nil) (cons : forall {n}, (hd : α) -> (tl : Vector α n) -> motive (Vector
.cons hd tl)) : motive v
参数：v : Vector α m；nil : motive nil；cons : forall {n}, (hd : α) -> (tl : Vector α
 n) -> motive (Vector.cons hd tl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `motive v₁ v₂` by case-analysis on `v₁ : Vector α n` and `v₂ : Vector β n
`.
-/
def casesOn₂ {motive : ∀ {n}, Vector α n → Vector β n → Sort*} (v₁ : Vector α m) (v₂ : Vector β m)
    (nil : motive nil nil)
    (cons : ∀ {n}, (x : α) → (y : β) → (xs : Vector α n) → (ys : Vector β n)
      → motive (x ::ᵥ xs) (y ::ᵥ ys)) :
    motive v₁ v₂ :=
  inductionOn₂ (C := motive) v₁ v₂ nil @fun _ x y xs ys _ => cons x y xs ys

/-- Define `motive v₁ v₂ v₃` by case-analysis on `v₁ : Vector α n`, `v₂ : Vector β n`, and
    `v₃ : Vector γ n`. -/
/-
**List.Vector.casesOn** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：casesOn {motive : forall {n}, Vector α n -> Sort*} (v : Vector α m) (nil :
 motive nil) (cons : forall {n}, (hd : α) -> (tl : Vector α n) -> motive (Vector
.cons hd tl)) : motive v
参数：v : Vector α m；nil : motive nil；cons : forall {n}, (hd : α) -> (tl : Vector α
 n) -> motive (Vector.cons hd tl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define `motive v₁ v₂ v₃` by case-analysis on `v₁ : Vector α n`, `v₂ : Vector β n
`, and
    `v₃ : Vector γ n`.
-/
def casesOn₃ {motive : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort*} (v₁ : Vector α m)
    (v₂ : Vector β m) (v₃ : Vector γ m) (nil : motive nil nil nil)
    (cons : ∀ {n}, (x : α) → (y : β) → (z : γ) → (xs : Vector α n) → (ys : Vector β n)
      → (zs : Vector γ n) → motive (x ::ᵥ xs) (y ::ᵥ ys) (z ::ᵥ zs)) :
    motive v₁ v₂ v₃ :=
  inductionOn₃ (C := motive) v₁ v₂ v₃ nil @fun _ x y z xs ys zs _ => cons x y z xs ys zs

/-- Cast a vector to an array. -/
/-
**List.Vector.toArray** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{α : Type u_1} → {n : ℕ} → List.Vector α n → Array α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast a vector to an array.
-/
def toArray : Vector α n → Array α
  | ⟨xs, _⟩ => xs.toArray

section InsertIdx

variable {a : α}

/-- `v.insertIdx a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
/-
**List.Vector.insertIdx** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：insertIdx (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1)
参数：a : α；i : Fin (n + 1)；v : Vector α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`v.insertIdx a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right).
-/
def insertIdx (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertIdx i a, by
    rw [List.length_insertIdx, v.2]
    split <;> lia⟩
/-
**List.Vector.insertIdx_val** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：insertIdx_val {i : Fin (n + 1)} {v : Vector α n} : (v.insertIdx a i).val =
 v.val.insertIdx i.1 a
参数：n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insertIdx_val {i : Fin (n + 1)} {v : Vector α n} :
    (v.insertIdx a i).val = v.val.insertIdx i.1 a :=
  rfl

@[simp]
/-
**List.Vector.eraseIdx_val** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {i : Fin n} {v : List.Vector α n}, ↑(List.Vector.
eraseIdx i v) = (↑v).eraseIdx ↑i
参数：List.Vector.eraseIdx i v；↑v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eraseIdx_val {i : Fin n} : ∀ {v : Vector α n}, (eraseIdx i v).val = v.val.eraseIdx i
  | _ => rfl
/-
**List.Vector.eraseIdx_insertIdx_self** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：eraseIdx_insertIdx_self {v : Vector α n} {i : Fin (n + 1)} : eraseIdx i (i
nsertIdx a i v) = v
参数：n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `List.eraseIdx_insertIdx_self`：∀ {α : Type u} {i : ℕ} {l : List α} (a : α
), (l.insertIdx i a).eraseIdx i = l
-/
theorem eraseIdx_insertIdx_self {v : Vector α n} {i : Fin (n + 1)} :
    eraseIdx i (insertIdx a i v) = v :=
  Subtype.ext (List.eraseIdx_insertIdx_self ..)

set_option backward.isDefEq.respectTransparency false in
/-- Erasing an element after inserting an element, at different indices. -/
/-
**List.Vector.eraseIdx_insertIdx'** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {a : α} {v : List.Vector α (n + 1)} {i : Fin (n +
 1)} {j : Fin (n + 2)},   List.Vector.eraseIdx (j.succAbove i) (List.Vector.inse
rtIdx a j v) =     List.Vector.insertIdx a (i.predAbove j) (List.Vector.eraseIdx
 i v)
参数：n + 1；n + 1；n + 2；j.succAbove i；List.Vector.insertIdx a j v；i.predAbove j；Lis
t.Vector.eraseIdx i v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.insertIdx_eraseIdx_of_ge`：∀ {α : Type u} {a : α} {i j : ℕ} {as : Li
st α},   i < as.length → i ≤ j → (as.eraseIdx i).insertIdx j a = (as.insertIdx (
j + 1) a).eraseIdx …
· 使用定理 `List.Vector.length_val`：∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n), 
(↑v).length = n
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `Fin.pred_mk_succ'`：∀ {n : ℕ} (i : ℕ) (h₁ : i + 1 < n + 1 + 1) (h₂ : ⟨i +
 1, h₁⟩ ≠ 0), ⟨i + 1, h₁⟩.pred h₂ = ⟨i, ⋯⟩
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `List.insertIdx_eraseIdx_of_le`：∀ {α : Type u} {a : α} {i j : ℕ} {as : Li
st α},   i < as.length → j ≤ i → (as.eraseIdx i).insertIdx j a = (as.insertIdx j
 a).eraseIdx (i + 1…

--- 原说明 ---
Erasing an element after inserting an element, at different indices.
-/
theorem eraseIdx_insertIdx' {v : Vector α (n + 1)} :
    ∀ {i : Fin (n + 1)} {j : Fin (n + 2)},
      eraseIdx (j.succAbove i) (insertIdx a j v) = insertIdx a (i.predAbove j) (eraseIdx i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ => by
    dsimp [insertIdx, eraseIdx, Fin.succAbove, Fin.predAbove]
    rw [Subtype.mk_eq_mk]
    simp only [Fin.lt_def]
    split_ifs with hij
    · rcases Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.1 (lt_of_le_of_lt (Nat.zero_le _) hij)) with ⟨j, rfl⟩
      rw [← List.insertIdx_eraseIdx_of_ge]
      · simp; rfl
      · simpa
      · simpa [Nat.lt_succ_iff] using hij
    · dsimp
      rw [← List.insertIdx_eraseIdx_of_le]
      · rfl
      · simpa
      · simpa [not_lt] using hij
/-
**List.Vector.insertIdx_comm** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (a b : α) (i j : Fin (n + 1)),   i ≤ j →     ∀ (v
 : List.Vector α n),       List.Vector.insertIdx b j.succ (List.Vector.insertIdx
 a i v) =         List.Vector.insertIdx a i.castSucc (List.Vector.insertIdx b j 
v)
参数：a b : α；i j : Fin (n + 1)；v : List.Vector α n；List.Vector.insertIdx a i v；Lis
t.Vector.insertIdx b j v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `List.insertIdx_comm`：∀ {α : Type u} (a b : α) {i j : ℕ} {l : List α},   
i ≤ j → j ≤ l.length → (l.insertIdx i a).insertIdx (j + 1) b = (l.insertIdx j b)
.insertId…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem insertIdx_comm (a b : α) (i j : Fin (n + 1)) (h : i ≤ j) :
    ∀ v : Vector α n,
      (v.insertIdx a i).insertIdx b j.succ = (v.insertIdx b j).insertIdx a (Fin.castSucc i)
  | ⟨l, hl⟩ => by
    refine Subtype.ext ?_
    simp only [insertIdx_val, Fin.val_succ, Fin.castSucc, Fin.val_castAdd]
    apply List.insertIdx_comm
    · assumption
    · rw [hl]
      exact Nat.le_of_succ_le_succ j.2

end InsertIdx

section Set

/-- `set v n a` replaces the `n`th element of `v` with `a`. -/
/-
**List.Vector.set** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：set (v : Vector α n) (i : Fin n) (a : α) : Vector α n
参数：v : Vector α n；i : Fin n；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`set v n a` replaces the `n`th element of `v` with `a`.
-/
def set (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.set i.1 a, by simp⟩

@[simp]
/-
**List.Vector.toList_set** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：toList_set (v : Vector α n) (i : Fin n) (a : α) : (v.set i a).toList = v.t
oList.set i a
参数：v : Vector α n；i : Fin n；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toList_set (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList = v.toList.set i a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.get_set_same** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_set_same (v : Vector α n) (i : Fin n) (a : α) : (v.set i a).get i = a
参数：v : Vector α n；i : Fin n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_set_self`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α} (h 
: i < (l.set i a).length), (l.set i a)[i] = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_set_same (v : Vector α n) (i : Fin n) (a : α) : (v.set i a).get i = a := by
  cases v; cases i; simp [Vector.set, get_eq_get_toList]

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.get_set_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_set_of_ne {v : Vector α n} {i j : Fin n} (h : i != j) (a : α) : (v.set
 i a).get j = v.get j
参数：h : i != j；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_set_of_ne`：getElem_set_of_ne {l : List α} {i j : Nat} (h : 
i != j) (a : α) (hj : j < (l.set i a).length) : (l.set i a)[j] = l[j]'(by simpa 
using hj)
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
-/
theorem get_set_of_ne {v : Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
    (v.set i a).get j = v.get j := by
  cases v; cases i; cases j
  simp only [get_eq_get_toList, toList_set, toList_mk, Fin.cast_mk, List.get_eq_getElem]
  rw [List.getElem_set_of_ne]
  · simpa using h
/-
**List.Vector.get_set_eq_if** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_set_eq_if {v : Vector α n} {i j : Fin n} (a : α) : (v.set i a).get j =
 if i = j then a else v.get j
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Vector.get_set_same`：get_set_same (v : Vector α n) (i : Fin n) (a :
 α) : (v.set i a).get i = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `List.Vector.get_set_of_ne`：get_set_of_ne {v : Vector α n} {i j : Fin n} 
(h : i != j) (a : α) : (v.set i a).get j = v.get j
-/
theorem get_set_eq_if {v : Vector α n} {i j : Fin n} (a : α) :
    (v.set i a).get j = if i = j then a else v.get j := by
  split_ifs <;> (try simp [*]); rwa [get_set_of_ne]

@[to_additive]
/-
**List.Vector.prod_set** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：prod_set [Monoid α] (v : Vector α n) (i : Fin n) (a : α) : (v.set i a).toL
ist.prod = (v.take i).toList.prod * a * (v.drop (i + 1)).toList.prod
参数：v : Vector α n；i : Fin n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.prod_set`：∀ {M : Type u_4} [inst : Monoid M] (L : List M) (n : ℕ) (
a : M),   (L.set n a).prod = ((List.take n L).prod * if n < L.length then a else
 1)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `List.Vector.toList_take`：toList_take {n m : Nat} (v : Vector α m) : toLi
st (take n v) = List.take n (toList v)
· 使用定理 `List.Vector.toList_drop`：toList_drop {n m : Nat} (v : Vector α m) : toLi
st (drop n v) = List.drop n (toList v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_set [Monoid α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = (v.take i).toList.prod * a * (v.drop (i + 1)).toList.prod := by
  refine (List.prod_set v.toList i a).trans ?_
  simp_all

/-- Variant of `List.Vector.prod_set` that multiplies by the inverse of the replaced element -/
@[to_additive
  /-- Variant of `List.Vector.sum_set` that subtracts the inverse of the replaced element -/]
/-
**List.Vector.prod_set'** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：prod_set' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) : (v.set i a)
.toList.prod = v.toList.prod * (v.get i)⁻¹ * a
参数：v : Vector α n；i : Fin n；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.prod_set'`：prod_set' (L : List G) (n : Nat) (a : G) : (L.set n a).p
rod = L.prod * if hn : n < L.length then L[n]⁻¹ * a else 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_set' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = v.toList.prod * (v.get i)⁻¹ * a := by
  refine (List.prod_set' v.toList i a).trans ?_
  simp [get_eq_get_toList, mul_assoc]

end Set

end Vector

namespace Vector

section Traverse

variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]

open Applicative Functor

open List (cons)

open Nat

/-
**List.Vector.traverseAux** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def traverseAux {α β : Type u} (f : α → F β) : ∀ x : List α, F (Vector β x.length)
  | [] => pure Vector.nil
  | x :: xs => Vector.cons <$> f x <*> traverseAux f xs

/-- Apply an applicative function to each component of a vector. -/
/-
**List.Vector.traverse** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：{n : ℕ} → {F : Type u → Type u} → [Applicative F] → {α β : Type u} → (α → 
F β) → List.Vector α n → F (List.Vector β n)
参数：α → F β；List.Vector β n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply an applicative function to each component of a vector.
-/
@[no_expose] protected def traverse {α β : Type u} (f : α → F β) : Vector α n → F (Vector β n)
  | ⟨v, Hv⟩ => cast (by rw [Hv]) <| traverseAux f v

section

variable {α β : Type u}

@[simp]
/-
**List.Vector.traverse_def** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {n : ℕ} {F : Type u → Type u} [inst : Applicative F] {α β : Type u} (f :
 α → F β) (x : α) (xs : List.Vector α n),   List.Vector.traverse f (x ::ᵥ xs) = 
List.Vector.cons <$> f x <*> List.Vector.traverse f xs
参数：f : α → F β；x : α；xs : List.Vector α n；x ::ᵥ xs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem traverse_def (f : α → F β) (x : α) :
    ∀ xs : Vector α n, (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.id_traverse** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {n : ℕ} {α : Type u} (x : List.Vector α n), List.Vector.traverse pure x 
= pure x
参数：x : List.Vector α n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem id_traverse : ∀ x : Vector α n, x.traverse (pure : _ → Id _) = pure x := by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  induction x with | nil => rfl | cons x xs IH => simp! [IH]

end

open Function

variable [LawfulApplicative G]
variable {α β γ : Type u}

-- We need to turn off the linter here as
-- the `LawfulTraversable` instance below expects a particular signature.
@[nolint unusedArguments]
/-
**List.Vector.comp_traverse** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {n : ℕ} {F G : Type u → Type u} [inst : Applicative F] [inst_1 : Applica
tive G] [LawfulApplicative G] {α β γ : Type u}   (f : β → F γ) (g : α → G β) (x 
: List.Vector α n),   List.Vector.traverse (Functor.Comp.mk ∘ Functor.map f ∘ g)
 x =     Functor.Comp.mk (List.Vector.traverse f <$> List.Vector.traverse g x)
参数：f : β → F γ；g : α → G β；x : List.Vector α n；Functor.Comp.mk ∘ Functor.map f ∘
 g；List.Vector.traverse f <$> List.Vector.traverse g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `List.Vector.traverse_def`：∀ {n : ℕ} {F : Type u → Type u} [inst : Applic
ative F] {α β : Type u} (f : α → F β) (x : α) (xs : List.Vector α n),   List.Vec
tor.traverse f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `seq_map_assoc`：seq_map_assoc (x : F (α -> β)) (f : γ -> α) (y : F γ) : x
 <*> f < > y = (· ∘ f) < > x <*> y
· 使用定理 `map_seq`：map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) : f < > (x <*> 
y) = (f ∘ ·) < > x <*> y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : Vector α n) :
    Vector.traverse (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Vector.traverse f <$> Vector.traverse g x) := by
  induction x with
  | nil =>
    simp! [cast, *, functor_norm]
    rfl
  | cons ih =>
    rw [Vector.traverse_def, ih]
    simp [functor_norm, Function.comp_def]

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.traverse_eq_map_id** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {n : ℕ} {α β : Type u_6} (f : α → β) (x : List.Vector α n),   List.Vecto
r.traverse (pure ∘ f) x = pure (List.Vector.map f x)
参数：f : α → β；x : List.Vector α n；pure ∘ f；List.Vector.map f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem traverse_eq_map_id {α β} (f : α → β) :
    ∀ x : Vector α n, x.traverse ((pure : _ → Id _) ∘ f) = pure (map f x) := by
  rintro ⟨x, rfl⟩
  simp!
  induction x <;> simp! [*, functor_norm]
  rfl

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)
/-
**List.Vector.naturality** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {n : ℕ} {F G : Type u → Type u} [inst : Applicative F] [inst_1 : Applica
tive G] [LawfulApplicative G]   [LawfulApplicative F] (η : ApplicativeTransforma
tion F G) {α β : Type u} (f : α → F β) (x : List.Vector α n),   (fun {α} => η.ap
p α) (List.Vector.traverse f x) = List.Vector.traverse ((fun {α} => η.app α) ∘ f
) x
参数：η : ApplicativeTransformation F G；f : α → F β；x : List.Vector α n；fun {α} => 
η.app α；List.Vector.traverse f x；(fun {α} => η.app α) ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ApplicativeTransformation.preserves_pure`：preserves_pure {α} : forall x 
: α, η (pure x) = pure x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.Vector.traverse_def`：∀ {n : ℕ} {F : Type u → Type u} [inst : Applic
ative F] {α β : Type u} (f : α → F β) (x : α) (xs : List.Vector α n),   List.Vec
tor.traverse f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ApplicativeTransformation.preserves_seq`：preserves_seq {α β : Type u} : 
forall (x : F (α -> β)) (y : F α), η (x <*> y) = η x <*> η y
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
-/
protected theorem naturality {α β : Type u} (f : α → F β) (x : Vector α n) :
    η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  induction x with
  | nil => simp! [functor_norm, cast, η.preserves_pure]
  | cons ih =>
    rw [Vector.traverse_def, Vector.traverse_def, ← ih, η.preserves_seq, η.preserves_map]
    rfl

end Traverse

/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Traversable.{u} (flip Vector n) where
  traverse := @Vector.traverse n
  map {α β} := @Vector.map.{u, u} α β n

set_option backward.isDefEq.respectTransparency false in
/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulTraversable.{u} (flip Vector n) where
  id_traverse := @Vector.id_traverse n
  comp_traverse := Vector.comp_traverse
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := Vector.naturality
  id_map := by intro _ x; cases x; simp! [(· <$> ·)]
  comp_map := by intro _ _ _ _ _ x; cases x; simp! [(· <$> ·)]
  map_const := rfl

section Simp

variable {x : α} {y : β} {s : σ} (xs : Vector α n)

@[simp]
/-
**List.Vector.replicate_succ** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (val : α), List.Vector.replicate (n + 1) val = va
l ::ᵥ List.Vector.replicate n val
参数：val : α；n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicate_succ (val : α) :
    replicate (n + 1) val = val ::ᵥ (replicate n val) :=
  rfl

section Append
variable (ys : Vector α m)

/-
**List.Vector.get_append_cons_zero** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {m n : ℕ} {x : α} (xs : List.Vector α n) (ys : List.Vecto
r α m), (x ::ᵥ xs ++ ys).get 0 = x
参数：xs : List.Vector α n；ys : List.Vector α m；x ::ᵥ xs ++ ys。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd`：∀ {n m : ℕ} [h : NeZero n], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma get_append_cons_zero : get (x ::ᵥ xs ++ ys) 0 = x := rfl

@[simp]
/-
**List.Vector.get_append_cons_succ** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {m n : ℕ} {x : α} (xs : List.Vector α n) (ys : List.Vecto
r α m) {i : Fin (n + m)}   {h : ↑i + 1 < n.succ + m}, (x ::ᵥ xs ++ ys).get ⟨↑i +
 1, h⟩ = (xs ++ ys).get i
参数：xs : List.Vector α n；ys : List.Vector α m；n + m；x ::ᵥ xs ++ ys；xs ++ ys。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_append_cons_succ {i : Fin (n + m)} {h} :
    get (x ::ᵥ xs ++ ys) ⟨i+1, h⟩ = get (xs ++ ys) i :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**List.Vector.append_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (xs : List.Vector α n), xs ++ List.Vector.nil = x
s
参数：xs : List.Vector α n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem append_nil : xs ++ (nil : Vector α 0) = xs := by
  cases xs; simp only [append_def, append_nil]

end Append

variable (ys : Vector β n)

@[simp]
/-
**List.Vector.get_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：get_map {β : Type*} (v : Vector α n) (f : α -> β) (i : Fin n) : (v.map f).
get i = f (v.get i)
参数：v : Vector α n；f : α -> β；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Vector.toList_length`：toList_length (v : Vector α n) : (toList v).l
ength = n
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_map₂ (v₁ : Vector α n) (v₂ : Vector β n) (f : α → β → γ) (i : Fin n) :
    get (map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i) := by
  induction v₁, v₂ using inductionOn₂ with
  | nil =>
    exact Fin.elim0 i
  | cons ih =>
    rw [map₂_cons]
    cases i using Fin.cases
    · simp only [get_zero, head_cons]
    · simp only [get_cons_succ, ih]

@[simp]
/-
**List.Vector.mapAccumr_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Vector`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_4} {n : ℕ} {x : α} {s : σ} (xs
 : List.Vector α n) {f : α → σ → σ × β},   List.Vector.mapAccumr f (x ::ᵥ xs) s 
=     have r := List.Vector.mapAccumr f xs s;     have q := f x r.1;     (q.1, q
.2 ::ᵥ r.2)
参数：xs : List.Vector α n；x ::ᵥ xs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr_cons {f : α → σ → σ × β} :
    mapAccumr f (x ::ᵥ xs) s
    = let r := mapAccumr f xs s
      let q := f x r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

@[simp]
/-
**List.Vector.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List.Vector`。
形式化陈述：mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n | ⟨x, 
px⟩, c => let res
参数：f : α -> σ -> σ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_cons {f : α → β → σ → σ × φ} :
    mapAccumr₂ f (x ::ᵥ xs) (y ::ᵥ ys) s
    = let r := mapAccumr₂ f xs ys s
      let q := f x y r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl

end Simp

end List.Vector

