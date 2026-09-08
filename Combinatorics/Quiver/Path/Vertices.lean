/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.List.Basic

/-!
# Path Vertices

This file provides lemmas for reasoning about the vertices of a path.
-/

@[expose] public section

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V]

/-- The end vertex of a path. A path `p : Path a b` has `p.end = b`. -/
/-
**Quiver.Path.** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The end vertex of a path. A path `p : Path a b` has `p.end = b`.
-/
def «end» {a : V} : ∀ {b : V}, Path a b → V
  | b, _ => b

@[simp]
/-
**Quiver.Path.end_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：end_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : (p.cons e).end = c
参数：p : Path a b；e : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma end_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : (p.cons e).end = c := rfl

/-- The list of vertices in a path, including the start and end vertices. -/
/-
**Quiver.Path.vertices** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{V : Type u_1} → [inst : Quiver V] → {a b : V} → Quiver.Path a b → List V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list of vertices in a path, including the start and end vertices.
-/
def vertices {a : V} : ∀ {b : V}, Path a b → List V
  | _, nil => [a]
  | _, cons p e => (p.vertices).concat (p.cons e).end

@[simp]
/-
**Quiver.Path.vertices_nil** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_nil (a : V) : (nil : Path a a).vertices = [a]
参数：a : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma vertices_nil (a : V) : (nil : Path a a).vertices = [a] := rfl

@[simp]
/-
**Quiver.Path.vertices_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) : (p.cons e).vertices
 = p.vertices.concat c
参数：p : Path a b；e : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma vertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
  (p.cons e).vertices = p.vertices.concat c := rfl

/-- The vertex list of `cons` — convenient `simp` form. -/
/-
**Quiver.Path.mem_vertices_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：mem_vertices_cons {a b c : V} (p : Path a b) (e : b ⟶ c) {x : V} : x in (p
.cons e).vertices ↔ x in p.vertices ∨ x = c
参数：p : Path a b；e : b ⟶ c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The vertex list of `cons` — convenient `simp` form.
-/
lemma mem_vertices_cons {a b c : V} (p : Path a b)
    (e : b ⟶ c) {x : V} :
    x ∈ (p.cons e).vertices ↔ x ∈ p.vertices ∨ x = c := by
  simp only [vertices_cons]
  simp_all only [concat_eq_append, mem_append, mem_cons, not_mem_nil, or_false]
/-
**Quiver.Path.verticesSet_nil** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：verticesSet_nil {a : V} : {v | v in (nil : Path a a).vertices} = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
-/
lemma verticesSet_nil {a : V} : {v | v ∈ (nil : Path a a).vertices} = {a} := by
  simp only [vertices_nil, mem_singleton, Set.ext_iff, Set.mem_singleton_iff]
  exact fun x ↦ Set.mem_ofPred

/-- The length of vertices list equals path length plus one -/
@[simp]
/-
**Quiver.Path.vertices_length** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_length {V : Type*} [Quiver V] {a b : V} (p : Path a b) : p.vertic
es.length = p.length + 1
参数：p : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length

--- 原说明 ---
The length of vertices list equals path length plus one
-/
lemma vertices_length {V : Type*} [Quiver V] {a b : V} (p : Path a b) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil => simp
  | cons p' e ih =>
    simp [vertices_cons, length_cons, ih]
/-
**Quiver.Path.length_vertices_pos** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：length_vertices_pos {a b : V} (p : Path a b) : 0 < p.vertices.length
参数：p : Path a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.vertices_length`：vertices_length {V : Type*} [Quiver V] {a b
 : V} (p : Path a b) : p.vertices.length = p.length + 1
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma length_vertices_pos {a b : V} (p : Path a b) :
    0 < p.vertices.length := by simp
/-
**Quiver.Path.vertices_ne_nil** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_ne_nil {a : V} {b : V} (p : Path a b) : p.vertices != []
参数：p : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.vertices_length`：vertices_length {V : Type*} [Quiver V] {a b
 : V} (p : Path a b) : p.vertices.length = p.length + 1
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma vertices_ne_nil {a : V} {b : V} (p : Path a b) : p.vertices ≠ [] := by
  simp [← length_pos_iff_ne_nil]
/-
**Quiver.Path.start_mem_vertices** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：start_mem_vertices {a b : V} (p : Path a b) : a in p.vertices
参数：p : Path a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma start_mem_vertices {a b : V} (p : Path a b) : a ∈ p.vertices := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

/-- The head of the vertices list is the start vertex -/
@[simp]
/-
**Quiver.Path.vertices_head** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a
参数：p : Path a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head of the vertices list is the start vertex
-/
lemma vertices_head? {a b : V} (p : Path a b) : p.vertices.head? = some a := by
  induction p with
  | nil => simp only [vertices_nil, head?_cons]
  | cons p' e ih => simp [ih]

/-- The head of the vertices list is the start vertex. -/
@[simp]
/-
**Quiver.Path.vertices_head_eq** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_head_eq {a b : V} (p : Path a b) (h : p.vertices != []
参数：p : Path a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.vertices_ne_nil`：vertices_ne_nil {a : V} {b : V} (p : Path a
 b) : p.vertices != []
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.head.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = as_
1) (a : as ≠ []), as.head a = as_1.head ⋯
· 使用定理 `List.head_append_of_ne_nil`：∀ {α : Type u_1} {l' l : List α} {w₁ : l ++ 
l' ≠ []} (w₂ : l ≠ []), (l ++ l').head w₁ = l.head w₂

--- 原说明 ---
The head of the vertices list is the start vertex.
-/
lemma vertices_head_eq {a b : V} (p : Path a b) (h : p.vertices ≠ [] := p.vertices_ne_nil) :
    p.vertices.head h = a := by
  induction p with
  | nil => simp only [vertices_nil, head_cons]
  | cons p' _ ih => simp [head_append_of_ne_nil (vertices_ne_nil p'), ih]

@[simp]
/-
**Quiver.Path.getElem_vertices_zero** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：getElem_vertices_zero {a b : V} (p : Path a b) : p.vertices[0] = a
参数：p : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.vertices_length`：vertices_length {V : Type*} [Quiver V] {a b
 : V} (p : Path a b) : p.vertices.length = p.length + 1
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_append_left`：∀ {α : Type u_1} {i : ℕ} {as bs : List α} (h :
 i < as.length) {h' : i < (as ++ bs).length}, (as ++ bs)[i] = as[i]
-/
lemma getElem_vertices_zero {a b : V} (p : Path a b) : p.vertices[0] = a := by
  induction p with
  | nil => simp
  | cons p' e ih => simp [ih]

@[simp]
/-
**Quiver.Path.vertices_getLast** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_getLast {a b : V} (p : Path a b) (h : p.vertices != []
参数：p : Path a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `List.getLast_append_of_ne_nil`：∀ {α : Type u_1} {l' l : List α} (h₁ : l 
++ l' ≠ []) (h₂ : l' ≠ []), (l ++ l').getLast h₁ = l'.getLast h₂
-/
lemma vertices_getLast {a b : V} (p : Path a b) (h : p.vertices ≠ [] := p.vertices_ne_nil) :
    p.vertices.getLast h = b := by
  induction p with
  | nil => simp only [vertices_nil, getLast_singleton]
  | cons p' e ih => simp

@[simp]
/-
**Quiver.Path.dropLast_append_end_eq** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：dropLast_append_end_eq {a b : V} (p : Path a b) : p.vertices.dropLast ++ [
b] = p.vertices
参数：p : Path a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用引理 `Quiver.Path.vertices_ne_nil`：vertices_ne_nil {a : V} {b : V} (p : Path a
 b) : p.vertices != []
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Quiver.Path.vertices_getLast`：vertices_getLast {a b : V} (p : Path a b) 
(h : p.vertices != []
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.dropLast_concat_getLast`：∀ {α : Type u_1} {l : List α} (h : l ≠ [])
, l.dropLast ++ [l.getLast h] = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dropLast_append_end_eq {a b : V} (p : Path a b) :
    p.vertices.dropLast ++ [b] = p.vertices := by
  simp_rw [← p.vertices_getLast p.vertices_ne_nil, dropLast_concat_getLast]

@[simp]
/-
**Quiver.Path.vertices_comp** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_comp {a b c : V} (p : Path a b) (q : Path b c) : (p.comp q).verti
ces = p.vertices.dropLast ++ q.vertices
参数：p : Path a b；q : Path b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.dropLast_append_end_eq`：dropLast_append_end_eq {a b : V} (p 
: Path a b) : p.vertices.dropLast ++ [b] = p.vertices
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
lemma vertices_comp {a b c : V} (p : Path a b) (q : Path b c) :
  (p.comp q).vertices = p.vertices.dropLast ++ q.vertices := by
  induction q with
  | nil => simp
  | cons q' e ih => simp [ih]
/-
**Quiver.Path.length_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path`。
形式化陈述：∀ {V : Type u_1} [inst : Quiver V] {a : V} (p : Quiver.Path a a), p.length
 = 0 ↔ p = Quiver.Path.nil
参数：p : Quiver.Path a a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
@[simp] lemma length_eq_zero_iff {a : V} (p : Path a a) :
    p.length = 0 ↔ p = Path.nil := by
  cases p <;> tauto
/-
**Quiver.Path.vertices_comp_get_length_eq** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path
`。
形式化陈述：vertices_comp_get_length_eq {a b c : V} (p₁ : Path a c) (p₂ : Path c b) (h
 : p₁.length < (p₁.comp p₂).vertices.length
参数：p₁ : Path a c；p₂ : Path c b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用引理 `Quiver.Path.vertices_length`：vertices_length {V : Type*} [Quiver V] {a b
 : V} (p : Path a b) : p.vertices.length = p.length + 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Quiver.Path.vertices_comp`：vertices_comp {a b c : V} (p : Path a b) (q :
 Path b c) : (p.comp q).vertices = p.vertices.dropLast ++ q.vertices
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_append_right`：∀ {α : Type u_1} {as bs : List α} {i : ℕ} (h₁
 : as.length ≤ i) {h₂ : i < (as ++ bs).length},   (as ++ bs)[i] = bs[i - as.leng
th]
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用引理 `Quiver.Path.getElem_vertices_zero`：getElem_vertices_zero {a b : V} (p : 
Path a b) : p.vertices[0] = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vertices_comp_get_length_eq {a b c : V} (p₁ : Path a c) (p₂ : Path c b)
    (h : p₁.length < (p₁.comp p₂).vertices.length := by simp) :
    (p₁.comp p₂).vertices.get ⟨p₁.length, h⟩ = c := by
  simp

@[simp]
/-
**Quiver.Path.vertices_toPath** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_toPath {i j : V} (e : i ⟶ j) : e.toPath.vertices = [i, j]
参数：e : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vertices_toPath {i j : V} (e : i ⟶ j) :
    e.toPath.vertices = [i, j] := by
  change (Path.nil.cons e).vertices = [i, j]
  simp
/-
**Quiver.Path.vertices_toPath_tail** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：vertices_toPath_tail {i j : V} (e : i ⟶ j) : e.toPath.vertices.tail = [j]
参数：e : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.vertices_toPath`：vertices_toPath {i j : V} (e : i ⟶ j) : e.t
oPath.vertices = [i, j]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vertices_toPath_tail {i j : V} (e : i ⟶ j) :
    e.toPath.vertices.tail = [j] := by
  simp

/-- If a composition is `nil`, the left component must be `nil`
    (proved via lengths, avoiding dependent pattern-matching). -/
/-
**Quiver.Path.nil_of_comp_eq_nil_left** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：nil_of_comp_eq_nil_left {a b : V} {p : Path a b} {q : Path b a} (h : p.com
p q = Path.nil) : p.length = 0
参数：h : p.comp q = Path.nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.length_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p :
 Quiver.Path a b) {c : V} (q : Quiver.Path b c),   (p.comp q).length = p.length 
+ q.length
· 使用定理 `Nat.eq_zero_of_add_eq_zero_right`：∀ {n m : ℕ}, n + m = 0 → n = 0

--- 原说明 ---
If a composition is `nil`, the left component must be `nil`
    (proved via lengths, avoiding dependent pattern-matching).
-/
lemma nil_of_comp_eq_nil_left {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = Path.nil) : p.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_right this

/-- If a composition is `nil`, the right component must be `nil` -/
/-
**Quiver.Path.nil_of_comp_eq_nil_right** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：nil_of_comp_eq_nil_right {a b : V} {p : Path a b} {q : Path b a} (h : p.co
mp q = Path.nil) : q.length = 0
参数：h : p.comp q = Path.nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.length_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p :
 Quiver.Path a b) {c : V} (q : Quiver.Path b c),   (p.comp q).length = p.length 
+ q.length
· 使用定理 `Nat.eq_zero_of_add_eq_zero_left`：∀ {n m : ℕ}, n + m = 0 → m = 0

--- 原说明 ---
If a composition is `nil`, the right component must be `nil`
-/
lemma nil_of_comp_eq_nil_right {a b : V} {p : Path a b} {q : Path b a}
    (h : p.comp q = Path.nil) : q.length = 0 := by
  have hlen : (p.comp q).length = 0 := by
    simpa using congrArg Path.length h
  have : p.length + q.length = 0 := by
    simpa [length_comp] using hlen
  exact Nat.eq_zero_of_add_eq_zero_left this
/-
**Quiver.Path.comp_eq_nil_iff** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：comp_eq_nil_iff {a b : V} {p : Path a b} {q : Path b a} : p.comp q = Path.
nil ↔ p.length = 0 ∧ q.length = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.Path.nil_of_comp_eq_nil_left`：nil_of_comp_eq_nil_left {a b : V} {
p : Path a b} {q : Path b a} (h : p.comp q = Path.nil) : p.length = 0
· 使用引理 `Quiver.Path.nil_of_comp_eq_nil_right`：nil_of_comp_eq_nil_right {a b : V}
 {p : Path a b} {q : Path b a} (h : p.comp q = Path.nil) : q.length = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.nil_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p : Qu
iver.Path a b), Quiver.Path.nil.comp p = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quiver.Path.length_eq_zero_iff`：∀ {V : Type u_1} [inst : Quiver V] {a : 
V} (p : Quiver.Path a a), p.length = 0 ↔ p = Quiver.Path.nil
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma comp_eq_nil_iff {a b : V} {p : Path a b} {q : Path b a} :
    p.comp q = Path.nil ↔ p.length = 0 ∧ q.length = 0 := by
  refine ⟨fun h ↦ ⟨nil_of_comp_eq_nil_left h, nil_of_comp_eq_nil_right h⟩, fun ⟨hp, hq⟩ ↦ ?_⟩
  induction p with
  | nil => simpa using (length_eq_zero_iff q).mp hq
  | cons p' _ ihp => simp at hp

@[simp]
/-
**Quiver.Path.end_mem_vertices** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：end_mem_vertices {a b : V} (p : Path a b) : b in p.vertices
参数：p : Path a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用引理 `Quiver.Path.vertices_ne_nil`：vertices_ne_nil {a : V} {b : V} (p : Path a
 b) : p.vertices != []
· 使用引理 `Quiver.Path.vertices_getLast`：vertices_getLast {a b : V} (p : Path a b) 
(h : p.vertices != []
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma end_mem_vertices {a b : V} (p : Path a b) : b ∈ p.vertices := by
  have h₁ : p.vertices.getLast (vertices_ne_nil p) = b :=
    vertices_getLast p (vertices_ne_nil p)
  have h₂ := getLast_mem (l := p.vertices) (vertices_ne_nil p)
  simpa [h₁] using h₂

/-!  ### Path vertices decomposition -/
section

variable {a b : V} (p : Path a b)

open List

/-- Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`. -/
/-
**Quiver.Path.exists_eq_comp_of_le_length** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Path
`。
形式化陈述：exists_eq_comp_of_le_length {n : Nat} (hn : n <= p.length) : exists (v : V
) (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ ∧ p₁.length = n
参数：hn : n <= p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_succ_iff`：∀ {m n : ℕ}, m ≤ n.succ ↔ m ≤ n ∨ m = n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.length_cons`：length_cons (a b c : V) (p : Path a b) (e : b ⟶
 c) : (p.cons e).length = p.length + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`.
-/
theorem exists_eq_comp_of_le_length {n : ℕ} (hn : n ≤ p.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ p₁.length = n := by
  induction p generalizing n with
  | nil =>
    obtain ⟨rfl⟩ : n = 0 := by simpa using hn
    exact ⟨a, Path.nil, Path.nil, by simp, rfl⟩
  | @cons _ c p' e ih =>
    rw [length_cons] at hn
    rcases (Nat.le_succ_iff).1 hn with h | rfl
    · obtain ⟨d, p₁, p₂, hp, hl⟩ := ih h
      exact ⟨d, p₁, p₂.cons e, by simp [hp], hl⟩
    · exact ⟨c, p'.cons e, Path.nil, by simp, by simp⟩

/-- `split_at_vertex` decomposes a path `p` at the vertex sitting in
    position `i` of its `vertices` -/
/-
**Quiver.Path.exists_eq_comp_and_length_eq_of_lt_length** 是 Mathlib 中的一个定理，位于命名空
间 `Quiver.Path`。
形式化陈述：exists_eq_comp_and_length_eq_of_lt_length (n : Nat) (hn : n < p.vertices.l
ength) : exists (v : V) (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ ∧ p₁.len
gth = n ∧ v = p.vertices[n]
参数：n : Nat；hn : n < p.vertices.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.vertices_length`：vertices_length {V : Type*} [Quiver V] {a b
 : V} (p : Path a b) : p.vertices.length = p.length + 1
· 使用定理 `Quiver.Path.exists_eq_comp_of_le_length`：exists_eq_comp_of_le_length {n 
: Nat} (hn : n <= p.length) : exists (v : V) (p₁ : Path a v) (p₂ : Path v b), p 
= p₁.comp p₂ ∧ p₁.length = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Quiver.Path.vertices_comp`：vertices_comp {a b c : V} (p : Path a b) (q :
 Path b c) : (p.comp q).vertices = p.vertices.dropLast ++ q.vertices
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_append_right`：∀ {α : Type u_1} {as bs : List α} {i : ℕ} (h₁
 : as.length ≤ i) {h₂ : i < (as ++ bs).length},   (as ++ bs)[i] = bs[i - as.leng
th]
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用引理 `Quiver.Path.getElem_vertices_zero`：getElem_vertices_zero {a b : V} (p : 
Path a b) : p.vertices[0] = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`split_at_vertex` decomposes a path `p` at the vertex sitting in
    position `i` of its `vertices`
-/
theorem exists_eq_comp_and_length_eq_of_lt_length (n : ℕ) (hn : n < p.vertices.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ p₁.length = n ∧ v = p.vertices[n] := by
  have hn_le_len : n ≤ p.length := by
    rw [vertices_length] at hn
    exact Nat.le_of_lt_succ hn
  obtain ⟨v, p₁, p₂, rfl, rfl⟩ := p.exists_eq_comp_of_le_length hn_le_len
  exact ⟨v, p₁, p₂, rfl, rfl, by simp⟩

/-- If a vertex `v` occurs in the list of vertices of a path `p : Path a b`, then `p` can be
decomposed as a concatenation of a subpath from `a` to `v` and a subpath from `v` to `b`. -/
/-
**Quiver.Path.exists_eq_comp_of_mem_vertices** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.P
ath`。
形式化陈述：exists_eq_comp_of_mem_vertices {v : V} (hv : v in p.vertices) : exists (p₁
 : Path a v) (p₂ : Path v b), p = p₁.comp p₂
参数：hv : v in p.vertices。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.exists_mem_iff_getElem`：exists_mem_iff_getElem {l : List α} {p : α 
-> Prop} : (exists x in l, p x) ↔ exists (i : Nat) (_ : i < l.length), p l[i]
· 使用定理 `Quiver.Path.exists_eq_comp_and_length_eq_of_lt_length`：exists_eq_comp_an
d_length_eq_of_lt_length (n : Nat) (hn : n < p.vertices.length) : exists (v : V)
 (p₁ : Path a v) (p₂ : Path v b), p = p₁.co…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a vertex `v` occurs in the list of vertices of a path `p : Path a b`, then `p
` can be
decomposed as a concatenation of a subpath from `a` to `v` and a subpath from `v
` to `b`.
-/
theorem exists_eq_comp_of_mem_vertices {v : V} (hv : v ∈ p.vertices) :
    ∃ (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ := by
  obtain ⟨n, hn, rfl⟩ : ∃ n, ∃ hn : n < p.vertices.length, v = p.vertices[n] :=
    exists_mem_iff_getElem.mp ⟨v, hv, rfl⟩
  obtain ⟨v, p₁, p₂, hp, hv, rfl⟩ := p.exists_eq_comp_and_length_eq_of_lt_length n hn
  exact ⟨p₁, p₂, hp⟩

/-- Split a path at the *last* occurrence of a vertex. -/
/-
**Quiver.Path.exists_eq_comp_and_notMem_tail_of_mem_vertices** 是 Mathlib 中的一个定理，
位于命名空间 `Quiver.Path`。
形式化陈述：exists_eq_comp_and_notMem_tail_of_mem_vertices {v : V} (hv : v in p.vertic
es) : exists (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ ∧ v ∉ p₂.vertices.t
ail
参数：hv : v in p.vertices。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Quiver.Path.mem_vertices_cons`：mem_vertices_cons {a b c : V} (p : Path a
 b) (e : b ⟶ c) {x : V} : x in (p.cons e).vertices ↔ x in p.vertices ∨ x = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Split a path at the *last* occurrence of a vertex.
-/
theorem exists_eq_comp_and_notMem_tail_of_mem_vertices {v : V} (hv : v ∈ p.vertices) :
    ∃ (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
  induction p with
  | nil =>
    have hxa : v = a := by
      simpa [vertices_nil, List.mem_singleton] using hv
    subst hxa
    exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
      by simp only [vertices_nil, tail_cons, not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
    have hv' : v ∈ pPrev.vertices ∨ v = (pPrev.cons e).end := by
      simpa using (mem_vertices_cons pPrev e).1 hv
    have h_case₁ : v = (pPrev.cons e).end → ∃ (p₁ : Path a v) (p₂ : Path v (pPrev.cons e).end),
        pPrev.cons e = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
      rintro rfl
      exact ⟨pPrev.cons e, Path.nil, by simp [comp_nil], by simp [vertices_nil]⟩
    have h_case₂ : v ∈ pPrev.vertices → v ≠ (pPrev.cons e).end →
        ∃ (p₁ : Path a v) (p₂ : Path v (pPrev.cons e).end),
          pPrev.cons e = p₁.comp p₂ ∧ v ∉ p₂.vertices.tail := by
      intro hxPrev hxe_ne
      obtain ⟨q₁, q₂, h_prev, h_not_tail⟩ := ih hxPrev
      let q₂' : Path v (pPrev.cons e).end := q₂.cons e
      have h_no_tail : v ∉ q₂'.vertices.tail := by grind [vertices_cons, end_cons]
      exact ⟨q₁, q₂', by simp [q₂', h_prev], h_no_tail⟩
    cases hv' with
    | inl h_in_prefix =>
      by_cases h_eq_end : v = (pPrev.cons e).end
      · exact h_case₁ h_eq_end
      · exact h_case₂ h_in_prefix h_eq_end
    | inr h_eq_end => exact h_case₁ h_eq_end

end

end Quiver.Path

