/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Order.CompleteLattice.SetLike

/-!
# Trees in the sense of descriptive set theory

This file defines trees of depth `ω` in the sense of descriptive set theory as sets of finite
sequences that are stable under taking prefixes.

## Main declarations

* `tree A`: a (possibly infinite) tree of depth at most `ω` with nodes in `A`
-/

@[expose] public section

namespace Descriptive

/-- A tree is a set of finite sequences, implemented as `List A`, that is stable under
  taking prefixes. For the definition we use the equivalent property `x ++ [a] ∈ T → x ∈ T`,
  which is more convenient to check. We define `tree A` as a complete sublattice of
  `Set (List A)`, which coerces to the type of trees on `A`. -/
/-
**Descriptive.tree** 是 Mathlib 中的一个定义，位于命名空间 `Descriptive`。
形式化陈述：tree (A : Type*) : CompleteSublattice (Set (List A))
参数：A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tree is a set of finite sequences, implemented as `List A`, that is stable und
er
  taking prefixes. For the definition we use the equivalent property `x ++ [a] ∈
 T → x ∈ T`,
  which is more convenient to check. We define `tree A` as a complete sublattice
 of
  `Set (List A)`, which coerces to the type of trees on `A`.
-/
def tree (A : Type*) : CompleteSublattice (Set (List A)) :=
  CompleteSublattice.mk' {T | ∀ ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] ∈ T → x ∈ T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)
/-
**Descriptive.** 是 Mathlib 中的一个实例，位于命名空间 `Descriptive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps!] instance (A : Type*) : SetLike (tree A) (List A) := SetLike.instSubtypeSet
/-
**Descriptive.** 是 Mathlib 中的一个示例，位于命名空间 `Descriptive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (A : Type*) : PartialOrder (tree A) := inferInstance

namespace Tree
variable {A : Type*} {S T : tree A}

/-
**Descriptive.Tree.mem_of_append** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tree`。
形式化陈述：mem_of_append {x y : List A} (h : x ++ y in T) : x in T
参数：h : x ++ y in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
lemma mem_of_append {x y : List A} (h : x ++ y ∈ T) : x ∈ T := by
  induction y generalizing x with
  | nil => simpa using h
  | cons y ys ih => exact T.prop (ih (by simpa))
/-
**Descriptive.Tree.mem_of_prefix** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tree`。
形式化陈述：mem_of_prefix {x y : List A} (h' : x <+: y) (h : y in T) : x in T
参数：h' : x <+: y；h : y in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Descriptive.Tree.mem_of_append`：mem_of_append {x y : List A} (h : x ++ y
 in T) : x in T
-/
lemma mem_of_prefix {x y : List A} (h' : x <+: y) (h : y ∈ T) : x ∈ T := by
  obtain ⟨_, rfl⟩ := h'; exact mem_of_append h
/-
**Descriptive.Tree.** 是 Mathlib 中的一个实例，位于命名空间 `Descriptive.Tree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans List.IsPrefix (fun x (T : tree A) ↦ x ∈ T) (fun x T ↦ x ∈ T) where
  trans := mem_of_prefix
/-
**Descriptive.Tree.singleton_mem** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tree`。
形式化陈述：singleton_mem (T : tree A) {a : A} {x : List A} (h : a :: x in T) : [a] in
 T
参数：T : tree A；h : a :: x in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Descriptive.Tree.mem_of_prefix`：mem_of_prefix {x y : List A} (h' : x <+:
 y) (h : y in T) : x in T
-/
lemma singleton_mem (T : tree A) {a : A} {x : List A} (h : a :: x ∈ T) : [a] ∈ T :=
  mem_of_prefix ⟨x, rfl⟩ h
/-
**Descriptive.Tree.tree_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} {T : ↥(Descriptive.tree A)}, T = ⊥ ↔ [] ∉ T
参数：Descriptive.tree A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CompleteSublattice.ext`：∀ {X : Type u_1} {L : CompleteSublattice (Set X)
} {S T : ↥L}, (∀ (x : X), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用引理 `Descriptive.Tree.mem_of_prefix`：mem_of_prefix {x y : List A} (h' : x <+:
 y) (h : y in T) : x in T
· 使用定理 `List.nil_prefix`：∀ {α : Type u_1} {l : List α}, [] <+: l
-/
@[simp] lemma tree_eq_bot : T = ⊥ ↔ [] ∉ T where
  mp := by rintro rfl; simp
  mpr h := by ext x; simpa using fun h' ↦ h <| mem_of_prefix x.nil_prefix h'
/-
**Descriptive.Tree.take_mem** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tree`。
形式化陈述：take_mem {n : Nat} (x : T) : x.val.take n in T
参数：x : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Descriptive.Tree.mem_of_prefix`：mem_of_prefix {x y : List A} (h' : x <+:
 y) (h : y in T) : x in T
· 使用定理 `List.take_prefix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take i l <
+: l
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma take_mem {n : ℕ} (x : T) : x.val.take n ∈ T :=
  mem_of_prefix (x.val.take_prefix n) x.prop

/-- A variant of `List.take` internally to a tree -/
/-
**Descriptive.Tree.take** 是 Mathlib 中的一个定义，位于命名空间 `Descriptive.Tree`。
形式化陈述：{A : Type u_1} → {T : ↥(Descriptive.tree A)} → ℕ → ↥T → ↥T
参数：Descriptive.tree A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Descriptive.Tree.take_mem`：take_mem {n : Nat} (x : T) : x.val.take n in 
T

--- 原说明 ---
A variant of `List.take` internally to a tree
-/
@[simps] def take (n : ℕ) (x : T) : T := ⟨x.val.take n, take_mem x⟩
/-
**Descriptive.Tree.take_take** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} {T : ↥(Descriptive.tree A)} (m n : ℕ) (x : ↥T),   Descrip
tive.Tree.take m (Descriptive.Tree.take n x) = Descriptive.Tree.take (min m n) x
参数：Descriptive.tree A；m n : ℕ；x : ↥T；Descriptive.Tree.take n x；min m n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Descriptive.Tree.take_coe`：∀ {A : Type u_1} {T : ↥(Descriptive.tree A)} 
(n : ℕ) (x : ↥T), ↑(Descriptive.Tree.take n x) = List.take n ↑x
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A variant of `List.take` internally to a tree
-/
@[simp] lemma take_take (m n : ℕ) (x : T) : take m (take n x) = take (m ⊓ n) x := by
  simp [Subtype.ext_iff, List.take_take]
/-
**Descriptive.Tree.take_eq_take** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} {T : ↥(Descriptive.tree A)} {x : ↥T} {m n : ℕ},   Descrip
tive.Tree.take m x = Descriptive.Tree.take n x ↔ min m (↑x).length = min n (↑x).
length
参数：Descriptive.tree A；↑x；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Descriptive.Tree.take_coe`：∀ {A : Type u_1} {T : ↥(Descriptive.tree A)} 
(n : ℕ) (x : ↥T), ↑(Descriptive.Tree.take n x) = List.take n ↑x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma take_eq_take {x : T} {m n : ℕ} :
    take m x = take n x ↔ m ⊓ x.val.length = n ⊓ x.val.length := by simp [Subtype.ext_iff]

-- ### `subAt`

variable (T) (x y : List A)

/-- The residual tree obtained by regarding the node x as new root -/
/-
**Descriptive.Tree.subAt** 是 Mathlib 中的一个定义，位于命名空间 `Descriptive.Tree`。
形式化陈述：subAt : tree A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residual tree obtained by regarding the node x as new root
-/
def subAt : tree A :=
  ⟨(x ++ ·)⁻¹' T, fun _ a _ ↦ mem_of_append (y := [a]) (by rwa [List.append_assoc])⟩
/-
**Descriptive.Tree.mem_subAt** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} (T : ↥(Descriptive.tree A)) (x y : List A), y ∈ Descripti
ve.Tree.subAt T x ↔ x ++ y ∈ T
参数：T : ↥(Descriptive.tree A)；x y : List A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_subAt : y ∈ subAt T x ↔ x ++ y ∈ T := Iff.rfl
/-
**Descriptive.Tree.subAt_nil** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} (T : ↥(Descriptive.tree A)), Descriptive.Tree.subAt T [] 
= T
参数：T : ↥(Descriptive.tree A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma subAt_nil : subAt T [] = T := rfl
/-
**Descriptive.Tree.subAt_append** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} (T : ↥(Descriptive.tree A)) (x y : List A),   Descriptive
.Tree.subAt (Descriptive.Tree.subAt T x) y = Descriptive.Tree.subAt T (x ++ y)
参数：T : ↥(Descriptive.tree A)；x y : List A；Descriptive.Tree.subAt T x；x ++ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.ext`：∀ {X : Type u_1} {L : CompleteSublattice (Set X)
} {S T : ↥L}, (∀ (x : X), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma subAt_append : subAt (subAt T x) y = subAt T (x ++ y) := by ext; simp
/-
**Descriptive.Tree.subAt_mono** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} {S : ↥(Descriptive.tree A)} (T : ↥(Descriptive.tree A)) (
x : List A),   S ≤ T → Descriptive.Tree.subAt S x ≤ Descriptive.Tree.subAt T x
参数：Descriptive.tree A；T : ↥(Descriptive.tree A)；x : List A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
@[gcongr] lemma subAt_mono (h : S ≤ T) : subAt S x ≤ subAt T x :=
  Set.preimage_mono h

/-- A variant of `List.drop` that takes values in `subAt` -/
/-
**Descriptive.Tree.drop** 是 Mathlib 中的一个定义，位于命名空间 `Descriptive.Tree`。
形式化陈述：{A : Type u_1} →   (T : ↥(Descriptive.tree A)) → (n : ℕ) → (x : ↥T) → ↥(De
scriptive.Tree.subAt T ↑(Descriptive.Tree.take n x))
参数：T : ↥(Descriptive.tree A)；n : ℕ；x : ↥T；Descriptive.Tree.subAt T ↑(Descriptive
.Tree.take n x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `List.drop` that takes values in `subAt`
-/
@[simps] def drop (n : ℕ) (x : T) : subAt T (Tree.take n x).val :=
  ⟨x.val.drop n, by simp⟩

-- ### `pullSub`

/-- Adjoint of `subAt`, given by pasting x before the root of T. Explicitly,
  elements are prefixes of x or x with an element of T appended -/
/-
**Descriptive.Tree.pullSub** 是 Mathlib 中的一个定义，位于命名空间 `Descriptive.Tree`。
形式化陈述：pullSub : tree A where val
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoint of `subAt`, given by pasting x before the root of T. Explicitly,
  elements are prefixes of x or x with an element of T appended
-/
def pullSub : tree A where
  val := { y | y.take x.length <+: x ∧ y.drop x.length ∈ T }
  property := fun y a ⟨h1, h2⟩ ↦
    ⟨((y.prefix_append [a]).take x.length).trans h1,
    mem_of_prefix ((y.prefix_append [a]).drop x.length) h2⟩

variable {T x y}

set_option backward.isDefEq.respectTransparency false in
/-
**Descriptive.Tree.mem_pullSub_short** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tree
`。
形式化陈述：mem_pullSub_short (hl : y.length <= x.length) : y in pullSub T x ↔ y <+: x
 ∧ [] in T
参数：hl : y.length <= x.length。
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
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.drop_eq_nil_iff`：∀ {α : Type u_1} {l : List α} {i : ℕ}, List.drop i
 l = [] ↔ l.length ≤ i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_pullSub_short (hl : y.length ≤ x.length) : y ∈ pullSub T x ↔ y <+: x ∧ [] ∈ T := by
  simp [pullSub, List.take_of_length_le hl, List.drop_eq_nil_iff.mpr hl]

set_option backward.isDefEq.respectTransparency false in
/-
**Descriptive.Tree.mem_pullSub_long** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tree`
。
形式化陈述：mem_pullSub_long (hl : x.length <= y.length) : y in pullSub T x ↔ exists z
 in T, y = x ++ z where mp
参数：hl : x.length <= y.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `List.append_cancel_right_eq`：∀ {α : Type u_1} (as bs cs : List α), (as +
+ bs = cs ++ bs) = (as = cs)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `List.take_length`：∀ {α : Type u_1} {l : List α}, List.take l.length l = 
l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.take_left'`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, l₁.length = 
i → List.take i (l₁ ++ l₂) = l₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.drop_left'`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, l₁.length = 
i → List.drop i (l₁ ++ l₂) = l₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma mem_pullSub_long (hl : x.length ≤ y.length) : y ∈ pullSub T x ↔ ∃ z ∈ T, y = x ++ z where
  mp := by
    intro ⟨h1, h2⟩; use y.drop x.length, h2
    nth_rw 1 [← List.take_append_drop x.length y]
    simpa [-List.take_append_drop, List.prefix_iff_eq_take, hl] using h1
  mpr := by simp +contextual [pullSub]
/-
**Descriptive.Tree.mem_pullSub_append** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tre
e`。
形式化陈述：∀ {A : Type u_1} {T : ↥(Descriptive.tree A)} {x y : List A}, x ++ y ∈ Desc
riptive.Tree.pullSub T x ↔ y ∈ T
参数：Descriptive.tree A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.append_cancel_left_eq`：∀ {α : Type u_1} (as bs cs : List α), (as ++
 bs = as ++ cs) = (bs = cs)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_pullSub_append : x ++ y ∈ pullSub T x ↔ y ∈ T := by simp [mem_pullSub_long]
/-
**Descriptive.Tree.mem_pullSub_self** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`
。
形式化陈述：∀ {A : Type u_1} {T : ↥(Descriptive.tree A)} {x : List A}, x ∈ Descriptive
.Tree.pullSub T x ↔ [] ∈ T
参数：Descriptive.tree A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `Descriptive.Tree.mem_pullSub_append`：∀ {A : Type u_1} {T : ↥(Descriptive
.tree A)} {x y : List A}, x ++ y ∈ Descriptive.Tree.pullSub T x ↔ y ∈ T
-/
@[simp] lemma mem_pullSub_self : x ∈ pullSub T x ↔ [] ∈ T := by
  simpa using mem_pullSub_append (y := [])


variable (T x y)
/-
**Descriptive.Tree.pullSub_subAt** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tree`。
形式化陈述：pullSub_subAt : pullSub (subAt T x) x <= T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `Descriptive.Tree.mem_of_prefix`：mem_of_prefix {x y : List A} (h' : x <+:
 y) (h : y in T) : x in T
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Descriptive.Tree.mem_pullSub_short`：mem_pullSub_short (hl : y.length <= 
x.length) : y in pullSub T x ↔ y <+: x ∧ [] in T
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Descriptive.Tree.mem_pullSub_long`：mem_pullSub_long (hl : x.length <= y.
length) : y in pullSub T x ↔ exists z in T, y = x ++ z where mp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pullSub_subAt : pullSub (subAt T x) x ≤ T := by
  intro y (h : y ∈ pullSub _ x); rcases le_total y.length x.length with h' | h'
  · rw [mem_pullSub_short h'] at h; exact mem_of_prefix h.1 (by simpa using h.2)
  · rw [mem_pullSub_long h'] at h; obtain ⟨_, h, rfl⟩ := h; exact h
/-
**Descriptive.Tree.subAt_pullSub** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} (T : ↥(Descriptive.tree A)) (x : List A), Descriptive.Tre
e.subAt (Descriptive.Tree.pullSub T x) x = T
参数：T : ↥(Descriptive.tree A)；x : List A；Descriptive.Tree.pullSub T x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.ext`：∀ {X : Type u_1} {L : CompleteSublattice (Set X)
} {S T : ↥L}, (∀ (x : X), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma subAt_pullSub : subAt (pullSub T x) x = T := by
  ext y; simp
/-
**Descriptive.Tree.pullSub_mono** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} {S : ↥(Descriptive.tree A)} (T : ↥(Descriptive.tree A)), 
  S ≤ T → ∀ (x : List A), Descriptive.Tree.pullSub S x ≤ Descriptive.Tree.pullSu
b T x
参数：Descriptive.tree A；T : ↥(Descriptive.tree A)；x : List A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] lemma pullSub_mono (h : S ≤ T) x : pullSub S x ≤ pullSub T x :=
  fun _ ⟨h1, h2⟩ ↦ ⟨h1, h h2⟩
/-
**Descriptive.Tree.pullSub_adjunction** 是 Mathlib 中的一个引理，位于命名空间 `Descriptive.Tre
e`。
形式化陈述：pullSub_adjunction (S T : tree A) (x : List A) : pullSub S x <= T ↔ S <= s
ubAt T x where mp _
参数：S T : tree A；x : List A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Descriptive.Tree.subAt_pullSub`：∀ {A : Type u_1} (T : ↥(Descriptive.tree
 A)) (x : List A), Descriptive.Tree.subAt (Descriptive.Tree.pullSub T x) x = T
· 使用定理 `Descriptive.Tree.subAt_mono`：∀ {A : Type u_1} {S : ↥(Descriptive.tree A)
} (T : ↥(Descriptive.tree A)) (x : List A),   S ≤ T → Descriptive.Tree.subAt S x
 ≤ Descriptive.Tr…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Descriptive.Tree.pullSub_mono`：∀ {A : Type u_1} {S : ↥(Descriptive.tree 
A)} (T : ↥(Descriptive.tree A)),   S ≤ T → ∀ (x : List A), Descriptive.Tree.pull
Sub S x ≤ Descripti…
· 使用引理 `Descriptive.Tree.pullSub_subAt`：pullSub_subAt : pullSub (subAt T x) x <=
 T
-/
lemma pullSub_adjunction (S T : tree A) (x : List A) : pullSub S x ≤ T ↔ S ≤ subAt T x where
  mp _ := by rw [← subAt_pullSub S x]; gcongr
  mpr _ := le_trans (by gcongr) (pullSub_subAt T x)
/-
**Descriptive.Tree.pullSub_nil** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} (T : ↥(Descriptive.tree A)), Descriptive.Tree.pullSub T [
] = T
参数：T : ↥(Descriptive.tree A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pullSub_nil : pullSub T [] = T := by simp [pullSub]

set_option backward.isDefEq.respectTransparency false in
/-
**Descriptive.Tree.pullSub_append** 是 Mathlib 中的一个定理，位于命名空间 `Descriptive.Tree`。
形式化陈述：∀ {A : Type u_1} (T : ↥(Descriptive.tree A)) (x y : List A),   Descriptive
.Tree.pullSub (Descriptive.Tree.pullSub T y) x = Descriptive.Tree.pullSub T (x +
+ y)
参数：T : ↥(Descriptive.tree A)；x y : List A；Descriptive.Tree.pullSub T y；x ++ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.ext`：∀ {X : Type u_1} {L : CompleteSublattice (Set X)
} {S T : ↥L}, (∀ (x : X), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `List.take_left'`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, l₁.length = 
i → List.take i (l₁ ++ l₂) = l₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.drop_left'`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, l₁.length = 
i → List.drop i (l₁ ++ l₂) = l₂
· 使用定理 `List.drop_length_add_append`：∀ {α : Type u_1} {l₁ l₂ : List α} (i : ℕ), 
List.drop (l₁.length + i) (l₁ ++ l₂) = List.drop i l₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.take_add`：∀ {α : Type u_1} {l : List α} {i j : ℕ}, List.take (i + j
) l = List.take i l ++ List.take j (List.drop i l)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.prefix_iff_eq_take`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ ↔ 
l₁ = List.take l₁.length l₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.IsPrefix.eq_of_length`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂
 → l₁.length = l₂.length → l₁ = l₂
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `List.take_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.take i (Li
st.take j l) = List.take (min i j) l
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `List.IsPrefix.take`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → ∀ (n 
: ℕ), List.take n l₁ <+: List.take n l₂
· 使用引理 `Descriptive.Tree.mem_pullSub_short`：mem_pullSub_short (hl : y.length <= 
x.length) : y in pullSub T x ↔ y <+: x ∧ [] in T
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `List.isPrefix_append_of_length`：isPrefix_append_of_length (h : l₁.length
 <= l₂.length) : l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂
-/
@[simp] lemma pullSub_append : pullSub (pullSub T y) x = pullSub T (x ++ y) := by
  ext z; rcases le_total x.length z.length with hl | hl
  · by_cases hp : x <+: z
    · obtain ⟨z, rfl⟩ := hp
      simp [pullSub, List.take_add]
    · constructor <;> intro ⟨h, _⟩ <;>
        [skip; replace h := by simpa [List.take_take] using h.take x.length] <;>
        cases hp <| List.prefix_iff_eq_take.mpr (h.eq_of_length (by simpa)).symm
  · rw [mem_pullSub_short hl, mem_pullSub_short (by simp), mem_pullSub_short (by simp; lia)]
    simpa using fun _ ↦ (z.isPrefix_append_of_length hl).symm

end Descriptive.Tree

