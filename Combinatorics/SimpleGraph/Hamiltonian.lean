/-
Copyright (c) 2023 Bhavik Mehta, Rishi Mehta, Linus Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Rishi Mehta, Linus Sommer, Yue Sun
-/
module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

/-!
# Hamiltonian Graphs

In this file we introduce Hamiltonian paths, cycles and graphs.

## Main definitions

- `SimpleGraph.Walk.IsHamiltonian`: Predicate for a walk to be Hamiltonian.
- `SimpleGraph.Walk.IsHamiltonianCycle`: Predicate for a walk to be a Hamiltonian cycle.
- `SimpleGraph.IsHamiltonian`: Predicate for a graph to be Hamiltonian.
-/

@[expose] public section

open Finset Function

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
variable {β : Type*} [DecidableEq β] {H : SimpleGraph β}
variable {a b v : α} {p : G.Walk a b} {f : G →g H}

namespace Walk

/-- A Hamiltonian path is a walk `p` that visits every vertex exactly once. Note that while
this definition doesn't contain that `p` is a path, `p.isPath` gives that. -/
/-
**SimpleGraph.Walk.IsHamiltonian** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：IsHamiltonian (p : G.Walk a b) : Prop
参数：p : G.Walk a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hamiltonian path is a walk `p` that visits every vertex exactly once. Note tha
t while
this definition doesn't contain that `p` is a path, `p.isPath` gives that.
-/
def IsHamiltonian (p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1

variable (f) in
/-
**SimpleGraph.Walk.IsHamiltonian.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {β : Type u_2}
 [inst_1 : DecidableEq β] {H : SimpleGraph β}   {a b : α} {p : G.Walk a b} (f : 
G →g H),   Function.Bijective ⇑f → p.IsHamiltonian → (SimpleGraph.Walk.map f p).
IsHamiltonian
参数：f : G →g H；SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `List.count_map_of_injective`：count_map_of_injective [BEq β] [LawfulBEq β
] (l : List α) (f : α -> β) (hf : Function.Injective f) (x : α) : count (f x) (m
ap f l) = count x…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsHamiltonian.map (hf : Bijective f) (hp : p.IsHamiltonian) :
    (p.map f).IsHamiltonian := by
  simp [IsHamiltonian, hf.surjective.forall, hf.injective, hp _]

/-- A Hamiltonian path visits every vertex. -/
/-
**SimpleGraph.Walk.IsHamiltonian.mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b},   p.IsHamiltonian → ∀ (c : α), c ∈ p.support
参数：c : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.one_le_count_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a 
: α} {l : List α}, 1 ≤ List.count a l ↔ a ∈ l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A Hamiltonian path visits every vertex.
-/
@[simp] lemma IsHamiltonian.mem_support (hp : p.IsHamiltonian) (c : α) : c ∈ p.support :=
  p.support.one_le_count_iff.mp <| hp c |>.symm.le

/-- Hamiltonian paths are paths. -/
/-
**SimpleGraph.Walk.IsHamiltonian.isPath** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b}, p.IsHamiltonian → p.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.mk'`：∀ {V : Type u} {G : SimpleGraph V} {u v : V
} {p : G.Walk u v}, p.support.Nodup → p.IsPath
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
Hamiltonian paths are paths.
-/
lemma IsHamiltonian.isPath (hp : p.IsHamiltonian) : p.IsPath :=
  IsPath.mk' <| List.nodup_iff_count_le_one.2 <| (le_of_eq <| hp ·)

/-- A path whose support contains every vertex is Hamiltonian. -/
/-
**SimpleGraph.Walk.IsPath.isHamiltonian_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk.IsPath`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b},   p.IsPath → (∀ (w : α), w ∈ p.support) → p.IsHamiltonian
参数：∀ (w : α), w ∈ p.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.count_pos_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, 0 < List.count a l ↔ a ∈ l

--- 原说明 ---
A path whose support contains every vertex is Hamiltonian.
-/
lemma IsPath.isHamiltonian_of_mem (hp : p.IsPath) (hp' : ∀ w, w ∈ p.support) :
    p.IsHamiltonian := fun _ ↦
  le_antisymm (List.nodup_iff_count_le_one.1 hp.support_nodup _) (List.count_pos_iff.2 (hp' _))
/-
**SimpleGraph.Walk.IsPath.isHamiltonian_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk.IsPath`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b},   p.IsPath → (p.IsHamiltonian ↔ ∀ (w : α), w ∈ p.support)
参数：p.IsHamiltonian ↔ ∀ (w : α), w ∈ p.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.mem_support`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b},   p.IsHamiltonian → 
∀ (c : α), c ∈ p.support
· 使用定理 `SimpleGraph.Walk.IsPath.isHamiltonian_of_mem`：∀ {α : Type u_1} [inst : D
ecidableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b},   p.IsPath → (∀ (w
 : α), w ∈ p.support) → p.IsHamilt…
-/
lemma IsPath.isHamiltonian_iff (hp : p.IsPath) : p.IsHamiltonian ↔ ∀ w, w ∈ p.support :=
  ⟨(·.mem_support), hp.isHamiltonian_of_mem⟩
/-
**SimpleGraph.Walk.IsHamiltonian.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b} [Subsingleton α], p.IsHamiltonian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.Walk.nil_iff_support_eq`：nil_iff_support_eq {p : G.Walk v w}
 : p.Nil ↔ p.support = [v]
· 使用引理 `SimpleGraph.Walk.nil_of_subsingleton`：nil_of_subsingleton [Subsingleton 
V] (p : G.Walk v w) : p.Nil
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `List.count_singleton_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α]
 {a : α}, List.count a [a] = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem IsHamiltonian.of_subsingleton [Subsingleton α] : p.IsHamiltonian := by
  intro v
  rw [nil_iff_support_eq.mp p.nil_of_subsingleton, Subsingleton.elim v a, List.count_singleton_self]

/-- If a path `p` is Hamiltonian then the graph has finitely many vertices. -/
@[instance_reducible]
/-
**SimpleGraph.Walk.IsHamiltonian.fintype** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.
Walk.IsHamiltonian`。
形式化陈述：{α : Type u_1} →   [inst : DecidableEq α] → {G : SimpleGraph α} → {a b : α
} → {p : G.Walk a b} → p.IsHamiltonian → Fintype α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a path `p` is Hamiltonian then the graph has finitely many vertices.
-/
protected def IsHamiltonian.fintype (hp : p.IsHamiltonian) : Fintype α where
  elems := p.support.toFinset
  complete x := List.mem_toFinset.mpr (mem_support hp x)

/-- If a path `p` is Hamiltonian then the graph has finitely many vertices. -/
/-
**SimpleGraph.Walk.IsHamiltonian.finite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b}, p.IsHamiltonian → Finite α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If a path `p` is Hamiltonian then the graph has finitely many vertices.
-/
protected lemma IsHamiltonian.finite (hp : p.IsHamiltonian) : Finite α := by
  have := hp.fintype; infer_instance
/-
**SimpleGraph.Walk.not_isHamiltonian_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b} [h : Infinite α],   ¬p.IsHamiltonian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.finite`：∀ {α : Type u_1} [inst : Decidabl
eEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b}, p.IsHamiltonian → Finite 
α
-/
@[simp] lemma not_isHamiltonian_of_infinite [h : Infinite α] : ¬ p.IsHamiltonian := by
  contrapose! h; exact h.finite

section
variable [Fintype α]

/-- The support of a Hamiltonian walk is the entire vertex set. -/
/-
**SimpleGraph.Walk.IsHamiltonian.toFinset_support** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b} [inst_1 : Fintype α],   p.IsHamiltonian → p.support.toFinset = Fins
et.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The support of a Hamiltonian walk is the entire vertex set.
-/
lemma IsHamiltonian.toFinset_support (hp : p.IsHamiltonian) : p.support.toFinset = Finset.univ := by
  simp [eq_univ_iff_forall, hp]

@[deprecated (since := "2026-03-11")]
alias IsHamiltonian.support_toFinset := IsHamiltonian.toFinset_support

omit [Fintype α] in
/-
**SimpleGraph.Walk.IsHamiltonian.setOfPred_support** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b},   p.IsHamiltonian → {v | v ∈ p.support} = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.mem_support`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b},   p.IsHamiltonian → 
∀ (c : α), c ∈ p.support
-/
theorem IsHamiltonian.setOfPred_support (hp : p.IsHamiltonian) : {v | v ∈ p.support} = Set.univ :=
  Set.eq_univ_iff_forall.mpr hp.mem_support

@[deprecated (since := "2026-07-09")]
alias IsHamiltonian.setOf_support := IsHamiltonian.setOfPred_support

/-- The length of a Hamiltonian path is one less than the number of vertices of the graph. -/
/-
**SimpleGraph.Walk.IsHamiltonian.length_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b} [inst_1 : Fintype α],   p.IsHamiltonian → p.length = Fintype.card α
 - 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_tsub_of_add_eq`：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `List.sum_toFinset_count_eq_length`：sum_toFinset_count_eq_length [Decidab
leEq ι] (l : List ι) : ∑ a in l.toFinset, l.count a = l.length
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.toFinset_support`：∀ {α : Type u_1} [inst 
: DecidableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b} [inst_1 : Fintyp
e α],   p.IsHamiltonian → p.support.t…
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α

--- 原说明 ---
The length of a Hamiltonian path is one less than the number of vertices of the 
graph.
-/
lemma IsHamiltonian.length_eq (hp : p.IsHamiltonian) : p.length = Fintype.card α - 1 :=
  eq_tsub_of_add_eq <| by
    rw [← length_support, ← List.sum_toFinset_count_eq_length, Finset.sum_congr rfl fun _ _ ↦ hp _,
      ← card_eq_sum_ones, hp.toFinset_support, card_univ]

/-- The length of the support of a Hamiltonian path equals the number of vertices of the graph. -/
/-
**SimpleGraph.Walk.IsHamiltonian.length_support** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b} [inst_1 : Fintype α],   p.IsHamiltonian → p.support.length = Fintyp
e.card α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of the support of a Hamiltonian path equals the number of vertices of
 the graph.
-/
lemma IsHamiltonian.length_support (hp : p.IsHamiltonian) : p.support.length = Fintype.card α := by
  have : Inhabited α := ⟨a⟩
  grind [Fintype.card_ne_zero, length_eq]

end

/-- If a path `p` is Hamiltonian, then `p.support.get` defines an equivalence between
`Fin p.support.length` and `α`. -/
@[simps!]
/-
**SimpleGraph.Walk.IsHamiltonian.supportGetEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Simp
leGraph.Walk.IsHamiltonian`。
形式化陈述：{α : Type u_1} →   [inst : DecidableEq α] →     {G : SimpleGraph α} → {a b
 : α} → {p : G.Walk a b} → p.IsHamiltonian → Fin p.support.length ≃ α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a path `p` is Hamiltonian, then `p.support.get` defines an equivalence betwee
n
`Fin p.support.length` and `α`.
-/
def IsHamiltonian.supportGetEquiv (hp : p.IsHamiltonian) : Fin p.support.length ≃ α :=
  p.support.getEquivOfForallCountEqOne hp

/-- If a path `p` is Hamiltonian, then `p.getVert` defines an equivalence between
`Fin p.support.length` and `α`. -/
@[simps]
/-
**SimpleGraph.Walk.IsHamiltonian.getVertEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SimpleG
raph.Walk.IsHamiltonian`。
形式化陈述：{α : Type u_1} →   [inst : DecidableEq α] →     {G : SimpleGraph α} → {a b
 : α} → {p : G.Walk a b} → p.IsHamiltonian → Fin p.support.length ≃ α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a path `p` is Hamiltonian, then `p.getVert` defines an equivalence between
`Fin p.support.length` and `α`.
-/
def IsHamiltonian.getVertEquiv (hp : p.IsHamiltonian) : Fin p.support.length ≃ α where
  toFun := p.getVert ∘ Fin.val
  invFun := hp.supportGetEquiv.invFun
  left_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.left_inv
  right_inv := p.getVert_comp_val_eq_get_support ▸ hp.supportGetEquiv.right_inv
/-
**SimpleGraph.Walk.isHamiltonian_iff_support_get_bijective** 是 Mathlib 中的一个定理，位于
命名空间 `SimpleGraph.Walk`。
形式化陈述：isHamiltonian_iff_support_get_bijective : p.IsHamiltonian ↔ p.support.get.
Bijective
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.get_bijective_iff`：get_bijective_iff [BEq α] [LawfulBEq α] : l.get.
Bijective ↔ forall a, l.count a = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem isHamiltonian_iff_support_get_bijective : p.IsHamiltonian ↔ p.support.get.Bijective :=
  p.support.get_bijective_iff.symm
/-
**SimpleGraph.Walk.IsHamiltonian.getVert_surjective** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a b},   p.IsHamiltonian → Function.Surjective p.getVert
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isHamiltonian_iff_support_get_bijective`：isHamiltonian_
iff_support_get_bijective : p.IsHamiltonian ↔ p.support.get.Bijective
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_comp_val_eq_get_support`：getVert_comp_val_eq_ge
t_support {u v : V} (p : G.Walk u v) : p.getVert ∘ Fin.val = p.support.get
-/
theorem IsHamiltonian.getVert_surjective (hp : p.IsHamiltonian) : p.getVert.Surjective :=
  .of_comp <| p.getVert_comp_val_eq_get_support ▸
    isHamiltonian_iff_support_get_bijective.mp hp |>.surjective

omit [DecidableEq β] in
/-
**SimpleGraph.Walk.IsHamiltonian.injective_of_isPath_map** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.Walk.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {β : Type u_2}
 {H : SimpleGraph β} {a b : α}   {p : G.Walk a b} {f : G →g H}, p.IsHamiltonian 
→ (SimpleGraph.Walk.map f p).IsPath → Function.Injective ⇑f
参数：SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.injOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.InjOn f
 Set.univ ↔ Function.Injective f
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.setOfPred_support`：∀ {α : Type u_1} [inst
 : DecidableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b},   p.IsHamilton
ian → {v | v ∈ p.support} = Set.univ
· 使用定理 `SimpleGraph.Walk.IsPath.injOn_support_of_isPath_map`：∀ {V : Type u} {V' 
: Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {u v : V} {p : G.Walk u v} {
f : G →g G'},   (SimpleGraph.Walk.map f p…
-/
theorem IsHamiltonian.injective_of_isPath_map (hp : p.IsHamiltonian) (h : (p.map f).IsPath) :
    Function.Injective f := by
  rw [← Set.injOn_univ, ← hp.setOfPred_support]
  exact h.injOn_support_of_isPath_map
/-
**SimpleGraph.Walk.isHamiltonian_iff_isPath_and_length_eq** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.Walk`。
形式化陈述：isHamiltonian_iff_isPath_and_length_eq [Fintype α] : p.IsHamiltonian ↔ p.I
sPath ∧ p.length = Fintype.card α - 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.isPath`：∀ {α : Type u_1} [inst : Decidabl
eEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b}, p.IsHamiltonian → p.IsPat
h
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.length_eq`：∀ {α : Type u_1} [inst : Decid
ableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b} [inst_1 : Fintype α],  
 p.IsHamiltonian → p.length = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_iff_injective_get_support`：isPath_iff_injective_
get_support {u v : V} (p : G.Walk u v) : p.IsPath ↔ (p.support.get ·).Injective
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.isHamiltonian_iff_support_get_bijective`：isHamiltonian_
iff_support_get_bijective : p.IsHamiltonian ↔ p.support.get.Bijective
· 使用定理 `Function.Injective.surjective_of_finite`：∀ {α : Type u_1} {β : Type u_2}
 [Finite α] {f : α → β} (e : α ≃ β), Function.Injective f → Function.Surjective 
f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_one_add_one`：∀ {a : ℕ}, a ≠ 0 → a - 1 + 1 = a
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isHamiltonian_iff_isPath_and_length_eq [Fintype α] :
    p.IsHamiltonian ↔ p.IsPath ∧ p.length = Fintype.card α - 1 := by
  by_cases! h : IsEmpty α
  · exact h.elim' a
  refine ⟨fun h ↦ ⟨h.isPath, h.length_eq⟩, fun ⟨hp, h⟩ ↦ ?_⟩
  have := p.isPath_iff_injective_get_support.mp hp
  refine isHamiltonian_iff_support_get_bijective.mpr ⟨this, this.surjective_of_finite ?_⟩
  refine (Fintype.equivFinOfCardEq ?_).symm
  simp_rw [length_support, h, Nat.sub_one_add_one Fintype.card_ne_zero]

/-- A Hamiltonian cycle is a cycle that visits every vertex once. -/
/-
**SimpleGraph.Walk.IsHamiltonianCycle** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → {G : SimpleGraph α} → {a : α} → G.Walk 
a a → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hamiltonian cycle is a cycle that visits every vertex once.
-/
structure IsHamiltonianCycle (p : G.Walk a a) : Prop extends p.IsCycle where
  isHamiltonian_tail : p.tail.IsHamiltonian

variable {p : G.Walk a a}
/-
**SimpleGraph.Walk.IsHamiltonianCycle.isCycle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsHamiltonianCycle`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G
.Walk a a}, p.IsHamiltonianCycle → p.IsCycle
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle
-/
lemma IsHamiltonianCycle.isCycle (hp : p.IsHamiltonianCycle) : p.IsCycle :=
  hp.toIsCycle
/-
**SimpleGraph.Walk.IsHamiltonianCycle.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk.IsHamiltonianCycle`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {β : Type u_2}
 [inst_1 : DecidableEq β] {H : SimpleGraph β}   {a : α} {f : G →g H} {p : G.Walk
 a a},   Function.Bijective ⇑f → p.IsHamiltonianCycle → (SimpleGraph.Walk.map f 
p).IsHamiltonianCycle
参数：SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCycle.map`：∀ {V : Type u} {V' : Type v} {G : SimpleGr
aph V} {G' : SimpleGraph V'} {f : G →g G'} {u : V} {p : G.Walk u u},   Function.
Injective ⇑f → p.I…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isCycle`：∀ {α : Type u_1} [inst : De
cidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycle 
→ p.IsCycle
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `SimpleGraph.Walk.IsCircuit.ne_nil`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {p : G.Walk u u}, p.IsCircuit → p ≠ SimpleGraph.Walk.nil
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `List.count_map_of_injective`：count_map_of_injective [BEq β] [LawfulBEq β
] (l : List α) (f : α -> β) (hf : Function.Injective f) (x : α) : count (f x) (m
ap f l) = count x…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail`：∀ {α : Type u_1}
 [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHami
ltonianCycle → p.tail.IsHamiltonian
-/
lemma IsHamiltonianCycle.map (hf : Bijective f)
    (hp : p.IsHamiltonianCycle) : (p.map f).IsHamiltonianCycle where
  toIsCycle := hp.isCycle.map hf.injective
  isHamiltonian_tail := by
    simp only [IsHamiltonian, hf.surjective.forall]
    intro x
    rcases p with (_ | ⟨y, p⟩)
    · cases hp.ne_nil rfl
    simp only [map_cons, getVert_cons_succ, tail_cons, support_copy, support_map]
    rw [List.count_map_of_injective _ _ hf.injective]
    simpa using hp.isHamiltonian_tail x

/-- If a cycle `p` is Hamiltonian then the graph has finitely many vertices. -/
/-
**SimpleGraph.Walk.IsHamiltonianCycle.finite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk.IsHamiltonianCycle`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G
.Walk a a}, p.IsHamiltonianCycle → Finite α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.finite`：∀ {α : Type u_1} [inst : Decidabl
eEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b}, p.IsHamiltonian → Finite 
α
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail`：∀ {α : Type u_1}
 [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHami
ltonianCycle → p.tail.IsHamiltonian

--- 原说明 ---
If a cycle `p` is Hamiltonian then the graph has finitely many vertices.
-/
protected lemma IsHamiltonianCycle.finite (hp : p.IsHamiltonianCycle) : Finite α :=
  hp.isHamiltonian_tail.finite
/-
**SimpleGraph.Walk.not_isHamiltonianCycle_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G
.Walk a a} [h : Infinite α],   ¬p.IsHamiltonianCycle
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.finite`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycle →
 Finite α
-/
@[simp] lemma not_isHamiltonianCycle_of_infinite [h : Infinite α] : ¬ p.IsHamiltonianCycle := by
  contrapose! h; exact h.finite
/-
**SimpleGraph.Walk.isHamiltonianCycle_isCycle_and_isHamiltonian_tail** 是 Mathlib
 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isHamiltonianCycle_isCycle_and_isHamiltonian_tail : p.IsHamiltonianCycle ↔
 p.IsCycle ∧ p.tail.IsHamiltonian
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isHamiltonianCycle_isCycle_and_isHamiltonian_tail :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.tail.IsHamiltonian :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'⟩⟩
/-
**SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one*
* 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one : p.IsHamilto
nianCycle ↔ p.IsCycle ∧ forall a, (support p).tail.count a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ ∀ a, (support p).tail.count a = 1 := by
  simp +contextual [isHamiltonianCycle_isCycle_and_isHamiltonian_tail,
    IsHamiltonian, support_tail_of_not_nil, IsCycle.not_nil]

/-- A Hamiltonian cycle visits every vertex. -/
/-
**SimpleGraph.Walk.IsHamiltonianCycle.mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk.IsHamiltonianCycle`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G
.Walk a a},   p.IsHamiltonianCycle → ∀ (b : α), b ∈ p.support
参数：b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.mem_support`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b},   p.IsHamiltonian → 
∀ (c : α), c ∈ p.support
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail`：∀ {α : Type u_1}
 [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHami
ltonianCycle → p.tail.IsHamiltonian
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle

--- 原说明 ---
A Hamiltonian cycle visits every vertex.
-/
lemma IsHamiltonianCycle.mem_support (hp : p.IsHamiltonianCycle) (b : α) :
    b ∈ p.support :=
  List.mem_of_mem_tail <|
    support_tail_of_not_nil p hp.1.not_nil ▸ hp.isHamiltonian_tail.mem_support _

/-- The length of a Hamiltonian cycle is the number of vertices. -/
/-
**SimpleGraph.Walk.IsHamiltonianCycle.length_eq** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk.IsHamiltonianCycle`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G
.Walk a a} [inst_1 : Fintype α],   p.IsHamiltonianCycle → p.length = Fintype.car
d α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.length_tail_add_one`：length_tail_add_one {p : G.Walk u 
v} (hp : ¬ p.Nil) : p.tail.length + 1 = p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.length_eq`：∀ {α : Type u_1} [inst : Decid
ableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b} [inst_1 : Fintype α],  
 p.IsHamiltonian → p.length = …
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail`：∀ {α : Type u_1}
 [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHami
ltonianCycle → p.tail.IsHamiltonian
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α

--- 原说明 ---
The length of a Hamiltonian cycle is the number of vertices.
-/
lemma IsHamiltonianCycle.length_eq [Fintype α] (hp : p.IsHamiltonianCycle) :
    p.length = Fintype.card α := by
  rw [← length_tail_add_one hp.not_nil, hp.isHamiltonian_tail.length_eq, Nat.sub_add_cancel]
  rw [Nat.succ_le_iff, Fintype.card_pos_iff]
  exact ⟨a⟩
/-
**SimpleGraph.Walk.IsHamiltonianCycle.count_support_self** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.Walk.IsHamiltonianCycle`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G
.Walk a a},   p.IsHamiltonianCycle → List.count a p.support = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.cons_tail_support`：cons_tail_support (p : G.Walk u v) :
 u :: p.support.tail = p.support
· 使用定理 `List.count_cons_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, List.count a (a :: l) = List.count a l + 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail`：∀ {α : Type u_1}
 [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHami
ltonianCycle → p.tail.IsHamiltonian
-/
lemma IsHamiltonianCycle.count_support_self (hp : p.IsHamiltonianCycle) :
    p.support.count a = 2 := by
  rw [← cons_tail_support, List.count_cons_self,
    ← support_tail_of_not_nil _ hp.1.not_nil, hp.isHamiltonian_tail]
/-
**SimpleGraph.Walk.IsHamiltonianCycle.support_count_of_ne** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Walk.IsHamiltonianCycle`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} {a b : α} {p :
 G.Walk a a},   p.IsHamiltonianCycle → a ≠ b → List.count b p.support = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.cons_support_tail`：cons_support_tail {p : G.Walk u v} (
hp : ¬p.Nil) : u :: p.tail.support = p.support
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail`：∀ {α : Type u_1}
 [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHami
ltonianCycle → p.tail.IsHamiltonian
-/
lemma IsHamiltonianCycle.support_count_of_ne (hp : p.IsHamiltonianCycle) (h : a ≠ b) :
    p.support.count b = 1 := by
  rw [← cons_support_tail hp.1.not_nil, List.count_cons_of_ne h, hp.isHamiltonian_tail]
/-
**SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq** 是 Mathlib 中的一个
引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isHamiltonianCycle_iff_isCycle_and_length_eq [Fintype α] : p.IsHamiltonian
Cycle ↔ p.IsCycle ∧ p.length = Fintype.card α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isCycle`：∀ {α : Type u_1} [inst : De
cidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycle 
→ p.IsCycle
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.length_eq`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a} [inst_1 : Fintype α]
,   p.IsHamiltonianCycle → p.length…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.Walk.isHamiltonian_iff_isPath_and_length_eq`：isHamiltonian_i
ff_isPath_and_length_eq [Fintype α] : p.IsHamiltonian ↔ p.IsPath ∧ p.length = Fi
ntype.card α - 1
· 使用定理 `SimpleGraph.Walk.IsCycle.isPath_tail`：∀ {V : Type u} {G : SimpleGraph V}
 {u : V} {p : G.Walk u u}, p.IsCycle → p.tail.IsPath
-/
lemma isHamiltonianCycle_iff_isCycle_and_length_eq [Fintype α] :
    p.IsHamiltonianCycle ↔ p.IsCycle ∧ p.length = Fintype.card α := by
  refine ⟨fun h ↦ ⟨h.isCycle, h.length_eq⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩⟩
  refine isHamiltonian_iff_isPath_and_length_eq.mpr ⟨h₁.isPath_tail, ?_⟩
  grind [length_tail_add_one, IsCycle.not_nil]

@[simp]
/-
**SimpleGraph.Walk.isHamiltonianCycle_rotate** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：isHamiltonianCycle_rotate (hv : v in p.support) : (p.rotate v hv).IsHamilt
onianCycle ↔ p.IsHamiltonianCycle
参数：hv : v in p.support。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_rotate`：∀ {V : Type u} {G : SimpleGraph V} {v : 
V} [inst : DecidableEq V] (c : G.Walk v v) (u : V) (h : u ∈ c.support),   (c.rot
ate u h).length = c.…
-/
lemma isHamiltonianCycle_rotate (hv : v ∈ p.support) :
    (p.rotate v hv).IsHamiltonianCycle ↔ p.IsHamiltonianCycle := by
  cases (finite_or_infinite α).symm
  · simp
  cases nonempty_fintype α
  simp [isHamiltonianCycle_iff_isCycle_and_length_eq]

protected alias ⟨IsHamiltonianCycle.of_rotate, IsHamiltonianCycle.rotate⟩ :=
  isHamiltonianCycle_rotate

end Walk

variable [Fintype α]

/-- A Hamiltonian graph is a graph that contains a Hamiltonian cycle.

This is equivalent to there being an Hamiltonian cycle based at each vertex.
See `IsHamiltonian.exists_isHamiltonianCycle`.

By convention, the singleton graph is considered to be Hamiltonian and the empty graph is not. -/
/-
**SimpleGraph.IsHamiltonian** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsHamiltonian (G : SimpleGraph α) : Prop
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hamiltonian graph is a graph that contains a Hamiltonian cycle.

This is equivalent to there being an Hamiltonian cycle based at each vertex.
See `IsHamiltonian.exists_isHamiltonianCycle`.

By convention, the singleton graph is considered to be Hamiltonian and the empty
 graph is not.
-/
def IsHamiltonian (G : SimpleGraph α) : Prop :=
  Fintype.card α ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle
/-
**SimpleGraph.IsHamiltonian.exists_isHamiltonianCycle** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} [inst_1 : Fint
ype α] [Nontrivial α],   G.IsHamiltonian → ∀ (v : α), ∃ p, p.IsHamiltonianCycle
参数：v : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.mem_support`：∀ {α : Type u_1} [inst 
: DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHamiltonian
Cycle → ∀ (b : α), b ∈ p.support
-/
lemma IsHamiltonian.exists_isHamiltonianCycle [Nontrivial α] (hG : G.IsHamiltonian) (v : α) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  obtain ⟨u, p, hp⟩ := hG Fintype.one_lt_card.ne'; exact ⟨p.rotate v <| hp.mem_support _, by simpa⟩
/-
**SimpleGraph.IsHamiltonian.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsHamilt
onian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} [inst_1 : Fint
ype α] {H : SimpleGraph α},   G ≤ H → G.IsHamiltonian → H.IsHamiltonian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.map`：∀ {α : Type u_1} [inst : Decida
bleEq α] {G : SimpleGraph α} {β : Type u_2} [inst_1 : DecidableEq β] {H : Simple
Graph β}   {a : α} {f : G →g …
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma IsHamiltonian.mono {H : SimpleGraph α} (hGH : G ≤ H) (hG : G.IsHamiltonian) :
    H.IsHamiltonian :=
  fun hα ↦ let ⟨_, p, hp⟩ := hG hα; ⟨_, p.map <| .ofLE hGH, hp.map bijective_id⟩
/-
**SimpleGraph.not_isHamiltonian_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：not_isHamiltonian_of_isEmpty [IsEmpty α] : ¬G.IsHamiltonian
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsEmpty.exists_iff`：exists_iff {p : α -> Prop} : (exists a, p a) ↔ False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_isHamiltonian_of_isEmpty [IsEmpty α] : ¬G.IsHamiltonian :=
  (IsEmpty.exists_iff.mp <| · <| by simp)
/-
**SimpleGraph.IsHamiltonian.connected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsH
amiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} [inst_1 : Fint
ype α], G.IsHamiltonian → G.Connected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.mem_support`：∀ {α : Type u_1} [inst 
: DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHamiltonian
Cycle → ∀ (b : α), b ∈ p.support
· 使用定理 `SimpleGraph.Walk.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
 (p : G.Walk u v), G.Reachable u v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用引理 `SimpleGraph.not_isHamiltonian_of_isEmpty`：not_isHamiltonian_of_isEmpty [
IsEmpty α] : ¬G.IsHamiltonian
-/
lemma IsHamiltonian.connected (hG : G.IsHamiltonian) : G.Connected where
  preconnected a b := by
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have : Nontrivial α := ⟨a, b, hab⟩
    obtain ⟨_, p, hp⟩ := hG Fintype.one_lt_card.ne'
    have a_mem := hp.mem_support a
    have b_mem := hp.mem_support b
    exact ((p.takeUntil a a_mem).reverse.append <| p.takeUntil b b_mem).reachable
  nonempty := not_isEmpty_iff.mp fun _ ↦ not_isHamiltonian_of_isEmpty hG
/-
**SimpleGraph.IsHamiltonian.of_card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsHamiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} [inst_1 : Fint
ype α], Fintype.card α = 1 → G.IsHamiltonian
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsHamiltonian.of_card_eq_one (h : Fintype.card α = 1) : G.IsHamiltonian :=
  (· h |>.elim)
/-
**SimpleGraph.not_isHamiltonian_of_card_eq_two** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：not_isHamiltonian_of_card_eq_two (h : Fintype.card α = 2) : ¬G.IsHamiltoni
an
参数：h : Fintype.card α = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_isHamiltonian_of_card_eq_two (h : Fintype.card α = 2) : ¬G.IsHamiltonian := by
  intro hG
  have ⟨v, p, hp⟩ := hG <| by lia
  grind [hp.three_le_length, hp.length_eq]

@[simp]
/-
**SimpleGraph.not_isHamiltonian_bot_of_card_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph`。
形式化陈述：not_isHamiltonian_bot_of_card_ne_one (h : Fintype.card α != 1) : ¬(⊥ : Sim
pleGraph α).IsHamiltonian
参数：h : Fintype.card α != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle
-/
lemma not_isHamiltonian_bot_of_card_ne_one (h : Fintype.card α ≠ 1) :
    ¬(⊥ : SimpleGraph α).IsHamiltonian := by
  intro hG
  have ⟨v, p, hp⟩ := hG h
  exact p.adj_snd hp.not_nil
/-
**SimpleGraph.IsHamiltonian.of_unique** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsH
amiltonian`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} [inst_1 : Fint
ype α] [Unique α], G.IsHamiltonian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsHamiltonian.of_card_eq_one`：∀ {α : Type u_1} [inst : Decid
ableEq α] {G : SimpleGraph α} [inst_1 : Fintype α], Fintype.card α = 1 → G.IsHam
iltonian
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
-/
lemma IsHamiltonian.of_unique [Unique α] : G.IsHamiltonian :=
  of_card_eq_one <| Fintype.card_unique

/-- A finite simple graph with a bridge is not hamiltonian. -/
/-
**SimpleGraph.IsBridge.not_isHamiltonian** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsBridge`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {G : SimpleGraph α} [inst_1 : Fint
ype α] {e : Sym2 α},   G.IsBridge e → ¬G.IsHamiltonian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.IsBridge.nontrivial`：∀ {V : Type u} {G : SimpleGraph V} {e :
 Sym2 V}, G.IsBridge e → Nontrivial V
· 使用定理 `SimpleGraph.IsHamiltonian.exists_isHamiltonianCycle`：∀ {α : Type u_1} [i
nst : DecidableEq α] {G : SimpleGraph α} [inst_1 : Fintype α] [Nontrivial α],   
G.IsHamiltonian → ∀ (v : α), ∃ p, p.IsHam…
· 使用定理 `SimpleGraph.Walk.IsTrail.not_mem_support_of_not_reachable`：∀ {V : Type u
} {G : SimpleGraph V} {u v x y : V} {w : G.Walk u v},   w.IsTrail → ¬(G.deleteEd
ges {s(x, y)}).Reachable u y → ¬(G.deleteEdges …
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.isPath`：∀ {α : Type u_1} [inst : Decidabl
eEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b}, p.IsHamiltonian → p.IsPat
h
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.isHamiltonian_tail`：∀ {α : Type u_1}
 [inst : DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a},   p.IsHami
ltonianCycle → p.tail.IsHamiltonian
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Walk.IsTrail.isEdgeReachable_two`：∀ {V : Type u_1} {G : Simp
leGraph V} {u x y : V} {w : G.Walk u u},   w.IsTrail → x ∈ w.support → y ∈ w.sup
port → G.IsEdgeReachable 2 x y
· 使用定理 `SimpleGraph.Walk.IsCircuit.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCircuit → p.IsTrail
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `SimpleGraph.Walk.IsHamiltonianCycle.toIsCycle`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {a : α} {p : G.Walk a a}, p.IsHamiltonianCycl
e → p.IsCycle
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `SimpleGraph.Walk.IsHamiltonian.mem_support`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {a b : α} {p : G.Walk a b},   p.IsHamiltonian → 
∀ (c : α), c ∈ p.support

--- 原说明 ---
A finite simple graph with a bridge is not hamiltonian.
-/
theorem IsBridge.not_isHamiltonian {e : Sym2 α} (he : G.IsBridge e) : ¬G.IsHamiltonian := by
  induction e with | h u v
  have := he.nontrivial
  intro hG
  obtain ⟨p, hp⟩ := hG.exists_isHamiltonianCycle u
  refine hp.isHamiltonian_tail.isPath.isTrail.not_mem_support_of_not_reachable
    (fun huv ↦ he <| .trans ?_ huv) he (hp.isHamiltonian_tail.mem_support v)
  apply hp.isTrail.isEdgeReachable_two <;> simp

end SimpleGraph

