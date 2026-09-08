/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Rat.BigOperators

/-!
# Miscellaneous definitions, lemmas, and constructions using finsupp

## Main declarations

* `Finsupp.graph`: the finset of input and output pairs with non-zero outputs.
* `Finsupp.mapRange.equiv`: `Finsupp.mapRange` as an equiv.
* `Finsupp.mapDomain`: maps the domain of a `Finsupp` by a function and by summing.
* `Finsupp.comapDomain`: postcomposition of a `Finsupp` with a function injective on the preimage
  of its support.
* `Finsupp.filter`: `filter p f` is the finitely supported function that is `f a` if `p a` is true
  and 0 otherwise.
* `Finsupp.frange`: the image of a finitely supported function on its support.
* `Finsupp.subtype_domain`: the restriction of a finitely supported function `f` to a subtype.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/

@[expose] public section


noncomputable section

open Finset Function

variable {α β γ ι M N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `graph` -/


section Graph

variable [Zero M]

/-- The graph of a finitely supported function over its support, i.e. the finset of input and output
pairs with non-zero outputs. -/
/-
**Finsupp.graph** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：graph (f : α ->₀ M) : Finset (α × M)
参数：f : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph of a finitely supported function over its support, i.e. the finset of 
input and output
pairs with non-zero outputs.
-/
def graph (f : α →₀ M) : Finset (α × M) :=
  f.support.map ⟨fun a => Prod.mk a (f a), fun _ _ h => (Prod.mk.inj h).1⟩
/-
**Finsupp.mk_mem_graph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mk_mem_graph_iff {a : α} {m : M} {f : α ->₀ M} : (a, m) in f.graph ↔ f a =
 m ∧ m != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mk_mem_graph_iff {a : α} {m : M} {f : α →₀ M} : (a, m) ∈ f.graph ↔ f a = m ∧ m ≠ 0 := by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp]
/-
**Finsupp.mem_graph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_graph_iff {c : α × M} {f : α ->₀ M} : c in f.graph ↔ f c.1 = c.2 ∧ c.2
 != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mk_mem_graph_iff`：mk_mem_graph_iff {a : α} {m : M} {f : α ->₀ M}
 : (a, m) in f.graph ↔ f a = m ∧ m != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_graph_iff {c : α × M} {f : α →₀ M} : c ∈ f.graph ↔ f c.1 = c.2 ∧ c.2 ≠ 0 := by
  cases c
  exact mk_mem_graph_iff
/-
**Finsupp.mk_mem_graph** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mk_mem_graph (f : α ->₀ M) {a : α} (ha : a in f.support) : (a, f a) in f.g
raph
参数：f : α ->₀ M；ha : a in f.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mk_mem_graph_iff`：mk_mem_graph_iff {a : α} {m : M} {f : α ->₀ M}
 : (a, m) in f.graph ↔ f a = m ∧ m != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem mk_mem_graph (f : α →₀ M) {a : α} (ha : a ∈ f.support) : (a, f a) ∈ f.graph :=
  mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩
/-
**Finsupp.apply_eq_of_mem_graph** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：apply_eq_of_mem_graph {a : α} {m : M} {f : α ->₀ M} (h : (a, m) in f.graph
) : f a = m
参数：h : (a, m) in f.graph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_graph_iff`：mem_graph_iff {c : α × M} {f : α ->₀ M} : c in f.
graph ↔ f c.1 = c.2 ∧ c.2 != 0
-/
theorem apply_eq_of_mem_graph {a : α} {m : M} {f : α →₀ M} (h : (a, m) ∈ f.graph) : f a = m :=
  (mem_graph_iff.1 h).1

@[simp 1100] -- Higher priority shortcut instance for `mem_graph_iff`.
/-
**Finsupp.notMem_graph_snd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：notMem_graph_snd_zero (a : α) (f : α ->₀ M) : (a, (0 : M)) ∉ f.graph
参数：a : α；f : α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.irrefl`：∀ {α : Sort u} {a : α}, a ≠ a → False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_graph_iff`：mem_graph_iff {c : α × M} {f : α ->₀ M} : c in f.
graph ↔ f c.1 = c.2 ∧ c.2 != 0
-/
theorem notMem_graph_snd_zero (a : α) (f : α →₀ M) : (a, (0 : M)) ∉ f.graph := fun h =>
  (mem_graph_iff.1 h).2.irrefl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Finsupp.image_fst_graph** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：image_fst_graph [DecidableEq α] (f : α ->₀ M) : f.graph.image Prod.fst = f
.support
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.image_id'`：image_id' [DecidableEq α] : (s.image fun x => x) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_fst_graph [DecidableEq α] (f : α →₀ M) : f.graph.image Prod.fst = f.support := by
  classical
  simp_rw [graph, map_eq_image, image_image, Embedding.coeFn_mk, Function.comp_def, image_id']
/-
**Finsupp.graph_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：graph_injective (α M) [Zero M] : Injective (@graph α M _)
参数：α M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.image_fst_graph`：image_fst_graph [DecidableEq α] (f : α ->₀ M) :
 f.graph.image Prod.fst = f.support
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.ext_iff'`：ext_iff' {f g : α ->₀ M} : f = g ↔ f.support = g.suppo
rt ∧ forall x in f.support, f x = g x
· 使用定理 `Finsupp.apply_eq_of_mem_graph`：apply_eq_of_mem_graph {a : α} {m : M} {f 
: α ->₀ M} (h : (a, m) in f.graph) : f a = m
· 使用定理 `Finsupp.mk_mem_graph`：mk_mem_graph (f : α ->₀ M) {a : α} (ha : a in f.su
pport) : (a, f a) in f.graph
-/
theorem graph_injective (α M) [Zero M] : Injective (@graph α M _) := by
  intro f g h
  classical
    have hsup : f.support = g.support := by rw [← image_fst_graph, h, image_fst_graph]
    refine ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph <| h.symm ▸ ?_⟩
    exact mk_mem_graph _ (hsup ▸ hx)

@[simp]
/-
**Finsupp.graph_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：graph_inj {f g : α ->₀ M} : f.graph = g.graph ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finsupp.graph_injective`：graph_injective (α M) [Zero M] : Injective (@gr
aph α M _)
-/
theorem graph_inj {f g : α →₀ M} : f.graph = g.graph ↔ f = g :=
  (graph_injective α M).eq_iff

@[simp]
/-
**Finsupp.graph_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：graph_zero : graph (0 : α ->₀ M) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem graph_zero : graph (0 : α →₀ M) = ∅ := by simp [graph]

@[simp]
/-
**Finsupp.graph_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：graph_eq_empty {f : α ->₀ M} : f.graph = ∅ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Finsupp.graph_injective`：graph_injective (α M) [Zero M] : Injective (@gr
aph α M _)
· 使用定理 `Finsupp.graph_zero`：graph_zero : graph (0 : α ->₀ M) = ∅
-/
theorem graph_eq_empty {f : α →₀ M} : f.graph = ∅ ↔ f = 0 :=
  (graph_injective α M).eq_iff' graph_zero

end Graph

end Finsupp

/-! ### Declarations about `mapRange` -/


section MapRange

namespace Finsupp
variable [AddCommMonoid M] [AddCommMonoid N]
variable {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]

/-
**Finsupp.mapRange_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_multiset_sum (f : F) (m : Multiset (α ->₀ M)) : mapRange f (map_z
ero f) m.sum = (m.map fun x => mapRange f (map_zero f) x).sum
参数：f : F；m : Multiset (α ->₀ M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_multiset_sum`：∀ {M : Type u_5} {N : Type u_6} [inst : A
ddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N) (s : Multiset M),   f s.
sum = (Multiset.map…
-/
theorem mapRange_multiset_sum (f : F) (m : Multiset (α →₀ M)) :
    mapRange f (map_zero f) m.sum = (m.map fun x => mapRange f (map_zero f) x).sum :=
  (mapRange.addMonoidHom (f : M →+ N) : (α →₀ _) →+ _).map_multiset_sum _
/-
**Finsupp.mapRange_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_finsetSum (f : F) (s : Finset ι) (g : ι -> α ->₀ M) : mapRange f 
(map_zero f) (∑ x in s, g x) = ∑ x in s, mapRange f (map_zero f) (g x)
参数：f : F；s : Finset ι；g : ι -> α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem mapRange_finsetSum (f : F) (s : Finset ι) (g : ι → α →₀ M) :
    mapRange f (map_zero f) (∑ x ∈ s, g x) = ∑ x ∈ s, mapRange f (map_zero f) (g x) :=
  map_sum (mapRange.addMonoidHom (f : M →+ N)) _ _

@[deprecated (since := "2026-04-08")] alias mapRange_finset_sum := mapRange_finsetSum

end Finsupp

end MapRange

/-! ### Declarations about `equivCongrLeft` -/


section EquivCongrLeft

variable [Zero M]

namespace Finsupp

/-- Given `f : α ≃ β`, we can map `l : α →₀ M` to `equivMapDomain f l : β →₀ M` (computably)
by mapping the support forwards and the function backwards. -/
/-
**Finsupp.equivMapDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain (f : α ≃ β) (l : α ->₀ M) : β ->₀ M where support
参数：f : α ≃ β；l : α ->₀ M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `f : α ≃ β`, we can map `l : α →₀ M` to `equivMapDomain f l : β →₀ M` (com
putably)
by mapping the support forwards and the function backwards.
-/
def equivMapDomain (f : α ≃ β) (l : α →₀ M) : β →₀ M where
  support := l.support.map f.toEmbedding
  toFun a := l (f.symm a)
  mem_support_toFun a := by simp only [Finset.mem_map_equiv, mem_support_toFun]; rfl

@[simp]
/-
**Finsupp.equivMapDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_apply (f : α ≃ β) (l : α ->₀ M) (b : β) : equivMapDomain f 
l b = l (f.symm b)
参数：f : α ≃ β；l : α ->₀ M；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivMapDomain_apply (f : α ≃ β) (l : α →₀ M) (b : β) :
    equivMapDomain f l b = l (f.symm b) :=
  rfl
/-
**Finsupp.equivMapDomain_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_symm_apply (f : α ≃ β) (l : β ->₀ M) (a : α) : equivMapDoma
in f.symm l a = l (f a)
参数：f : α ≃ β；l : β ->₀ M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivMapDomain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) :
    equivMapDomain f.symm l a = l (f a) :=
  rfl

@[simp]
/-
**Finsupp.equivMapDomain_refl** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_refl (l : α ->₀ M) : equivMapDomain (Equiv.refl _) l = l
参数：l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem equivMapDomain_refl (l : α →₀ M) : equivMapDomain (Equiv.refl _) l = l := by ext x; rfl
/-
**Finsupp.equivMapDomain_refl'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_refl' : equivMapDomain (Equiv.refl _) = @id (α ->₀ M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem equivMapDomain_refl' : equivMapDomain (Equiv.refl _) = @id (α →₀ M) := by ext x; rfl
/-
**Finsupp.equivMapDomain_trans** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_trans (f : α ≃ β) (g : β ≃ γ) (l : α ->₀ M) : equivMapDomai
n (f.trans g) l = equivMapDomain g (equivMapDomain f l)
参数：f : α ≃ β；g : β ≃ γ；l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem equivMapDomain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by ext x; rfl
/-
**Finsupp.equivMapDomain_trans'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_trans' (f : α ≃ β) (g : β ≃ γ) : @equivMapDomain _ _ M _ (f
.trans g) = equivMapDomain g ∘ equivMapDomain f
参数：f : α ≃ β；g : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem equivMapDomain_trans' (f : α ≃ β) (g : β ≃ γ) :
    @equivMapDomain _ _ M _ (f.trans g) = equivMapDomain g ∘ equivMapDomain f := by ext x; rfl

@[simp]
/-
**Finsupp.equivMapDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_single (f : α ≃ β) (a : α) (b : M) : equivMapDomain f (sing
le a b) = single (f a) b
参数：f : α ≃ β；a : α；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivMapDomain_single (f : α ≃ β) (a : α) (b : M) :
    equivMapDomain f (single a b) = single (f a) b := by
  classical
    ext x
    simp only [single_apply, ← Equiv.eq_symm_apply, equivMapDomain_apply]

@[simp]
/-
**Finsupp.equivMapDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_zero {f : α ≃ β} : equivMapDomain f (0 : α ->₀ M) = (0 : β 
->₀ M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivMapDomain_zero {f : α ≃ β} : equivMapDomain f (0 : α →₀ M) = (0 : β →₀ M) := by
  ext; simp only [equivMapDomain_apply, coe_zero, Pi.zero_apply]

@[to_additive (attr := simp)]
/-
**Finsupp.prod_equivMapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_equivMapDomain [CommMonoid N] (f : α ≃ β) (l : α ->₀ M) (g : β -> M -
> N) : prod (equivMapDomain f l) g = prod l (fun a m => g (f a) m)
参数：f : α ≃ β；l : α ->₀ M；g : β -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_equivMapDomain [CommMonoid N] (f : α ≃ β) (l : α →₀ M) (g : β → M → N) :
    prod (equivMapDomain f l) g = prod l (fun a m => g (f a) m) := by
  simp [prod, equivMapDomain]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `Equiv.piCongrLeft`. -/
/-
**Finsupp.equivCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：equivCongrLeft (f : α ≃ β) : (α ->₀ M) ≃ (β ->₀ M)
参数：f : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `Equiv.piCongrLeft`.
-/
def equivCongrLeft (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) := by
  refine ⟨equivMapDomain f, equivMapDomain f.symm, fun f => ?_, fun f => ?_⟩ <;> ext x <;>
    simp only [equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]

@[simp]
/-
**Finsupp.equivCongrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivCongrLeft_apply (f : α ≃ β) (l : α ->₀ M) : equivCongrLeft f l = equi
vMapDomain f l
参数：f : α ≃ β；l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivCongrLeft_apply (f : α ≃ β) (l : α →₀ M) : equivCongrLeft f l = equivMapDomain f l :=
  rfl

@[simp]
/-
**Finsupp.equivCongrLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivCongrLeft_symm (f : α ≃ β) : (@equivCongrLeft _ _ M _ f).symm = equiv
CongrLeft f.symm
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivCongrLeft_symm (f : α ≃ β) :
    (@equivCongrLeft _ _ M _ f).symm = equivCongrLeft f.symm :=
  rfl

end Finsupp

end EquivCongrLeft

section CastFinsupp

variable [Zero M] (f : α →₀ M)

namespace Nat

@[simp, norm_cast]
/-
**Nat.cast_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_finsuppProd [CommSemiring R] (g : α -> M -> Nat) : (↑(f.prod g) : R) 
= f.prod fun a b => ↑(g a b)
参数：g : α -> M -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
-/
theorem cast_finsuppProd [CommSemiring R] (g : α → M → ℕ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Nat.cast_prod _ _

@[simp, norm_cast]
/-
**Nat.cast_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_finsupp_sum [AddCommMonoidWithOne R] (g : α -> M -> Nat) : (↑(f.sum g
) : R) = f.sum fun a b => ↑(g a b)
参数：g : α -> M -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
-/
theorem cast_finsupp_sum [AddCommMonoidWithOne R] (g : α → M → ℕ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Nat.cast_sum _ _

end Nat

namespace Int

@[simp, norm_cast]
/-
**Int.cast_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_finsuppProd [CommRing R] (g : α -> M -> Int) : (↑(f.prod g) : R) = f.
prod fun a b => ↑(g a b)
参数：g : α -> M -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_prod`：cast_prod {R : Type*} [CommRing R] (f : ι -> Int) (s : Fi
nset ι) : (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
-/
theorem cast_finsuppProd [CommRing R] (g : α → M → ℤ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  Int.cast_prod _ _

@[simp, norm_cast]
/-
**Int.cast_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：cast_finsupp_sum [AddCommGroupWithOne R] (g : α -> M -> Int) : (↑(f.sum g)
 : R) = f.sum fun a b => ↑(g a b)
参数：g : α -> M -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_sum`：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 
Int) : ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R)
-/
theorem cast_finsupp_sum [AddCommGroupWithOne R] (g : α → M → ℤ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  Int.cast_sum _ _

end Int

namespace Rat

@[simp, norm_cast]
/-
**Rat.cast_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_finsupp_sum [DivisionRing R] [CharZero R] (g : α -> M -> Rat) : (↑(f.
sum g) : R) = f.sum fun a b => ↑(g a b)
参数：g : α -> M -> Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_sum`：cast_sum (s : Finset ι) (f : ι -> Rat) : ∑ i in s, f i = ∑
 i in s, (f i : α)
-/
theorem cast_finsupp_sum [DivisionRing R] [CharZero R] (g : α → M → ℚ) :
    (↑(f.sum g) : R) = f.sum fun a b => ↑(g a b) :=
  cast_sum _ _

@[simp, norm_cast]
/-
**Rat.cast_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_finsuppProd [Field R] [CharZero R] (g : α -> M -> Rat) : (↑(f.prod g)
 : R) = f.prod fun a b => ↑(g a b)
参数：g : α -> M -> Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_prod`：cast_prod (s : Finset ι) (f : ι -> Rat) : ∏ i in s, f i =
 ∏ i in s, (f i : α)
-/
theorem cast_finsuppProd [Field R] [CharZero R] (g : α → M → ℚ) :
    (↑(f.prod g) : R) = f.prod fun a b => ↑(g a b) :=
  cast_prod _ _

end Rat

end CastFinsupp

/-! ### Declarations about `mapDomain` -/


namespace Finsupp

section MapDomain

variable [AddCommMonoid M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `mapDomain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
/-
**Finsupp.mapDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：mapDomain (f : α -> β) (v : α ->₀ M) : β ->₀ M
参数：f : α -> β；v : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α → β` and `v : α →₀ M`, `mapDomain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`.
-/
def mapDomain (f : α → β) (v : α →₀ M) : β →₀ M :=
  v.sum fun a => single (f a)
/-
**Finsupp.mapDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : AddCommMonoid M] {f
 : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a : α), (Finsupp.mapDomain f
 x) (f a) = x a
参数：x : α →₀ M；a : α；Finsupp.mapDomain f x；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain.eq_1`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   Finsupp.mapDomain f v = v.su
m fun a => F…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `Finsupp.coe_zero`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M], ⇑0 = 
0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
@[simp] theorem mapDomain_apply {f : α → β} (hf : Function.Injective f) (x : α →₀ M) (a : α) :
    mapDomain f x (f a) = x a := by
  rw [mapDomain, sum_apply, sum_eq_single a, single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne' (hf.ne hba)
  · intro _
    rw [single_zero, coe_zero, Pi.zero_apply]
/-
**Finsupp.mapDomain_of_not_mem_image_support** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`
。
形式化陈述：mapDomain_of_not_mem_image_support {f : α -> β} {x : α ->₀ M} {b : β} (hb 
: b ∉ f '' x.support) : mapDomain f x b = 0
参数：hb : b ∉ f '' x.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain.eq_1`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   Finsupp.mapDomain f v = v.su
m fun a => F…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mapDomain_of_not_mem_image_support {f : α → β} {x : α →₀ M} {b : β}
    (hb : b ∉ f '' x.support) : mapDomain f x b = 0 := by
  rw [mapDomain, sum_apply, sum, Finset.sum_eq_zero]
  exact fun a ha ↦ single_eq_of_ne fun eq => hb <| eq ▸ Set.mem_image_of_mem _ ha
/-
**Finsupp.mapDomain_of_notMem_range** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_of_notMem_range {f : α -> β} (x : α ->₀ M) (a : β) (h : a ∉ Set.
range f) : mapDomain f x a = 0
参数：x : α ->₀ M；a : β；h : a ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.mapDomain_of_not_mem_image_support`：mapDomain_of_not_mem_image_s
upport {f : α -> β} {x : α ->₀ M} {b : β} (hb : b ∉ f '' x.support) : mapDomain 
f x b = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem mapDomain_of_notMem_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ Set.range f) :
    mapDomain f x a = 0 :=
  mapDomain_of_not_mem_image_support <| by grw [Set.image_subset_range]; exact h

@[deprecated (since := "2026-07-15")] alias mapDomain_notin_range := mapDomain_of_notMem_range
/-
**Finsupp.mem_range_of_mapDomain_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mem_range_of_mapDomain_ne_zero {f : α -> β} {x : α ->₀ M} {b : β} (h : map
Domain f x b != 0) : b in Set.range f
参数：h : mapDomain f x b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Finsupp.mapDomain_of_notMem_range`：mapDomain_of_notMem_range {f : α -> β
} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f) : mapDomain f x a = 0
-/
lemma mem_range_of_mapDomain_ne_zero {f : α → β} {x : α →₀ M} {b : β} (h : mapDomain f x b ≠ 0) :
    b ∈ Set.range f := by contrapose! h; exact mapDomain_of_notMem_range _ _ h

@[simp]
/-
**Finsupp.mapDomain_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_id : mapDomain id v = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
-/
theorem mapDomain_id : mapDomain id v = v :=
  sum_single _
/-
**Finsupp.mapDomain_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDomain (g ∘ f) v = mapDomain
 g (mapDomain f v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.sum_sum_index`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} {P : Type u_11} [inst : Zero M]   [inst_1 : AddCommMonoid N] [inst
_2 : AddCom…
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `Finsupp.sum_congr`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {g1 g2 : α → M → N}, (∀ x ∈
 f.supp…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
theorem mapDomain_comp {f : α → β} {g : β → γ} :
    mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) := by
  refine ((sum_sum_index ?_ ?_).trans ?_).symm
  · intro
    exact single_zero _
  · intro
    exact single_add _
  refine sum_congr fun _ _ => sum_single_index ?_
  exact single_zero _

@[simp]
/-
**Finsupp.mapDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_single {f : α -> β} {a : α} {b : M} : mapDomain f (single a b) =
 single (f a) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
-/
theorem mapDomain_single {f : α → β} {a : α} {b : M} : mapDomain f (single a b) = single (f a) b :=
  sum_single_index <| single_zero _

@[simp]
/-
**Finsupp.mapDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_zero {f : α -> β} : mapDomain f (0 : α ->₀ M) = (0 : β ->₀ M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_zero_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : Zero M] [inst_1 : AddCommMonoid N] {h : α → M → N},   Finsupp.sum 0 h = 
0
-/
theorem mapDomain_zero {f : α → β} : mapDomain f (0 : α →₀ M) = (0 : β →₀ M) :=
  sum_zero_index
/-
**Finsupp.mapDomain_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_congr {f g : α -> β} (h : forall x in v.support, f x = g x) : v.
mapDomain f = v.mapDomain g
参数：h : forall x in v.support, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain_congr {f g : α → β} (h : ∀ x ∈ v.support, f x = g x) :
    v.mapDomain f = v.mapDomain g :=
  Finset.sum_congr rfl fun _ H => by simp only [h _ H]
/-
**Finsupp.mapDomain_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapD
omain f v₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
-/
theorem mapDomain_add {f : α → β} : mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂ :=
  sum_add_index' (fun _ => single_zero _) fun _ => single_add _
/-
**Finsupp.mapDomain_sub** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_sub {α β M : Type*} [AddCommGroup M] {v₁ v₂ : α ->₀ M} {f : α ->
 β} : mapDomain f (v₁ - v₂) = mapDomain f v₁ - mapDomain f v₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_sub_index`：sum_sub_index [AddGroup β] [AddCommGroup γ] {f g 
: α ->₀ β} {h : α -> β -> γ} (h_sub : forall a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h
 a b₂) : (f…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Finsupp.single_sub`：single_sub (a : ι) (b₁ b₂ : G) : single a (b₁ - b₂) 
= single a b₁ - single a b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma mapDomain_sub {α β M : Type*} [AddCommGroup M] {v₁ v₂ : α →₀ M} {f : α → β} :
    mapDomain f (v₁ - v₂) = mapDomain f v₁ - mapDomain f v₂ := by
  simp [mapDomain, sum_sub_index]

@[simp]
/-
**Finsupp.mapDomain_equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_equiv_apply {f : α ≃ β} (x : α ->₀ M) (a : β) : mapDomain f x a 
= x (f.symm a)
参数：x : α ->₀ M；a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem mapDomain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) :
    mapDomain f x a = x (f.symm a) := by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact mapDomain_apply f.injective _ _
/-
**Finsupp.support_mapDomain_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : AddCommMonoid M] (f
 : α ↪ β) (x : α →₀ M),   (Finsupp.mapDomain (⇑f) x).support = Finset.map f x.su
pport
参数：f : α ↪ β；x : α →₀ M；Finsupp.mapDomain (⇑f) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.mem_range_of_mapDomain_ne_zero`：mem_range_of_mapDomain_ne_zero {
f : α -> β} {x : α ->₀ M} {b : β} (h : mapDomain f x b != 0) : b in Set.range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
@[simp] lemma support_mapDomain_embedding (f : α ↪ β) (x : α →₀ M) :
    (mapDomain f x).support = x.support.map f := by
  ext b
  simp only [mem_support_iff, ne_eq, mem_map]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := mem_range_of_mapDomain_ne_zero h
    exact ⟨a, by simpa [f.injective] using h⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [f.injective]

/-- `Finsupp.mapDomain` is an `AddMonoidHom`. -/
@[simps]
/-
**Finsupp.mapDomain.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapDomain`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {M : Type u_5} → [inst : AddCommMonoid M
] → (α → β) → (α →₀ M) →+ β →₀ M
参数：α → β；α →₀ M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂

--- 原说明 ---
`Finsupp.mapDomain` is an `AddMonoidHom`.
-/
def mapDomain.addMonoidHom (f : α → β) : (α →₀ M) →+ β →₀ M where
  toFun := mapDomain f
  map_zero' := mapDomain_zero
  map_add' _ _ := mapDomain_add

@[simp]
/-
**Finsupp.mapDomain.addMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapDomain
`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M], Finsupp.mapDomai
n.addMonoidHom id = AddMonoidHom.id (α →₀ M)
参数：α →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
-/
theorem mapDomain.addMonoidHom_id : mapDomain.addMonoidHom id = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext fun _ => mapDomain_id
/-
**Finsupp.mapDomain.addMonoidHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapDoma
in`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {M : Type u_5} [inst : AddC
ommMonoid M] (f : β → γ) (g : α → β),   Finsupp.mapDomain.addMonoidHom (f ∘ g) =
 (Finsupp.mapDomain.addMonoidHom f).comp (Finsupp.mapDomain.addMonoidHom g)
参数：f : β → γ；g : α → β；f ∘ g；Finsupp.mapDomain.addMonoidHom f；Finsupp.mapDomain.
addMonoidHom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
-/
theorem mapDomain.addMonoidHom_comp (f : β → γ) (g : α → β) :
    (mapDomain.addMonoidHom (f ∘ g) : (α →₀ M) →+ γ →₀ M) =
      (mapDomain.addMonoidHom f).comp (mapDomain.addMonoidHom g) :=
  AddMonoidHom.ext fun _ => mapDomain_comp
/-
**Finsupp.mapDomain_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_finsetSum {f : α -> β} {s : Finset ι} {v : ι -> α ->₀ M} : mapDo
main f (∑ i in s, v i) = ∑ i in s, mapDomain f (v i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem mapDomain_finsetSum {f : α → β} {s : Finset ι} {v : ι → α →₀ M} :
    mapDomain f (∑ i ∈ s, v i) = ∑ i ∈ s, mapDomain f (v i) :=
  map_sum (mapDomain.addMonoidHom f) _ _

@[deprecated (since := "2026-04-08")] alias mapDomain_finset_sum := mapDomain_finsetSum
/-
**Finsupp.mapDomain_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_sum [Zero N] {f : α -> β} {s : α ->₀ N} {v : α -> N -> α ->₀ M} 
: mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem mapDomain_sum [Zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  map_finsuppSum (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M) _ _
/-
**Finsupp.mapDomain_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_support [DecidableEq β] {f : α -> β} {s : α ->₀ M} : (s.mapDomai
n f).support subseteq s.support.image f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Finsupp.support_sum`：support_sum [DecidableEq β] [Zero M] [AddCommMonoid
 N] {f : α ->₀ M} {g : α -> M -> β ->₀ N} : (f.sum g).support subseteq f.support
.biUnion …
· 使用引理 `Finset.biUnion_mono`：biUnion_mono (h : forall a in s, t₁ a subseteq t₂ a
) : s.biUnion t₁ subseteq s.biUnion t₂
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.biUnion_singleton`：biUnion_singleton {f : α -> β} : (s.biUnion fu
n a => {f a}) = s.image f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mapDomain_support [DecidableEq β] {f : α → β} {s : α →₀ M} :
    (s.mapDomain f).support ⊆ s.support.image f :=
  Finset.Subset.trans support_sum <|
    Finset.Subset.trans (Finset.biUnion_mono fun _ _ => support_single_subset) <| by
      rw [Finset.biUnion_singleton]
/-
**Finsupp.mapDomain_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_apply' (S : Set α) {f : α -> β} (x : α ->₀ M) (hS : (x.support :
 Set α) subseteq S) (hf : Set.InjOn f S) {a : α} (ha : a in S) : mapDomain f x (
f a) = x a
参数：S : Set α；x : α ->₀ M；hS : (x.support : Set α) subseteq S；hf : Set.InjOn f S；
ha : a in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain.eq_1`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   Finsupp.mapDomain f v = v.su
m fun a => F…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.InjOn.ne`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x
 y : α}, Set.InjOn f s → x ∈ s → y ∈ s → x ≠ y → f x ≠ f y
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem mapDomain_apply' (S : Set α) {f : α → β} (x : α →₀ M) (hS : (x.support : Set α) ⊆ S)
    (hf : Set.InjOn f S) {a : α} (ha : a ∈ S) : mapDomain f x (f a) = x a := by
  classical
    rw [mapDomain, sum_apply, sum]
    simp_rw [single_apply]
    by_cases hax : a ∈ x.support
    · rw [← Finset.add_sum_erase _ _ hax, if_pos rfl]
      convert! add_zero (x a)
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact (hf.mono hS).ne (Finset.mem_of_mem_erase hi) hax (Finset.ne_of_mem_erase hi)
    · rw [notMem_support_iff.1 hax]
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact hf.ne (hS hi) ha (ne_of_mem_of_not_mem hi hax)
/-
**Finsupp.mapDomain_support_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_support_of_injOn [DecidableEq β] {f : α -> β} (s : α ->₀ M) (hf 
: Set.InjOn f s.support) : (mapDomain f s).support = Finset.image f s.support
参数：s : α ->₀ M；hf : Set.InjOn f s.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapDomain_apply'`：mapDomain_apply' (S : Set α) {f : α -> β} (x :
 α ->₀ M) (hS : (x.support : Set α) subseteq S) (hf : Set.InjOn f S) {a : α} (ha
 : a in S) : m…
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem mapDomain_support_of_injOn [DecidableEq β] {f : α → β} (s : α →₀ M)
    (hf : Set.InjOn f s.support) : (mapDomain f s).support = Finset.image f s.support :=
  Finset.Subset.antisymm mapDomain_support <| by
    intro x hx
    simp only [mem_image, mem_support_iff, Ne] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [mem_support_iff, Ne]
    rw [mapDomain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
    · simp_rw [mem_coe, mem_support_iff, Ne]
      exact hx_h_left
    · exact Subset.refl _
/-
**Finsupp.mapDomain_support_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_support_of_injective [DecidableEq β] {f : α -> β} (hf : Function
.Injective f) (s : α ->₀ M) : (mapDomain f s).support = Finset.image f s.support
参数：hf : Function.Injective f；s : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_support_of_injOn`：mapDomain_support_of_injOn [Decidabl
eEq β] {f : α -> β} (s : α ->₀ M) (hf : Set.InjOn f s.support) : (mapDomain f s)
.support = Finset.image …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem mapDomain_support_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (s : α →₀ M) : (mapDomain f s).support = Finset.image f s.support :=
  mapDomain_support_of_injOn s hf.injOn

@[to_additive]
/-
**Finsupp.prod_mapDomain_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_mapDomain_index [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β -> M
 -> N} (h_zero : forall b, h b 0 = 1) (h_add : forall b m₁ m₂, h b (m₁ + m₂) = h
 b m₁ * h b m₂) : (mapDomain f s).prod h = s.prod fun a m => h (f a) m
参数：h_zero : forall b, h b 0 = 1；h_add : forall b m₁ m₂, h b (m₁ + m₂) = h b m₁ *
 h b m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.prod_sum_index`：prod_sum_index [Zero M] [AddCommMonoid N] [CommM
onoid P] {f : α ->₀ M} {g : α -> M -> β ->₀ N} {h : β -> N -> P} (h_zero : foral
l a, h a 0 =…
· 使用定理 `Finsupp.prod_congr`：prod_congr {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : 
forall x in f.support, g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
-/
theorem prod_mapDomain_index [CommMonoid N] {f : α → β} {s : α →₀ M} {h : β → M → N}
    (h_zero : ∀ b, h b 0 = 1) (h_add : ∀ b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
    (mapDomain f s).prod h = s.prod fun a m => h (f a) m :=
  (prod_sum_index h_zero h_add).trans <| prod_congr fun _ _ => prod_single_index (h_zero _)

-- Note that in `prod_mapDomain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `MonoidHom`.
/-- A version of `sum_mapDomain_index` that takes a bundled `AddMonoidHom`,
rather than separate linearity hypotheses.
-/
@[simp]
/-
**Finsupp.sum_mapDomain_index_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_mapDomain_index_addMonoidHom [AddCommMonoid N] {f : α -> β} {s : α ->₀
 M} (h : β -> M ->+ N) : ((mapDomain f s).sum fun b m => h b m) = s.sum fun a m 
=> h (f a) m
参数：h : β -> M ->+ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b

--- 原说明 ---
A version of `sum_mapDomain_index` that takes a bundled `AddMonoidHom`,
rather than separate linearity hypotheses.
-/
theorem sum_mapDomain_index_addMonoidHom [AddCommMonoid N] {f : α → β} {s : α →₀ M}
    (h : β → M →+ N) : ((mapDomain f s).sum fun b m => h b m) = s.sum fun a m => h (f a) m :=
  sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)
/-
**Finsupp.embDomain_eq_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_eq_mapDomain (f : α ↪ β) (v : α ->₀ M) : embDomain f v = mapDoma
in f v
参数：f : α ↪ β；v : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `Finsupp.mapDomain_of_notMem_range`：mapDomain_of_notMem_range {f : α -> β
} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f) : mapDomain f x a = 0
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0
-/
theorem embDomain_eq_mapDomain (f : α ↪ β) (v : α →₀ M) : embDomain f v = mapDomain f v := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective, embDomain_apply_self]
  · rw [mapDomain_of_notMem_range, embDomain_of_notMem_range] <;> assumption

@[to_additive]
/-
**Finsupp.prod_mapDomain_index_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_mapDomain_index_inj [CommMonoid N] {f : α -> β} {s : α ->₀ M} {h : β 
-> M -> N} (hf : Function.Injective f) : (s.mapDomain f).prod h = s.prod fun a b
 => h (f a) b
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用定理 `Finsupp.prod_embDomain`：prod_embDomain [Zero M] [CommMonoid N] {v : α ->
₀ M} {f : α ↪ β} {g : β -> M -> N} : (v.embDomain f).prod g = v.prod fun a b => 
g (f a) b
-/
theorem prod_mapDomain_index_inj [CommMonoid N] {f : α → β} {s : α →₀ M} {h : β → M → N}
    (hf : Function.Injective f) : (s.mapDomain f).prod h = s.prod fun a b => h (f a) b := by
  rw [← Function.Embedding.coeFn_mk f hf, ← embDomain_eq_mapDomain, prod_embDomain]
/-
**Finsupp.mapDomain_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_injective {f : α -> β} (hf : Function.Injective f) : Function.In
jective (mapDomain f : (α ->₀ M) -> β ->₀ M)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
-/
theorem mapDomain_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (α →₀ M) → β →₀ M) := by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this
/-
**Finsupp.mapDomain_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_surjective {f : α -> β} (hf : f.Surjective) : (mapDomain (M
参数：hf : f.Surjective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
· 使用定理 `Function.RightInverse.id`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f
 : α → β}, Function.RightInverse g f → f ∘ g = id
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
-/
theorem mapDomain_surjective {f : α → β} (hf : f.Surjective) :
    (mapDomain (M := M) f).Surjective := by
  intro x
  use mapDomain (surjInv hf) x
  rw [← mapDomain_comp, (rightInverse_surjInv hf).id, mapDomain_id]

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ) ↪ (β →₀ ℕ)` given by `mapDomain`. -/
@[simps]
/-
**Finsupp.mapDomainEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：mapDomainEmbedding {α β : Type*} (f : α ↪ β) : (α ->₀ Nat) ↪ β ->₀ Nat
参数：f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f` is an embedding we have an embedding `(α →₀ ℕ) ↪ (β →₀ ℕ)` given by `ma
pDomain`.
-/
def mapDomainEmbedding {α β : Type*} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
  ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective f.injective⟩
/-
**Finsupp.mapDomain.addMonoidHom_comp_mapRange** 是 Mathlib 中的一个定理，位于命名空间 `Finsup
p.mapDomain`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} {N : Type u_6} [inst : AddC
ommMonoid M] [inst_1 : AddCommMonoid N]   (f : α → β) (g : M →+ N),   (Finsupp.m
apDomain.addMonoidHom f).comp (Finsupp.mapRange.addMonoidHom g) =     (Finsupp.m
apRange.addMonoidHom g).comp (Finsupp.mapDomain.addMonoidHom f)
参数：f : α → β；g : M →+ N；Finsupp.mapDomain.addMonoidHom f；Finsupp.mapRange.addMon
oidHom g；Finsupp.mapRange.addMonoidHom g；Finsupp.mapDomain.addMonoidHom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.addHom_ext'`：addHom_ext' [AddZeroClass N] ⦃f g : (α ->₀ M) ->+ N
⦄ (H : forall x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.singleAddHom_apply`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZ
eroClass M] (a : ι) (b : M), (Finsupp.singleAddHom a) b = fun₀ | a => b
· 使用定理 `Finsupp.mapRange.addMonoidHom_apply`：∀ {ι : Type u_1} {M : Type u_3} {N 
: Type u_4} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N)   (
g : ι →₀ M), (Finsupp.map…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `Finsupp.mapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} {M
 : Type u_5} [inst : AddCommMonoid M] (f : α → β) (v : α →₀ M),   (Finsupp.mapDo
main.addMonoidHom f) v = F…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain.addMonoidHom_comp_mapRange [AddCommMonoid N] (f : α → β) (g : M →+ N) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom g) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) := by
  ext
  simp

/-- When `g` preserves addition, `mapRange` and `mapDomain` commute. -/
/-
**Finsupp.mapDomain_mapRange** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_mapRange [AddCommMonoid N] (f : α -> β) (v : α ->₀ M) (g : M -> 
N) (h0 : g 0 = 0) (hadd : forall x y, g (x + y) = g x + g y) : mapDomain f (mapR
ange g h0 v) = mapRange g h0 (mapDomain f v)
参数：f : α -> β；v : α ->₀ M；g : M -> N；h0 : g 0 = 0；hadd : forall x y, g (x + y) =
 g x + g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Finsupp.mapDomain.addMonoidHom_comp_mapRange`：∀ {α : Type u_1} {β : Type
 u_2} {M : Type u_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMo
noid N]   (f : α → β) (g : M →+ N)…

--- 原说明 ---
When `g` preserves addition, `mapRange` and `mapDomain` commute.
-/
theorem mapDomain_mapRange [AddCommMonoid N] (f : α → β) (v : α →₀ M) (g : M → N) (h0 : g 0 = 0)
    (hadd : ∀ x y, g (x + y) = g x + g y) :
    mapDomain f (mapRange g h0 v) = mapRange g h0 (mapDomain f v) :=
  let g' : M →+ N :=
    { toFun := g
      map_zero' := h0
      map_add' := hadd }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v
/-
**Finsupp.sum_update_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_update_add [AddZeroClass α] [AddCommMonoid β] (f : ι ->₀ α) (i : ι) (a
 : α) (g : ι -> α -> β) (hg : forall i, g i 0 = 0) (hgg : forall (j : ι) (a₁ a₂ 
: α), g j (a₁ + a₂) = g j a₁ + g j a₂) : (f.update i a).sum g + g i (f i) = f.su
m g + g i a
参数：f : ι ->₀ α；i : ι；a : α；g : ι -> α -> β；hg : forall i, g i 0 = 0；hgg : forall
 (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.update_eq_erase_add_single`：update_eq_erase_add_single (f : ι ->
₀ M) (a : ι) (b : M) : f.update a b = f.erase a + single a b
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.update_self`：update_self : f.update a (f a) = f
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
theorem sum_update_add [AddZeroClass α] [AddCommMonoid β] (f : ι →₀ α) (i : ι) (a : α)
    (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
    (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
    (f.update i a).sum g + g i (f i) = f.sum g + g i a := by
  rw [update_eq_erase_add_single, sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assoc, add_assoc]
  congr 1
  rw [add_comm, sum_single_index (hg _), sum_single_index (hg _)]
/-
**Finsupp.mapDomain_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_injOn (S : Set α) {f : α -> β} (hf : Set.InjOn f S) : Set.InjOn 
(mapDomain f : (α ->₀ M) -> β ->₀ M) { w | (w.support : Set α) subseteq S }
参数：S : Set α；hf : Set.InjOn f S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mapDomain_apply'`：mapDomain_apply' (S : Set α) {f : α -> β} (x :
 α ->₀ M) (hS : (x.support : Set α) subseteq S) (hf : Set.InjOn f S) {a : α} (ha
 : a in S) : m…
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain_injOn (S : Set α) {f : α → β} (hf : Set.InjOn f S) :
    Set.InjOn (mapDomain f : (α →₀ M) → β →₀ M) { w | (w.support : Set α) ⊆ S } := by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  classical
    by_cases h : a ∈ v₁.support ∪ v₂.support
    · rw [← mapDomain_apply' S _ hv₁ hf _, ← mapDomain_apply' S _ hv₂ hf _, eq] <;>
        · apply Set.union_subset hv₁ hv₂
          exact mod_cast h
    · simp_all
/-
**Finsupp.equivMapDomain_eq_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：equivMapDomain_eq_mapDomain {M} [AddCommMonoid M] (f : α ≃ β) (l : α ->₀ M
) : equivMapDomain f l = mapDomain f l
参数：f : α ≃ β；l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivMapDomain_eq_mapDomain {M} [AddCommMonoid M] (f : α ≃ β) (l : α →₀ M) :
    equivMapDomain f l = mapDomain f l := by ext x; simp

end MapDomain

/-! ### Declarations about `comapDomain` -/


section ComapDomain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comapDomain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
@[simps support]
/-
**Finsupp.comapDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：comapDomain [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑
l.support)) : α ->₀ M where support
参数：f : α -> β；l : β ->₀ M；hf : Set.InjOn f (f ⁻¹' ↑l.support)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comapDomain f l hf` is the finitely supported func
tion
from `α` to `M` given by composing `l` with `f`.
-/
def comapDomain [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) :
    α →₀ M where
  support := l.support.preimage f hf
  toFun a := l (f a)
  mem_support_toFun := by
    intro a
    rw [Finset.mem_preimage]
    exact l.mem_support_toFun (f a)

@[simp]
/-
**Finsupp.comapDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_apply [Zero M] (f : α -> β) (l : β ->₀ M) (hf : Set.InjOn f (f
 ⁻¹' ↑l.support)) (a : α) : comapDomain f l hf a = l (f a)
参数：f : α -> β；l : β ->₀ M；hf : Set.InjOn f (f ⁻¹' ↑l.support)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapDomain_apply [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support))
    (a : α) : comapDomain f l hf a = l (f a) :=
  rfl
/-
**Finsupp.sum_comapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_comapDomain [Zero M] [AddCommMonoid N] (f : α -> β) (l : β ->₀ M) (g :
 β -> M -> N) (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) : (comapDomain f 
l hf.injOn).sum (g ∘ f) = l.sum g
参数：f : α -> β；l : β ->₀ M；g : β -> M -> N；hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l
.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_preimage_of_bij`：∀ {ι : Type u_1} {κ : Type u_2} {β : Type u_
3} [inst : AddCommMonoid β] (f : ι → κ) (s : Finset κ)   (hf : Set.BijOn f (f ⁻¹
' ↑s) ↑s) (g : κ…
-/
theorem sum_comapDomain [Zero M] [AddCommMonoid N] (f : α → β) (l : β →₀ M) (g : β → M → N)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) :
    (comapDomain f l hf.injOn).sum (g ∘ f) = l.sum g :=
  Finset.sum_preimage_of_bij f _ hf fun x => g x (l x)
/-
**Finsupp.eq_zero_of_comapDomain_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：eq_zero_of_comapDomain_eq_zero [Zero M] (f : α -> β) (l : β ->₀ M) (hf : S
et.BijOn f (f ⁻¹' ↑l.support) ↑l.support) : comapDomain f l hf.injOn = 0 -> l = 
0
参数：f : α -> β；l : β ->₀ M；hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `Finsupp.comapDomain.eq_1`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5}
 [inst : Zero M] (f : α → β) (l : β →₀ M)   (hf : Set.InjOn f (f ⁻¹' ↑l.support)
),   Finsupp.c…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eq_zero_of_comapDomain_eq_zero [Zero M] (f : α → β) (l : β →₀ M)
    (hf : Set.BijOn f (f ⁻¹' ↑l.support) ↑l.support) : comapDomain f l hf.injOn = 0 → l = 0 := by
  rw [← support_eq_empty, ← support_eq_empty, comapDomain]
  simp_rw [Finset.ext_iff, Finset.notMem_empty, iff_false, mem_preimage]
  intro h a ha
  obtain ⟨b, hb⟩ := hf.2.2 ha
  exact h b (hb.2.symm ▸ ha)

@[simp]
/-
**Finsupp.comapDomain_single_of_not_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp
`。
形式化陈述：comapDomain_single_of_not_mem_range [Zero M] {f : α -> β} {b : β} (hb : b 
∉ Set.range f) (m : M) (hf) : comapDomain f (single b m) hf = 0
参数：hb : b ∉ Set.range f；m : M；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma comapDomain_single_of_not_mem_range [Zero M] {f : α → β} {b : β} (hb : b ∉ Set.range f)
    (m : M) (hf) : comapDomain f (single b m) hf = 0 := by
  classical
  ext a
  simp only [comapDomain, single_apply, coe_mk, coe_zero, Pi.zero_apply, ite_eq_right_iff]
  rintro rfl
  simp at hb

section FInjective

section Zero

variable [Zero M]

/-
**Finsupp.embDomain_comapDomain** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_comapDomain {f : α ↪ β} {g : β ->₀ M} (hg : ↑g.support subseteq 
Set.range f) : embDomain f (comapDomain f g f.injective.injOn) = g
参数：hg : ↑g.support subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `Finsupp.comapDomain_apply`：comapDomain_apply [Zero M] (f : α -> β) (l : 
β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) (a : α) : comapDomain f l hf a = 
l (f a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0
-/
lemma embDomain_comapDomain {f : α ↪ β} {g : β →₀ M} (hg : ↑g.support ⊆ Set.range f) :
    embDomain f (comapDomain f g f.injective.injOn) = g := by
  ext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_apply_self, comapDomain_apply]
  · replace hg : g b = 0 := notMem_support_iff.mp <| mt (hg ·) hb
    rw [embDomain_of_notMem_range _ _ _ hb, hg]

@[simp]
/-
**Finsupp.comapDomain_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_embDomain (f : α ↪ β) (l : α ->₀ M) : comapDomain f (embDomain
 f l) f.injective.injOn = l
参数：f : α ↪ β；l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comapDomain_embDomain (f : α ↪ β) (l : α →₀ M) :
    comapDomain f (embDomain f l) f.injective.injOn = l := by
  ext; simp

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp]
/-
**Finsupp.comapDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_zero (f : α -> β) (hif : Set.InjOn f (f ⁻¹' ↑(0 : β ->₀ M).sup
port)
参数：f : α -> β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g

--- 原说明 ---
Note the `hif` argument is needed for this to work in `rw`.
-/
theorem comapDomain_zero (f : α → β)
    (hif : Set.InjOn f (f ⁻¹' ↑(0 : β →₀ M).support) := Finset.coe_empty ▸ (Set.injOn_empty f)) :
    comapDomain f (0 : β →₀ M) hif = (0 : α →₀ M) := by
  ext
  rfl

@[simp]
/-
**Finsupp.comapDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_single (f : α -> β) (a : α) (m : M) (hif : Set.InjOn f (f ⁻¹' 
(single (f a) m).support)) : comapDomain f (Finsupp.single (f a) m) hif = Finsup
p.single a m
参数：f : α -> β；a : α；m : M；hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.comapDomain.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {M : Typ
e u_5} [inst : Zero M] (f f_1 : α → β) (e_f : f = f_1) (l l_1 : β →₀ M)   (e_l :
 l = l_1) (hf : Set.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.comapDomain_zero`：comapDomain_zero (f : α -> β) (hif : Set.InjOn
 f (f ⁻¹' ↑(0 : β ->₀ M).support)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.eq_single_iff`：eq_single_iff {f : α ->₀ M} {a b} : f = single a 
b ↔ f.support subseteq {a} ∧ f a = b
· 使用定理 `Finsupp.comapDomain_apply`：comapDomain_apply [Zero M] (f : α -> β) (l : 
β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) (a : α) : comapDomain f l hf a = 
l (f a)
· 使用定理 `Finsupp.comapDomain_support`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} [inst : Zero M] (f : α → β) (l : β →₀ M)   (hf : Set.InjOn f (f ⁻¹' ↑l.suppo
rt)), (Finsupp.co…
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem comapDomain_single (f : α → β) (a : α) (m : M)
    (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) :
    comapDomain f (Finsupp.single (f a) m) hif = Finsupp.single a m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_rw [single_zero, comapDomain_zero]
  · rw [eq_single_iff, comapDomain_apply, comapDomain_support, ← Finset.coe_subset, coe_preimage,
      support_single _ hm, coe_singleton, coe_singleton, single_eq_same]
    rw [support_single _ hm, coe_singleton] at hif
    exact ⟨fun x hx => hif hx rfl hx, rfl⟩
/-
**Finsupp.comapDomain_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_surjective {f : α -> β} (hf : Function.Injective f) : Function
.Surjective fun l : β ->₀ M => Finsupp.comapDomain f l hf.injOn
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finsupp.comapDomain_embDomain`：comapDomain_embDomain (f : α ↪ β) (l : α 
->₀ M) : comapDomain f (embDomain f l) f.injective.injOn = l
-/
lemma comapDomain_surjective {f : α → β} (hf : Function.Injective f) :
    Function.Surjective fun l : β →₀ M ↦ Finsupp.comapDomain f l hf.injOn := by
  intro l'
  use l'.embDomain ⟨f, hf⟩
  exact Finsupp.comapDomain_embDomain ..

end Zero

section AddZeroClass

variable [AddZeroClass M] {f : α → β}

/-
**Finsupp.comapDomain_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_add (v₁ v₂ : β ->₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support)) 
(hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.support)) (hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).su
pport)) : comapDomain f (v₁ + v₂) hv₁₂ = comapDomain f v₁ hv₁ + comapDomain f v₂
 hv₂
参数：v₁ v₂ : β ->₀ M；hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support)；hv₂ : Set.InjOn f (f ⁻¹
' ↑v₂.support)；hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).support)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comapDomain_add (v₁ v₂ : β →₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.support))
    (hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.support)) (hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).support)) :
    comapDomain f (v₁ + v₂) hv₁₂ = comapDomain f v₁ hv₁ + comapDomain f v₂ hv₂ := by
  ext
  simp

/-- A version of `Finsupp.comapDomain_add` that's easier to use. -/
/-
**Finsupp.comapDomain_add_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_add_of_injective (hf : Function.Injective f) (v₁ v₂ : β ->₀ M)
 : comapDomain f (v₁ + v₂) hf.injOn = comapDomain f v₁ hf.injOn + comapDomain f 
v₂ hf.injOn
参数：hf : Function.Injective f；v₁ v₂ : β ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.comapDomain_add`：comapDomain_add (v₁ v₂ : β ->₀ M) (hv₁ : Set.In
jOn f (f ⁻¹' ↑v₁.support)) (hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.support)) (hv₁₂ : Set.I
njOn f (f ⁻¹'…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
A version of `Finsupp.comapDomain_add` that's easier to use.
-/
theorem comapDomain_add_of_injective (hf : Function.Injective f) (v₁ v₂ : β →₀ M) :
    comapDomain f (v₁ + v₂) hf.injOn =
      comapDomain f v₁ hf.injOn + comapDomain f v₂ hf.injOn :=
  comapDomain_add ..

/-- `Finsupp.comapDomain` is an `AddMonoidHom`. -/
@[simps]
/-
**Finsupp.comapDomain.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.comapDomai
n`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → {M : Type u_5} → [inst : AddZeroClass 
M] → {f : α → β} → Function.Injective f → (β →₀ M) →+ α →₀ M
参数：β →₀ M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.comapDomain_add_of_injective`：comapDomain_add_of_injective (hf :
 Function.Injective f) (v₁ v₂ : β ->₀ M) : comapDomain f (v₁ + v₂) hf.injOn = co
mapDomain f v₁ hf.injOn + …

--- 原说明 ---
`Finsupp.comapDomain` is an `AddMonoidHom`.
-/
def comapDomain.addMonoidHom (hf : Function.Injective f) : (β →₀ M) →+ α →₀ M where
  toFun x := comapDomain f x hf.injOn
  map_zero' := comapDomain_zero f
  map_add' := comapDomain_add_of_injective hf

end AddZeroClass

variable [AddCommMonoid M] (f : α → β)

/-
**Finsupp.mapDomain_comapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_comapDomain (hf : Function.Injective f) (l : β ->₀ M) (hl : ↑l.s
upport subseteq Set.range f) : mapDomain f (comapDomain f l hf.injOn) = l
参数：hf : Function.Injective f；l : β ->₀ M；hl : ↑l.support subseteq Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.embDomain_comapDomain`：embDomain_comapDomain {f : α ↪ β} {g : β 
->₀ M} (hg : ↑g.support subseteq Set.range f) : embDomain f (comapDomain f g f.i
njective.injOn) = g
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
-/
theorem mapDomain_comapDomain (hf : Function.Injective f) (l : β →₀ M)
    (hl : ↑l.support ⊆ Set.range f) :
    mapDomain f (comapDomain f l hf.injOn) = l := by
  conv_rhs => rw [← embDomain_comapDomain (f := ⟨f, hf⟩) hl (M := M), embDomain_eq_mapDomain]
  rfl
/-
**Finsupp.mapDomain_comapDomain_nat_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_comapDomain_nat_add_one (l : Nat ->₀ M) : mapDomain (· + 1) (com
apDomain.addMonoidHom (add_left_injective 1) l) = l.erase 0
参数：l : Nat ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.comapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} 
{M : Type u_5} [inst : AddZeroClass M] {f : α → β} (hf : Function.Injective f)  
 (x : β →₀ M), (Finsupp.coma…
· 使用定理 `Finsupp.erase_ne`：erase_ne {a a' : α} {f : α ->₀ M} (h : a' != a) : (f.e
rase a) a' = f a'
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.mapDomain_comapDomain`：mapDomain_comapDomain (hf : Function.Inje
ctive f) (l : β ->₀ M) (hl : ↑l.support subseteq Set.range f) : mapDomain f (com
apDomain f l hf.inj…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mapDomain_comapDomain_nat_add_one (l : ℕ →₀ M) :
    mapDomain (· + 1) (comapDomain.addMonoidHom (add_left_injective 1) l) = l.erase 0 := by
  refine .trans ?_ (mapDomain_comapDomain _ (add_left_injective 1) _ fun _ ↦ ?_)
  · congr; ext; simp
  · simp_all [Nat.pos_iff_ne_zero]
/-
**Finsupp.comapDomain_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_mapDomain (hf : Function.Injective f) (l : α ->₀ M) : comapDom
ain f (mapDomain f l) hf.injOn = l
参数：hf : Function.Injective f；l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.comapDomain_apply`：comapDomain_apply [Zero M] (f : α -> β) (l : 
β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) (a : α) : comapDomain f l hf a = 
l (f a)
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
-/
theorem comapDomain_mapDomain (hf : Function.Injective f) (l : α →₀ M) :
    comapDomain f (mapDomain f l) hf.injOn = l := by
  ext; rw [comapDomain_apply, mapDomain_apply hf]
/-
**Finsupp.mem_range_mapDomain_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mem_range_mapDomain_iff (hf : Function.Injective f) (x : β ->₀ M) : x in S
et.range (Finsupp.mapDomain f) ↔ forall b ∉ Set.range f, x b = 0
参数：hf : Function.Injective f；x : β ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_of_notMem_range`：mapDomain_of_notMem_range {f : α -> β
} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f) : mapDomain f x a = 0
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finsupp.mapDomain_comapDomain`：mapDomain_comapDomain (hf : Function.Inje
ctive f) (l : β ->₀ M) (hl : ↑l.support subseteq Set.range f) : mapDomain f (com
apDomain f l hf.inj…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma mem_range_mapDomain_iff (hf : Function.Injective f) (x : β →₀ M) :
    x ∈ Set.range (Finsupp.mapDomain f) ↔ ∀ b ∉ Set.range f, x b = 0 := by
  refine ⟨fun ⟨y, hy⟩ x hx ↦ hy ▸ Finsupp.mapDomain_of_notMem_range y x hx, fun h ↦ ?_⟩
  refine ⟨Finsupp.comapDomain f x hf.injOn, Finsupp.mapDomain_comapDomain f hf _ fun i hi ↦ ?_⟩
  by_contra hc
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq] at hi
  exact hi (h _ hc)

end FInjective

end ComapDomain


/-! ### Declarations about `Finsupp.filter` -/


section Filter

section Zero

variable [Zero M] (p : α → Prop) [DecidablePred p] (f : α →₀ M)

/--
`Finsupp.filter p f` is the finitely supported function that is `f a` if `p a` is true and `0`
otherwise. -/
/-
**Finsupp.filter** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：filter (p : α -> Prop) [DecidablePred p] (f : α ->₀ M) : α ->₀ M where toF
un a
参数：p : α -> Prop；f : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.filter p f` is the finitely supported function that is `f a` if `p a` i
s true and `0`
otherwise.
-/
def filter (p : α → Prop) [DecidablePred p] (f : α →₀ M) : α →₀ M where
  toFun a := if p a then f a else 0
  support := f.support.filter p
  mem_support_toFun a := by
    split_ifs with h <;>
      · simp only [h, mem_filter, mem_support_iff]
        tauto
/-
**Finsupp.filter_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_apply (a : α) : f.filter p a = if p a then f a else 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_apply (a : α) : f.filter p a = if p a then f a else 0 := rfl
/-
**Finsupp.filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] [inst_1 : DecidableEq α] (
f : α →₀ M) (a : α),   Finsupp.filter (fun x => a = x) f = fun₀ | a => f a
参数：f : α →₀ M；a : α；fun x => a = x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.filter_apply`：filter_apply (a : α) : f.filter p a = if p a then 
f a else 0
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma filter_eq [DecidableEq α] (f : α →₀ M) (a : α) :
    f.filter (a = ·) = single a (f a) := by ext; rw [filter_apply, single_apply]; congr!; simp_all
/-
**Finsupp.filter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] [inst_1 : DecidableEq α] (
f : α →₀ M) (a : α),   Finsupp.filter (fun x => x = a) f = fun₀ | a => f a
参数：f : α →₀ M；a : α；fun x => x = a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.filter.congr_simp`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero 
M] (p p_1 : α → Prop),   p = p_1 →     ∀ {inst_1 : DecidablePred p} [inst_2 : De
cidablePred p_1…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.filter_eq`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] [inst
_1 : DecidableEq α] (f : α →₀ M) (a : α),   Finsupp.filter (fun x => a = x) f = 
fun₀ | …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma filter_eq' [DecidableEq α] (f : α →₀ M) (a : α) :
    f.filter (· = a) = single a (f a) := by simp [eq_comm]
/-
**Finsupp.filter_eq_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_eq_indicator : ⇑(f.filter p) = Set.indicator { x | p x } f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_eq_indicator : ⇑(f.filter p) = Set.indicator { x | p x } f := by
  ext
  simp [filter_apply, Set.indicator_apply]
/-
**Finsupp.filter_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_eq_zero_iff : f.filter p = 0 ↔ forall x, p x -> f x = 0
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.filter_eq_indicator`：filter_eq_indicator : ⇑(f.filter p) = Set.i
ndicator { x | p x } f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_eq_zero_iff : f.filter p = 0 ↔ ∀ x, p x → f x = 0 := by
  simp [DFunLike.ext_iff, filter_eq_indicator]
/-
**Finsupp.filter_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_eq_self_iff : f.filter p = f ↔ forall x, f x != 0 -> p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.filter_eq_indicator`：filter_eq_indicator : ⇑(f.filter p) = Set.i
ndicator { x | p x } f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_eq_self_iff : f.filter p = f ↔ ∀ x, f x ≠ 0 → p x := by
  simp only [DFunLike.ext_iff, filter_eq_indicator, Set.indicator_apply_eq_self, Set.mem_ofPred_eq,
    not_imp_comm]

@[simp]
/-
**Finsupp.filter_apply_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_apply_pos {a : α} (h : p a) : f.filter p a = f a
参数：h : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem filter_apply_pos {a : α} (h : p a) : f.filter p a = f a := if_pos h

@[simp]
/-
**Finsupp.filter_apply_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0
参数：h : ¬p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0 := if_neg h

@[simp]
/-
**Finsupp.support_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_filter : (f.filter p).support = {x in f.support | p x}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_filter : (f.filter p).support = {x ∈ f.support | p x} := rfl
/-
**Finsupp.filter_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_zero : (0 : α ->₀ M).filter p = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `Finsupp.support_filter`：support_filter : (f.filter p).support = {x in f.
support | p x}
· 使用定理 `Finsupp.support_zero`：support_zero : (0 : α ->₀ M).support = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
-/
theorem filter_zero : (0 : α →₀ M).filter p = 0 := by
  rw [← support_eq_empty, support_filter, support_zero, Finset.filter_empty]

@[simp]
/-
**Finsupp.filter_single_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = s
ingle a b
参数：h : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.filter_eq_self_iff`：filter_eq_self_iff : f.filter p = f ↔ forall
 x, f x != 0 -> p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_apply_ne_zero`：single_apply_ne_zero {a x : α} {b : M} : s
ingle a b x != 0 ↔ x = a ∧ b != 0
-/
theorem filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
  (filter_eq_self_iff _ _).2 fun _ hx => (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp]
/-
**Finsupp.filter_single_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 
0
参数：h : ¬p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.filter_eq_zero_iff`：filter_eq_zero_iff : f.filter p = 0 ↔ forall
 x, p x -> f x = 0
· 使用定理 `Finsupp.single_apply_eq_zero`：single_apply_eq_zero {a x : α} {b : M} : s
ingle a b x = 0 ↔ x = a -> b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 0 :=
  (filter_eq_zero_iff _ _).2 fun _ hpx =>
    single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)

@[to_additive]
/-
**Finsupp.prod_filter_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_filter_index [CommMonoid N] (g : α -> M -> N) : (f.filter p).prod g =
 ∏ x in (f.filter p).support, g x (f x)
参数：g : α -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.filter_apply_pos`：filter_apply_pos {a : α} (h : p a) : f.filter 
p a = f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finsupp.support_filter`：support_filter : (f.filter p).support = {x in f.
support | p x}
-/
theorem prod_filter_index [CommMonoid N] (g : α → M → N) :
    (f.filter p).prod g = ∏ x ∈ (f.filter p).support, g x (f x) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [support_filter, Finset.mem_filter] at hx
  rw [filter_apply_pos _ _ hx.2]

@[to_additive (attr := simp)]
/-
**Finsupp.prod_filter_mul_prod_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_filter_mul_prod_filter_not [CommMonoid N] (g : α -> M -> N) : (f.filt
er p).prod g * (f.filter fun a => ¬p a).prod g = f.prod g
参数：g : α -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.prod_filter_index`：prod_filter_index [CommMonoid N] (g : α -> M 
-> N) : (f.filter p).prod g = ∏ x in (f.filter p).support, g x (f x)
· 使用定理 `Finset.prod_filter_mul_prod_filter_not`：prod_filter_mul_prod_filter_not 
(s : Finset ι) (p : ι -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] (f
 : ι -> M) : (∏ x in s with …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_filter_mul_prod_filter_not [CommMonoid N] (g : α → M → N) :
    (f.filter p).prod g * (f.filter fun a => ¬p a).prod g = f.prod g := by
  simp_rw [prod_filter_index, support_filter, Finset.prod_filter_mul_prod_filter_not, Finsupp.prod]

@[to_additive (attr := simp)]
/-
**Finsupp.prod_div_prod_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_div_prod_filter [CommGroup G] (g : α -> M -> G) : f.prod g / (f.filte
r p).prod g = (f.filter fun a => ¬p a).prod g
参数：g : α -> M -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_eq_of_eq_mul'`：div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b
 = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.prod_filter_mul_prod_filter_not`：prod_filter_mul_prod_filter_not
 [CommMonoid N] (g : α -> M -> N) : (f.filter p).prod g * (f.filter fun a => ¬p 
a).prod g = f.prod g
-/
theorem prod_div_prod_filter [CommGroup G] (g : α → M → G) :
    f.prod g / (f.filter p).prod g = (f.filter fun a => ¬p a).prod g :=
  div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

end Zero

section AddCommMonoid
variable [AddCommMonoid M]

@[simp]
/-
**Finsupp.filter_add_filter_not** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：filter_add_filter_not (f : α ->₀ M) (p : α -> Prop) [DecidablePred p] : f.
filter p + f.filter (¬ p ·) = f
参数：f : α ->₀ M；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma filter_add_filter_not (f : α →₀ M) (p : α → Prop) [DecidablePred p] :
    f.filter p + f.filter (¬ p ·) = f := by ext; simp [filter_apply]; split <;> simp

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

end AddCommMonoid
end Filter

/-! ### Declarations about `frange` -/


section Frange

variable [Zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
/-
**Finsupp.frange** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：frange (f : α ->₀ M) : Finset M
参数：f : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`frange f` is the image of `f` on the support of `f`.
-/
def frange (f : α →₀ M) : Finset M :=
  haveI := Classical.decEq M
  Finset.image f f.support

@[simp, grind =]
/-
**Finsupp.mem_frange** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_frange {f : α ->₀ M} {y : M} : y in f.frange ↔ y != 0 ∧ y in Set.range
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.frange.eq_1`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] (f 
: α →₀ M), f.frange = Finset.image (⇑f) f.support
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_frange {f : α →₀ M} {y : M} : y ∈ f.frange ↔ y ≠ 0 ∧ y ∈ Set.range f := by
  rw [frange, @Finset.mem_image _ _ (Classical.decEq _) _ f.support]
  exact ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
    ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩
/-
**Finsupp.zero_notMem_frange** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：zero_notMem_frange {f : α ->₀ M} : (0 : M) ∉ f.frange
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_frange`：mem_frange {f : α ->₀ M} {y : M} : y in f.frange ↔ y
 != 0 ∧ y in Set.range f
-/
theorem zero_notMem_frange {f : α →₀ M} : (0 : M) ∉ f.frange := fun H => (mem_frange.1 H).1 rfl
/-
**Finsupp.frange_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：frange_single {x : α} {y : M} : frange (single x y) subseteq {y}
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} := by
  classical grind
/-
**Finsupp.mem_frange_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_frange_of_mem {x} {f : α ->₀ M} (h : x in f.support) : f x in f.frange
参数：h : x in f.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mem_frange_of_mem {x} {f : α →₀ M} (h : x ∈ f.support) : f x ∈ f.frange := by
  simp_all
/-
**Finsupp.range_subset_insert_frange** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：range_subset_insert_frange (f : α ->₀ M) : Set.range f subseteq insert 0 f
.frange
参数：f : α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_subset_insert_frange (f : α →₀ M) : Set.range f ⊆ insert 0 f.frange := by
  grind
/-
**Finsupp.finite_range** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：finite_range (f : α ->₀ M) : (Set.range f).Finite
参数：f : α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.range_subset_insert_frange`：range_subset_insert_frange (f : α ->
₀ M) : Set.range f subseteq insert 0 f.frange
-/
theorem finite_range (f : α →₀ M) : (Set.range f).Finite :=
  .subset (by simp) (range_subset_insert_frange f)

end Frange

/-! ### Declarations about `Finsupp.subtypeDomain` -/


section SubtypeDomain

section Zero

variable [Zero M] {p : α → Prop}

/--
`subtypeDomain p f` is the restriction of the finitely supported function `f` to subtype `p`. -/
/-
**Finsupp.subtypeDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain (p : α -> Prop) (f : α ->₀ M) : Subtype p ->₀ M where suppor
t
参数：p : α -> Prop；f : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`subtypeDomain p f` is the restriction of the finitely supported function `f` to
 subtype `p`.
-/
def subtypeDomain (p : α → Prop) (f : α →₀ M) : Subtype p →₀ M where
  support :=
    haveI := Classical.decPred p
    f.support.subtype p
  toFun := f ∘ Subtype.val
  mem_support_toFun a := by simp only [@mem_subtype _ _ (Classical.decPred p), mem_support_iff]; rfl

@[simp]
/-
**Finsupp.support_subtypeDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_subtypeDomain [D : DecidablePred p] {f : α ->₀ M} : (subtypeDomain
 p f).support = f.support.subtype p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem support_subtypeDomain [D : DecidablePred p] {f : α →₀ M} :
    (subtypeDomain p f).support = f.support.subtype p := by rw [Subsingleton.elim D] <;> rfl

@[simp]
/-
**Finsupp.subtypeDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_apply {a : Subtype p} {v : α ->₀ M} : (subtypeDomain p v) a 
= v a.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeDomain_apply {a : Subtype p} {v : α →₀ M} : (subtypeDomain p v) a = v a.val :=
  rfl

@[simp]
/-
**Finsupp.subtypeDomain_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_zero : subtypeDomain p (0 : α ->₀ M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeDomain_zero : subtypeDomain p (0 : α →₀ M) = 0 :=
  rfl
/-
**Finsupp.subtypeDomain_eq_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_eq_iff_forall {f g : α ->₀ M} : f.subtypeDomain p = g.subtyp
eDomain p ↔ forall x, p x -> f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subtypeDomain_eq_iff_forall {f g : α →₀ M} :
    f.subtypeDomain p = g.subtypeDomain p ↔ ∀ x, p x → f x = g x := by
  simp_rw [DFunLike.ext_iff, subtypeDomain_apply, Subtype.forall]
/-
**Finsupp.subtypeDomain_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_eq_iff {f g : α ->₀ M} (hf : forall x in f.support, p x) (hg
 : forall x in g.support, p x) : f.subtypeDomain p = g.subtypeDomain p ↔ f = g
参数：hf : forall x in f.support, p x；hg : forall x in g.support, p x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finsupp.subtypeDomain_eq_iff_forall`：subtypeDomain_eq_iff_forall {f g : 
α ->₀ M} : f.subtypeDomain p = g.subtypeDomain p ↔ forall x, p x -> f x = g x
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem subtypeDomain_eq_iff {f g : α →₀ M}
    (hf : ∀ x ∈ f.support, p x) (hg : ∀ x ∈ g.support, p x) :
    f.subtypeDomain p = g.subtypeDomain p ↔ f = g :=
  subtypeDomain_eq_iff_forall.trans
    ⟨fun H ↦ Finsupp.ext fun _a ↦ (em _).elim (H _ <| hf _ ·) fun haf ↦ (em _).elim (H _ <| hg _ ·)
        fun hag ↦ (notMem_support_iff.mp haf).trans (notMem_support_iff.mp hag).symm,
      fun H _ _ ↦ congr($H _)⟩
/-
**Finsupp.subtypeDomain_eq_zero_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_eq_zero_iff' {f : α ->₀ M} : f.subtypeDomain p = 0 ↔ forall 
x, p x -> f x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.subtypeDomain_eq_iff_forall`：subtypeDomain_eq_iff_forall {f g : 
α ->₀ M} : f.subtypeDomain p = g.subtypeDomain p ↔ forall x, p x -> f x = g x
-/
theorem subtypeDomain_eq_zero_iff' {f : α →₀ M} : f.subtypeDomain p = 0 ↔ ∀ x, p x → f x = 0 :=
  subtypeDomain_eq_iff_forall (g := 0)
/-
**Finsupp.subtypeDomain_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_eq_zero_iff {f : α ->₀ M} (hf : forall x in f.support, p x) 
: f.subtypeDomain p = 0 ↔ f = 0
参数：hf : forall x in f.support, p x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.subtypeDomain_eq_iff`：subtypeDomain_eq_iff {f g : α ->₀ M} (hf :
 forall x in f.support, p x) (hg : forall x in g.support, p x) : f.subtypeDomain
 p = g.subtypeDoma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem subtypeDomain_eq_zero_iff {f : α →₀ M} (hf : ∀ x ∈ f.support, p x) :
    f.subtypeDomain p = 0 ↔ f = 0 :=
  subtypeDomain_eq_iff (g := 0) hf (by simp)

@[to_additive]
/-
**Finsupp.prod_subtypeDomain_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_subtypeDomain_index [CommMonoid N] {v : α ->₀ M} {h : α -> M -> N} (h
p : forall x in v.support, p x) : (v.subtypeDomain p).prod (fun a b => h a b) = 
v.prod h
参数：hp : forall x in v.support, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem prod_subtypeDomain_index [CommMonoid N] {v : α →₀ M} {h : α → M → N}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun a b ↦ h a b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop

end Zero

section AddZeroClass

variable [AddZeroClass M] {p : α → Prop} {v v' : α →₀ M}

@[simp]
/-
**Finsupp.subtypeDomain_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_add {v v' : α ->₀ M} : (v + v').subtypeDomain p = v.subtypeD
omain p + v'.subtypeDomain p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem subtypeDomain_add {v v' : α →₀ M} :
    (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  ext fun _ => rfl

/-- `subtypeDomain` but as an `AddMonoidHom`. -/
/-
**Finsupp.subtypeDomainAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomainAddMonoidHom : (α ->₀ M) ->+ Subtype p ->₀ M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.subtypeDomain_add`：subtypeDomain_add {v v' : α ->₀ M} : (v + v')
.subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p

--- 原说明 ---
`subtypeDomain` but as an `AddMonoidHom`.
-/
def subtypeDomainAddMonoidHom : (α →₀ M) →+ Subtype p →₀ M where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' _ _ := subtypeDomain_add

/-- `Finsupp.filter` as an `AddMonoidHom`. -/
/-
**Finsupp.filterAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：filterAddHom (p : α -> Prop) [DecidablePred p] : (α ->₀ M) ->+ α ->₀ M whe
re toFun
参数：p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.filter` as an `AddMonoidHom`.
-/
def filterAddHom (p : α → Prop) [DecidablePred p] : (α →₀ M) →+ α →₀ M where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' f g := DFunLike.coe_injective <| by
    simp_rw [coe_add, filter_eq_indicator]
    exact Set.indicator_add { x | p x } f g

@[simp]
/-
**Finsupp.filter_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_add [DecidablePred p] {v v' : α ->₀ M} : (v + v').filter p = v.filt
er p + v'.filter p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
theorem filter_add [DecidablePred p] {v v' : α →₀ M} :
    (v + v').filter p = v.filter p + v'.filter p :=
  (filterAddHom p).map_add v v'

end AddZeroClass

section CommMonoid

variable [AddCommMonoid M] {p : α → Prop}

/-
**Finsupp.subtypeDomain_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_sum {s : Finset ι} {h : ι -> α ->₀ M} : (∑ c in s, h c).subt
ypeDomain p = ∑ c in s, (h c).subtypeDomain p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem subtypeDomain_sum {s : Finset ι} {h : ι → α →₀ M} :
    (∑ c ∈ s, h c).subtypeDomain p = ∑ c ∈ s, (h c).subtypeDomain p :=
  map_sum subtypeDomainAddMonoidHom _ s
/-
**Finsupp.subtypeDomain_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_finsupp_sum [Zero N] {s : β ->₀ N} {h : β -> N -> α ->₀ M} :
 (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.subtypeDomain_sum`：subtypeDomain_sum {s : Finset ι} {h : ι -> α 
->₀ M} : (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p
-/
theorem subtypeDomain_finsupp_sum [Zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum
/-
**Finsupp.filter_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_sum [DecidablePred p] (s : Finset ι) (f : ι -> α ->₀ M) : (∑ a in s
, f a).filter p = ∑ a in s, filter p (f a)
参数：s : Finset ι；f : ι -> α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem filter_sum [DecidablePred p] (s : Finset ι) (f : ι → α →₀ M) :
    (∑ a ∈ s, f a).filter p = ∑ a ∈ s, filter p (f a) :=
  map_sum (filterAddHom p) f s
/-
**Finsupp.filter_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_eq_sum (p : α -> Prop) [DecidablePred p] (f : α ->₀ M) : f.filter p
 = ∑ i in f.support.filter p, single i (f i)
参数：p : α -> Prop；f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.filter_apply_pos`：filter_apply_pos {a : α} (h : p a) : f.filter 
p a = f a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem filter_eq_sum (p : α → Prop) [DecidablePred p] (f : α →₀ M) :
    f.filter p = ∑ i ∈ f.support.filter p, single i (f i) :=
  (f.filter p).sum_single.symm.trans <|
    Finset.sum_congr rfl fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end CommMonoid

section Group

variable [AddGroup G] {p : α → Prop} {v v' : α →₀ G}

@[simp]
/-
**Finsupp.subtypeDomain_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_neg : (-v).subtypeDomain p = -v.subtypeDomain p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem subtypeDomain_neg : (-v).subtypeDomain p = -v.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
/-
**Finsupp.subtypeDomain_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_sub : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subt
ypeDomain p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem subtypeDomain_sub : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
/-
**Finsupp.filter_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_neg (p : α -> Prop) [DecidablePred p] (f : α ->₀ G) : filter p (-f)
 = -filter p f
参数：p : α -> Prop；f : α ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (a : α), f (-a) = -f a
-/
theorem filter_neg (p : α → Prop) [DecidablePred p] (f : α →₀ G) : filter p (-f) = -filter p f :=
  (filterAddHom p : (_ →₀ G) →+ _).map_neg f

@[simp]
/-
**Finsupp.filter_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_sub (p : α -> Prop) [DecidablePred p] (f₁ f₂ : α ->₀ G) : filter p 
(f₁ - f₂) = filter p f₁ - filter p f₂
参数：p : α -> Prop；f₁ f₂ : α ->₀ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α
] [inst_1 : SubtractionMonoid β] (f : α →+ β) (g h : α),   f (g - h) = f g - f h
-/
theorem filter_sub (p : α → Prop) [DecidablePred p] (f₁ f₂ : α →₀ G) :
    filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
  (filterAddHom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end Group

end SubtypeDomain

/-
**Finsupp.mem_support_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_support_multiset_sum [AddCommMonoid M] {s : Multiset (α ->₀ M)} (a : α
) : a in s.sum.support -> exists f in s, a in (f : α ->₀ M).support
参数：α ->₀ M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem mem_support_multiset_sum [AddCommMonoid M] {s : Multiset (α →₀ M)} (a : α) :
    a ∈ s.sum.support → ∃ f ∈ s, a ∈ (f : α →₀ M).support :=
  Multiset.induction_on s (fun h => False.elim (by simp at h))
    (by
      intro f s ih ha
      by_cases h : a ∈ f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
      · simp_rw [Multiset.sum_cons, mem_support_iff, add_apply, notMem_support_iff.1 h,
          zero_add] at ha
        rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩
        exact ⟨f', Multiset.mem_cons_of_mem h₀, h₁⟩)
/-
**Finsupp.mem_support_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_support_finsetSum [AddCommMonoid M] {s : Finset ι} {h : ι -> α ->₀ M} 
(a : α) (ha : a in (∑ c in s, h c).support) : exists c in s, a in (h c).support
参数：a : α；ha : a in (∑ c in s, h c).support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mem_support_multiset_sum`：mem_support_multiset_sum [AddCommMonoi
d M] {s : Multiset (α ->₀ M)} (a : α) : a in s.sum.support -> exists f in s, a i
n (f : α ->₀ M).suppor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_support_finsetSum [AddCommMonoid M] {s : Finset ι} {h : ι → α →₀ M} (a : α)
    (ha : a ∈ (∑ c ∈ s, h c).support) : ∃ c ∈ s, a ∈ (h c).support :=
  let ⟨_, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

@[deprecated (since := "2026-04-08")] alias mem_support_finset_sum := mem_support_finsetSum

/-! ### Declarations about `curry` and `uncurry` -/


section Uncurry

variable [Zero M]

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
/-
**Finsupp.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {M : Type u_5} → [inst : Zero M] → (α →₀
 β →₀ M) → α × β →₀ M
参数：α →₀ β →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`.
-/
protected def uncurry (f : α →₀ β →₀ M) : α × β →₀ M where
  toFun x := f x.1 x.2
  support := f.support.disjiUnion (fun a ↦ (f a).support.map <| .sectR a _) <| by
    intro a₁ _ a₂ _ hne
    simp [Finset.disjoint_iff_ne, hne]
  mem_support_toFun := by aesop
/-
**Finsupp.uncurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : Zero M] (f : α →₀ β
 →₀ M) (x : α × β), f.uncurry x = (f x.1) x.2
参数：f : α →₀ β →₀ M；x : α × β；f x.1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem uncurry_apply (f : α →₀ β →₀ M) (x : α × β) : f.uncurry x = f x.1 x.2 := rfl

@[simp]
/-
**Finsupp.uncurry_apply_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : Zero M] (f : α →₀ β
 →₀ M) (a : α) (b : β),   f.uncurry (a, b) = (f a) b
参数：f : α →₀ β →₀ M；a : α；b : β；a, b；f a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem uncurry_apply_pair (f : α →₀ β →₀ M) (a : α) (b : β) :
    f.uncurry (a, b) = f a b :=
  rfl

@[simp]
/-
**Finsupp.uncurry_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：uncurry_single (a : α) (b : β) (m : M) : (single a (single b m)).uncurry =
 single (a, b) m
参数：a : α；b : β；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
lemma uncurry_single (a : α) (b : β) (m : M) :
    (single a (single b m)).uncurry = single (a, b) m := by
  ext ⟨x, y⟩
  rcases eq_or_ne a x with rfl | hne <;> classical simp [single_apply, *]
/-
**Finsupp.sum_uncurry_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_uncurry_index [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α × β -> M ->
 N) : f.uncurry.sum (fun p c => g p c) = f.sum fun a f => f.sum fun b => g (a, b
)
参数：f : α ->₀ β ->₀ M；g : α × β -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_disjiUnion`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [i
nst : AddCommMonoid M] {f : ι → M} (s : Finset κ) (t : κ → Finset ι)   (h : (↑s)
.PairwiseDi…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Function.Embedding.sectR_apply`：∀ {α : Type u_1} (a : α) (β : Type u_2) 
(b : β), (Function.Embedding.sectR a β) b = (a, b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_uncurry_index [AddCommMonoid N] (f : α →₀ β →₀ M) (g : α × β → M → N) :
    f.uncurry.sum (fun p c => g p c) = f.sum fun a f => f.sum fun b ↦ g (a, b) := by
  simp [Finsupp.sum, Finsupp.uncurry, Finset.sum_disjiUnion]
/-
**Finsupp.sum_uncurry_index'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_uncurry_index' [AddCommMonoid N] (f : α ->₀ β ->₀ M) (g : α -> β -> M 
-> N) : f.uncurry.sum (fun p c => g p.1 p.2 c) = f.sum fun a f => f.sum (g a)
参数：f : α ->₀ β ->₀ M；g : α -> β -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_uncurry_index`：sum_uncurry_index [AddCommMonoid N] (f : α ->
₀ β ->₀ M) (g : α × β -> M -> N) : f.uncurry.sum (fun p c => g p c) = f.sum fun 
a f => f.sum fu…
-/
theorem sum_uncurry_index' [AddCommMonoid N] (f : α →₀ β →₀ M) (g : α → β → M → N) :
    f.uncurry.sum (fun p c => g p.1 p.2 c) = f.sum fun a f => f.sum (g a) :=
  sum_uncurry_index ..

end Uncurry

section Curry

variable [Zero M]

open scoped Classical in
/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
/-
**Finsupp.curry** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {M : Type u_5} → [inst : Zero M] → (α × 
β →₀ M) → α →₀ β →₀ M
参数：α × β →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`.
-/
protected def curry (f : α × β →₀ M) : α →₀ β →₀ M where
  toFun a :=
    { toFun b := f (a, b)
      support := f.support.filterMap (fun x ↦ if x.1 = a then x.2 else none) <| by simp +contextual
      mem_support_toFun := by simp }
  support := f.support.image Prod.fst
  mem_support_toFun := by simp [DFunLike.ext_iff]

@[simp]
/-
**Finsupp.curry_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：curry_apply (f : α × β ->₀ M) (x : α) (y : β) : f.curry x y = f (x, y)
参数：f : α × β ->₀ M；x : α；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_apply (f : α × β →₀ M) (x : α) (y : β) : f.curry x y = f (x, y) := rfl

@[simp]
/-
**Finsupp.support_curry** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：support_curry [DecidableEq α] (f : α × β ->₀ M) : f.curry.support = f.supp
ort.image Prod.fst
参数：f : α × β ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
lemma support_curry [DecidableEq α] (f : α × β →₀ M) :
    f.curry.support = f.support.image Prod.fst := by unfold Finsupp.curry; congr!

@[simp]
/-
**Finsupp.curry_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：curry_uncurry (f : α ->₀ β ->₀ M) : f.uncurry.curry = f
参数：f : α ->₀ β ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem curry_uncurry (f : α →₀ β →₀ M) : f.uncurry.curry = f := by
  ext a b
  simp

@[simp]
/-
**Finsupp.uncurry_curry** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：uncurry_curry (f : α × β ->₀ M) : f.curry.uncurry = f
参数：f : α × β ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uncurry_curry (f : α × β →₀ M) : f.curry.uncurry = f := by
  ext ⟨a, b⟩
  simp

@[simp]
/-
**Finsupp.curry_single** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：curry_single (a : α × β) (m : M) : (single a m).curry = single a.1 (single
 a.2 m)
参数：a : α × β；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.curry_uncurry`：curry_uncurry (f : α ->₀ β ->₀ M) : f.uncurry.cur
ry = f
· 使用引理 `Finsupp.uncurry_single`：uncurry_single (a : α) (b : β) (m : M) : (single
 a (single b m)).uncurry = single (a, b) m
-/
lemma curry_single (a : α × β) (m : M) :
    (single a m).curry = single a.1 (single a.2 m) := by
  rw [← curry_uncurry (single _ _), uncurry_single]
/-
**Finsupp.sum_curry_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_curry_index [AddCommMonoid N] (f : α × β ->₀ M) (g : α -> β -> M -> N)
 : (f.curry.sum fun a f => f.sum (g a)) = f.sum fun p c => g p.1 p.2 c
参数：f : α × β ->₀ M；g : α -> β -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_uncurry_index'`：sum_uncurry_index' [AddCommMonoid N] (f : α 
->₀ β ->₀ M) (g : α -> β -> M -> N) : f.uncurry.sum (fun p c => g p.1 p.2 c) = f
.sum fun a f => …
· 使用定理 `Finsupp.uncurry_curry`：uncurry_curry (f : α × β ->₀ M) : f.curry.uncurry
 = f
-/
theorem sum_curry_index [AddCommMonoid N] (f : α × β →₀ M) (g : α → β → M → N) :
    (f.curry.sum fun a f => f.sum (g a)) = f.sum fun p c => g p.1 p.2 c := by
  rw [← sum_uncurry_index', uncurry_curry]

/-- The equivalence between `α × β →₀ M` and `α →₀ β →₀ M` given by currying/uncurrying. -/
@[simps]
/-
**Finsupp.curryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：curryEquiv : (α × β ->₀ M) ≃ (α ->₀ β ->₀ M) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.uncurry_curry`：uncurry_curry (f : α × β ->₀ M) : f.curry.uncurry
 = f
· 使用定理 `Finsupp.curry_uncurry`：curry_uncurry (f : α ->₀ β ->₀ M) : f.uncurry.cur
ry = f

--- 原说明 ---
The equivalence between `α × β →₀ M` and `α →₀ β →₀ M` given by currying/uncurry
ing.
-/
def curryEquiv : (α × β →₀ M) ≃ (α →₀ β →₀ M) where
  toFun := Finsupp.curry
  invFun := Finsupp.uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

@[deprecated (since := "2026-01-03")] noncomputable alias finsuppProdEquiv := curryEquiv
/-
**Finsupp.filter_curry** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_curry (f : α × β ->₀ M) (p : α -> Prop) [DecidablePred p] : (f.filt
er fun a : α × β => p a.1).curry = f.curry.filter p
参数：f : α × β ->₀ M；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_curry (f : α × β →₀ M) (p : α → Prop) [DecidablePred p] :
    (f.filter fun a : α × β => p a.1).curry = f.curry.filter p := by
  ext a b
  simp [filter_apply, apply_ite (DFunLike.coe · b)]

end Curry

section
variable [AddZeroClass M]

/-- The additive monoid isomorphism between `α × β →₀ M` and `α →₀ β →₀ M` given by
currying/uncurrying. -/
@[simps! symm_apply]
/-
**Finsupp.curryAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：curryAddEquiv : (α × β ->₀ M) ≃+ (α ->₀ β ->₀ M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive monoid isomorphism between `α × β →₀ M` and `α →₀ β →₀ M` given by
currying/uncurrying.
-/
noncomputable def curryAddEquiv : (α × β →₀ M) ≃+ (α →₀ β →₀ M) where
  __ := curryEquiv
  map_add' _ _ := by ext; simp
/-
**Finsupp.coe_curryAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : AddZeroClass M], ⇑F
insupp.curryAddEquiv = Finsupp.curry
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_curryAddEquiv : (curryAddEquiv : (α × β →₀ M) → α →₀ β →₀ M) = .curry := rfl

end

/-! ### Declarations about finitely supported functions whose support is a `Sum` type -/


section Sum
variable [Zero γ]

/-- `Finsupp.sumElim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
@[simps support]
/-
**Finsupp.sumElim** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sumElim (f : α ->₀ γ) (g : β ->₀ γ) : α oplus β ->₀ γ where support
参数：f : α ->₀ γ；g : β ->₀ γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.sumElim f g` maps `inl x` to `f x` and `inr y` to `g y`.
-/
def sumElim (f : α →₀ γ) (g : β →₀ γ) : α ⊕ β →₀ γ where
  support := f.support.disjSum g.support
  toFun := Sum.elim f g
  mem_support_toFun := by simp

@[simp, norm_cast]
/-
**Finsupp.coe_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_sumElim (f : α ->₀ γ) (g : β ->₀ γ) : ⇑(sumElim f g) = Sum.elim f g
参数：f : α ->₀ γ；g : β ->₀ γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sumElim (f : α →₀ γ) (g : β →₀ γ) : ⇑(sumElim f g) = Sum.elim f g := rfl
/-
**Finsupp.sumElim_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sumElim_apply (f : α ->₀ γ) (g : β ->₀ γ) (x : α oplus β) : sumElim f g x 
= Sum.elim f g x
参数：f : α ->₀ γ；g : β ->₀ γ；x : α oplus β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumElim_apply (f : α →₀ γ) (g : β →₀ γ) (x : α ⊕ β) : sumElim f g x = Sum.elim f g x := rfl
/-
**Finsupp.sumElim_inl** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sumElim_inl (f : α ->₀ γ) (g : β ->₀ γ) (x : α) : sumElim f g (Sum.inl x) 
= f x
参数：f : α ->₀ γ；g : β ->₀ γ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumElim_inl (f : α →₀ γ) (g : β →₀ γ) (x : α) : sumElim f g (Sum.inl x) = f x := rfl
/-
**Finsupp.sumElim_inr** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sumElim_inr (f : α ->₀ γ) (g : β ->₀ γ) (x : β) : sumElim f g (Sum.inr x) 
= g x
参数：f : α ->₀ γ；g : β ->₀ γ；x : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sumElim_inr (f : α →₀ γ) (g : β →₀ γ) (x : β) : sumElim f g (Sum.inr x) = g x := rfl
/-
**Finsupp.sumElim_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Zero γ], Finsupp.su
mElim 0 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sumElim_zero_zero : sumElim 0 0 = (0 : α ⊕ β →₀ γ) := by ext (_ | _) <;> simp
/-
**Finsupp.sumElim_single_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Zero γ] (a : α) (c 
: γ),   (fun₀ | a => c).sumElim 0 = fun₀ | Sum.inl a => c
参数：a : α；c : γ；fun₀ | a => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma sumElim_single_zero (a : α) (c : γ) :
    sumElim (single a c) (0 : β →₀ γ) = single (.inl a) c := by
  classical ext (_ | _) <;> simp [single_apply]
/-
**Finsupp.sumElim_zero_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Zero γ] (b : β) (c 
: γ),   (Finsupp.sumElim 0 fun₀ | b => c) = fun₀ | Sum.inr b => c
参数：b : β；c : γ；Finsupp.sumElim 0 fun₀ | b => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
@[simp] lemma sumElim_zero_single (b : β) (c : γ) :
    sumElim (0 : α →₀ γ) (single b c) = single (.inr b) c := by
  classical ext (_ | _) <;> simp [single_apply]
/-
**Finsupp.sumElim_single_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : AddMonoid M] (a : α
) (b : β) (m₁ m₂ : M),   ((fun₀ | a => m₁).sumElim fun₀ | b => m₂) = (fun₀ | Sum
.inl a => m₁) + fun₀ | Sum.inr b => m₂
参数：a : α；b : β；m₁ m₂ : M；(fun₀ | a => m₁).sumElim fun₀ | b => m₂；fun₀ | Sum.inl 
a => m₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
@[simp] lemma sumElim_single_single [AddMonoid M] (a : α) (b : β) (m₁ m₂ : M) :
    sumElim (single a m₁) (single b m₂) = single (.inl a) m₁ + single (.inr b) m₂ := by
  classical ext (_ | _) <;> simp [single_apply]
/-
**Finsupp.sumElim_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sumElim_eq_add [AddCommMonoid M] (f : α ->₀ M) (g : β ->₀ M) : sumElim f g
 = mapDomain Sum.inl f + mapDomain Sum.inr g
参数：f : α ->₀ M；g : β ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
· 使用定理 `Finsupp.mapDomain_of_notMem_range`：mapDomain_of_notMem_range {f : α -> β
} (x : α ->₀ M) (a : β) (h : a ∉ Set.range f) : mapDomain f x a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma sumElim_eq_add [AddCommMonoid M] (f : α →₀ M) (g : β →₀ M) :
    sumElim f g = mapDomain Sum.inl f + mapDomain Sum.inr g := by
  ext (_ | _) <;> simp [mapDomain_of_notMem_range, Sum.inl_injective, Sum.inr_injective]
/-
**Finsupp.mapDomain_swap_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst : AddCommMonoid M] (f
 : α →₀ M) (g : β →₀ M),   Finsupp.mapDomain Sum.swap (f.sumElim g) = g.sumElim 
f
参数：f : α →₀ M；g : β →₀ M；f.sumElim g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.sumElim_eq_add`：sumElim_eq_add [AddCommMonoid M] (f : α ->₀ M) (
g : β ->₀ M) : sumElim f g = mapDomain Sum.inl f + mapDomain Sum.inr g
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapDomain_swap_sumElim [AddCommMonoid M] (f : α →₀ M) (g : β →₀ M) :
    mapDomain Sum.swap (sumElim f g) = sumElim g f := by
  simp [sumElim_eq_add, mapDomain_add, ← mapDomain_comp, Function.comp_def, add_comm]

@[to_additive]
/-
**Finsupp.prod_sumElim** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：prod_sumElim {ι₁ ι₂ α M : Type*} [Zero α] [CommMonoid M] (f₁ : ι₁ ->₀ α) (
f₂ : ι₂ ->₀ α) (g : ι₁ oplus ι₂ -> α -> M) : (f₁.sumElim f₂).prod g = f₁.prod (g
 ∘ Sum.inl) * f₂.prod (g ∘ Sum.inr)
参数：f₁ : ι₁ ->₀ α；f₂ : ι₂ ->₀ α；g : ι₁ oplus ι₂ -> α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sumElim_support`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : Zero γ] (f : α →₀ γ) (g : β →₀ γ),   (f.sumElim g).support = f.support.d
isjSum g.supp…
· 使用定理 `Finset.prod_disjSum`：prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι o
plus κ -> M) : ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f
 (Sum.inr…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_sumElim {ι₁ ι₂ α M : Type*} [Zero α] [CommMonoid M]
    (f₁ : ι₁ →₀ α) (f₂ : ι₂ →₀ α) (g : ι₁ ⊕ ι₂ → α → M) :
    (f₁.sumElim f₂).prod g = f₁.prod (g ∘ Sum.inl) * f₂.prod (g ∘ Sum.inr) := by
  simp [Finsupp.prod, Finset.prod_disjSum]

@[simp]
/-
**Finsupp.comapDomain_inl_sumElim** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_inl_sumElim (f : α ->₀ γ) (g : β ->₀ γ) : comapDomain Sum.inl 
(f.sumElim g) Sum.inl_injective.injOn = f
参数：f : α ->₀ γ；g : β ->₀ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapDomain_inl_sumElim (f : α →₀ γ) (g : β →₀ γ) :
    comapDomain Sum.inl (f.sumElim g) Sum.inl_injective.injOn = f := by
  ext; simp

@[simp]
/-
**Finsupp.comapDomain_inr_sumElim** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_inr_sumElim (f : α ->₀ γ) (g : β ->₀ γ) : comapDomain Sum.inr 
(f.sumElim g) Sum.inr_injective.injOn = g
参数：f : α ->₀ γ；g : β ->₀ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapDomain_inr_sumElim (f : α →₀ γ) (g : β →₀ γ) :
    comapDomain Sum.inr (f.sumElim g) Sum.inr_injective.injOn = g := by
  ext; simp

@[simp]
/-
**Finsupp.embDomain_inl** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_inl (a : α ->₀ γ) : embDomain Function.Embedding.inl a = sumElim
 a (0 : β ->₀ γ)
参数：a : α ->₀ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.inl_apply`：∀ {α : Type u_1} {β : Type u_2} (val : α),
 Function.Embedding.inl val = Sum.inl val
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma embDomain_inl (a : α →₀ γ) :
    embDomain Function.Embedding.inl a = sumElim a (0 : β →₀ γ) := by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]
/-
**Finsupp.embDomain_inr** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_inr (b : β ->₀ γ) : embDomain Function.Embedding.inr b = sumElim
 (0 : α ->₀ γ) b
参数：b : β ->₀ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Embedding.inr_apply`：∀ {α : Type u_1} {β : Type u_2} (val : β),
 Function.Embedding.inr val = Sum.inr val
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
-/
lemma embDomain_inr (b : β →₀ γ) :
    embDomain Function.Embedding.inr b = sumElim (0 : α →₀ γ) b := by
  ext (_ | _) <;> simp [embDomain_apply]

@[simp]
/-
**Finsupp.comapDomain_sumElim_comapDomain** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_sumElim_comapDomain (c : α oplus β ->₀ γ) : (comapDomain Sum.i
nl c Sum.inl_injective.injOn).sumElim (comapDomain Sum.inr c Sum.inr_injective.i
njOn) = c
参数：c : α oplus β ->₀ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comapDomain_sumElim_comapDomain (c : α ⊕ β →₀ γ) :
    (comapDomain Sum.inl c Sum.inl_injective.injOn).sumElim
      (comapDomain Sum.inr c Sum.inr_injective.injOn) = c := by
  ext (_ | _) <;> simp

@[simp]
/-
**Finsupp.sumElim_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：sumElim_add [AddZeroClass M] (a b : α ->₀ M) (c d : β ->₀ M) : (a + b).sum
Elim (c + d) = a.sumElim c + b.sumElim d
参数：a b : α ->₀ M；c d : β ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumElim_add [AddZeroClass M] (a b : α →₀ M) (c d : β →₀ M) :
    (a + b).sumElim (c + d) = a.sumElim c + b.sumElim d := by
  ext (_ | _) <;> simp

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symm_apply]
/-
**Finsupp.sumFinsuppEquivProdFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] : (α oplus β ->₀ γ) ≃ 
(α ->₀ γ) × (β ->₀ γ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`.
-/
def sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] : (α ⊕ β →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) where
  toFun f :=
    ⟨f.comapDomain Sum.inl Sum.inl_injective.injOn,
      f.comapDomain Sum.inr Sum.inr_injective.injOn⟩
  invFun fg := sumElim fg.1 fg.2
  left_inv f := by
    ext ab
    rcases ab with a | b <;> simp
  right_inv fg := by ext <;> simp
/-
**Finsupp.fst_sumFinsuppEquivProdFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：fst_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α oplus β ->₀
 γ) (x : α) : (sumFinsuppEquivProdFinsupp f).1 x = f (Sum.inl x)
参数：f : α oplus β ->₀ γ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α ⊕ β →₀ γ) (x : α) :
    (sumFinsuppEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl
/-
**Finsupp.snd_sumFinsuppEquivProdFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：snd_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α oplus β ->₀
 γ) (y : β) : (sumFinsuppEquivProdFinsupp f).2 y = f (Sum.inr y)
参数：f : α oplus β ->₀ γ；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sumFinsuppEquivProdFinsupp {α β γ : Type*} [Zero γ] (f : α ⊕ β →₀ γ) (y : β) :
    (sumFinsuppEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl
/-
**Finsupp.sumFinsuppEquivProdFinsupp_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp
`。
形式化陈述：sumFinsuppEquivProdFinsupp_symm_inl {α β γ : Type*} [Zero γ] (fg : (α ->₀ 
γ) × (β ->₀ γ)) (x : α) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inl x) = fg.
1 x
参数：fg : (α ->₀ γ) × (β ->₀ γ)；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sumFinsuppEquivProdFinsupp_symm_inl {α β γ : Type*} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ))
    (x : α) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl
/-
**Finsupp.sumFinsuppEquivProdFinsupp_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp
`。
形式化陈述：sumFinsuppEquivProdFinsupp_symm_inr {α β γ : Type*} [Zero γ] (fg : (α ->₀ 
γ) × (β ->₀ γ)) (y : β) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inr y) = fg.
2 y
参数：fg : (α ->₀ γ) × (β ->₀ γ)；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sumFinsuppEquivProdFinsupp_symm_inr {α β γ : Type*} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ))
    (y : β) : (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

variable [AddMonoid M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps! apply symm_apply]
/-
**Finsupp.sumFinsuppAddEquivProdFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sumFinsuppAddEquivProdFinsupp {α β : Type*} : (α oplus β ->₀ M) ≃+ (α ->₀ 
M) × (β ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `Finsupp` version of `Equiv.sum_arrow_equiv_prod_arrow`.
-/
def sumFinsuppAddEquivProdFinsupp {α β : Type*} : (α ⊕ β →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
  { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [Equiv.toFun_as_coe, Prod.fst_add, Prod.snd_add, add_apply,
          snd_sumFinsuppEquivProdFinsupp, fst_sumFinsuppEquivProdFinsupp] }
/-
**Finsupp.fst_sumFinsuppAddEquivProdFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：fst_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (x :
 α) : (sumFinsuppAddEquivProdFinsupp f).1 x = f (Sum.inl x)
参数：f : α oplus β ->₀ M；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α ⊕ β →₀ M) (x : α) :
    (sumFinsuppAddEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl
/-
**Finsupp.snd_sumFinsuppAddEquivProdFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：snd_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (y :
 β) : (sumFinsuppAddEquivProdFinsupp f).2 y = f (Sum.inr y)
参数：f : α oplus β ->₀ M；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sumFinsuppAddEquivProdFinsupp {α β : Type*} (f : α ⊕ β →₀ M) (y : β) :
    (sumFinsuppAddEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl
/-
**Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `Fins
upp`。
形式化陈述：sumFinsuppAddEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α ->₀ M) × (β 
->₀ M)) (x : α) : (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x
参数：fg : (α ->₀ M) × (β ->₀ M)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumFinsuppAddEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl
/-
**Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `Fins
upp`。
形式化陈述：sumFinsuppAddEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α ->₀ M) × (β 
->₀ M)) (y : β) : (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y
参数：fg : (α ->₀ M) × (β ->₀ M)；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumFinsuppAddEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section

variable [Zero R]

/-- The `Finsupp` version of `Pi.unique`. -/
/-
**Finsupp.uniqueOfRight** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：uniqueOfRight [Subsingleton R] : Unique (α ->₀ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finsupp` version of `Pi.unique`.
-/
instance uniqueOfRight [Subsingleton R] : Unique (α →₀ R) :=
  DFunLike.coe_injective.unique

/-- The `Finsupp` version of `Pi.uniqueOfIsEmpty`. -/
/-
**Finsupp.uniqueOfLeft** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：uniqueOfLeft [IsEmpty α] : Unique (α ->₀ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finsupp` version of `Pi.uniqueOfIsEmpty`.
-/
instance uniqueOfLeft [IsEmpty α] : Unique (α →₀ R) :=
  DFunLike.coe_injective.unique

end

section
variable {M : Type*} [Zero M] {P : α → Prop} [DecidablePred P]

/-- Combine finitely supported functions over `{a // P a}` and `{a // ¬P a}`, by case-splitting on
`P a`. -/
@[simps]
/-
**Finsupp.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：piecewise (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M) : α ->₀ M where t
oFun a
参数：f : Subtype P ->₀ M；g : {a // ¬ P a} ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine finitely supported functions over `{a // P a}` and `{a // ¬P a}`, by cas
e-splitting on
`P a`.
-/
def piecewise (f : Subtype P →₀ M) (g : {a // ¬ P a} →₀ M) : α →₀ M where
  toFun a := if h : P a then f ⟨a, h⟩ else g ⟨a, h⟩
  support := (f.support.map (.subtype _)).disjUnion (g.support.map (.subtype _)) <| by
    simp_rw [Finset.disjoint_left, mem_map, forall_exists_index, Embedding.coe_subtype,
      Subtype.forall, Subtype.exists]
    rintro _ a ha ⟨-, rfl⟩ ⟨b, hb, -, rfl⟩
    exact hb ha
  mem_support_toFun a := by
    by_cases ha : P a <;> simp [ha]

@[simp]
/-
**Finsupp.subtypeDomain_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_piecewise (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M) : s
ubtypeDomain P (f.piecewise g) = f
参数：f : Subtype P ->₀ M；g : {a // ¬ P a} ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem subtypeDomain_piecewise (f : Subtype P →₀ M) (g : {a // ¬ P a} →₀ M) :
    subtypeDomain P (f.piecewise g) = f :=
  Finsupp.ext fun a => dif_pos a.prop

@[simp]
/-
**Finsupp.subtypeDomain_not_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_not_piecewise (f : Subtype P ->₀ M) (g : {a // ¬ P a} ->₀ M)
 : subtypeDomain (¬P ·) (f.piecewise g) = g
参数：f : Subtype P ->₀ M；g : {a // ¬ P a} ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem subtypeDomain_not_piecewise (f : Subtype P →₀ M) (g : {a // ¬ P a} →₀ M) :
    subtypeDomain (¬P ·) (f.piecewise g) = g :=
  Finsupp.ext fun a => dif_neg a.prop

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend the domain of a `Finsupp` by using `0` where `P x` does not hold. -/
@[simps! (attr := grind =) support apply]
/-
**Finsupp.extendDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：extendDomain (f : Subtype P ->₀ M) : α ->₀ M
参数：f : Subtype P ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the domain of a `Finsupp` by using `0` where `P x` does not hold.
-/
def extendDomain (f : Subtype P →₀ M) : α →₀ M := piecewise f 0
/-
**Finsupp.extendDomain_eq_embDomain_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：extendDomain_eq_embDomain_subtype (f : Subtype P ->₀ M) : extendDomain f =
 embDomain (.subtype _) f
参数：f : Subtype P ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.extendDomain_apply`：∀ {α : Type u_1} {M : Type u_12} [inst : Zer
o M] {P : α → Prop} [inst_1 : DecidablePred P] (f : Subtype P →₀ M) (a : α),   f
.extendDomain a …
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem extendDomain_eq_embDomain_subtype (f : Subtype P →₀ M) :
    extendDomain f = embDomain (.subtype _) f := by
  ext a
  by_cases h : P a
  · refine Eq.trans ?_ (embDomain_apply_self (.subtype P) f (Subtype.mk a h)).symm
    simp [h]
  · rw [embDomain_of_notMem_range] <;> simp [*]
/-
**Finsupp.support_extendDomain_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_extendDomain_subset (f : Subtype P ->₀ M) : ↑(f.extendDomain).supp
ort subseteq {x | P x}
参数：f : Subtype P ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_extendDomain_subset (f : Subtype P →₀ M) :
    ↑(f.extendDomain).support ⊆ {x | P x} := by
  grind

@[simp]
/-
**Finsupp.subtypeDomain_extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：subtypeDomain_extendDomain (f : Subtype P ->₀ M) : subtypeDomain P f.exten
dDomain = f
参数：f : Subtype P ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.subtypeDomain_piecewise`：subtypeDomain_piecewise (f : Subtype P 
->₀ M) (g : {a // ¬ P a} ->₀ M) : subtypeDomain P (f.piecewise g) = f
-/
theorem subtypeDomain_extendDomain (f : Subtype P →₀ M) :
    subtypeDomain P f.extendDomain = f :=
  subtypeDomain_piecewise _ _
/-
**Finsupp.extendDomain_subtypeDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：extendDomain_subtypeDomain (f : α ->₀ M) (hf : forall a in f.support, P a)
 : (subtypeDomain P f).extendDomain = f
参数：f : α ->₀ M；hf : forall a in f.support, P a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.extendDomain_apply`：∀ {α : Type u_1} {M : Type u_12} [inst : Zer
o M] {P : α → Prop} [inst_1 : DecidablePred P] (f : Subtype P →₀ M) (a : α),   f
.extendDomain a …
-/
theorem extendDomain_subtypeDomain (f : α →₀ M) (hf : ∀ a ∈ f.support, P a) :
    (subtypeDomain P f).extendDomain = f := by
  ext
  simp only [extendDomain_apply, subtypeDomain_apply, dite_eq_ite, ite_eq_left_iff]
  grind

@[simp]
/-
**Finsupp.extendDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：extendDomain_single (a : Subtype P) (m : M) : (single a m).extendDomain = 
single a.val m
参数：a : Subtype P；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.extendDomain_apply`：∀ {α : Type u_1} {M : Type u_12} [inst : Zer
o M] {P : α → Prop} [inst_1 : DecidablePred P] (f : Subtype P →₀ M) (a : α),   f
.extendDomain a …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
theorem extendDomain_single (a : Subtype P) (m : M) :
    (single a m).extendDomain = single a.val m := by
  ext a'
  obtain rfl | ha := eq_or_ne a' a.val <;>
    simp [*, a.prop, single, Pi.single, Function.update, Subtype.ext_iff]

end

/-- Given an `AddCommMonoid M` and `s : Set α`, `restrictSupportEquiv s M` is the `Equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
-- TODO: add [DecidablePred (· ∈ s)] as an assumption
/-
**Finsupp.restrictSupportEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} → (s : Set α) → (M : Type u_12) → [inst : AddCommMonoid M] 
→ { f // ↑f.support ⊆ s } ≃ (↑s →₀ M)
参数：s : Set α；M : Type u_12；↑s →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps apply] def restrictSupportEquiv (s : Set α) (M : Type*) [AddCommMonoid M] :
    { f : α →₀ M // ↑f.support ⊆ s } ≃ (s →₀ M) where
  toFun f := subtypeDomain (· ∈ s) f.1
  invFun f := letI := Classical.decPred (· ∈ s); ⟨f.extendDomain, support_extendDomain_subset _⟩
  left_inv f :=
    letI := Classical.decPred (· ∈ s); Subtype.ext <| extendDomain_subtypeDomain f.1 f.prop
  right_inv _ := letI := Classical.decPred (· ∈ s); subtypeDomain_extendDomain _

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.restrictSupportEquiv_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp
`。
形式化陈述：∀ {α : Type u_1} (s : Set α) (M : Type u_12) [inst : AddCommMonoid M] [ins
t_1 : DecidablePred fun x => x ∈ s]   (f : ↑s →₀ M), ↑((Finsupp.restrictSupportE
quiv s M).symm f) = f.extendDomain
参数：s : Set α；M : Type u_12；f : ↑s →₀ M；(Finsupp.restrictSupportEquiv s M).symm f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.restrictSupportEquiv.eq_1`：∀ {α : Type u_1} (s : Set α) (M : Typ
e u_12) [inst : AddCommMonoid M],   Finsupp.restrictSupportEquiv s M =     { toF
un := fun f => Finsupp.…
· 使用定理 `Equiv.coe_fn_symm_mk`：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α
) (l : Function.LeftInverse g f) (r : Function.RightInverse g f),   ⇑{ toFun := 
f, invFun …
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
@[simp] lemma restrictSupportEquiv_symm_apply_coe (s : Set α) (M : Type*) [AddCommMonoid M]
    [DecidablePred (· ∈ s)] (f : s →₀ M) :
    (restrictSupportEquiv s M).symm f = f.extendDomain := by
  rw [restrictSupportEquiv, Equiv.coe_fn_symm_mk, Subtype.coe_mk]; congr
/-
**Finsupp.restrictSupportEquiv_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} (s : Set α) (M : Type u_12) [inst : AddCommMonoid M] (a :
 ↑s) (x : M),   ↑((Finsupp.restrictSupportEquiv s M).symm fun₀ | a => x) = fun₀ 
| ↑a => x
参数：s : Set α；M : Type u_12；a : ↑s；x : M；(Finsupp.restrictSupportEquiv s M).symm 
fun₀ | a => x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.restrictSupportEquiv_symm_apply_coe`：∀ {α : Type u_1} (s : Set α
) (M : Type u_12) [inst : AddCommMonoid M] [inst_1 : DecidablePred fun x => x ∈ 
s]   (f : ↑s →₀ M), ↑((Finsupp.re…
· 使用定理 `Finsupp.extendDomain_single`：extendDomain_single (a : Subtype P) (m : M)
 : (single a m).extendDomain = single a.val m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma restrictSupportEquiv_symm_single (s : Set α) (M : Type*) [AddCommMonoid M]
    (a : s) (x : M) :
    (restrictSupportEquiv s M).symm (single a x) = single (a : α) x := by
  classical simp

/-- Given `AddCommMonoid M` and `e : α ≃ β`, `domCongr e` is the corresponding `Equiv` between
`α →₀ M` and `β →₀ M`.

This is `Finsupp.equivCongrLeft` as an `AddEquiv`. -/
@[simps apply]
/-
**Finsupp.domCongr** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {M : Type u_5} → [inst : AddCommMonoid M
] → α ≃ β → (α →₀ M) ≃+ (β →₀ M)
参数：α →₀ M；β →₀ M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `AddCommMonoid M` and `e : α ≃ β`, `domCongr e` is the corresponding `Equi
v` between
`α →₀ M` and `β →₀ M`.

This is `Finsupp.equivCongrLeft` as an `AddEquiv`.
-/
protected def domCongr [AddCommMonoid M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) where
  toFun := equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv v := by
    simp_rw [← equivMapDomain_trans, Equiv.self_trans_symm]
    exact equivMapDomain_refl _
  right_inv := by
    intro v
    simp_rw [← equivMapDomain_trans, Equiv.symm_trans_self]
    exact equivMapDomain_refl _
  map_add' a b := by simp only [equivMapDomain_eq_mapDomain, mapDomain_add]

@[simp]
/-
**Finsupp.domCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domCongr_refl [AddCommMonoid M] : Finsupp.domCongr (Equiv.refl α) = AddEqu
iv.refl (α ->₀ M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Finsupp.equivMapDomain_refl`：equivMapDomain_refl (l : α ->₀ M) : equivMa
pDomain (Equiv.refl _) l = l
-/
theorem domCongr_refl [AddCommMonoid M] :
    Finsupp.domCongr (Equiv.refl α) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext fun _ => equivMapDomain_refl _

@[simp]
/-
**Finsupp.domCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domCongr_symm [AddCommMonoid M] (e : α ≃ β) : (Finsupp.domCongr e).symm = 
(Finsupp.domCongr e.symm : (β ->₀ M) ≃+ (α ->₀ M))
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem domCongr_symm [AddCommMonoid M] (e : α ≃ β) :
    (Finsupp.domCongr e).symm = (Finsupp.domCongr e.symm : (β →₀ M) ≃+ (α →₀ M)) :=
  AddEquiv.ext fun _ => rfl

@[simp]
/-
**Finsupp.domCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domCongr_trans [AddCommMonoid M] (e : α ≃ β) (f : β ≃ γ) : (Finsupp.domCon
gr e).trans (Finsupp.domCongr f) = (Finsupp.domCongr (e.trans f) : (α ->₀ M) ≃+ 
_)
参数：e : α ≃ β；f : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.equivMapDomain_trans`：equivMapDomain_trans (f : α ≃ β) (g : β ≃ 
γ) (l : α ->₀ M) : equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDoma
in f l)
-/
theorem domCongr_trans [AddCommMonoid M] (e : α ≃ β) (f : β ≃ γ) :
    (Finsupp.domCongr e).trans (Finsupp.domCongr f) =
      (Finsupp.domCongr (e.trans f) : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

end Finsupp

namespace Finsupp

/-! ### Declarations about sigma types -/


section Sigma

variable {αs : ι → Type*} [Zero M] (l : (Σ i, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `Finsupp` version of `Sigma.curry`.
-/
/-
**Finsupp.split** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：split (i : ι) : αs i ->₀ M
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` t
o `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `Finsupp` version of `Sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
  l.comapDomain (Sigma.mk i) fun _ _ _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.split_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩
参数：i : ι；x : αs i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.split.eq_1`：∀ {ι : Type u_4} {M : Type u_5} {αs : ι → Type u_12}
 [inst : Zero M] (l : (i : ι) × αs i →₀ M) (i : ι),   l.split i = Finsupp.comapD
omain (S…
· 使用定理 `Finsupp.comapDomain_apply`：comapDomain_apply [Zero M] (f : α -> β) (l : 
β ->₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) (a : α) : comapDomain f l hf a = 
l (f a)
-/
theorem split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ := by
  rw [split, comapDomain_apply]

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
/-
**Finsupp.splitSupport** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：splitSupport (l : (Σ i, αs i) ->₀ M) : Finset ι
参数：l : (Σ i, αs i) ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` t
o `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of 
`l`.
-/
def splitSupport (l : (Σ i, αs i) →₀ M) : Finset ι :=
  haveI := Classical.decEq ι
  l.support.image Sigma.fst

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.mem_splitSupport_iff_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_splitSupport_iff_nonzero (i : ι) : i in splitSupport l ↔ split l i != 
0
参数：i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.splitSupport.eq_1`：∀ {ι : Type u_4} {M : Type u_5} {αs : ι → Typ
e u_12} [inst : Zero M] (l : (i : ι) × αs i →₀ M),   l.splitSupport = Finset.ima
ge Sigma.fst l.…
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.support_eq_empty`：support_eq_empty {f : α ->₀ M} : f.support = ∅
 ↔ f = 0
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Finsupp.split.eq_1`：∀ {ι : Type u_4} {M : Type u_5} {αs : ι → Type u_12}
 [inst : Zero M] (l : (i : ι) × αs i →₀ M) (i : ι),   l.split i = Finsupp.comapD
omain (S…
· 使用定理 `Finsupp.comapDomain.eq_1`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5}
 [inst : Zero M] (f : α → β) (l : β →₀ M)   (hf : Set.InjOn f (f ⁻¹' ↑l.support)
),   Finsupp.c…
· 使用定理 `Finset.Nonempty.eq_1`：∀ {α : Type u_1} (s : Finset α), s.Nonempty = ∃ x,
 x ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_splitSupport_iff_nonzero (i : ι) : i ∈ splitSupport l ↔ split l i ≠ 0 := by
  classical rw [splitSupport, mem_image, Ne, ← support_eq_empty, ← Ne,
    ← Finset.nonempty_iff_ne_empty, split, comapDomain, Finset.Nonempty]
  simp only [Finset.mem_preimage, exists_and_right, exists_eq_right, mem_support_iff,
    Sigma.exists, Ne]

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
/-
**Finsupp.splitComp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：splitComp [Zero N] (g : forall i, (αs i ->₀ M) -> N) (hg : forall i x, x =
 0 ↔ g i x = 0) : ι ->₀ N where support
参数：g : forall i, (αs i ->₀ M) -> N；hg : forall i x, x = 0 ↔ g i x = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` 
and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` d
efines a
finitely supported function from the index type `ι` to `γ` given by composing `g
 i` with
`split l i`.
-/
def splitComp [Zero N] (g : ∀ i, (αs i →₀ M) → N) (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N where
  support := splitSupport l
  toFun i := g i (split l i)
  mem_support_toFun := by
    intro i
    rw [mem_splitSupport_iff_nonzero, not_iff_not, hg]

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.sigma_support** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sigma_support : l.support = l.splitSupport.sigma fun i => (l.split i).supp
ort
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem sigma_support : l.support = l.splitSupport.sigma fun i => (l.split i).support := by
  simp_rw [Finset.ext_iff, splitSupport, split, comapDomain, Sigma.forall, mem_sigma, mem_image,
    mem_preimage]
  tauto
/-
**Finsupp.sigma_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sigma_sum [AddCommMonoid N] (f : (Σ i : ι, αs i) -> M -> N) : l.sum f = ∑ 
i in splitSupport l, (split l i).sum fun (a : αs i) b => f ⟨i, a⟩ b
参数：f : (Σ i : ι, αs i) -> M -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.sigma_support`：sigma_support : l.support = l.splitSupport.sigma 
fun i => (l.split i).support
· 使用定理 `Finset.sum_sigma`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid 
β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : Sigma σ
 → β),…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.split_apply`：split_apply (i : ι) (x : αs i) : split l i x = l ⟨i
, x⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_sum [AddCommMonoid N] (f : (Σ i : ι, αs i) → M → N) :
    l.sum f = ∑ i ∈ splitSupport l, (split l i).sum fun (a : αs i) b => f ⟨i, a⟩ b := by
  simp only [sum, sigma_support, sum_sigma, split_apply]

variable {η : Type*} [Fintype η] {ιs : η → Type*} [Zero α]

set_option backward.isDefEq.respectTransparency false in
/-- On a `Fintype η`, `Finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `Finsupp` version of `Equiv.Pi_curry`. -/
/-
**Finsupp.sigmaFinsuppEquivPiFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sigmaFinsuppEquivPiFinsupp : ((Σ j, ιs j) ->₀ α) ≃ forall j, ιs j ->₀ α wh
ere toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a `Fintype η`, `Finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →
₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `Finsupp` version of `Equiv.Pi_curry`.
-/
noncomputable def sigmaFinsuppEquivPiFinsupp : ((Σ j, ιs j) →₀ α) ≃ ∀ j, ιs j →₀ α where
  toFun := split
  invFun f :=
    onFinset (Finset.univ.sigma fun j => (f j).support) (fun ji => f ji.1 ji.2) fun _ hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv f := by
    ext
    simp [split]
  right_inv f := by
    ext
    simp [split]

@[simp]
/-
**Finsupp.sigmaFinsuppEquivPiFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sigmaFinsuppEquivPiFinsupp_apply (f : (Σ j, ιs j) ->₀ α) (j i) : sigmaFins
uppEquivPiFinsupp f j i = f ⟨j, i⟩
参数：f : (Σ j, ιs j) ->₀ α；j i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaFinsuppEquivPiFinsupp_apply (f : (Σ j, ιs j) →₀ α) (j i) :
    sigmaFinsuppEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

/-- On a `Fintype η`, `Finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `AddEquiv` version of `Finsupp.sigmaFinsuppEquivPiFinsupp`.
-/
/-
**Finsupp.sigmaFinsuppAddEquivPiFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sigmaFinsuppAddEquivPiFinsupp {α : Type*} {ιs : η -> Type*} [AddMonoid α] 
: ((Σ j, ιs j) ->₀ α) ≃+ forall j, ιs j ->₀ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a `Fintype η`, `Finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `AddEquiv` version of `Finsupp.sigmaFinsuppEquivPiFinsupp`.
-/
noncomputable def sigmaFinsuppAddEquivPiFinsupp {α : Type*} {ιs : η → Type*} [AddMonoid α] :
    ((Σ j, ιs j) →₀ α) ≃+ ∀ j, ιs j →₀ α :=
  { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }

@[simp]
/-
**Finsupp.sigmaFinsuppAddEquivPiFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp
`。
形式化陈述：sigmaFinsuppAddEquivPiFinsupp_apply {α : Type*} {ιs : η -> Type*} [AddMono
id α] (f : (Σ j, ιs j) ->₀ α) (j i) : sigmaFinsuppAddEquivPiFinsupp f j i = f ⟨j
, i⟩
参数：f : (Σ j, ιs j) ->₀ α；j i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaFinsuppAddEquivPiFinsupp_apply {α : Type*} {ιs : η → Type*} [AddMonoid α]
    (f : (Σ j, ιs j) →₀ α) (j i) : sigmaFinsuppAddEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

end Sigma

/-
**Finsupp.mem_range_embDomain_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mem_range_embDomain_iff [AddCommMonoid M] (f : α ↪ β) (x : β ->₀ M) : x in
 Set.range (embDomain f) ↔ ↑x.support subseteq Set.range f
参数：f : α ↪ β；x : β ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用引理 `Finsupp.mem_range_mapDomain_iff`：mem_range_mapDomain_iff (hf : Function.
Injective f) (x : β ->₀ M) : x in Set.range (Finsupp.mapDomain f) ↔ forall b ∉ S
et.range f, x b = 0
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
lemma mem_range_embDomain_iff [AddCommMonoid M] (f : α ↪ β) (x : β →₀ M) :
    x ∈ Set.range (embDomain f) ↔ ↑x.support ⊆ Set.range f := by
  convert! mem_range_mapDomain_iff _ f.injective _
  · ext; rw [embDomain_eq_mapDomain]
  · grind
/-
**Finsupp.embDomain_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_trans_apply [AddCommMonoid M] (v : α ->₀ M) (f : α ↪ β) (g : β ↪
 γ) : embDomain (f.trans g) v = embDomain g (embDomain f v)
参数：v : α ->₀ M；f : α ↪ β；g : β ↪ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.embDomain_eq_mapDomain`：embDomain_eq_mapDomain (f : α ↪ β) (v : 
α ->₀ M) : embDomain f v = mapDomain f v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem embDomain_trans_apply [AddCommMonoid M] (v : α →₀ M) (f : α ↪ β) (g : β ↪ γ) :
    embDomain (f.trans g) v = embDomain g (embDomain f v) := by
  simp only [embDomain_eq_mapDomain, ← mapDomain_comp, Embedding.coe_trans]
/-
**Finsupp.mapDomain_support_of_subsingletonAddUnits** 是 Mathlib 中的一个定理，位于命名空间 `F
insupp`。
形式化陈述：mapDomain_support_of_subsingletonAddUnits [DecidableEq β] [AddCommMonoid M
] (f : α -> β) [Subsingleton (AddUnits M)] (x : α ->₀ M) : (x.mapDomain f).suppo
rt = x.support.image f
参数：f : α -> β；AddUnits M；x : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mapDomain_support_of_subsingletonAddUnits [DecidableEq β] [AddCommMonoid M]
    (f : α → β) [Subsingleton (AddUnits M)] (x : α →₀ M) :
      (x.mapDomain f).support = x.support.image f := by
  ext t
  rw [mem_support_iff, ne_eq, Finset.mem_image]
  refine ⟨?_, fun ⟨i, i_in, hi⟩ ↦ ?_⟩
  · simpa [mapDomain, sum, single_apply] using fun i h h' _ ↦ ⟨i, h, h'⟩
  simpa [mapDomain, sum, ← hi, single_apply] using ⟨i, by simp [mem_support_iff.mp i_in]⟩
/-
**Finsupp.mapDomain_apply_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_apply_eq_sum [DecidableEq β] [AddCommMonoid M] (f : α -> β) (x :
 α ->₀ M) {a : α} : (x.mapDomain f) (f a) = ∑ i in x.support with f i = f a, x i
参数：f : α -> β；x : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain_apply_eq_sum [DecidableEq β] [AddCommMonoid M] (f : α → β)
    (x : α →₀ M) {a : α} : (x.mapDomain f) (f a) = ∑ i ∈ x.support with f i = f a, x i := by
  simp [mapDomain, sum, single_apply, Finset.sum_ite]
/-
**Finsupp.mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits** 是 Mathlib 中的一个定理
，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits [AddCommMonoid M] (f :
 α -> β) [Subsingleton (AddUnits M)] (x : α ->₀ M) : mapDomain (M
参数：f : α -> β；AddUnits M；x : α ->₀ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.ext_iff`：∀ {α : Type u_1} {M : Type u_4} [inst : Zero M] {f g : 
α →₀ M}, f = g ↔ ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_apply_eq_sum`：mapDomain_apply_eq_sum [DecidableEq β] [
AddCommMonoid M] (f : α -> β) (x : α ->₀ M) {a : α} : (x.mapDomain f) (f a) = ∑ 
i in x.support with …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
-/
theorem mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits [AddCommMonoid M] (f : α → β)
    [Subsingleton (AddUnits M)] (x : α →₀ M) : mapDomain (M := M) f x = 0 ↔ x = 0 := by
  classical
  refine ⟨fun h ↦ Finsupp.ext (fun i ↦ ?_), fun h ↦ by rw [h, mapDomain_zero]⟩
  replace h := Finsupp.ext_iff.mp h (f i)
  simp [mapDomain_apply_eq_sum] at h; grind

end Finsupp

