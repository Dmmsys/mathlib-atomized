/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges.  The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- `SimpleGraph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `SimpleGraph.even_card_odd_degree_vertices` is the handshaking lemma.
- `SimpleGraph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/

public section

assert_not_exists Field TwoSidedIdeal

open Finset

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj]

/-
**SimpleGraph.dart_fst_fiber** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dart_fst_fiber [DecidableEq V] (v : V) : ({d : G.Dart | d.fst = v} : Finse
t _) = univ.image (G.dartOfNeighborSet v)
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
· 使用定理 `SimpleGraph.Dart.ext`：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : G.Da
rt), d₁.toProd = d₂.toProd → d₁ = d₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem dart_fst_fiber [DecidableEq V] (v : V) :
    ({d : G.Dart | d.fst = v} : Finset _) = univ.image (G.dartOfNeighborSet v) := by
  ext d
  simp only [mem_image, true_and, mem_filter, SetCoe.exists, mem_univ]
  constructor
  · rintro rfl
    exact ⟨_, d.adj, by ext <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    rfl
/-
**SimpleGraph.dart_fst_fiber_card_eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) : #{d : G.Dart | d.f
st = v} = G.degree v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dart_fst_fiber`：dart_fst_fiber [DecidableEq V] (v : V) : ({d
 : G.Dart | d.fst = v} : Finset _) = univ.image (G.dartOfNeighborSet v)
· 使用定理 `SimpleGraph.card_neighborSet_eq_degree`：card_neighborSet_eq_degree : Fin
type.card (G.neighborSet v) = G.degree v
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `SimpleGraph.dartOfNeighborSet_injective`：dartOfNeighborSet_injective (v 
: V) : Function.Injective (G.dartOfNeighborSet v)
-/
theorem dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) :
    #{d : G.Dart | d.fst = v} = G.degree v := by
  simpa only [dart_fst_fiber, Finset.card_univ, card_neighborSet_eq_degree] using
    card_image_of_injective univ (G.dartOfNeighborSet_injective v)
/-
**SimpleGraph.dart_card_eq_sum_degrees** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
-/
theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v := by
  have := Classical.decEq V
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  exact card_eq_sum_card_fiberwise (by simp)

variable {G} in
/-
**SimpleGraph.Dart.edge_fiber** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : Fintype V] [inst_1 : DecidableR
el G.Adj] [inst_2 : DecidableEq V]   (d : G.Dart), {d' | d'.edge = d.edge} = {d,
 d.symm}
参数：d : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SimpleGraph.dart_edge_eq_iff`：dart_edge_eq_iff : forall d₁ d₂ : G.Dart, 
d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm
-/
theorem Dart.edge_fiber [DecidableEq V] (d : G.Dart) :
    ({d' : G.Dart | d'.edge = d.edge} : Finset _) = {d, d.symm} :=
  Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d
/-
**SimpleGraph.dart_edge_fiber_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dart_edge_fiber_card [DecidableEq V] (e : Sym2 V) (h : e in G.edgeSet) : #
{d : G.Dart | d.edge = e} = 2
参数：e : Sym2 V；h : e in G.edgeSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Dart.symm_ne`：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.Da
rt), d.symm ≠ d
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SimpleGraph.Dart.edge_fiber`：∀ {V : Type u} {G : SimpleGraph V} [inst : 
Fintype V] [inst_1 : DecidableRel G.Adj] [inst_2 : DecidableEq V]   (d : G.Dart)
, {d' | d'.edge =…
-/
theorem dart_edge_fiber_card [DecidableEq V] (e : Sym2 V) (h : e ∈ G.edgeSet) :
    #{d : G.Dart | d.edge = e} = 2 := by
  obtain ⟨v, w⟩ := e
  let d : G.Dart := ⟨(v, w), h⟩
  convert! congr_arg card d.edge_fiber
  rw [card_insert_of_notMem, card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm
/-
**SimpleGraph.dart_card_eq_twice_card_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * #G.edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `SimpleGraph.mem_edgeFinset`：mem_edgeFinset : e in G.edgeFinset ↔ e in G.
edgeSet
· 使用定理 `SimpleGraph.Dart.edge_mem`：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.D
art), d.edge ∈ G.edgeSet
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.sum_const_nat`：sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : foral
l x in s, f x = m) : ∑ x in s, f x = #s * m
· 使用定理 `SimpleGraph.dart_edge_fiber_card`：dart_edge_fiber_card [DecidableEq V] (
e : Sym2 V) (h : e in G.edgeSet) : #{d : G.Dart | d.edge = e} = 2
-/
theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * #G.edgeFinset := by
  classical
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_coe, mem_edgeFinset]; apply Dart.edge_mem]
  rw [← mul_comm, sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edgeFinset]

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `SimpleGraph.even_card_odd_degree_vertices`. -/
/-
**SimpleGraph.sum_degrees_eq_twice_card_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * #G.edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.dart_card_eq_sum_degrees`：dart_card_eq_sum_degrees : Fintype
.card G.Dart = ∑ v, G.degree v
· 使用定理 `SimpleGraph.dart_card_eq_twice_card_edges`：dart_card_eq_twice_card_edges
 : Fintype.card G.Dart = 2 * #G.edgeFinset

--- 原说明 ---
The degree-sum formula.  This is also known as the handshaking lemma, which migh
t
more specifically refer to `SimpleGraph.even_card_odd_degree_vertices`.
-/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * #G.edgeFinset :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges
/-
**SimpleGraph.two_mul_card_edgeFinset** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：two_mul_card_edgeFinset : 2 * #G.edgeFinset = #(univ.filter fun (x, y) => 
G.Adj x y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.dart_card_eq_twice_card_edges`：dart_card_eq_twice_card_edges
 : Fintype.card G.Dart = 2 * #G.edgeFinset
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用引理 `Finset.card_bij'`：card_bij' (i : forall a in s, β) (j : forall a in t, α
) (hi : forall a ha, i a ha in t) (hj : forall a ha, j a ha in s) (left_inv : fo
rall a…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `SimpleGraph.Dart.mk.congr_simp`：∀ {V : Type u_1} {G : SimpleGraph V} (to
Prod toProd_1 : V × V) (e_toProd : toProd = toProd_1)   (adj : G.Adj toProd.1 to
Prod.2), { toProd :=…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma two_mul_card_edgeFinset : 2 * #G.edgeFinset = #(univ.filter fun (x, y) ↦ G.Adj x y) := by
  rw [← dart_card_eq_twice_card_edges, ← card_univ]
  refine card_bij' (fun d _ ↦ (d.fst, d.snd)) (fun xy h ↦ ⟨xy, (mem_filter.1 h).2⟩) ?_ ?_ ?_ ?_
    <;> simp

/-- The degree-sum formula only counting over the vertices that form edges.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version. -/
/-
**SimpleGraph.sum_degrees_support_eq_twice_card_edges** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：sum_degrees_support_eq_twice_card_edges : ∑ v in G.support, G.degree v = 2
 * #G.edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_sum_compl`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `SimpleGraph.degree_eq_zero_iff_notMem_support`：degree_eq_zero_iff_notMem
_support : G.degree v = 0 ↔ v ∉ G.support
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s

--- 原说明 ---
The degree-sum formula only counting over the vertices that form edges.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version.
-/
theorem sum_degrees_support_eq_twice_card_edges :
    ∑ v ∈ G.support, G.degree v = 2 * #G.edgeFinset := by
  classical
  simp_rw [← sum_degrees_eq_twice_card_edges,
    ← sum_add_sum_compl G.support.toFinset, left_eq_add]
  apply Finset.sum_eq_zero
  intro v hv
  rw [degree_eq_zero_iff_notMem_support]
  rwa [mem_compl, Set.mem_toFinset] at hv

end DegreeSum

/-- The handshaking lemma.  See also `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
/-
**SimpleGraph.even_card_odd_degree_vertices** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] : Even #{v 
| Odd (G.degree v)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SimpleGraph.sum_degrees_eq_twice_card_edges`：sum_degrees_eq_twice_card_e
dges : ∑ v, G.degree v = 2 * #G.edgeFinset
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_eq_zero_iff_even`：natCast_eq_zero_iff_even {n : Nat} : (n :
 ZMod 2) = 0 ↔ Even n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ZMod.natCast_ne_zero_iff_odd`：natCast_ne_zero_iff_odd {n : Nat} : (n : Z
Mod 2) != 0 ↔ Odd n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ZMod.natCast_eq_one_iff_odd`：natCast_eq_one_iff_odd {n : Nat} : (n : ZMo
d 2) = 1 ↔ Odd n
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
The handshaking lemma.  See also `SimpleGraph.sum_degrees_eq_twice_card_edges`.
-/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even #{v | Odd (G.degree v)} := by
  have h := congr_arg (fun n => ↑n : ℕ → ZMod 2) G.sum_degrees_eq_twice_card_edges
  simp only [ZMod.natCast_self, zero_mul, Nat.cast_mul] at h
  rw [Nat.cast_sum, ← sum_filter_ne_zero] at h
  rw [sum_congr (g := fun _v ↦ (1 : ZMod 2)) rfl] at h
  · simp only [mul_one, nsmul_eq_mul, sum_const, Ne] at h
    rw [← ZMod.natCast_eq_zero_iff_even]
    convert! h
    exact ZMod.natCast_ne_zero_iff_odd.symm
  · intro v
    rw [mem_filter_univ, Ne, ZMod.natCast_eq_zero_iff_even, ZMod.natCast_eq_one_iff_odd,
      ← Nat.not_even_iff_odd]
    tauto
/-
**SimpleGraph.odd_card_odd_degree_vertices_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel 
G.Adj] (v : V) (h : Odd (G.degree v)) : Odd #{w | w != v ∧ Odd (G.degree w)}
参数：v : V；h : Odd (G.degree v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.even_card_odd_degree_vertices`：even_card_odd_degree_vertices
 [Fintype V] [DecidableRel G.Adj] : Even #{v | Odd (G.degree v)}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos_iff_of_pos_left`：mul_pos_iff_of_pos_left [PosMulStrictMono α] [P
osMulReflectLT α] (h : 0 < a) : 0 < a * b ↔ 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.filter_filter`：∀ {α : Type u_1} (p q : α → Prop) [inst : Decidabl
ePred p] [inst_1 : DecidablePred q] (s : Finset α),   Finset.filter q (Finset.fi
lter p s) …
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `tsub_eq_of_eq_add`：tsub_eq_of_eq_add (h : a = c + b) : a - b = c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd #{w | w ≠ v ∧ Odd (G.degree w)} := by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : Finset.Nonempty {v : V | Odd (G.degree v)} := by
      use v
      rw [mem_filter_univ]
      exact h
    rwa [← card_pos, hg, ← two_mul, mul_pos_iff_of_pos_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w ≠ v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w ≠ v := by
    ext w
    rw [and_comm]
  simp only [hc]
  rw [← filter_filter, filter_ne', card_erase_of_mem]
  · refine ⟨k - 1, tsub_eq_of_eq_add <| hg.trans ?_⟩
    lia
  · rwa [mem_filter_univ]
/-
**SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph`。
形式化陈述：exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj]
 (v : V) (h : Odd (G.degree v)) : exists w : V, w != v ∧ Odd (G.degree w)
参数：v : V；h : Odd (G.degree v)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.odd_card_odd_degree_vertices_ne`：odd_card_odd_degree_vertice
s_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V) (h : Odd (G.degree
 v)) : Odd #{w | w != v ∧ Odd (G.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
-/
theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : ∃ w : V, w ≠ v ∧ Odd (G.degree w) := by
  have := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : 0 < #{w | w ≠ v ∧ Odd (G.degree w)} := by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  rw [mem_filter_univ] at hw
  exact ⟨w, hw⟩

end SimpleGraph

