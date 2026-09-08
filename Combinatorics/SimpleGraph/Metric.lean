/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara, Rida Hamadani, Nelson Spence
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.ENat.Lattice

/-!
# Graph metric

This module defines the `SimpleGraph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`
which is the `ℕ`-valued version of `SimpleGraph.edist`, and `SimpleGraph.ball` which is the open
ball in the graph extended metric.

## Main definitions

- `SimpleGraph.edist` is the graph extended metric.
- `SimpleGraph.dist` is the graph metric.
- `SimpleGraph.ball` is the open ball of a given radius around a vertex.

## TODO

- Provide an additional computable version of `SimpleGraph.dist`
  for when `G` is connected.

- When directed graphs exist, a directed notion of distance,
  likely `ENat`-valued.

## Tags

graph metric, distance, ball

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ## Metric -/

section edist

/--
The extended distance between two vertices is the length of the shortest walk between them.
It is `⊤` if no such walk exists.
-/
/-
**SimpleGraph.edist** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：edist (u v : V) : Nat∞
参数：u v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended distance between two vertices is the length of the shortest walk be
tween them.
It is `⊤` if no such walk exists.
-/
noncomputable def edist (u v : V) : ℕ∞ :=
  ⨅ w : G.Walk u v, w.length

variable {G} {u v w : V}
/-
**SimpleGraph.edist_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_eq_sInf : G.edist u v = sInf (Set.range fun w : G.Walk u v => (w.len
gth : Nat∞))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_eq_sInf : G.edist u v = sInf (Set.range fun w : G.Walk u v ↦ (w.length : ℕ∞)) := rfl
/-
**SimpleGraph.Reachable.exists_walk_length_eq_edist** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, ↑p.
length = G.edist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `instWellFoundedLTENat`：WellFoundedLT ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_nonempty_iff_nonempty`：range_nonempty_iff_nonempty : (range f)
.Nonempty ↔ Nonempty ι
-/
protected theorem Reachable.exists_walk_length_eq_edist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr
/-
**SimpleGraph.Connected.exists_walk_length_eq_edist** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.Connected → ∀ (u v : V), ∃ p, ↑p.l
ength = G.edist u v
参数：u v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_edist`：∀ {V : Type u_1} {G :
 SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, ↑p.length = G.edist u v
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
protected theorem Connected.exists_walk_length_eq_edist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (hconn u v).exists_walk_length_eq_edist
/-
**SimpleGraph.edist_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_le (p : G.Walk u v) : G.edist u v <= p.length
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem edist_le (p : G.Walk u v) :
    G.edist u v ≤ p.length :=
  sInf_le ⟨p, rfl⟩
protected alias Walk.edist_le := edist_le

@[simp]
/-
**SimpleGraph.edist_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_eq_zero_iff : G.edist u v = 0 ↔ u = v
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
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edist_eq_zero_iff : G.edist u v = 0 ↔ u = v := by
  simp [edist]

@[simp]
/-
**SimpleGraph.edist_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_self : edist G v v = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.edist_eq_zero_iff`：edist_eq_zero_iff : G.edist u v = 0 ↔ u =
 v
-/
theorem edist_self : edist G v v = 0 :=
  edist_eq_zero_iff.mpr rfl
/-
**SimpleGraph.edist_pos_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_pos_of_ne (hne : u != v) : 0 < G.edist u v
参数：hne : u != v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `SimpleGraph.edist_eq_zero_iff`：edist_eq_zero_iff : G.edist u v = 0 ↔ u =
 v
-/
theorem edist_pos_of_ne (hne : u ≠ v) :
    0 < G.edist u v :=
  pos_iff_ne_zero.mpr <| edist_eq_zero_iff.ne.mpr hne
/-
**SimpleGraph.edist_eq_top_of_not_reachable** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：edist_eq_top_of_not_reachable (h : ¬G.Reachable u v) : G.edist u v = ⊤
参数：h : ¬G.Reachable u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.iInf_eq_top_of_isEmpty`：iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (
f i : Nat∞) = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.not_reachable_iff_isEmpty_walk`：not_reachable_iff_isEmpty_wa
lk {u v : V} : ¬G.Reachable u v ↔ IsEmpty (G.Walk u v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_eq_top_of_not_reachable (h : ¬G.Reachable u v) :
    G.edist u v = ⊤ := by
  simp [edist, not_reachable_iff_isEmpty_walk.mp h]
/-
**SimpleGraph.reachable_of_edist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：reachable_of_edist_ne_top (h : G.edist u v != ⊤) : G.Reachable u v
参数：h : G.edist u v != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `SimpleGraph.edist_eq_top_of_not_reachable`：edist_eq_top_of_not_reachable
 (h : ¬G.Reachable u v) : G.edist u v = ⊤
-/
theorem reachable_of_edist_ne_top (h : G.edist u v ≠ ⊤) :
    G.Reachable u v :=
  not_not.mp <| edist_eq_top_of_not_reachable.mt h
/-
**SimpleGraph.exists_walk_of_edist_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：exists_walk_of_edist_ne_top (h : G.edist u v != ⊤) : exists p : G.Walk u v
, p.length = G.edist u v
参数：h : G.edist u v != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_edist`：∀ {V : Type u_1} {G :
 SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, ↑p.length = G.edist u v
· 使用定理 `SimpleGraph.reachable_of_edist_ne_top`：reachable_of_edist_ne_top (h : G.
edist u v != ⊤) : G.Reachable u v
-/
lemma exists_walk_of_edist_ne_top (h : G.edist u v ≠ ⊤) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (reachable_of_edist_ne_top h).exists_walk_length_eq_edist
/-
**SimpleGraph.edist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v w : V}, G.edist u w ≤ G.edist u 
v + G.edist v w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用引理 `SimpleGraph.exists_walk_of_edist_ne_top`：exists_walk_of_edist_ne_top (h 
: G.edist u v != ⊤) : exists p : G.Walk u v, p.length = G.edist u v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
· 使用定理 `SimpleGraph.edist_le`：edist_le (p : G.Walk u v) : G.edist u v <= p.lengt
h
-/
protected theorem edist_triangle : G.edist u w ≤ G.edist u v + G.edist v w := by
  cases eq_or_ne (G.edist u v) ⊤ with
  | inl huv => simp [huv]
  | inr huv =>
    cases eq_or_ne (G.edist v w) ⊤ with
    | inl hvw => simp [hvw]
    | inr hvw =>
      obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top huv
      obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hvw
      rw [← hp, ← hq, ← Nat.cast_add, ← Walk.length_append]
      exact edist_le _
/-
**SimpleGraph.edist_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_comm : G.edist u v = G.edist v u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edist_eq_sInf`：edist_eq_sInf : G.edist u v = sInf (Set.range
 fun w : G.Walk u v => (w.length : Nat∞))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `SimpleGraph.Walk.reverse_surjective`：reverse_surjective {u v : V} : Func
tion.Surjective (reverse : G.Walk u v -> _)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_comm : G.edist u v = G.edist v u := by
  rw [edist_eq_sInf, ← Set.image_univ, ← Set.image_univ_of_surjective Walk.reverse_surjective,
    ← Set.image_comp, Set.image_univ, Function.comp_def]
  simp_rw [Walk.length_reverse, ← edist_eq_sInf]
/-
**SimpleGraph.exists_walk_of_edist_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：exists_walk_of_edist_eq_coe {k : Nat} (h : G.edist u v = k) : exists p : G
.Walk u v, p.length = k
参数：h : G.edist u v = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用引理 `SimpleGraph.exists_walk_of_edist_ne_top`：exists_walk_of_edist_ne_top (h 
: G.edist u v != ⊤) : exists p : G.Walk u v, p.length = G.edist u v
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma exists_walk_of_edist_eq_coe {k : ℕ} (h : G.edist u v = k) :
    ∃ p : G.Walk u v, p.length = k :=
  have : G.edist u v ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_edist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩
/-
**SimpleGraph.edist_ne_top_iff_reachable** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：edist_ne_top_iff_reachable : G.edist u v != ⊤ ↔ G.Reachable u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.reachable_of_edist_ne_top`：reachable_of_edist_ne_top (h : G.
edist u v != ⊤) : G.Reachable u v
· 使用定理 `SimpleGraph.Reachable.elim`：∀ {V : Type u} {G : SimpleGraph V} {p : Prop
} {u v : V}, G.Reachable u v → (∀ (a : G.Walk u v), p) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma edist_ne_top_iff_reachable : G.edist u v ≠ ⊤ ↔ G.Reachable u v := by
  refine ⟨reachable_of_edist_ne_top, fun h ↦ ?_⟩
  by_contra hx
  simp only [edist, iInf_eq_top, ENat.natCast_ne_top] at hx
  exact h.elim hx

/--
The extended distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
/-
**SimpleGraph.edist_eq_one_iff_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_eq_one_iff_adj : G.edist u v = 1 ↔ G.Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_walk_of_edist_ne_top`：exists_walk_of_edist_ne_top (h 
: G.edist u v != ⊤) : exists p : G.Walk u v, p.length = G.edist u v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SimpleGraph.Walk.adj_of_length_eq_one`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.length = 1 → G.Adj u v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_eq_one`：cast_eq_one {n : Nat} : (n : R) = 1 ↔ n = 1
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.edist_le`：edist_le (p : G.Walk u v) : G.edist u v <= p.lengt
h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `SimpleGraph.edist_pos_of_ne`：edist_pos_of_ne (hne : u != v) : 0 < G.edis
t u v
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b

--- 原说明 ---
The extended distance between vertices is equal to `1` if and only if these vert
ices are adjacent.
-/
theorem edist_eq_one_iff_adj : G.edist u v = 1 ↔ G.Adj u v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top <| by rw [h]; simp
    exact w.adj_of_length_eq_one <| Nat.cast_eq_one.mp <| h ▸ hw
  · exact le_antisymm (edist_le h.toWalk) (Order.one_le_iff_pos.mpr <| edist_pos_of_ne h.ne)
/-
**SimpleGraph.edist_le_one_iff_adj_or_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：edist_le_one_iff_adj_or_eq : G.edist u v <= 1 ↔ G.Adj u v ∨ u = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edist_self`：edist_self : edist G v v = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `SimpleGraph.edist_pos_of_ne`：edist_pos_of_ne (hne : u != v) : 0 < G.edis
t u v
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `SimpleGraph.edist_eq_one_iff_adj`：edist_eq_one_iff_adj : G.edist u v = 1
 ↔ G.Adj u v
-/
lemma edist_le_one_iff_adj_or_eq : G.edist u v ≤ 1 ↔ G.Adj u v ∨ u = v := by
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, or_false]
    have h : 0 < G.edist u v := edist_pos_of_ne huv
    rw [(Order.one_le_iff_pos.mpr h).ge_iff_eq']
    exact edist_eq_one_iff_adj
/-
**SimpleGraph.edist_eq_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_eq_two_iff {u v : V} : G.edist u v = 2 ↔ u != v ∧ ¬ G.Adj u v ∧ (G.c
ommonNeighbors u v).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SimpleGraph.edist_eq_zero_iff`：edist_eq_zero_iff : G.edist u v = 0 ↔ u =
 v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `SimpleGraph.exists_walk_of_edist_eq_coe`：exists_walk_of_edist_eq_coe {k 
: Nat} (h : G.edist u v = k) : exists p : G.Walk u v, p.length = k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.mem_commonNeighbors`：mem_commonNeighbors {u v w : V} : u in 
G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Walk.edist_le`：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V
} (p : G.Walk u v), G.edist u v ≤ ↑p.length
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 31 条，此处仅展示前 30 条）
-/
lemma edist_eq_two_iff {u v : V} :
    G.edist u v = 2 ↔ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ le_antisymm ?_ ?_⟩
  · simp +decide [← G.edist_eq_zero_iff.not (b := u = v), h]
  · simp +decide [← edist_eq_one_iff_adj, h]
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_coe h
    use w.getVert 1
    suffices w.getVert 1 ∈ G.commonNeighbors (w.getVert 0) (w.getVert w.length) by simpa
    refine hw ▸ G.mem_commonNeighbors.mp ?_
    exact ⟨w.adj_getVert_succ (by simp [hw]), (w.adj_getVert_succ (by simp [hw])).symm⟩
  · obtain ⟨w, hw⟩ := h.2.2
    rw [mem_commonNeighbors] at hw
    have := (Walk.cons hw.1 <| .cons hw.2.symm .nil).edist_le
    simp_all
  · by_contra
    simp_all [Order.le_one_iff]
/-
**SimpleGraph.two_lt_edist_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：two_lt_edist_iff {u v : V} : 2 < G.edist u v ↔ u != v ∧ ¬ G.Adj u v ∧ (G.c
ommonNeighbors u v) = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edist_self`：edist_self : edist G v v = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.edist_eq_one_iff_adj`：edist_eq_one_iff_adj : G.edist u v = 1
 ↔ G.Adj u v
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `SimpleGraph.edist_eq_two_iff`：edist_eq_two_iff {u v : V} : G.edist u v =
 2 ↔ u != v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma two_lt_edist_iff {u v : V} :
    2 < G.edist u v ↔ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v) = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ lt_of_le_of_ne ?_ (Ne.symm ?_)⟩
  · have hn : u ≠ v := fun hc ↦ by simp [hc] at h
    have : ¬ G.Adj u v := fun hc ↦ by simp +decide [edist_eq_one_iff_adj.mpr hc] at h
    use hn, this
    by_contra! hc
    simp [edist_eq_two_iff.mpr ⟨hn, this, hc⟩] at h
  · rw [← one_add_one_eq_two]
    refine Order.add_one_le_of_lt <| lt_of_le_of_ne ?_ ?_
    <;> grind [Order.one_le_iff_pos, pos_iff_ne_zero, edist_eq_zero_iff, edist_eq_one_iff_adj]
  · simp_all [edist_eq_two_iff]
/-
**SimpleGraph.edist_bot_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_bot_of_ne (h : u != v) : (⊥ : SimpleGraph V).edist u v = ⊤
参数：h : u != v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.edist_ne_top_iff_reachable`：edist_ne_top_iff_reachable : G.e
dist u v != ⊤ ↔ G.Reachable u v
· 使用引理 `SimpleGraph.reachable_bot`：reachable_bot {u v : V} : (⊥ : SimpleGraph V)
.Reachable u v ↔ u = v
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
-/
lemma edist_bot_of_ne (h : u ≠ v) : (⊥ : SimpleGraph V).edist u v = ⊤ := by
  rwa [ne_eq, ← reachable_bot.not, ← edist_ne_top_iff_reachable.not, not_not] at h
/-
**SimpleGraph.edist_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_bot [DecidableEq V] : (⊥ : SimpleGraph V).edist u v = (if u = v then
 0 else ⊤)
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
· 使用定理 `SimpleGraph.edist_self`：edist_self : edist G v v = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SimpleGraph.edist_bot_of_ne`：edist_bot_of_ne (h : u != v) : (⊥ : SimpleG
raph V).edist u v = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma edist_bot [DecidableEq V] : (⊥ : SimpleGraph V).edist u v = (if u = v then 0 else ⊤) := by
  by_cases h : u = v <;> simp [h, edist_bot_of_ne]
/-
**SimpleGraph.edist_top_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_top_of_ne (h : u != v) : (⊤ : SimpleGraph V).edist u v = 1
参数：h : u != v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma edist_top_of_ne (h : u ≠ v) : (⊤ : SimpleGraph V).edist u v = 1 := by
  simp [h]
/-
**SimpleGraph.edist_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_top [DecidableEq V] : (⊤ : SimpleGraph V).edist u v = (if u = v then
 0 else 1)
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
· 使用定理 `SimpleGraph.edist_self`：edist_self : edist G v v = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma edist_top [DecidableEq V] : (⊤ : SimpleGraph V).edist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

/-- Supergraphs have smaller or equal extended distances to their subgraphs. -/
@[gcongr]
/-
**SimpleGraph.edist_anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_anti {G' : SimpleGraph V} (h : G <= G') : G'.edist u v <= G.edist u 
v
参数：h : G <= G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_edist`：∀ {V : Type u_1} {G :
 SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, ↑p.length = G.edist u v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
· 使用定理 `SimpleGraph.edist_le`：edist_le (p : G.Walk u v) : G.edist u v <= p.lengt
h
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `SimpleGraph.edist_eq_top_of_not_reachable`：edist_eq_top_of_not_reachable
 (h : ¬G.Reachable u v) : G.edist u v = ⊤

--- 原说明 ---
Supergraphs have smaller or equal extended distances to their subgraphs.
-/
theorem edist_anti {G' : SimpleGraph V} (h : G ≤ G') :
    G'.edist u v ≤ G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_edist
    rw [← hw, ← Walk.length_map (.ofLE h)]
    apply edist_le
  · exact edist_eq_top_of_not_reachable hr ▸ le_top

end edist

section dist

/--
The distance between two vertices is the length of the shortest walk between them.
If no such walk exists, this uses the junk value of `0`.
-/
/-
**SimpleGraph.dist** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：dist (u v : V) : Nat
参数：u v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance between two vertices is the length of the shortest walk between the
m.
If no such walk exists, this uses the junk value of `0`.
-/
noncomputable def dist (u v : V) : ℕ :=
  (G.edist u v).toNat

variable {G} {u v w : V}
/-
**SimpleGraph.dist_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_eq_sInf : G.dist u v = sInf (Set.range (Walk.length : G.Walk u v -> N
at))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.iInf_toNat`：iInf_toNat : (⨅ i, (f i : Nat∞)).toNat = ⨅ i, f i
-/
theorem dist_eq_sInf : G.dist u v = sInf (Set.range (Walk.length : G.Walk u v → ℕ)) :=
  ENat.iInf_toNat

@[grind =]
/-
**SimpleGraph.Reachable.coe_dist_eq_edist** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → ↑(G.dist
 u v) = G.edist u v
参数：G.dist u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.edist_ne_top_iff_reachable`：edist_ne_top_iff_reachable : G.e
dist u v != ⊤ ↔ G.Reachable u v
-/
lemma Reachable.coe_dist_eq_edist (h : G.Reachable u v) : G.dist u v = G.edist u v :=
  ENat.natCast_toNat <| edist_ne_top_iff_reachable.mpr h
/-
**SimpleGraph.Reachable.exists_walk_length_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.l
ength = G.dist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_nonempty_iff_nonempty`：range_nonempty_iff_nonempty : (range f)
.Nonempty ↔ Nonempty ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.dist_eq_sInf`：dist_eq_sInf : G.dist u v = sInf (Set.range (W
alk.length : G.Walk u v -> Nat))
-/
protected theorem Reachable.exists_walk_length_eq_dist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)
/-
**SimpleGraph.Connected.exists_walk_length_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.Connected → ∀ (u v : V), ∃ p, p.le
ngth = G.dist u v
参数：u v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_dist`：∀ {V : Type u_1} {G : 
SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.length = G.dist u v
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.dist_eq_sInf`：dist_eq_sInf : G.dist u v = sInf (Set.range (W
alk.length : G.Walk u v -> Nat))
-/
protected theorem Connected.exists_walk_length_eq_dist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ (hconn u v).exists_walk_length_eq_dist
/-
**SimpleGraph.dist_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_le (p : G.Walk u v) : G.dist u v <= p.length
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.dist_eq_sInf`：dist_eq_sInf : G.dist u v = sInf (Set.range (W
alk.length : G.Walk u v -> Nat))
-/
theorem dist_le (p : G.Walk u v) : G.dist u v ≤ p.length :=
  dist_eq_sInf ▸ Nat.sInf_le ⟨p, rfl⟩

@[simp]
/-
**SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：dist_eq_zero_iff_eq_or_not_reachable : G.dist u v = 0 ↔ u = v ∨ ¬G.Reachab
le u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.dist_eq_sInf`：dist_eq_sInf : G.dist u v = sInf (Set.range (W
alk.length : G.Walk u v -> Nat))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dist_eq_zero_iff_eq_or_not_reachable :
    G.dist u v = 0 ↔ u = v ∨ ¬G.Reachable u v := by simp [dist_eq_sInf, Nat.sInf_eq_zero, Reachable]

@[simp, grind =]
/-
**SimpleGraph.dist_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_self : dist G v v = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem dist_self : dist G v v = 0 := by simp
/-
**SimpleGraph.Reachable.dist_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → (G.dist 
u v = 0 ↔ u = v)
参数：G.dist u v = 0 ↔ u = v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem Reachable.dist_eq_zero_iff (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by simp [hr]
/-
**SimpleGraph.Reachable.pos_dist_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Re
achable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → u ≠ v → 
0 < G.dist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected theorem Reachable.pos_dist_of_ne (h : G.Reachable u v) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [h, hne])
/-
**SimpleGraph.Reachable.one_lt_dist_of_ne_of_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → u ≠ v → 
¬G.Adj u v → 1 < G.dist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_le_of_ne`：∀ {n m : ℕ}, n ≤ m → ¬n = m → n < m
· 使用定理 `SimpleGraph.Reachable.pos_dist_of_ne`：∀ {V : Type u_1} {G : SimpleGraph 
V} {u v : V}, G.Reachable u v → u ≠ v → 0 < G.dist u v
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_dist`：∀ {V : Type u_1} {G : 
SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.length = G.dist u v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.Walk.exists_length_eq_one_iff`：exists_length_eq_one_iff {u v
 : V} : (exists (p : G.Walk u v), p.length = 1) ↔ G.Adj u v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Reachable.one_lt_dist_of_ne_of_not_adj (h : G.Reachable u v) (hne : u ≠ v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v :=
  Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) (by
    by_contra hc
    obtain ⟨p, hp⟩ := Reachable.exists_walk_length_eq_dist h
    exact hnadj (Walk.exists_length_eq_one_iff.mp ⟨p, hc ▸ hp⟩))
/-
**SimpleGraph.Connected.dist_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Connected → (G.dist u v 
= 0 ↔ u = v)
参数：G.dist u v = 0 ↔ u = v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) :
    G.dist u v = 0 ↔ u = v := by simp [hconn u v]
/-
**SimpleGraph.Connected.pos_dist_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Co
nnected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Connected → u ≠ v → 0 < 
G.dist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Connected.dist_eq_zero_iff`：∀ {V : Type u_1} {G : SimpleGrap
h V} {u v : V}, G.Connected → (G.dist u v = 0 ↔ u = v)
-/
protected theorem Connected.pos_dist_of_ne (hconn : G.Connected) (hne : u ≠ v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero fun h ↦ False.elim <| hne <| (hconn.dist_eq_zero_iff).mp h
/-
**SimpleGraph.Connected.one_lt_dist_of_ne_of_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Connected → u ≠ v → ¬G.A
dj u v → 1 < G.dist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.one_lt_dist_of_ne_of_not_adj`：∀ {V : Type u_1} {G 
: SimpleGraph V} {u v : V}, G.Reachable u v → u ≠ v → ¬G.Adj u v → 1 < G.dist u 
v
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
protected theorem Connected.one_lt_dist_of_ne_of_not_adj (h : G.Connected) (hne : u ≠ v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v :=
  Reachable.one_lt_dist_of_ne_of_not_adj (h u v) hne hnadj
/-
**SimpleGraph.dist_eq_zero_of_not_reachable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：dist_eq_zero_of_not_reachable (h : ¬G.Reachable u v) : G.dist u v = 0
参数：h : ¬G.Reachable u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem dist_eq_zero_of_not_reachable (h : ¬G.Reachable u v) : G.dist u v = 0 := by
  simp [h]
/-
**SimpleGraph.nonempty_of_pos_dist** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：nonempty_of_pos_dist (h : 0 < G.dist u v) : (Set.univ : Set (G.Walk u v)).
Nonempty
参数：h : 0 < G.dist u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.nonempty_of_pos_sInf`：nonempty_of_pos_sInf {s : Set Nat} (h : 0 < sI
nf s) : s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dist_eq_sInf`：dist_eq_sInf : G.dist u v = sInf (Set.range (W
alk.length : G.Walk u v -> Nat))
-/
theorem nonempty_of_pos_dist (h : 0 < G.dist u v) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [dist_eq_sInf] at h
  simpa [Set.range_nonempty_iff_nonempty, Set.nonempty_iff_univ_nonempty] using
    Nat.nonempty_of_pos_sInf h
/-
**SimpleGraph.Connected.dist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Con
nected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v w : V}, G.Connected → G.dist u w
 ≤ G.dist u v + G.dist v w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.exists_walk_length_eq_dist`：∀ {V : Type u_1} {G : 
SimpleGraph V}, G.Connected → ∀ (u v : V), ∃ p, p.length = G.dist u v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
· 使用定理 `SimpleGraph.dist_le`：dist_le (p : G.Walk u v) : G.dist u v <= p.length
-/
protected theorem Connected.dist_triangle (hconn : G.Connected) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist v w
  rw [← hp, ← hq, ← Walk.length_append]
  apply dist_le
/-
**SimpleGraph.Reachable.dist_triangle_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → ∀ (w : V
), G.dist u w ≤ G.dist u v + G.dist v w
参数：w : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
-/
lemma Reachable.dist_triangle_left (h : G.Reachable u v) (w) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast, ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]
/-
**SimpleGraph.Reachable.dist_triangle_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {v w : V}, G.Reachable v w → ∀ (u : V
), G.dist u w ≤ G.dist u v + G.dist v w
参数：u : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
-/
lemma Reachable.dist_triangle_right (h : G.Reachable v w) (u) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast, ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]
/-
**SimpleGraph.dist_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_comm : G.dist u v = G.dist v u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dist.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (u v : V), G
.dist u v = (G.edist u v).toNat
· 使用定理 `SimpleGraph.edist_comm`：edist_comm : G.edist u v = G.edist v u
-/
theorem dist_comm : G.dist u v = G.dist v u := by
  rw [dist, dist, edist_comm]
/-
**SimpleGraph.dist_ne_zero_iff_ne_and_reachable** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：dist_ne_zero_iff_ne_and_reachable : G.dist u v != 0 ↔ u != v ∧ G.Reachable
 u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dist_ne_zero_iff_ne_and_reachable : G.dist u v ≠ 0 ↔ u ≠ v ∧ G.Reachable u v := by
  simp
/-
**SimpleGraph.Reachable.of_dist_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.R
eachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.dist u v ≠ 0 → G.Reachab
le u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.dist_ne_zero_iff_ne_and_reachable`：dist_ne_zero_iff_ne_and_r
eachable : G.dist u v != 0 ↔ u != v ∧ G.Reachable u v
-/
lemma Reachable.of_dist_ne_zero (h : G.dist u v ≠ 0) : G.Reachable u v :=
  (dist_ne_zero_iff_ne_and_reachable.mp h).2
/-
**SimpleGraph.exists_walk_of_dist_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：exists_walk_of_dist_ne_zero (h : G.dist u v != 0) : exists p : G.Walk u v,
 p.length = G.dist u v
参数：h : G.dist u v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_dist`：∀ {V : Type u_1} {G : 
SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.length = G.dist u v
· 使用定理 `SimpleGraph.Reachable.of_dist_ne_zero`：∀ {V : Type u_1} {G : SimpleGraph
 V} {u v : V}, G.dist u v ≠ 0 → G.Reachable u v
-/
lemma exists_walk_of_dist_ne_zero (h : G.dist u v ≠ 0) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  (Reachable.of_dist_ne_zero h).exists_walk_length_eq_dist

/--
The distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
/-
**SimpleGraph.dist_eq_one_iff_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_eq_one_iff_adj : G.dist u v = 1 ↔ G.Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dist.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (u v : V), G
.dist u v = (G.edist u v).toNat
· 使用定理 `ENat.toNat_eq_iff`：toNat_eq_iff {m : Nat∞} {n : Nat} (hn : n != 0) : toN
at m = n ↔ m = n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ENat.natCast_one`：natCast_one : ((1 : Nat) : Nat∞) = 1
· 使用定理 `SimpleGraph.edist_eq_one_iff_adj`：edist_eq_one_iff_adj : G.edist u v = 1
 ↔ G.Adj u v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The distance between vertices is equal to `1` if and only if these vertices are 
adjacent.
-/
theorem dist_eq_one_iff_adj : G.dist u v = 1 ↔ G.Adj u v := by
  rw [dist, ENat.toNat_eq_iff, ENat.natCast_one, edist_eq_one_iff_adj]
  decide
/-
**SimpleGraph.Adj.diff_dist_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v w : V},   G.Adj v w → G.dist u w
 = G.dist u v ∨ G.dist u w = G.dist u v + 1 ∨ G.dist u w = G.dist u v - 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.dist_eq_one_iff_adj`：dist_eq_one_iff_adj : G.dist u v = 1 ↔ 
G.Adj u v
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Reachable.dist_triangle_right`：∀ {V : Type u_1} {G : SimpleG
raph V} {v w : V}, G.Reachable v w → ∀ (u : V), G.dist u w ≤ G.dist u v + G.dist
 v w
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
· 使用定理 `SimpleGraph.Reachable.dist_triangle_left`：∀ {V : Type u_1} {G : SimpleGr
aph V} {u v : V}, G.Reachable u v → ∀ (w : V), G.dist u w ≤ G.dist u v + G.dist 
v w
-/
theorem Adj.diff_dist_adj (hadj : G.Adj v w) :
    G.dist u w = G.dist u v ∨ G.dist u w = G.dist u v + 1 ∨ G.dist u w = G.dist u v - 1 := by
  by_cases! huw : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable, Reachable.trans, Adj.reachable]
  have : G.dist v w = 1 := dist_eq_one_iff_adj.mpr hadj
  have : G.dist w v = 1 := dist_eq_one_iff_adj.mpr hadj.symm
  have : G.dist u w ≤ G.dist u v + G.dist v w := hadj.reachable.dist_triangle_right u
  have : G.dist u v ≤ G.dist u w + G.dist w v := huw.dist_triangle_left v
  lia
/-
**SimpleGraph.Walk.isPath_of_length_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V} (p : G.Walk u v), p.length 
= G.dist u v → p.IsPath
参数：p : G.Walk u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.bypass_eq_self_of_length_le_length_bypass`：bypass_eq_se
lf_of_length_le_length_bypass (p : G.Walk u v) (h : p.length <= p.bypass.length)
 : p.bypass = p
· 使用定理 `SimpleGraph.dist_le`：dist_le (p : G.Walk u v) : G.dist u v <= p.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.bypass_isPath`：bypass_isPath (p : G.Walk u v) : p.bypas
s.IsPath
-/
theorem Walk.isPath_of_length_eq_dist (p : G.Walk u v) (hp : p.length = G.dist u v) :
    p.IsPath := by
  classical
  have : p.bypass = p := by
    apply bypass_eq_self_of_length_le_length_bypass
    calc p.length
      _ = G.dist u v := hp
      _ ≤ p.bypass.length := dist_le p.bypass
  rw [← this]
  apply Walk.bypass_isPath
/-
**SimpleGraph.Reachable.exists_path_of_dist** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.I
sPath ∧ p.length = G.dist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_dist`：∀ {V : Type u_1} {G : 
SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.length = G.dist u v
· 使用定理 `SimpleGraph.Walk.isPath_of_length_eq_dist`：∀ {V : Type u_1} {G : SimpleG
raph V} {u v : V} (p : G.Walk u v), p.length = G.dist u v → p.IsPath
-/
lemma Reachable.exists_path_of_dist (hr : G.Reachable u v) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hr.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩
/-
**SimpleGraph.Connected.exists_path_of_dist** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.Connected → ∀ (u v : V), ∃ p, p.Is
Path ∧ p.length = G.dist u v
参数：u v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.exists_walk_length_eq_dist`：∀ {V : Type u_1} {G : 
SimpleGraph V}, G.Connected → ∀ (u v : V), ∃ p, p.length = G.dist u v
· 使用定理 `SimpleGraph.Walk.isPath_of_length_eq_dist`：∀ {V : Type u_1} {G : SimpleG
raph V} {u v : V} (p : G.Walk u v), p.length = G.dist u v → p.IsPath
-/
lemma Connected.exists_path_of_dist (hconn : G.Connected) (u v : V) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hconn.exists_walk_length_eq_dist u v
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

@[simp]
/-
**SimpleGraph.dist_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_bot : (⊥ : SimpleGraph V).dist u v = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dist_self`：dist_self : dist G v v = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma dist_bot : (⊥ : SimpleGraph V).dist u v = 0 := by
  by_cases h : u = v <;> simp [h]
/-
**SimpleGraph.dist_top_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_top_of_ne (h : u != v) : (⊤ : SimpleGraph V).dist u v = 1
参数：h : u != v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma dist_top_of_ne (h : u ≠ v) : (⊤ : SimpleGraph V).dist u v = 1 := by
  simp [h]
/-
**SimpleGraph.dist_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_top [DecidableEq V] : (⊤ : SimpleGraph V).dist u v = (if u = v then 0
 else 1)
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
· 使用定理 `SimpleGraph.dist_self`：dist_self : dist G v v = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma dist_top [DecidableEq V] : (⊤ : SimpleGraph V).dist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]
/-
**SimpleGraph.length_eq_dist_of_subwalk** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：length_eq_dist_of_subwalk {u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'
} (h₁ : p₁.length = G.dist u v) (h₂ : p₂.IsSubwalk p₁) : p₂.length = G.dist u' v
'
参数：h₁ : p₁.length = G.dist u v；h₂ : p₂.IsSubwalk p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_of_not_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 b ≤ a → ¬b < a → a = b
· 使用定理 `SimpleGraph.dist_le`：dist_le (p : G.Walk u v) : G.dist u v <= p.length
· 使用定理 `SimpleGraph.Reachable.exists_path_of_dist`：∀ {V : Type u_1} {G : SimpleG
raph V} {u v : V}, G.Reachable u v → ∃ p, p.IsPath ∧ p.length = G.dist u v
· 使用定理 `SimpleGraph.Walk.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
 (p : G.Walk u v), G.Reachable u v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma length_eq_dist_of_subwalk {u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h₁ : p₁.length = G.dist u v) (h₂ : p₂.IsSubwalk p₁) : p₂.length = G.dist u' v' := by
  refine (dist_le _).eq_of_not_lt' fun hh ↦ ?_
  obtain ⟨ru, rv, h⟩ := h₂
  obtain ⟨s, _⟩ := p₂.reachable.exists_path_of_dist
  let r := ru.append s |>.append rv
  have : p₁.length = ru.length + p₂.length + rv.length := by simp [h]
  have : r.length = ru.length + s.length + rv.length := by simp [r]
  have := dist_le r
  lia

/-- Supergraphs have smaller or equal distances to their subgraphs. -/
@[gcongr]
/-
**SimpleGraph.Reachable.dist_anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachab
le`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V} {G' : SimpleGraph V}, G ≤ G
' → G.Reachable u v → G'.dist u v ≤ G.dist u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_walk_length_eq_dist`：∀ {V : Type u_1} {G : 
SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.length = G.dist u v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
· 使用定理 `SimpleGraph.dist_le`：dist_le (p : G.Walk u v) : G.dist u v <= p.length

--- 原说明 ---
Supergraphs have smaller or equal distances to their subgraphs.
-/
protected theorem Reachable.dist_anti {G' : SimpleGraph V} (h : G ≤ G') (hr : G.Reachable u v) :
    G'.dist u v ≤ G.dist u v := by
  obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_dist
  rw [← hw, ← Walk.length_map (.ofLE h)]
  apply dist_le

/-- This bundles and abstracts some facts about the first three vertices of a shortest walk
of length at least two: the first and third nodes are different and not connected. -/
/-
**SimpleGraph.Walk.exists_adj_adj_not_adj_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {v w : V} {p : G.Walk v w},   p.lengt
h = G.dist v w → 1 < G.dist v w → ∃ x a b, G.Adj x a ∧ G.Adj a b ∧ ¬G.Adj x b ∧ 
x ≠ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.length_tail_add_one`：length_tail_add_one {p : G.Walk u 
v} (hp : ¬ p.Nil) : p.tail.length + 1 = p.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.length_tail`：length_tail (p : G.Walk u v) : p.tail.leng
th = p.length - 1
· 使用定理 `SimpleGraph.Walk.getVert_tail`：∀ {V : Type u} {G : SimpleGraph V} {u v :
 V} {n : ℕ} (p : G.Walk u v), p.tail.getVert n = p.getVert (n + 1)
· 使用定理 `SimpleGraph.dist_le`：dist_le (p : G.Walk u v) : G.dist u v <= p.length
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))

--- 原说明 ---
This bundles and abstracts some facts about the first three vertices of a shorte
st walk
of length at least two: the first and third nodes are different and not connecte
d.
-/
lemma Walk.exists_adj_adj_not_adj_ne {p : G.Walk v w} (hp : p.length = G.dist v w)
    (hl : 1 < G.dist v w) : ∃ (x a b : V), G.Adj x a ∧ G.Adj a b ∧ ¬ G.Adj x b ∧ x ≠ b := by
  use v, p.getVert 1, p.getVert 2
  have hnp : ¬p.Nil := by grind [Nil.length_eq_zero]
  have : p.tail.tail.length < p.tail.length := by
    rw [← p.tail.length_tail_add_one (by
      simp only [not_nil_iff_lt_length, ← p.length_tail_add_one hnp] at hp ⊢
      lia)]
    lia
  have : p.tail.length < p.length := by rw [← p.length_tail_add_one hnp]; lia
  by_cases hv : v = p.getVert 2
  · have : G.dist v w ≤ p.tail.tail.length := by
      simpa [hv, p.getVert_tail] using dist_le p.tail.tail
    lia
  by_cases hadj : G.Adj v (p.getVert 2)
  · have : G.dist v w ≤ p.tail.tail.length + 1 :=
      dist_le <| p.tail.tail.cons <| p.getVert_tail ▸ hadj
    lia
  exact ⟨p.adj_snd hnp, p.adj_getVert_succ (hp ▸ hl), hadj, hv⟩

end dist

/-! ## Ball -/

section ball

/-- The open ball of radius `r` centered at the vertex `c` in the graph extended metric. -/
/-
**SimpleGraph.ball** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：ball (c : V) (r : Nat∞) : Set V
参数：c : V；r : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open ball of radius `r` centered at the vertex `c` in the graph extended met
ric.
-/
def ball (c : V) (r : ℕ∞) : Set V :=
  {v | G.edist v c < r}

variable {G} {c v : V} {r r₁ r₂ : ℕ∞}

@[simp]
/-
**SimpleGraph.mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_ball : v in G.ball c r ↔ G.edist v c < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball : v ∈ G.ball c r ↔ G.edist v c < r := .rfl

/-- The ball of radius zero is empty. -/
@[simp]
/-
**SimpleGraph.ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ball_zero : G.ball c 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The ball of radius zero is empty.
-/
theorem ball_zero : G.ball c 0 = ∅ := by simp [ball]

/-- The ball of radius one consists of just the center. -/
@[simp]
/-
**SimpleGraph.ball_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ball_one : G.ball c 1 = {c}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The ball of radius one consists of just the center.
-/
theorem ball_one : G.ball c 1 = {c} := by
  simp [ball]

/-- The ball of radius two consists of the center and its neighbors. -/
@[simp]
/-
**SimpleGraph.ball_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ball_two : G.ball c 2 = insert c (G.neighborSet c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `ENat.lt_add_one_iff`：lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The ball of radius two consists of the center and its neighbors.
-/
theorem ball_two : G.ball c 2 = insert c (G.neighborSet c) := by
  ext v
  simp [one_add_one_eq_two.symm, ENat.lt_add_one_iff ENat.one_ne_top,
    edist_le_one_iff_adj_or_eq, adj_comm, or_comm]

/-- The ball of radius `⊤` is the connected component of the center. -/
/-
**SimpleGraph.ball_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ball_top : G.ball c ⊤ = (G.connectedComponentMk c).supp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The ball of radius `⊤` is the connected component of the center.
-/
theorem ball_top :
    G.ball c ⊤ = (G.connectedComponentMk c).supp := by
  simp [Set.ext_iff, lt_top_iff_ne_top, edist_ne_top_iff_reachable]

/-- A vertex is in the ball of radius `⊤` iff it is reachable from the center. -/
/-
**SimpleGraph.mem_ball_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_ball_top : v in G.ball c ⊤ ↔ G.Reachable v c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A vertex is in the ball of radius `⊤` iff it is reachable from the center.
-/
theorem mem_ball_top : v ∈ G.ball c ⊤ ↔ G.Reachable v c := by
  simp [lt_top_iff_ne_top, edist_ne_top_iff_reachable]

/-- Balls are monotone in the radius. -/
@[gcongr]
/-
**SimpleGraph.ball_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：ball_mono (h : r₁ <= r₂) : G.ball c r₁ subseteq G.ball c r₂
参数：h : r₁ <= r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c

--- 原说明 ---
Balls are monotone in the radius.
-/
theorem ball_mono (h : r₁ ≤ r₂) : G.ball c r₁ ⊆ G.ball c r₂ :=
  fun _ hv ↦ lt_of_lt_of_le hv h

/-- The center vertex belongs to any ball of positive radius. -/
/-
**SimpleGraph.mem_ball_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_ball_self (hr : 0 < r) : c in G.ball c r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edist_self`：edist_self : edist G v v = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
The center vertex belongs to any ball of positive radius.
-/
theorem mem_ball_self (hr : 0 < r) : c ∈ G.ball c r := by
  simp [ball, hr]

/-- Ball membership is symmetric in center and point. -/
/-
**SimpleGraph.mem_ball_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_ball_comm : v in G.ball c r ↔ c in G.ball v r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `SimpleGraph.edist_comm`：edist_comm : G.edist u v = G.edist v u
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Ball membership is symmetric in center and point.
-/
theorem mem_ball_comm : v ∈ G.ball c r ↔ c ∈ G.ball v r := by
  simp [ball, edist_comm]

end ball

end SimpleGraph

