/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Diameter of a simple graph

This module defines the eccentricity of vertices, the diameter, and the radius of a simple graph.

## Main definitions

- `SimpleGraph.eccent`: the eccentricity of a vertex in a simple graph, which is the maximum
  distances between it and the other vertices.

- `SimpleGraph.ediam`: the graph extended diameter, which is the maximum eccentricity.
  It is `ℕ∞`-valued.

- `SimpleGraph.diam`: the graph diameter, an `ℕ`-valued version of `SimpleGraph.ediam`.

- `SimpleGraph.radius`: the graph radius, which is the minimum eccentricity. It is `ℕ∞`-valued.

- `SimpleGraph.center`: the set of vertices with eccentricity equal to the graph's radius.

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

section eccent

/-- The eccentricity of a vertex is the greatest distance between it and any other vertex. -/
/-
**SimpleGraph.eccent** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：eccent (G : SimpleGraph α) (u : α) : Nat∞
参数：G : SimpleGraph α；u : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The eccentricity of a vertex is the greatest distance between it and any other v
ertex.
-/
noncomputable def eccent (G : SimpleGraph α) (u : α) : ℕ∞ :=
  ⨆ v, G.edist u v
/-
**SimpleGraph.eccent_def** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_def : G.eccent = fun u => ⨆ v, G.edist u v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eccent_def : G.eccent = fun u ↦ ⨆ v, G.edist u v := rfl
/-
**SimpleGraph.edist_le_eccent** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_le_eccent {u v : α} : G.edist u v <= G.eccent u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma edist_le_eccent {u v : α} : G.edist u v ≤ G.eccent u :=
  le_iSup (G.edist u) v
/-
**SimpleGraph.exists_edist_eq_eccent_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：exists_edist_eq_eccent_of_finite [Finite α] (u : α) : exists v, G.edist u 
v = G.eccent u
参数：u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_ciSup_of_finite`：exists_eq_ciSup_of_finite [Nonempty ι] [Finit
e ι] {f : ι -> α} : exists i, f i = ⨆ i, f i
-/
lemma exists_edist_eq_eccent_of_finite [Finite α] (u : α) :
    ∃ v, G.edist u v = G.eccent u :=
  have : Nonempty α := Nonempty.intro u
  exists_eq_ciSup_of_finite
/-
**SimpleGraph.eccent_eq_top_of_not_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：eccent_eq_top_of_not_connected (h : ¬ G.Connected) (u : α) : G.eccent u = 
⊤
参数：h : ¬ G.Connected；u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_iff_exists_forall_reachable`：connected_iff_exists_
forall_reachable : G.Connected ↔ exists v, forall w, G.Reachable v w
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.edist_eq_top_of_not_reachable`：edist_eq_top_of_not_reachable
 (h : ¬G.Reachable u v) : G.edist u v = ⊤
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma eccent_eq_top_of_not_connected (h : ¬ G.Connected) (u : α) :
    G.eccent u = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨v, h⟩ := h u
  rw [eq_top_iff, ← edist_eq_top_of_not_reachable h]
  exact le_iSup (G.edist u) v
/-
**SimpleGraph.eccent_eq_zero_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：eccent_eq_zero_of_subsingleton [Subsingleton α] (u : α) : G.eccent u = 0
参数：u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
-/
lemma eccent_eq_zero_of_subsingleton [Subsingleton α] (u : α) : G.eccent u = 0 := by
  simpa [eccent, edist_eq_zero_iff] using subsingleton_iff.mp ‹_› u
/-
**SimpleGraph.eccent_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_ne_zero [Nontrivial α] (u : α) : G.eccent u != 0
参数：u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma eccent_ne_zero [Nontrivial α] (u : α) : G.eccent u ≠ 0 := by
  obtain ⟨v, huv⟩ := exists_ne ‹_›
  contrapose huv
  simp only [eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact (huv v).symm
/-
**SimpleGraph.eccent_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_eq_zero_iff (u : α) : G.eccent u = 0 ↔ Subsingleton α
参数：u : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `SimpleGraph.eccent_ne_zero`：eccent_ne_zero [Nontrivial α] (u : α) : G.ec
cent u != 0
· 使用引理 `SimpleGraph.eccent_eq_zero_of_subsingleton`：eccent_eq_zero_of_subsinglet
on [Subsingleton α] (u : α) : G.eccent u = 0
-/
lemma eccent_eq_zero_iff (u : α) : G.eccent u = 0 ↔ Subsingleton α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ eccent_eq_zero_of_subsingleton u⟩
  contrapose! h
  exact eccent_ne_zero u
/-
**SimpleGraph.eccent_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_pos_iff (u : α) : 0 < G.eccent u ↔ Nontrivial α
参数：u : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用引理 `SimpleGraph.eccent_eq_zero_iff`：eccent_eq_zero_iff (u : α) : G.eccent u 
= 0 ↔ Subsingleton α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eccent_pos_iff (u : α) : 0 < G.eccent u ↔ Nontrivial α := by
  rw [pos_iff_ne_zero, ← not_subsingleton_iff_nontrivial, ← eccent_eq_zero_iff]

@[simp]
/-
**SimpleGraph.eccent_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_bot [Nontrivial α] (u : α) : (⊥ : SimpleGraph α).eccent u = ⊤
参数：u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.eccent_eq_top_of_not_connected`：eccent_eq_top_of_not_connect
ed (h : ¬ G.Connected) (u : α) : G.eccent u = ⊤
· 使用引理 `SimpleGraph.not_connected_bot`：not_connected_bot [Nontrivial V] : ¬(⊥ : 
SimpleGraph V).Connected
-/
lemma eccent_bot [Nontrivial α] (u : α) : (⊥ : SimpleGraph α).eccent u = ⊤ :=
  eccent_eq_top_of_not_connected not_connected_bot u

@[simp]
/-
**SimpleGraph.eccent_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleGraph α).eccent u = 1
参数：u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.eccent.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α) (u : α), G
.eccent u = ⨆ v, G.edist u v
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edist_self`：edist_self : edist G v v = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `SimpleGraph.edist_top_of_ne`：edist_top_of_ne (h : u != v) : (⊤ : SimpleG
raph V).edist u v = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用引理 `SimpleGraph.eccent_ne_zero`：eccent_ne_zero [Nontrivial α] (u : α) : G.ec
cent u != 0
-/
lemma eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleGraph α).eccent u = 1 := by
  apply le_antisymm ?_ <| Order.one_le_iff_pos.mpr <| pos_iff_ne_zero.mpr <| eccent_ne_zero u
  rw [eccent, iSup_le_iff]
  intro v
  cases eq_or_ne u v <;> simp_all [edist_top_of_ne]
/-
**SimpleGraph.eq_top_iff_forall_eccent_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph`。
形式化陈述：eq_top_iff_forall_eccent_eq_one [Nontrivial α] : G = ⊤ ↔ forall u, G.eccen
t u = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.eccent_top`：eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleG
raph α).eccent u = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edist_eq_one_iff_adj`：edist_eq_one_iff_adj : G.edist u v = 1
 ↔ G.Adj u v
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SimpleGraph.edist_le_eccent`：edist_le_eccent {u v : α} : G.edist u v <= 
G.eccent u
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
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
lemma eq_top_iff_forall_eccent_eq_one [Nontrivial α] :
    G = ⊤ ↔ ∀ u, G.eccent u = 1 := by
  refine ⟨fun h ↦ h ▸ eccent_top, fun h ↦ ?_⟩
  ext u v
  refine ⟨Adj.ne, fun huv ↦ ?_⟩
  rw [← edist_eq_one_iff_adj]
  apply le_antisymm ((h u).symm ▸ edist_le_eccent)
  rw [Order.one_le_iff_pos, pos_iff_ne_zero, edist_eq_zero_iff.ne]
  exact huv.ne
/-
**SimpleGraph.eccent_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_le_iff (u : α) (k : Nat∞) : G.eccent u <= k ↔ forall v, G.edist u v
 <= k
参数：u : α；k : Nat∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
-/
lemma eccent_le_iff (u : α) (k : ℕ∞) : G.eccent u ≤ k ↔ ∀ v, G.edist u v ≤ k :=
  iSup_le_iff
/-
**SimpleGraph.eccent_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_le_one_iff (u : α) : G.eccent u <= 1 ↔ forall v, u != v -> G.Adj u 
v
参数：u : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SimpleGraph.edist_le_eccent`：edist_le_eccent {u v : α} : G.edist u v <= 
G.eccent u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `SimpleGraph.edist_pos_of_ne`：edist_pos_of_ne (hne : u != v) : 0 < G.edis
t u v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.edist_eq_one_iff_adj`：edist_eq_one_iff_adj : G.edist u v = 1
 ↔ G.Adj u v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.eccent_le_iff`：eccent_le_iff (u : α) (k : Nat∞) : G.eccent u
 <= k ↔ forall v, G.edist u v <= k
· 使用引理 `SimpleGraph.edist_le_one_iff_adj_or_eq`：edist_le_one_iff_adj_or_eq : G.e
dist u v <= 1 ↔ G.Adj u v ∨ u = v
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
-/
lemma eccent_le_one_iff (u : α) : G.eccent u ≤ 1 ↔ ∀ v, u ≠ v → G.Adj u v := by
  constructor
  · intro h v huv
    have hd : G.edist u v ≤ 1 := edist_le_eccent.trans h
    have hd' : 1 ≤ G.edist u v := Order.one_le_iff_pos.mpr (G.edist_pos_of_ne huv)
    exact edist_eq_one_iff_adj.mp (le_antisymm (hd') hd).symm
  · intro hall
    rw [eccent_le_iff]
    intro v
    rw [edist_le_one_iff_adj_or_eq]
    exact or_iff_not_imp_right.mpr (hall v)
/-
**SimpleGraph.eccent_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_eq_one_iff [Nontrivial α] (u : α) : G.eccent u = 1 ↔ forall v, u !=
 v -> G.Adj u v
参数：u : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `SimpleGraph.eccent_ne_zero`：eccent_ne_zero [Nontrivial α] (u : α) : G.ec
cent u != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用引理 `SimpleGraph.eccent_le_one_iff`：eccent_le_one_iff (u : α) : G.eccent u <=
 1 ↔ forall v, u != v -> G.Adj u v
-/
lemma eccent_eq_one_iff [Nontrivial α] (u : α) :
    G.eccent u = 1 ↔ ∀ v, u ≠ v → G.Adj u v := by
  have h : 1 ≤ G.eccent u := Order.one_le_iff_ne_zero.mpr (eccent_ne_zero u)
  rw [← h.ge_iff_eq']
  exact eccent_le_one_iff u

end eccent

section ediam

/--
The extended diameter is the greatest distance between any two vertices, with the value `⊤` in
case the distances are not bounded above, or the graph is not connected.
-/
/-
**SimpleGraph.ediam** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：ediam (G : SimpleGraph α) : Nat∞
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended diameter is the greatest distance between any two vertices, with th
e value `⊤` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def ediam (G : SimpleGraph α) : ℕ∞ :=
  ⨆ u, G.eccent u
/-
**SimpleGraph.ediam_eq_iSup_iSup_edist** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_eq_iSup_iSup_edist : G.ediam = ⨆ u, ⨆ v, G.edist u v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ediam_eq_iSup_iSup_edist : G.ediam = ⨆ u, ⨆ v, G.edist u v :=
  rfl
/-
**SimpleGraph.ediam_def** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.ediam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.ediam = 
⨆ u, G.eccent u
· 使用引理 `SimpleGraph.eccent_def`：eccent_def : G.eccent = fun u => ⨆ v, G.edist u 
v
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
-/
lemma ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.2 := by
  rw [ediam, eccent_def, iSup_prod]
/-
**SimpleGraph.eccent_le_ediam** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：eccent_le_ediam {u : α} : G.eccent u <= G.ediam
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma eccent_le_ediam {u : α} : G.eccent u ≤ G.ediam :=
  le_iSup G.eccent u
/-
**SimpleGraph.edist_le_ediam** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_le_ediam {u v : α} : G.edist u v <= G.ediam
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
lemma edist_le_ediam {u v : α} : G.edist u v ≤ G.ediam :=
  le_iSup₂ (f := G.edist) u v
/-
**SimpleGraph.ediam_le_of_edist_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_le_of_edist_le {k : Nat∞} (h : forall u v, G.edist u v <= k) : G.edi
am <= k
参数：h : forall u v, G.edist u v <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
-/
lemma ediam_le_of_edist_le {k : ℕ∞} (h : ∀ u v, G.edist u v ≤ k) : G.ediam ≤ k :=
  iSup₂_le h
/-
**SimpleGraph.ediam_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_le_iff {k : Nat∞} : G.ediam <= k ↔ forall u v, G.edist u v <= k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
-/
lemma ediam_le_iff {k : ℕ∞} : G.ediam ≤ k ↔ ∀ u v, G.edist u v ≤ k :=
  iSup₂_le_iff
/-
**SimpleGraph.ediam_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_eq_top : G.ediam = ⊤ ↔ forall b < ⊤, exists u v, b < G.edist u v
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ediam_eq_top : G.ediam = ⊤ ↔ ∀ b < ⊤, ∃ u v, b < G.edist u v := by
  simp only [ediam, eccent, iSup_eq_top, lt_iSup_iff]
/-
**SimpleGraph.ediam_eq_zero_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：ediam_eq_zero_of_subsingleton [Subsingleton α] : G.ediam = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.ediam_def`：ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.
2
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma ediam_eq_zero_of_subsingleton [Subsingleton α] : G.ediam = 0 := by
  simp [ediam_def]
/-
**SimpleGraph.nontrivial_of_ediam_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：nontrivial_of_ediam_ne_zero (h : G.ediam != 0) : Nontrivial α
参数：h : G.ediam != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `SimpleGraph.ediam_eq_zero_of_subsingleton`：ediam_eq_zero_of_subsingleton
 [Subsingleton α] : G.ediam = 0
-/
lemma nontrivial_of_ediam_ne_zero (h : G.ediam ≠ 0) : Nontrivial α := by
  contrapose! h
  exact ediam_eq_zero_of_subsingleton
/-
**SimpleGraph.ediam_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_ne_zero [Nontrivial α] : G.ediam != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma ediam_ne_zero [Nontrivial α] : G.ediam ≠ 0 := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne ‹_›
  contrapose huv
  simp only [ediam, eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact huv u v
/-
**SimpleGraph.subsingleton_of_ediam_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：subsingleton_of_ediam_eq_zero (h : G.ediam = 0) : Subsingleton α
参数：h : G.ediam = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `SimpleGraph.ediam_ne_zero`：ediam_ne_zero [Nontrivial α] : G.ediam != 0
-/
lemma subsingleton_of_ediam_eq_zero (h : G.ediam = 0) : Subsingleton α := by
  contrapose! h
  exact ediam_ne_zero
/-
**SimpleGraph.ediam_ne_zero_iff_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：ediam_ne_zero_iff_nontrivial : G.ediam != 0 ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.nontrivial_of_ediam_ne_zero`：nontrivial_of_ediam_ne_zero (h 
: G.ediam != 0) : Nontrivial α
· 使用引理 `SimpleGraph.ediam_ne_zero`：ediam_ne_zero [Nontrivial α] : G.ediam != 0
-/
lemma ediam_ne_zero_iff_nontrivial :
    G.ediam ≠ 0 ↔ Nontrivial α :=
  ⟨nontrivial_of_ediam_ne_zero, fun _ ↦ ediam_ne_zero⟩

@[simp]
/-
**SimpleGraph.ediam_eq_zero_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：ediam_eq_zero_iff_subsingleton : G.ediam = 0 ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.subsingleton_of_ediam_eq_zero`：subsingleton_of_ediam_eq_zero
 (h : G.ediam = 0) : Subsingleton α
· 使用引理 `SimpleGraph.ediam_eq_zero_of_subsingleton`：ediam_eq_zero_of_subsingleton
 [Subsingleton α] : G.ediam = 0
-/
lemma ediam_eq_zero_iff_subsingleton :
    G.ediam = 0 ↔ Subsingleton α :=
  ⟨subsingleton_of_ediam_eq_zero, fun _ ↦ ediam_eq_zero_of_subsingleton⟩
/-
**SimpleGraph.ediam_eq_top_of_not_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：ediam_eq_top_of_not_connected [Nonempty α] (h : ¬ G.Connected) : G.ediam =
 ⊤
参数：h : ¬ G.Connected。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_iff_exists_forall_reachable`：connected_iff_exists_
forall_reachable : G.Connected ↔ exists v, forall w, G.Reachable v w
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.edist_eq_top_of_not_reachable`：edist_eq_top_of_not_reachable
 (h : ¬G.Reachable u v) : G.edist u v = ⊤
· 使用引理 `SimpleGraph.edist_le_ediam`：edist_le_ediam {u v : α} : G.edist u v <= G.
ediam
-/
lemma ediam_eq_top_of_not_connected [Nonempty α] (h : ¬ G.Connected) : G.ediam = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push Not at h
  obtain ⟨_, hw⟩ := h Classical.ofNonempty
  rw [eq_top_iff, ← edist_eq_top_of_not_reachable hw]
  exact edist_le_ediam
/-
**SimpleGraph.ediam_eq_top_of_not_preconnected** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：ediam_eq_top_of_not_preconnected (h : ¬ G.Preconnected) : G.ediam = ⊤
参数：h : ¬ G.Preconnected。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsEmpty.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ True
· 使用定理 `trivial`：True
· 使用引理 `SimpleGraph.ediam_eq_top_of_not_connected`：ediam_eq_top_of_not_connected
 [Nonempty α] (h : ¬ G.Connected) : G.ediam = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.connected_iff`：∀ {V : Type u} (G : SimpleGraph V), G.Connect
ed ↔ G.Preconnected ∧ Nonempty V
-/
lemma ediam_eq_top_of_not_preconnected (h : ¬ G.Preconnected) : G.ediam = ⊤ := by
  cases isEmpty_or_nonempty α
  · exfalso
    exact h <| IsEmpty.forall_iff.mpr trivial
  · apply ediam_eq_top_of_not_connected
    rw [connected_iff]
    tauto
/-
**SimpleGraph.preconnected_of_ediam_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：preconnected_of_ediam_ne_top (h : G.ediam != ⊤) : G.Preconnected
参数：h : G.ediam != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用引理 `SimpleGraph.ediam_eq_top_of_not_preconnected`：ediam_eq_top_of_not_precon
nected (h : ¬ G.Preconnected) : G.ediam = ⊤
-/
lemma preconnected_of_ediam_ne_top (h : G.ediam ≠ ⊤) : G.Preconnected :=
  Not.imp_symm G.ediam_eq_top_of_not_preconnected h
/-
**SimpleGraph.connected_of_ediam_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：connected_of_ediam_ne_top [Nonempty α] (h : G.ediam != ⊤) : G.Connected
参数：h : G.ediam != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.connected_iff`：∀ {V : Type u} (G : SimpleGraph V), G.Connect
ed ↔ G.Preconnected ∧ Nonempty V
· 使用引理 `SimpleGraph.preconnected_of_ediam_ne_top`：preconnected_of_ediam_ne_top (
h : G.ediam != ⊤) : G.Preconnected
-/
lemma connected_of_ediam_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) : G.Connected :=
  G.connected_iff.mpr ⟨preconnected_of_ediam_ne_top h, ‹_›⟩
/-
**SimpleGraph.exists_eccent_eq_ediam_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：exists_eccent_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam != ⊤) : exists 
u, G.eccent u = G.ediam
参数：h : G.ediam != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.exists_eq_iSup_of_lt_top`：exists_eq_iSup_of_lt_top [Nonempty ι] (h 
: ⨆ i, f i < ⊤) : exists i, f i = ⨆ i, f i
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
lemma exists_eccent_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) :
    ∃ u, G.eccent u = G.ediam :=
  ENat.exists_eq_iSup_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
/-
**SimpleGraph.exists_eccent_eq_ediam_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：exists_eccent_eq_ediam_of_finite [Nonempty α] [Finite α] : exists u, G.ecc
ent u = G.ediam
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_ciSup_of_finite`：exists_eq_ciSup_of_finite [Nonempty ι] [Finit
e ι] {f : ι -> α} : exists i, f i = ⨆ i, f i
-/
lemma exists_eccent_eq_ediam_of_finite [Nonempty α] [Finite α] :
    ∃ u, G.eccent u = G.ediam :=
  exists_eq_ciSup_of_finite
/-
**SimpleGraph.exists_edist_eq_ediam_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph`。
形式化陈述：exists_edist_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam != ⊤) : exists u
 v, G.edist u v = G.ediam
参数：h : G.ediam != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.exists_eq_iSup₂_of_lt_top`：exists_eq_iSup₂_of_lt_top {ι₁ ι₂ : Type*
} {f : ι₁ -> ι₂ -> Nat∞} [Nonempty ι₁] [Nonempty ι₂] (h : ⨆ i, ⨆ j, f i j < ⊤) :
 exists i j, f i j =…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
lemma exists_edist_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) :
    ∃ u v, G.edist u v = G.ediam :=
  ENat.exists_eq_iSup₂_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
/-
**SimpleGraph.exists_edist_eq_ediam_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph`。
形式化陈述：exists_edist_eq_ediam_of_finite [Nonempty α] [Finite α] : exists u v, G.ed
ist u v = G.ediam
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.exists'`：exists' {p : α -> β -> Prop} : (exists x : α × β, p x.1 x.
2) ↔ exists a b, p a b
· 使用定理 `exists_eq_ciSup_of_finite`：exists_eq_ciSup_of_finite [Nonempty ι] [Finit
e ι] {f : ι -> α} : exists i, f i = ⨆ i, f i
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.ediam_def`：ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.
2
-/
lemma exists_edist_eq_ediam_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.edist u v = G.ediam :=
  Prod.exists'.mp <| ediam_def ▸ exists_eq_ciSup_of_finite

/-- In a finite graph with nontrivial vertex set, the graph is connected
if and only if the extended diameter is not `⊤`.
See `connected_of_ediam_ne_top` for one of the implications without
the finiteness assumptions -/
/-
**SimpleGraph.connected_iff_ediam_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：connected_iff_ediam_ne_top [Nonempty α] [Finite α] : G.Connected ↔ G.ediam
 != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_edist_eq_ediam_of_finite`：exists_edist_eq_ediam_of_fi
nite [Nonempty α] [Finite α] : exists u v, G.edist u v = G.ediam
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.edist_ne_top_iff_reachable`：edist_ne_top_iff_reachable : G.e
dist u v != ⊤ ↔ G.Reachable u v
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用引理 `SimpleGraph.connected_of_ediam_ne_top`：connected_of_ediam_ne_top [Nonemp
ty α] (h : G.ediam != ⊤) : G.Connected

--- 原说明 ---
In a finite graph with nontrivial vertex set, the graph is connected
if and only if the extended diameter is not `⊤`.
See `connected_of_ediam_ne_top` for one of the implications without
the finiteness assumptions
-/
lemma connected_iff_ediam_ne_top [Nonempty α] [Finite α] : G.Connected ↔ G.ediam ≠ ⊤ :=
  have ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  ⟨fun h ↦ huv ▸ edist_ne_top_iff_reachable.mpr (h u v),
   fun h ↦ G.connected_of_ediam_ne_top h⟩

@[gcongr]
/-
**SimpleGraph.ediam_anti** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_anti (h : G <= G') : G'.ediam <= G.ediam
参数：h : G <= G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `SimpleGraph.edist_anti`：edist_anti {G' : SimpleGraph V} (h : G <= G') : 
G'.edist u v <= G.edist u v
-/
lemma ediam_anti (h : G ≤ G') : G'.ediam ≤ G.ediam :=
  iSup₂_mono fun _ _ ↦ edist_anti h

@[simp]
/-
**SimpleGraph.ediam_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ediam = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ediam_eq_top_of_not_connected`：ediam_eq_top_of_not_connected
 [Nonempty α] (h : ¬ G.Connected) : G.ediam = ⊤
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用引理 `SimpleGraph.not_connected_bot`：not_connected_bot [Nontrivial V] : ¬(⊥ : 
SimpleGraph V).Connected
-/
lemma ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ediam = ⊤ :=
  ediam_eq_top_of_not_connected not_connected_bot

@[simp]
/-
**SimpleGraph.ediam_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ediam = 1
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
· 使用引理 `SimpleGraph.eccent_top`：eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleG
raph α).eccent u = 1
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ediam = 1 := by
  simp [ediam]

@[simp]
/-
**SimpleGraph.ediam_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.eq_top_iff_forall_eccent_eq_one`：eq_top_iff_forall_eccent_eq
_one [Nontrivial α] : G = ⊤ ↔ forall u, G.eccent u = 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SimpleGraph.eccent_le_ediam`：eccent_le_ediam {u : α} : G.eccent u <= G.e
diam
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `SimpleGraph.eccent_ne_zero`：eccent_ne_zero [Nontrivial α] (u : α) : G.ec
cent u != 0
· 使用引理 `SimpleGraph.ediam_top`：ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ed
iam = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ediam_top⟩
  rw [eq_top_iff_forall_eccent_eq_one]
  intro u
  apply le_antisymm (h ▸ eccent_le_ediam)
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
  exact eccent_ne_zero u
/-
**SimpleGraph.ediam_le_two_mul_eccent** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_le_two_mul_eccent (u : α) : G.ediam <= 2 * G.eccent u
参数：u : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ediam_le_of_edist_le`：ediam_le_of_edist_le {k : Nat∞} (h : f
orall u v, G.edist u v <= k) : G.ediam <= k
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.edist_triangle`：∀ {V : Type u_1} {G : SimpleGraph V} {u v w 
: V}, G.edist u w ≤ G.edist u v + G.edist v w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edist_comm`：edist_comm : G.edist u v = G.edist v u
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `SimpleGraph.edist_le_eccent`：edist_le_eccent {u v : α} : G.edist u v <= 
G.eccent u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
lemma ediam_le_two_mul_eccent (u : α) : G.ediam ≤ 2 * G.eccent u := by
  refine ediam_le_of_edist_le fun v w ↦ ?_
  calc
    G.edist v w
      ≤ G.edist v u + G.edist u w := G.edist_triangle
    _ = G.edist u v + G.edist u w := by rw [edist_comm]
    _ ≤ G.eccent u + G.eccent u := add_le_add edist_le_eccent edist_le_eccent
    _ = 2 * G.eccent u := (two_mul _).symm

end ediam

section diam

/--
The diameter is the greatest distance between any two vertices, with the value `0` in
case the distances are not bounded above, or the graph is not connected.
-/
/-
**SimpleGraph.diam** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：diam (G : SimpleGraph α)
参数：G : SimpleGraph α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diameter is the greatest distance between any two vertices, with the value `
0` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def diam (G : SimpleGraph α) :=
  G.ediam.toNat
/-
**SimpleGraph.diam_def** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：diam_def : G.diam = (⨆ p : α × α, G.edist p.1 p.2).toNat
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用引理 `SimpleGraph.ediam_def`：ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.
2
-/
lemma diam_def : G.diam = (⨆ p : α × α, G.edist p.1 p.2).toNat := by
  rw [diam, ediam_def]
/-
**SimpleGraph.dist_le_diam** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：dist_le_diam (h : G.ediam != ⊤) {u v : α} : G.dist u v <= G.diam
参数：h : G.ediam != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_toNat`：toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n !=
 ⊤) : toNat m <= toNat n
· 使用引理 `SimpleGraph.edist_le_ediam`：edist_le_ediam {u v : α} : G.edist u v <= G.
ediam
-/
lemma dist_le_diam (h : G.ediam ≠ ⊤) {u v : α} : G.dist u v ≤ G.diam :=
  ENat.toNat_le_toNat edist_le_ediam h
/-
**SimpleGraph.nontrivial_of_diam_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：nontrivial_of_diam_ne_zero (h : G.diam != 0) : Nontrivial α
参数：h : G.diam != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma nontrivial_of_diam_ne_zero (h : G.diam ≠ 0) : Nontrivial α := by
  contrapose! h
  simp [diam, h]
/-
**SimpleGraph.diam_eq_zero_of_not_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：diam_eq_zero_of_not_connected (h : ¬ G.Connected) : G.diam = 0
参数：h : ¬ G.Connected。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用定理 `SimpleGraph.ediam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.ediam = 
⨆ u, G.eccent u
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `SimpleGraph.ediam_eq_top_of_not_connected`：ediam_eq_top_of_not_connected
 [Nonempty α] (h : ¬ G.Connected) : G.ediam = ⊤
· 使用定理 `ENat.toNat_top`：toNat_top : toNat ⊤ = 0
-/
lemma diam_eq_zero_of_not_connected (h : ¬ G.Connected) : G.diam = 0 := by
  cases isEmpty_or_nonempty α
  · rw [diam, ediam, ciSup_of_empty, bot_eq_zero']; rfl
  · rw [diam, ediam_eq_top_of_not_connected h, ENat.toNat_top]
/-
**SimpleGraph.diam_eq_zero_of_ediam_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：diam_eq_zero_of_ediam_eq_top (h : G.ediam = ⊤) : G.diam = 0
参数：h : G.ediam = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用定理 `ENat.toNat_top`：toNat_top : toNat ⊤ = 0
-/
lemma diam_eq_zero_of_ediam_eq_top (h : G.ediam = ⊤) : G.diam = 0 := by
  rw [diam, h, ENat.toNat_top]
/-
**SimpleGraph.ediam_ne_top_of_diam_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：ediam_ne_top_of_diam_ne_zero (h : G.diam != 0) : G.ediam != ⊤
参数：h : G.diam != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `SimpleGraph.diam_eq_zero_of_ediam_eq_top`：diam_eq_zero_of_ediam_eq_top (
h : G.ediam = ⊤) : G.diam = 0
-/
lemma ediam_ne_top_of_diam_ne_zero (h : G.diam ≠ 0) : G.ediam ≠ ⊤ :=
  mt diam_eq_zero_of_ediam_eq_top h
/-
**SimpleGraph.exists_dist_eq_diam** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_dist_eq_diam [Nonempty α] : exists u v, G.dist u v = G.diam
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SimpleGraph.exists_edist_eq_ediam_of_ne_top`：exists_edist_eq_ediam_of_ne
_top [Nonempty α] (h : G.ediam != ⊤) : exists u v, G.edist u v = G.ediam
· 使用引理 `SimpleGraph.ediam_ne_top_of_diam_ne_zero`：ediam_ne_top_of_diam_ne_zero (
h : G.diam != 0) : G.ediam != ⊤
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用定理 `SimpleGraph.dist.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (u v : V), G
.dist u v = (G.edist u v).toNat
-/
lemma exists_dist_eq_diam [Nonempty α] :
    ∃ u v, G.dist u v = G.diam := by
  by_cases h : G.diam = 0
  · simp [h]
  · obtain ⟨u, v, huv⟩ := exists_edist_eq_ediam_of_ne_top <| ediam_ne_top_of_diam_ne_zero h
    use u, v
    rw [diam, dist, congrArg ENat.toNat huv]
/-
**SimpleGraph.diam_ne_zero_of_ediam_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：diam_ne_zero_of_ediam_ne_top [Nontrivial α] (h : G.ediam != ⊤) : G.diam !=
 0
参数：h : G.ediam != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `SimpleGraph.Connected.pos_dist_of_ne`：∀ {V : Type u_1} {G : SimpleGraph 
V} {u v : V}, G.Connected → u ≠ v → 0 < G.dist u v
· 使用引理 `SimpleGraph.connected_of_ediam_ne_top`：connected_of_ediam_ne_top [Nonemp
ty α] (h : G.ediam != ⊤) : G.Connected
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用引理 `SimpleGraph.dist_le_diam`：dist_le_diam (h : G.ediam != ⊤) {u v : α} : G.
dist u v <= G.diam
-/
lemma diam_ne_zero_of_ediam_ne_top [Nontrivial α] (h : G.ediam ≠ ⊤) : G.diam ≠ 0 :=
  have ⟨_, _, hne⟩ := exists_pair_ne ‹_›
  pos_iff_ne_zero.mp <|
    lt_of_lt_of_le ((connected_of_ediam_ne_top h).pos_dist_of_ne hne) <| dist_le_diam h

@[gcongr]
/-
**SimpleGraph.diam_anti_of_ediam_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：diam_anti_of_ediam_ne_top (h : G <= G') (hn : G.ediam != ⊤) : G'.diam <= G
.diam
参数：h : G <= G'；hn : G.ediam != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_toNat`：toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n !=
 ⊤) : toNat m <= toNat n
· 使用引理 `SimpleGraph.ediam_anti`：ediam_anti (h : G <= G') : G'.ediam <= G.ediam
-/
lemma diam_anti_of_ediam_ne_top (h : G ≤ G') (hn : G.ediam ≠ ⊤) : G'.diam ≤ G.diam :=
  ENat.toNat_le_toNat (ediam_anti h) hn

@[simp]
/-
**SimpleGraph.diam_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：diam_bot : (⊥ : SimpleGraph α).diam = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用定理 `ENat.toNat_eq_zero`：∀ {n : ℕ∞}, n.toNat = 0 ↔ n = 0 ∨ n = ⊤
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `SimpleGraph.ediam_eq_zero_of_subsingleton`：ediam_eq_zero_of_subsingleton
 [Subsingleton α] : G.ediam = 0
· 使用引理 `SimpleGraph.ediam_bot`：ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ed
iam = ⊤
-/
lemma diam_bot : (⊥ : SimpleGraph α).diam = 0 := by
  rw [diam, ENat.toNat_eq_zero]
  cases subsingleton_or_nontrivial α
  · exact Or.inl ediam_eq_zero_of_subsingleton
  · exact Or.inr ediam_bot

@[simp]
/-
**SimpleGraph.diam_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：diam_top [Nontrivial α] : (⊤ : SimpleGraph α).diam = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用引理 `SimpleGraph.ediam_top`：ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ed
iam = 1
· 使用定理 `ENat.toNat_one`：toNat_one : toNat 1 = 1
-/
lemma diam_top [Nontrivial α] : (⊤ : SimpleGraph α).diam = 1 := by
  rw [diam, ediam_top, ENat.toNat_one]

@[simp]
/-
**SimpleGraph.diam_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：diam_eq_zero : G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用定理 `ENat.toNat_eq_zero`：∀ {n : ℕ∞}, n.toNat = 0 ↔ n = 0 ∨ n = ⊤
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用引理 `SimpleGraph.ediam_eq_zero_iff_subsingleton`：ediam_eq_zero_iff_subsinglet
on : G.ediam = 0 ↔ Subsingleton α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma diam_eq_zero : G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α := by
  rw [diam, ENat.toNat_eq_zero, or_comm, ediam_eq_zero_iff_subsingleton]

@[simp]
/-
**SimpleGraph.diam_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：diam_eq_one [Nontrivial α] : G.diam = 1 ↔ G = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.diam.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.diam = G.
ediam.toNat
· 使用定理 `ENat.toNat_eq_iff`：toNat_eq_iff {m : Nat∞} {n : Nat} (hn : n != 0) : toN
at m = n ↔ m = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `SimpleGraph.ediam_eq_one`：ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G 
= ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma diam_eq_one [Nontrivial α] : G.diam = 1 ↔ G = ⊤ := by
  rw [diam, ENat.toNat_eq_iff one_ne_zero, Nat.cast_one, ediam_eq_one]
/-
**SimpleGraph.diam_eq_zero_iff_ediam_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：diam_eq_zero_iff_ediam_eq_top [Nontrivial α] : G.diam = 0 ↔ G.ediam = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `SimpleGraph.ediam_ne_top_of_diam_ne_zero`：ediam_ne_top_of_diam_ne_zero (
h : G.diam != 0) : G.ediam != ⊤
· 使用引理 `SimpleGraph.diam_ne_zero_of_ediam_ne_top`：diam_ne_zero_of_ediam_ne_top [
Nontrivial α] (h : G.ediam != ⊤) : G.diam != 0
-/
lemma diam_eq_zero_iff_ediam_eq_top [Nontrivial α] : G.diam = 0 ↔ G.ediam = ⊤ := by
  rw [← not_iff_not]
  exact ⟨ediam_ne_top_of_diam_ne_zero, diam_ne_zero_of_ediam_ne_top⟩

/-- A finite and nontrivial graph is connected if and only if its diameter is not zero.
See also `connected_iff_ediam_ne_top` for the extended diameter version. -/
/-
**SimpleGraph.connected_iff_diam_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：connected_iff_diam_ne_zero [Finite α] [Nontrivial α] : G.Connected ↔ G.dia
m != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_iff_ediam_ne_top`：connected_iff_ediam_ne_top [None
mpty α] [Finite α] : G.Connected ↔ G.ediam != ⊤
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `SimpleGraph.diam_eq_zero_iff_ediam_eq_top`：diam_eq_zero_iff_ediam_eq_top
 [Nontrivial α] : G.diam = 0 ↔ G.ediam = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finite and nontrivial graph is connected if and only if its diameter is not ze
ro.
See also `connected_iff_ediam_ne_top` for the extended diameter version.
-/
lemma connected_iff_diam_ne_zero [Finite α] [Nontrivial α] : G.Connected ↔ G.diam ≠ 0 := by
  rw [connected_iff_ediam_ne_top, not_iff_not, diam_eq_zero_iff_ediam_eq_top]

end diam

section radius

/-- The radius of a simple graph is the minimum eccentricity of any vertex. -/
/-
**SimpleGraph.radius** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：radius (G : SimpleGraph α) : Nat∞
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The radius of a simple graph is the minimum eccentricity of any vertex.
-/
noncomputable def radius (G : SimpleGraph α) : ℕ∞ :=
  ⨅ u, G.eccent u
/-
**SimpleGraph.radius_eq_iInf_iSup_edist** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_eq_iInf_iSup_edist : G.radius = ⨅ u, ⨆ v, G.edist u v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma radius_eq_iInf_iSup_edist : G.radius = ⨅ u, ⨆ v, G.edist u v :=
  rfl
/-
**SimpleGraph.radius_le_eccent** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_le_eccent {u : α} : G.radius <= G.eccent u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma radius_le_eccent {u : α} : G.radius ≤ G.eccent u :=
  iInf_le G.eccent u
/-
**SimpleGraph.exists_eccent_eq_radius** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_eccent_eq_radius [Nonempty α] : exists u, G.eccent u = G.radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.exists_eq_iInf`：exists_eq_iInf [Nonempty ι] (f : ι -> Nat∞) : exist
s a, f a = ⨅ x, f x
-/
lemma exists_eccent_eq_radius [Nonempty α] : ∃ u, G.eccent u = G.radius :=
  ENat.exists_eq_iInf G.eccent
/-
**SimpleGraph.exists_edist_eq_radius_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：exists_edist_eq_radius_of_finite [Nonempty α] [Finite α] : exists u v, G.e
dist u v = G.radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_eccent_eq_radius`：exists_eccent_eq_radius [Nonempty α
] : exists u, G.eccent u = G.radius
· 使用引理 `SimpleGraph.exists_edist_eq_eccent_of_finite`：exists_edist_eq_eccent_of_
finite [Finite α] (u : α) : exists v, G.edist u v = G.eccent u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma exists_edist_eq_radius_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.edist u v = G.radius := by
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite w
  use w, v
  rw [hv, hw]
/-
**SimpleGraph.radius_eq_top_of_not_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：radius_eq_top_of_not_connected (h : ¬ G.Connected) : G.radius = ⊤
参数：h : ¬ G.Connected。
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
· 使用引理 `SimpleGraph.eccent_eq_top_of_not_connected`：eccent_eq_top_of_not_connect
ed (h : ¬ G.Connected) (u : α) : G.eccent u = ⊤
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma radius_eq_top_of_not_connected (h : ¬ G.Connected) : G.radius = ⊤ := by
  simp [radius, eccent_eq_top_of_not_connected h]
/-
**SimpleGraph.radius_eq_top_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_eq_top_of_isEmpty [IsEmpty α] : G.radius = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
-/
lemma radius_eq_top_of_isEmpty [IsEmpty α] : G.radius = ⊤ :=
  iInf_of_empty G.eccent
/-
**SimpleGraph.radius_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_ne_top_iff [Nonempty α] [Finite α] : G.radius != ⊤ ↔ G.Connected
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用引理 `SimpleGraph.radius_eq_top_of_not_connected`：radius_eq_top_of_not_connect
ed (h : ¬ G.Connected) : G.radius = ⊤
· 使用引理 `SimpleGraph.exists_edist_eq_radius_of_finite`：exists_edist_eq_radius_of_
finite [Nonempty α] [Finite α] : exists u v, G.edist u v = G.radius
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.edist_ne_top_iff_reachable`：edist_ne_top_iff_reachable : G.e
dist u v != ⊤ ↔ G.Reachable u v
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
lemma radius_ne_top_iff [Nonempty α] [Finite α] : G.radius ≠ ⊤ ↔ G.Connected := by
  refine ⟨Not.imp_symm radius_eq_top_of_not_connected, fun h ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  rw [← huv, edist_ne_top_iff_reachable]
  exact h u v
/-
**SimpleGraph.radius_ne_zero_of_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：radius_ne_zero_of_nontrivial [Nontrivial α] : G.radius != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `SimpleGraph.eccent_ne_zero`：eccent_ne_zero [Nontrivial α] (u : α) : G.ec
cent u != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma radius_ne_zero_of_nontrivial [Nontrivial α] : G.radius ≠ 0 := by
  rw [← Order.one_le_iff_ne_zero]
  apply le_iInf
  simp [Order.one_le_iff_ne_zero, G.eccent_ne_zero]
/-
**SimpleGraph.radius_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_eq_zero_iff : G.radius = 0 ↔ Nonempty α ∧ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SimpleGraph.radius.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α), G.radius 
= ⨅ u, G.eccent u
· 使用定理 `ENat.iInf_eq_zero`：∀ {ι : Sort u_1} {f : ι → ℕ∞}, ⨅ i, f i = 0 ↔ ∃ i, f 
i = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma radius_eq_zero_iff : G.radius = 0 ↔ Nonempty α ∧ Subsingleton α := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ ?_⟩
  · contrapose! h
    simp [radius]
  · contrapose! h
    simp [radius_ne_zero_of_nontrivial]
  · rw [radius, ENat.iInf_eq_zero]
    use Classical.ofNonempty
    simpa [eccent] using Subsingleton.elim _
/-
**SimpleGraph.radius_le_ediam** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_le_ediam [Nonempty α] : G.radius <= G.ediam
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iInf_le_iSup`：iInf_le_iSup [Nonempty ι] : ⨅ i, f i <= ⨆ i, f i
-/
lemma radius_le_ediam [Nonempty α] : G.radius ≤ G.ediam :=
  iInf_le_iSup
/-
**SimpleGraph.ediam_eq_top_iff_radius_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：ediam_eq_top_iff_radius_eq_top [Nonempty α] : G.ediam = ⊤ ↔ G.radius = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `SimpleGraph.exists_eccent_eq_radius`：exists_eccent_eq_radius [Nonempty α
] : exists u, G.eccent u = G.radius
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SimpleGraph.ediam_le_two_mul_eccent`：ediam_le_two_mul_eccent (u : α) : G
.ediam <= 2 * G.eccent u
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `WithTop.mul_lt_top`：mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb
 : b < ⊤) : a * b < ⊤
· 使用引理 `ENat.natCast_lt_top`：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `SimpleGraph.radius_le_ediam`：radius_le_ediam [Nonempty α] : G.radius <= 
G.ediam
-/
lemma ediam_eq_top_iff_radius_eq_top [Nonempty α] : G.ediam = ⊤ ↔ G.radius = ⊤ := by
  refine ⟨?_, fun hr ↦ eq_top_iff.mpr (hr ▸ radius_le_ediam)⟩
  contrapose
  intro hr
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  have hdiam : G.ediam ≤ 2 * G.eccent w := ediam_le_two_mul_eccent w
  exact ne_top_of_lt <| lt_of_le_of_lt hdiam <| WithTop.mul_lt_top (ENat.natCast_lt_top 2) <|
    lt_top_iff_ne_top.mpr (hw ▸ hr)
/-
**SimpleGraph.ediam_le_two_mul_radius** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：ediam_le_two_mul_radius : G.ediam <= 2 * G.radius
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.radius_eq_top_of_isEmpty`：radius_eq_top_of_isEmpty [IsEmpty 
α] : G.radius = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.ediam_eq_top_iff_radius_eq_top`：ediam_eq_top_iff_radius_eq_t
op [Nonempty α] : G.ediam = ⊤ ↔ G.radius = ⊤
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `SimpleGraph.exists_eccent_eq_radius`：exists_eccent_eq_radius [Nonempty α
] : exists u, G.eccent u = G.radius
· 使用引理 `SimpleGraph.exists_edist_eq_ediam_of_ne_top`：exists_edist_eq_ediam_of_ne
_top [Nonempty α] (h : G.ediam != ⊤) : exists u v, G.edist u v = G.ediam
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `SimpleGraph.edist_triangle`：∀ {V : Type u_1} {G : SimpleGraph V} {u v w 
: V}, G.edist u w ≤ G.edist u v + G.edist v w
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `SimpleGraph.edist_le_eccent`：edist_le_eccent {u v : α} : G.edist u v <= 
G.eccent u
· 使用定理 `SimpleGraph.edist_comm`：edist_comm : G.edist u v = G.edist v u
-/
lemma ediam_le_two_mul_radius : G.ediam ≤ 2 * G.radius := by
  cases isEmpty_or_nonempty α
  · rw [radius_eq_top_of_isEmpty]
    exact le_top
  · by_cases hdiam : G.ediam = ⊤
    · simp [hdiam, ediam_eq_top_iff_radius_eq_top.mp hdiam]
    · obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
      obtain ⟨_, _, h⟩ := G.exists_edist_eq_ediam_of_ne_top hdiam
      apply le_trans (h ▸ G.edist_triangle (v := w))
      rw [two_mul]
      exact hw ▸ add_le_add (G.edist_comm ▸ G.edist_le_eccent) G.edist_le_eccent
/-
**SimpleGraph.radius_eq_ediam_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_eq_ediam_iff [Nonempty α] : G.radius = G.ediam ↔ exists e, forall u
, G.eccent u = e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SimpleGraph.eccent_le_ediam`：eccent_le_ediam {u : α} : G.eccent u <= G.e
diam
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.radius_le_eccent`：radius_le_eccent {u : α} : G.radius <= G.e
ccent u
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma radius_eq_ediam_iff [Nonempty α] :
    G.radius = G.ediam ↔ ∃ e, ∀ u, G.eccent u = e := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · use G.radius
    intro u
    exact le_antisymm (h ▸ eccent_le_ediam) radius_le_eccent
  · obtain ⟨e, h⟩ := h
    have ediam_eq : G.ediam = e :=
      le_antisymm (iSup_le fun u ↦ (h u).le) ((h Classical.ofNonempty) ▸ eccent_le_ediam)
    rw [ediam_eq]
    exact le_antisymm ((h Classical.ofNonempty) ▸ radius_le_eccent) (le_iInf fun u ↦ (h u).ge)

@[simp]
/-
**SimpleGraph.radius_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_bot [Nontrivial α] : (⊥ : SimpleGraph α).radius = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.radius_eq_top_of_not_connected`：radius_eq_top_of_not_connect
ed (h : ¬ G.Connected) : G.radius = ⊤
· 使用引理 `SimpleGraph.not_connected_bot`：not_connected_bot [Nontrivial V] : ¬(⊥ : 
SimpleGraph V).Connected
-/
lemma radius_bot [Nontrivial α] : (⊥ : SimpleGraph α).radius = ⊤ :=
  radius_eq_top_of_not_connected not_connected_bot

@[simp]
/-
**SimpleGraph.radius_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：radius_top [Nontrivial α] : (⊤ : SimpleGraph α).radius = 1
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
· 使用引理 `SimpleGraph.eccent_top`：eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleG
raph α).eccent u = 1
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma radius_top [Nontrivial α] : (⊤ : SimpleGraph α).radius = 1 := by
  simp [radius]

end radius

section center

/-- The center of a simple graph is the set of vertices with eccentricity equal to the radius. -/
/-
**SimpleGraph.center** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：center (G : SimpleGraph α) : Set α
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a simple graph is the set of vertices with eccentricity equal to t
he radius.
-/
def center (G : SimpleGraph α) : Set α :=
  {u | G.eccent u = G.radius}
/-
**SimpleGraph.center_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：center_nonempty [Nonempty α] : G.center.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_eccent_eq_radius`：exists_eccent_eq_radius [Nonempty α
] : exists u, G.eccent u = G.radius
-/
lemma center_nonempty [Nonempty α] : G.center.Nonempty :=
  exists_eccent_eq_radius
/-
**SimpleGraph.mem_center_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_center_iff (u : α) : u in G.center ↔ G.eccent u = G.radius
参数：u : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_center_iff (u : α) : u ∈ G.center ↔ G.eccent u = G.radius := .rfl
/-
**SimpleGraph.center_eq_univ_iff_radius_eq_ediam** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph`。
形式化陈述：center_eq_univ_iff_radius_eq_ediam [Nonempty α] : G.center = Set.univ ↔ G.
radius = G.ediam
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.radius_eq_ediam_iff`：radius_eq_ediam_iff [Nonempty α] : G.ra
dius = G.ediam ↔ exists e, forall u, G.eccent u = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `trivial`：True
· 使用引理 `SimpleGraph.mem_center_iff`：mem_center_iff (u : α) : u in G.center ↔ G.e
ccent u = G.radius
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `SimpleGraph.radius_le_eccent`：radius_le_eccent {u : α} : G.radius <= G.e
ccent u
-/
lemma center_eq_univ_iff_radius_eq_ediam [Nonempty α] :
    G.center = Set.univ ↔ G.radius = G.ediam := by
  rw [radius_eq_ediam_iff, ← Set.univ_subset_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · use G.radius
    exact fun _ ↦ h trivial
  · obtain ⟨e, h⟩ := h
    intro u hu
    rw [mem_center_iff, h u]
    exact le_antisymm (le_iInf fun u ↦ (h u).ge) ((h Classical.ofNonempty) ▸ radius_le_eccent)
/-
**SimpleGraph.center_eq_univ_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：center_eq_univ_of_subsingleton [Subsingleton α] : G.center = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `SimpleGraph.mem_center_iff`：mem_center_iff (u : α) : u in G.center ↔ G.e
ccent u = G.radius
· 使用引理 `SimpleGraph.eccent_eq_zero_of_subsingleton`：eccent_eq_zero_of_subsinglet
on [Subsingleton α] (u : α) : G.eccent u = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `SimpleGraph.radius_eq_zero_iff`：radius_eq_zero_iff : G.radius = 0 ↔ None
mpty α ∧ Subsingleton α
-/
lemma center_eq_univ_of_subsingleton [Subsingleton α] : G.center = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro u
  rw [mem_center_iff, eccent_eq_zero_of_subsingleton u, eq_comm, radius_eq_zero_iff]
  tauto
/-
**SimpleGraph.center_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：center_bot : (⊥ : SimpleGraph α).center = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `SimpleGraph.center_eq_univ_of_subsingleton`：center_eq_univ_of_subsinglet
on [Subsingleton α] : G.center = Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `SimpleGraph.mem_center_iff`：mem_center_iff (u : α) : u in G.center ↔ G.e
ccent u = G.radius
· 使用引理 `SimpleGraph.eccent_bot`：eccent_bot [Nontrivial α] (u : α) : (⊥ : SimpleG
raph α).eccent u = ⊤
· 使用引理 `SimpleGraph.radius_bot`：radius_bot [Nontrivial α] : (⊥ : SimpleGraph α).
radius = ⊤
-/
lemma center_bot : (⊥ : SimpleGraph α).center = Set.univ := by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff, eccent_bot, radius_bot]
/-
**SimpleGraph.center_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：center_top : (⊤ : SimpleGraph α).center = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `SimpleGraph.center_eq_univ_of_subsingleton`：center_eq_univ_of_subsinglet
on [Subsingleton α] : G.center = Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用引理 `SimpleGraph.mem_center_iff`：mem_center_iff (u : α) : u in G.center ↔ G.e
ccent u = G.radius
· 使用引理 `SimpleGraph.eccent_top`：eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleG
raph α).eccent u = 1
· 使用引理 `SimpleGraph.radius_top`：radius_top [Nontrivial α] : (⊤ : SimpleGraph α).
radius = 1
-/
lemma center_top : (⊤ : SimpleGraph α).center = Set.univ := by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff, eccent_top, radius_top]

end center

end SimpleGraph

