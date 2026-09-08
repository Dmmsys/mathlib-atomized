/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Logic.Embedding.Set

/-!
# Maps between graphs

This file defines two functions and three structures relating graphs.
The structures directly correspond to the classification of functions as
injective, surjective and bijective, and have corresponding notation.

## Main definitions

* `SimpleGraph.map`: the graph obtained by pushing the adjacency relation through
  an injective function between vertex types.
* `SimpleGraph.comap`: the graph obtained by pulling the adjacency relation behind
  an arbitrary function between vertex types.
* `SimpleGraph.induce`: the subgraph induced by the given vertex set, a wrapper around `comap`.
* `SimpleGraph.spanningCoe`: the supergraph without any additional edges, a wrapper around `map`.
* `SimpleGraph.Hom`, `G →g H`: a graph homomorphism from `G` to `H`.
* `SimpleGraph.Embedding`, `G ↪g H`: a graph embedding of `G` in `H`.
* `SimpleGraph.Iso`, `G ≃g H`: a graph isomorphism between `G` and `H`.

Note that a graph embedding is a stronger notion than an injective graph homomorphism,
since its image is an induced subgraph.

## Implementation notes

Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding` and `RelIso`.
To make use of pre-existing simp lemmas, definitions involving morphisms are
abbreviations as well.
-/

@[expose] public section


open Function

namespace SimpleGraph

variable {V W X Y : Type*} (G : SimpleGraph V) (G' : SimpleGraph W) {u v : V}

/-! ## Map and comap -/


/-- Given a function, there is a covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective when the function is (see `SimpleGraph.map_injective`). -/
/-
**SimpleGraph.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_1} → {W : Type u_2} → (V → W) → SimpleGraph V → SimpleGraph W
参数：V → W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function, there is a covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective when the function is (see `SimpleGraph.map_injective`).
-/
protected def map (f : V → W) (G : SimpleGraph V) : SimpleGraph W where
  Adj := Ne ⊓ Relation.Map G.Adj f f
  symm.symm a b := by aesop (add norm unfold Relation.Map) (add forward safe Adj.symm)
/-
**SimpleGraph.instDecidableMapAdj** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：instDecidableMapAdj [DecidableEq W] {f : V -> W} {a b} [Decidable (Relatio
n.Map G.Adj f f a b)] : Decidable ((G.map f).Adj a b)
参数：Relation.Map G.Adj f f a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableMapAdj [DecidableEq W] {f : V → W} {a b}
    [Decidable (Relation.Map G.Adj f f a b)] : Decidable ((G.map f).Adj a b) :=
  inferInstanceAs <| Decidable (_ ∧ _)

@[simp]
/-
**SimpleGraph.map_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) : (G.map f).Adj u v ↔ ex
ists u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v
参数：f : V ↪ W；G : SimpleGraph V；u v : W。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v := by
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]
/-
**SimpleGraph.map_adj'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_adj' (f : V -> W) (G : SimpleGraph V) (u v : W) : (G.map f).Adj u v ↔ 
u != v ∧ exists u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v
参数：f : V -> W；G : SimpleGraph V；u v : W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_adj' (f : V → W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ u ≠ v ∧ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl
/-
**SimpleGraph.edgeSet_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_map (f : V ↪ W) (G : SimpleGraph V) : (G.map f).edgeSet = f.sym2Ma
p '' G.edgeSet
参数：f : V ↪ W；G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `SimpleGraph.map_adj`：map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
 (G.map f).Adj u v ↔ exists u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Function.Embedding.sym2Map_apply`：∀ {α : Type u_1} {β : Type u_2} (f : α
 ↪ β) (a : Sym2 α), f.sym2Map a = Sym2.map (⇑f) a
· 使用定理 `Sym2.map_mk`：map_mk (f : α -> β) (a b : α) : map f s(a, b) = s(f a, f b)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Sym2.eq_iff`：eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ 
x = w ∧ y = z
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
theorem edgeSet_map (f : V ↪ W) (G : SimpleGraph V) :
    (G.map f).edgeSet = f.sym2Map '' G.edgeSet := by
  ext v
  induction v
  rw [mem_edgeSet, map_adj, Set.mem_image]
  constructor
  · intro ⟨a, b, hadj, ha, hb⟩
    use s(a, b), hadj
    rw [Embedding.sym2Map_apply, Sym2.map_mk, ha, hb]
  · intro ⟨e, hadj, he⟩
    induction e
    rw [Embedding.sym2Map_apply, Sym2.map_mk, Sym2.eq_iff] at he
    exact he.elim (fun ⟨h, h'⟩ ↦ ⟨_, _, hadj, h, h'⟩) (fun ⟨h', h⟩ ↦ ⟨_, _, hadj.symm, h, h'⟩)

@[simp]
/-
**SimpleGraph.neighborSet_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_map (f : V ↪ W) (v : V) : (G.map f).neighborSet (f v) = f '' G
.neighborSet v
参数：f : V ↪ W；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem neighborSet_map (f : V ↪ W) (v : V) :
    (G.map f).neighborSet (f v) = f '' G.neighborSet v := by
  refine Set.ext fun u ↦ ⟨?_, ?_⟩
  · exact fun ⟨hne, v', u', hadj, hv, hu⟩ ↦ ⟨u', f.injective hv ▸ hadj, hu⟩
  · exact fun ⟨u', hadj, hu⟩ ↦ ⟨hu ▸ f.injective.ne hadj.ne, v, u', hadj, rfl, hu⟩
/-
**SimpleGraph.map_adj_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：map_adj_apply {G : SimpleGraph V} {f : V ↪ W} {a b : V} : (G.map f).Adj (f
 a) (f b) ↔ G.Adj a b
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_adj_apply {G : SimpleGraph V} {f : V ↪ W} {a b : V} :
    (G.map f).Adj (f a) (f b) ↔ G.Adj a b := by simp

variable {G} in
/-
**SimpleGraph.map_adj_apply'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_adj_apply' {f : V -> W} (hadj : G.Adj u v) (hne : f u != f v) : (G.map
 f).Adj (f u) (f v)
参数：hadj : G.Adj u v；hne : f u != f v。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_adj_apply' {f : V → W} (hadj : G.Adj u v) (hne : f u ≠ f v) :
    (G.map f).Adj (f u) (f v) :=
  ⟨hne, u, v, hadj, rfl, rfl⟩

@[gcongr]
/-
**SimpleGraph.map_monotone** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_monotone (f : V -> W) : Monotone (SimpleGraph.map f)
参数：f : V -> W。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_monotone (f : V → W) : Monotone (SimpleGraph.map f) := by
  rintro G G' h z1 z2 ⟨huv, u, v, ha, rfl, rfl⟩
  exact ⟨huv, _, _, h ha, rfl, rfl⟩
/-
**SimpleGraph.map_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V), SimpleGraph.map id G = G
参数：G : SimpleGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[simp] lemma map_id : G.map id = G := by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]
/-
**SimpleGraph.map_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {X : Type u_3} (G : SimpleGraph V) (f : V 
→ W) (g : W → X),   SimpleGraph.map g (SimpleGraph.map f G) = SimpleGraph.map (g
 ∘ f) G
参数：G : SimpleGraph V；f : V → W；g : W → X；SimpleGraph.map f G；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[simp] lemma map_map (f : V → W) (g : W → X) : (G.map f).map g = G.map (g ∘ f) := by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]
/-
**SimpleGraph.support_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_map (f : V ↪ W) (G : SimpleGraph V) : (G.map f).support = f '' G.s
upport
参数：f : V ↪ W；G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_map (f : V ↪ W) (G : SimpleGraph V) :
    (G.map f).support = f '' G.support := by
  ext; simp [mem_support]

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`). -/
/-
**SimpleGraph.comap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_1} → {W : Type u_2} → (V → W) → SimpleGraph W → SimpleGraph V
参数：V → W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function, there is a contravariant induced map on graphs by pulling back
 the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for
 a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`).
-/
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm
/-
**SimpleGraph.comap_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {u v : V} {G : SimpleGraph W} {f : V → W},
   (SimpleGraph.comap f G).Adj u v ↔ G.Adj (f u) (f v)
参数：SimpleGraph.comap f G；f u；f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma comap_adj {G : SimpleGraph W} {f : V → W} :
    (G.comap f).Adj u v ↔ G.Adj (f u) (f v) := Iff.rfl
/-
**SimpleGraph.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, SimpleGraph.comap id G = G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
-/
@[simp] lemma comap_id {G : SimpleGraph V} : G.comap id = G := SimpleGraph.ext rfl
/-
**SimpleGraph.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {X : Type u_3} {G : SimpleGraph X} (f : V 
→ W) (g : W → X),   SimpleGraph.comap f (SimpleGraph.comap g G) = SimpleGraph.co
map (g ∘ f) G
参数：f : V → W；g : W → X；SimpleGraph.comap g G；g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_comap {G : SimpleGraph X} (f : V → W) (g : W → X) :
    (G.comap g).comap f = G.comap (g ∘ f) := rfl
/-
**SimpleGraph.support_comap_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_comap_subset (f : V -> W) (G : SimpleGraph W) : (G.comap f).suppor
t subseteq f ⁻¹' G.support
参数：f : V -> W；G : SimpleGraph W。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_comap_subset (f : V → W) (G : SimpleGraph W) :
    (G.comap f).support ⊆ f ⁻¹' G.support :=
  fun _ ⟨v, h⟩ ↦ ⟨f v, h⟩
/-
**SimpleGraph.instDecidableComapAdj** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：instDecidableComapAdj (f : V -> W) (G : SimpleGraph W) [DecidableRel G.Adj
] : DecidableRel (G.comap f).Adj
参数：f : V -> W；G : SimpleGraph W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableComapAdj (f : V → W) (G : SimpleGraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj := fun _ _ ↦ ‹DecidableRel G.Adj› _ _
/-
**SimpleGraph.comap_symm** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：comap_symm (G : SimpleGraph V) (e : V ≃ W) : G.comap e.symm.toEmbedding = 
G.map e.toEmbedding
参数：G : SimpleGraph V；e : V ≃ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_symm (G : SimpleGraph V) (e : V ≃ W) :
    G.comap e.symm.toEmbedding = G.map e.toEmbedding := by
  ext; simp only [← Equiv.eq_symm_apply, comap_adj, map_adj, Equiv.toEmbedding_apply,
    exists_eq_right_right, exists_eq_right]
/-
**SimpleGraph.map_symm** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：map_symm (G : SimpleGraph W) (e : V ≃ W) : G.map e.symm.toEmbedding = G.co
map e.toEmbedding
参数：G : SimpleGraph W；e : V ≃ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.comap_symm`：comap_symm (G : SimpleGraph V) (e : V ≃ W) : G.c
omap e.symm.toEmbedding = G.map e.toEmbedding
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
-/
lemma map_symm (G : SimpleGraph W) (e : V ≃ W) :
    G.map e.symm.toEmbedding = G.comap e.toEmbedding := by rw [← comap_symm, e.symm_symm]

@[gcongr]
/-
**SimpleGraph.comap_monotone** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f)
参数：f : V ↪ W。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) :=
  fun _ _ h _ _ ha ↦ h ha
/-
**SimpleGraph.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} (f : V → W), SimpleGraph.comap f (SimpleGr
aph.emptyGraph W) = SimpleGraph.emptyGraph V
参数：f : V → W；SimpleGraph.emptyGraph W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_bot (f : V → W) : (emptyGraph W).comap f = emptyGraph V := rfl
/-
**SimpleGraph.comap_top** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：comap_top {f : V -> W} (hf : f.Injective) : (completeGraph W).comap f = co
mpleteGraph V
参数：hf : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_top {f : V → W} (hf : f.Injective) : (completeGraph W).comap f = completeGraph V := by
  ext; simp [hf.eq_iff]

@[simp]
/-
**SimpleGraph.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G
参数：f : V ↪ W；G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := by
  ext
  simp
/-
**SimpleGraph.leftInverse_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：leftInverse_comap_map (f : V ↪ W) : Function.LeftInverse (SimpleGraph.coma
p f) (SimpleGraph.map f)
参数：f : V ↪ W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.comap_map_eq`：comap_map_eq (f : V ↪ W) (G : SimpleGraph V) :
 (G.map f).comap f = G
-/
theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f
/-
**SimpleGraph.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f)
参数：f : V ↪ W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `SimpleGraph.leftInverse_comap_map`：leftInverse_comap_map (f : V ↪ W) : F
unction.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f)
-/
theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (leftInverse_comap_map f).injective
/-
**SimpleGraph.comap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f)
参数：f : V ↪ W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `SimpleGraph.leftInverse_comap_map`：leftInverse_comap_map (f : V ↪ W) : F
unction.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f)
-/
theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (leftInverse_comap_map f).surjective
/-
**SimpleGraph.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
 G.map f <= G' ↔ G <= G'.comap f
参数：f : V ↪ W；G : SimpleGraph V；G' : SimpleGraph W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
    G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h _ _ ha => h ⟨f.injective.ne ha.ne, _, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨-, u, v, ha, rfl, rfl⟩
    exact h ha⟩
/-
**SimpleGraph.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f <= G
参数：f : V ↪ W；G : SimpleGraph W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.map_le_iff_le_comap`：map_le_iff_le_comap (f : V ↪ W) (G : Si
mpleGraph V) (G' : SimpleGraph W) : G.map f <= G' ↔ G <= G'.comap f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]
/-
**SimpleGraph.le_comap_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：le_comap_of_subsingleton (f : V -> W) [Subsingleton V] : G <= G'.comap f
参数：f : V -> W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma le_comap_of_subsingleton (f : V → W) [Subsingleton V] : G ≤ G'.comap f := by
  intro v w; simp [Subsingleton.elim v w]
/-
**SimpleGraph.map_le_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：map_le_of_subsingleton (f : V ↪ W) [Subsingleton V] : G.map f <= G'
参数：f : V ↪ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.map_le_iff_le_comap`：map_le_iff_le_comap (f : V ↪ W) (G : Si
mpleGraph V) (G' : SimpleGraph W) : G.map f <= G' ↔ G <= G'.comap f
· 使用引理 `SimpleGraph.le_comap_of_subsingleton`：le_comap_of_subsingleton (f : V ->
 W) [Subsingleton V] : G <= G'.comap f
-/
lemma map_le_of_subsingleton (f : V ↪ W) [Subsingleton V] : G.map f ≤ G' := by
  rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton

/-- Given a family of vertex types indexed by `ι`, pulling back from `⊤ : SimpleGraph ι`
yields the complete multipartite graph on the family.
Two vertices are adjacent if and only if their indices are not equal. -/
/-
**SimpleGraph.completeMultipartiteGraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph
`。
形式化陈述：completeMultipartiteGraph {ι : Type*} (V : ι -> Type*) : SimpleGraph (Σ i,
 V i)
参数：V : ι -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of vertex types indexed by `ι`, pulling back from `⊤ : SimpleGrap
h ι`
yields the complete multipartite graph on the family.
Two vertices are adjacent if and only if their indices are not equal.
-/
abbrev completeMultipartiteGraph {ι : Type*} (V : ι → Type*) : SimpleGraph (Σ i, V i) :=
  .comap Sigma.fst ⊤

/-- Equivalent types have equivalent simple graphs. -/
@[simps apply]
/-
**SimpleGraph._root_.Equiv.simpleGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalent types have equivalent simple graphs.
-/
protected def _root_.Equiv.simpleGraph (e : V ≃ W) : SimpleGraph V ≃ SimpleGraph W where
  toFun := .comap e.symm
  invFun := .comap e
  left_inv _ := by simp
  right_inv _ := by simp
/-
**SimpleGraph._root_.Equiv.simpleGraph_refl** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.Equiv.simpleGraph_refl : (Equiv.refl V).simpleGraph = Equiv.refl _ := by
  ext; rfl
/-
**SimpleGraph._root_.Equiv.simpleGraph_trans** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.Equiv.simpleGraph_trans (e₁ : V ≃ W) (e₂ : W ≃ X) :
    (e₁.trans e₂).simpleGraph = e₁.simpleGraph.trans e₂.simpleGraph := rfl

@[simp]
/-
**SimpleGraph._root_.Equiv.symm_simpleGraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Equiv.symm_simpleGraph (e : V ≃ W) : e.simpleGraph.symm = e.symm.simpleGraph := rfl

/-! ## Induced graphs -/


/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `SimpleGraph V` and `SimpleGraph s`.

There is also a notion of induced subgraphs (see `SimpleGraph.Subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
/-
**SimpleGraph.induce** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s
参数：s : Set V；G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a graph to the vertices in the set `s`, deleting all edges incident to 
vertices
outside the set. This is a wrapper around `SimpleGraph.comap`.
-/
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)

variable {G} in
/-
**SimpleGraph.induce_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：induce_adj {s : Set V} {u v : s} : (G.induce s).Adj u v ↔ G.Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma induce_adj {s : Set V} {u v : s} : (G.induce s).Adj u v ↔ G.Adj u v := .rfl
/-
**SimpleGraph.induce_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (s : Set V), SimpleGraph.induce s (SimpleGraph.completeGr
aph V) = SimpleGraph.completeGraph ↑s
参数：s : Set V；SimpleGraph.completeGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.comap_top`：comap_top {f : V -> W} (hf : f.Injective) : (comp
leteGraph W).comap f = completeGraph V
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
@[simp] lemma induce_top (s : Set V) : (completeGraph V).induce s = completeGraph s :=
  comap_top Subtype.val_injective
/-
**SimpleGraph.induce_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：induce_bot (s : Set V) : (⊥ : SimpleGraph V).induce s = ⊥
参数：s : Set V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma induce_bot (s : Set V) : (⊥ : SimpleGraph V).induce s = ⊥ := by
  dsimp
/-
**SimpleGraph.support_induce_subset_coe_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph`。
形式化陈述：support_induce_subset_coe_preimage (s : Set V) : (G.induce s).support subs
eteq (↑) ⁻¹' s
参数：s : Set V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma support_induce_subset_coe_preimage (s : Set V) : (G.induce s).support ⊆ (↑) ⁻¹' s :=
  fun v _ ↦ v.prop
/-
**SimpleGraph.support_induce_subset_coe_preimage_support** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph`。
形式化陈述：support_induce_subset_coe_preimage_support (s : Set V) : (G.induce s).supp
ort subseteq (↑) ⁻¹' G.support
参数：s : Set V。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma support_induce_subset_coe_preimage_support (s : Set V) :
    (G.induce s).support ⊆ (↑) ⁻¹' G.support :=
  fun _ ⟨v, hadj⟩ ↦ ⟨v, hadj⟩
/-
**SimpleGraph.induce_singleton_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (v : V), SimpleGraph.induce {v} G = ⊤
参数：G : SimpleGraph V；v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `SimpleGraph.le_comap_of_subsingleton`：le_comap_of_subsingleton (f : V ->
 W) [Subsingleton V] : G <= G'.comap f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
@[simp] lemma induce_singleton_eq_top (v : V) : G.induce {v} = ⊤ := by
  rw [eq_top_iff]; apply le_comap_of_subsingleton

/-- Given a graph on a set of vertices, we can make it be a `SimpleGraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `SimpleGraph.map`. -/
/-
**SimpleGraph.spanningCoe** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V
参数：G : SimpleGraph s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a graph on a set of vertices, we can make it be a `SimpleGraph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `SimpleGraph.map`.
-/
abbrev spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)
/-
**SimpleGraph.support_spanningCoe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：support_spanningCoe {s : Set V} (G : SimpleGraph s) : G.spanningCoe.suppor
t = (↑) '' G.support
参数：G : SimpleGraph s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.support_map`：support_map (f : V ↪ W) (G : SimpleGraph V) : (
G.map f).support = f '' G.support
-/
theorem support_spanningCoe {s : Set V} (G : SimpleGraph s) :
    G.spanningCoe.support = (↑) '' G.support :=
  G.support_map _
/-
**SimpleGraph.induce_spanningCoe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce 
s = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.comap_map_eq`：comap_map_eq (f : V ↪ W) (G : SimpleGraph V) :
 (G.map f).comap f = G
-/
theorem induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _
/-
**SimpleGraph.spanningCoe_induce_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe <= G
参数：s : Set V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.map_comap_le`：map_comap_le (f : V ↪ W) (G : SimpleGraph W) :
 (G.comap f).map f <= G
-/
theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _
/-
**SimpleGraph.spanningCoe_induce_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：spanningCoe_induce_eq_self (s : Set V) : (G.induce s).spanningCoe = G ↔ G.
support subseteq s
参数：s : Set V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.support_spanningCoe`：support_spanningCoe {s : Set V} (G : Si
mpleGraph s) : G.spanningCoe.support = (↑) '' G.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.spanningCoe_induce_le`：spanningCoe_induce_le (s : Set V) : (
G.induce s).spanningCoe <= G
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.Adj.left_mem_support`：∀ {V : Type u} (G : SimpleGraph V) {u 
v : V}, G.Adj u v → u ∈ G.support
· 使用定理 `SimpleGraph.Adj.right_mem_support`：∀ {V : Type u} (G : SimpleGraph V) {u
 v : V}, G.Adj u v → v ∈ G.support
-/
theorem spanningCoe_induce_eq_self (s : Set V) : (G.induce s).spanningCoe = G ↔ G.support ⊆ s := by
  refine ⟨fun h v hv ↦ ?_, fun h ↦ le_antisymm (G.spanningCoe_induce_le s) fun u v hadj ↦ ?_⟩
  · rw [← h, support_spanningCoe] at hv
    have ⟨u, _, hvu⟩ := hv
    exact hvu ▸ u.prop
  · exact ⟨hadj.ne, ⟨u, h hadj.left_mem_support⟩, ⟨v, h hadj.right_mem_support⟩, hadj, rfl, rfl⟩

@[simp]
/-
**SimpleGraph.spanningCoe_induce_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：spanningCoe_induce_support : (G.induce G.support).spanningCoe = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.spanningCoe_induce_eq_self`：spanningCoe_induce_eq_self (s : 
Set V) : (G.induce s).spanningCoe = G ↔ G.support subseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem spanningCoe_induce_support : (G.induce G.support).spanningCoe = G :=
  G.spanningCoe_induce_eq_self _ |>.mpr .rfl

@[simp]
/-
**SimpleGraph.spanningCoe_induce_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：spanningCoe_induce_univ : (G.induce .univ).spanningCoe = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.spanningCoe_induce_eq_self`：spanningCoe_induce_eq_self (s : 
Set V) : (G.induce s).spanningCoe = G ↔ G.support subseteq s
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem spanningCoe_induce_univ : (G.induce .univ).spanningCoe = G :=
  G.spanningCoe_induce_eq_self _ |>.mpr G.support.subset_univ

open Set.Notation in
/-
**SimpleGraph.IsCompleteBetween.induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
CompleteBetween`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) {s t : Set V},   G.IsCompleteBetween 
s t →     ∀ (u : Set V), (SimpleGraph.induce u G).IsCompleteBetween (Subtype.val
 ⁻¹' s) (Subtype.val ⁻¹' t)
参数：G : SimpleGraph V；u : Set V；SimpleGraph.induce u G；Subtype.val ⁻¹' s；Subtype.
val ⁻¹' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.comap_adj`：∀ {V : Type u_1} {W : Type u_2} {u v : V} {G : Si
mpleGraph W} {f : V → W},   (SimpleGraph.comap f G).Adj u v ↔ G.Adj (f u) (f v)
· 使用定理 `Function.Embedding.coe_subtype`：coe_subtype {α} (p : α -> Prop) : ↑(subt
ype p) = Subtype.val
-/
theorem IsCompleteBetween.induce {s t : Set V} (h : G.IsCompleteBetween s t) (u : Set V) :
    (G.induce u).IsCompleteBetween (u ↓∩ s) (u ↓∩ t) := by
  intro _ hs _ ht
  rw [comap_adj, Embedding.coe_subtype]
  exact h hs ht

/-! ## Homomorphisms, embeddings and isomorphisms -/


/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
/-
**SimpleGraph.Hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：Hom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms.
-/
abbrev Hom :=
  RelHom G.Adj G'.Adj

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G'.Adj (f v) (f w) ↔ G.Adj v w`. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
/-
**SimpleGraph.Embedding** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：Embedding
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G'.Adj (f v) (f w) ↔ G.Adj v w`. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings.
-/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj

/-- A graph isomorphism is a bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
/-
**SimpleGraph.Iso** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：Iso
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph isomorphism is a bijective map on vertex sets that respects adjacency re
lations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj

@[inherit_doc] infixl:50 " →g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso

/-- `HomClass F G H` asserts that `F` is a type of adjacency-preserving morphism. -/
/-
**SimpleGraph.HomClass** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：HomClass (F : Type*) (G : SimpleGraph V) (H : SimpleGraph W) [FunLike F V 
W]
参数：F : Type*；G : SimpleGraph V；H : SimpleGraph W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HomClass F G H` asserts that `F` is a type of adjacency-preserving morphism.
-/
abbrev HomClass (F : Type*) (G : SimpleGraph V) (H : SimpleGraph W) [FunLike F V W] :=
  RelHomClass F G.Adj H.Adj

namespace Hom

variable {G G'} {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
/-
**SimpleGraph.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → G →g G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity homomorphism from a graph to itself.
-/
protected abbrev id : G →g G :=
  RelHom.id _
/-
**SimpleGraph.Hom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, ⇑SimpleGraph.Hom.id = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_id : ⇑(Hom.id : G →g G) = id := rfl
/-
**SimpleGraph.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty (V → W)] : IsEmpty (G →g H) := DFunLike.coe.isEmpty
/-
**SimpleGraph.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton (V → W)] : Subsingleton (G →g H) := DFunLike.coe_injective.subsingleton
/-
**SimpleGraph.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty V] : Unique (G →g H) where
  default := ⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _
/-
**SimpleGraph.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite V] [Finite W] : Finite (G →g H) := DFunLike.finite _
/-
**SimpleGraph.Hom.map_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w)
参数：h : G.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.map_rel'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} {s :
 β → β → Prop} (self : r →r s) {a b : α},   r a b → s (self.toFun a) (self.toFun
 b)
-/
theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h
/-
**SimpleGraph.Hom.map_mem_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：map_mem_edgeSet {e : Sym2 V} (h : e in G.edgeSet) : e.map f in G'.edgeSet
参数：h : e in G.edgeSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `RelHom.map_rel'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} {s :
 β → β → Prop} (self : r →r s) {a b : α},   r a b → s (self.toFun a) (self.toFun
 b)
-/
theorem map_mem_edgeSet {e : Sym2 V} (h : e ∈ G.edgeSet) : e.map f ∈ G'.edgeSet :=
  Sym2.ind (fun _ _ => f.map_rel') e h
/-
**SimpleGraph.Hom.subset_preimage_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Hom`。
形式化陈述：subset_preimage_edgeSet : G.edgeSet subseteq Sym2.map f ⁻¹' G'.edgeSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Hom.map_mem_edgeSet`：map_mem_edgeSet {e : Sym2 V} (h : e in 
G.edgeSet) : e.map f in G'.edgeSet
-/
theorem subset_preimage_edgeSet : G.edgeSet ⊆ Sym2.map f ⁻¹' G'.edgeSet :=
  fun _ ↦ f.map_mem_edgeSet
/-
**SimpleGraph.Hom.image_edgeSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Ho
m`。
形式化陈述：image_edgeSet_subset : Sym2.map f '' G.edgeSet subseteq G'.edgeSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `SimpleGraph.Hom.subset_preimage_edgeSet`：subset_preimage_edgeSet : G.edg
eSet subseteq Sym2.map f ⁻¹' G'.edgeSet
-/
theorem image_edgeSet_subset : Sym2.map f '' G.edgeSet ⊆ G'.edgeSet :=
  Set.image_subset_iff.mpr f.subset_preimage_edgeSet
/-
**SimpleGraph.Hom.apply_mem_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.H
om`。
形式化陈述：apply_mem_neighborSet {v w : V} (h : w in G.neighborSet v) : f w in G'.nei
ghborSet (f v)
参数：h : w in G.neighborSet v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
-/
theorem apply_mem_neighborSet {v w : V} (h : w ∈ G.neighborSet v) : f w ∈ G'.neighborSet (f v) :=
  map_adj f h

variable (v) in
/-
**SimpleGraph.Hom.subset_preimage_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Hom`。
形式化陈述：subset_preimage_neighborSet : G.neighborSet v subseteq f ⁻¹' G'.neighborSe
t (f v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Hom.apply_mem_neighborSet`：apply_mem_neighborSet {v w : V} (
h : w in G.neighborSet v) : f w in G'.neighborSet (f v)
-/
theorem subset_preimage_neighborSet : G.neighborSet v ⊆ f ⁻¹' G'.neighborSet (f v) :=
  fun _ ↦ f.apply_mem_neighborSet

variable (v) in
/-
**SimpleGraph.Hom.image_neighborSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Hom`。
形式化陈述：image_neighborSet_subset : f '' G.neighborSet v subseteq G'.neighborSet (f
 v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `SimpleGraph.Hom.subset_preimage_neighborSet`：subset_preimage_neighborSet
 : G.neighborSet v subseteq f ⁻¹' G'.neighborSet (f v)
-/
theorem image_neighborSet_subset : f '' G.neighborSet v ⊆ G'.neighborSet (f v) :=
  Set.image_subset_iff.mpr <| f.subset_preimage_neighborSet v

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
/-
**SimpleGraph.Hom.mapEdgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：mapEdgeSet (e : G.edgeSet) : G'.edgeSet
参数：e : G.edgeSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`.
-/
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
/-
**SimpleGraph.Hom.mapNeighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v)
参数：v : V；w : G.neighborSet v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between neighbor sets induced by a homomorphism.
-/
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, f.apply_mem_neighborSet w.property⟩

/-- The map between darts induced by a homomorphism. -/
/-
**SimpleGraph.Hom.mapDart** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：mapDart (d : G.Dart) : G'.Dart
参数：d : G.Dart。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map between darts induced by a homomorphism.
-/
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩

@[simp]
/-
**SimpleGraph.Hom.mapDart_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩
参数：d : G.Dart。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl

/-- The graph homomorphism from a smaller graph to a bigger one. -/
@[implicit_reducible]
/-
**SimpleGraph.Hom.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：ofLE (h : G₁ <= G₂) : G₁ ->g G₂
参数：h : G₁ <= G₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph homomorphism from a smaller graph to a bigger one.
-/
def ofLE (h : G₁ ≤ G₂) : G₁ →g G₂ := ⟨id, @h⟩
/-
**SimpleGraph.Hom.coe_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂), ⇑(SimpleGraph.Hom.
ofLE h) = id
参数：h : G₁ ≤ G₂；SimpleGraph.Hom.ofLE h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE h) = id := rfl
/-
**SimpleGraph.Hom.ofLE_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：ofLE_apply (h : G₁ <= G₂) (v : V) : ofLE h v = v
参数：h : G₁ <= G₂；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofLE_apply (h : G₁ ≤ G₂) (v : V) : ofLE h v = v := rfl
/-
**SimpleGraph.Hom.mapEdgeSet.injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Ho
m.mapEdgeSet`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph W} (
f : G →g G'),   Function.Injective ⇑f → Function.Injective f.mapEdgeSet
参数：f : G →g G'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Sym2.map.injective`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Functio
n.Injective f → Function.Injective (Sym2.map f)
-/
theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj

/-- Every graph homomorphism from a complete graph is injective. -/
/-
**SimpleGraph.Hom.injective_of_top_hom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Ho
m`。
形式化陈述：injective_of_top_hom (f : (⊤ : SimpleGraph V) ->g G') : Function.Injective
 f
参数：f : (⊤ : SimpleGraph V) ->g G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.top_adj`：top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v
 != w

--- 原说明 ---
Every graph homomorphism from a complete graph is injective.
-/
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) →g G') : Function.Injective f := by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))

/-- A function `f` that is injective on adjacent vertices in a graph `G`
(equivalently `f` is a valid `W`-coloring of `G`, or `G ≤ comap ⊤ f`)
is a homomorphism from `G` to the mapped graph. -/
@[simps]
/-
**SimpleGraph.Hom.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：{V : Type u_1} →   {W : Type u_2} → (f : V → W) → (G : SimpleGraph V) → (∀
 {u v : V}, G.Adj u v → f u ≠ f v) → G →g SimpleGraph.map f G
参数：f : V → W；G : SimpleGraph V；∀ {u v : V}, G.Adj u v → f u ≠ f v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` that is injective on adjacent vertices in a graph `G`
(equivalently `f` is a valid `W`-coloring of `G`, or `G ≤ comap ⊤ f`)
is a homomorphism from `G` to the mapped graph.
-/
protected def map (f : V → W) (G : SimpleGraph V) (h : ∀ {u v}, G.Adj u v → f u ≠ f v) :
    G →g G.map f where
  toFun := f
  map_rel' {u v} hadj := ⟨h hadj, u, v, hadj, rfl, rfl⟩

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `SimpleGraph.Embedding.comap`). -/
@[simps]
/-
**SimpleGraph.Hom.comap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：{V : Type u_1} → {W : Type u_2} → (f : V → W) → (G : SimpleGraph W) → Simp
leGraph.comap f G →g G
参数：f : V → W；G : SimpleGraph W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `SimpleGraph.Embedding
.comap`).
-/
protected def comap (f : V → W) (G : SimpleGraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp
/-
**SimpleGraph.Hom.le_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：le_comap (f : H ->g G) : H <= G.comap f
参数：f : H ->g G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
-/
theorem le_comap (f : H →g G) : H ≤ G.comap f :=
  fun _ _ ↦ f.map_adj
/-
**SimpleGraph.Hom.nonempty_hom_iff_exists_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Hom`。
形式化陈述：nonempty_hom_iff_exists_le_comap : Nonempty (H ->g G) ↔ exists f, H <= G.c
omap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Hom.le_comap`：le_comap (f : H ->g G) : H <= G.comap f
-/
theorem nonempty_hom_iff_exists_le_comap : Nonempty (H →g G) ↔ ∃ f, H ≤ G.comap f :=
  ⟨fun ⟨f⟩ ↦ ⟨f, f.le_comap⟩, fun ⟨f, h⟩ ↦ ⟨f, (h ·)⟩⟩

variable {G'' : SimpleGraph X} {G''' : SimpleGraph Y}

/-- Composition of graph homomorphisms. -/
/-
**SimpleGraph.Hom.comp** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：comp (f' : G' ->g G'') (f : G ->g G') : G ->g G''
参数：f' : G' ->g G''；f : G ->g G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of graph homomorphisms.
-/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  RelHom.comp f' f

@[simp]
/-
**SimpleGraph.Hom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：coe_comp (f' : G' ->g G'') (f : G ->g G') : ⇑(f'.comp f) = f' ∘ f
参数：f' : G' ->g G''；f : G ->g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
/-
**SimpleGraph.Hom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：comp_assoc (f : G'' ->g G''') (g : G' ->g G'') (h : G ->g G') : f.comp (g.
comp h) = (f.comp g).comp h
参数：f : G'' ->g G'''；g : G' ->g G''；h : G ->g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : G'' →g G''') (g : G' →g G'') (h : G →g G') :
    f.comp (g.comp h) = (f.comp g).comp h := rfl

@[simp]
/-
**SimpleGraph.Hom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：comp_id (f : G ->g G') : f.comp .id = f
参数：f : G ->g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : G →g G') : f.comp .id = f := rfl

@[simp]
/-
**SimpleGraph.Hom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：id_comp (f : G ->g G') : .comp .id f = f
参数：f : G ->g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : G →g G') : .comp .id f = f := rfl

@[simp]
/-
**SimpleGraph.Hom.comp_comap_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：comp_comap_ofLE (f : H ->g G) : .comp (.comap f G) (.ofLE f.le_comap) = f
参数：f : H ->g G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Hom.le_comap`：le_comap (f : H ->g G) : H <= G.comap f
-/
theorem comp_comap_ofLE (f : H →g G) : .comp (.comap f G) (.ofLE f.le_comap) = f :=
  rfl

end Hom

namespace Embedding

variable {G G'} {H : SimpleGraph W} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
/-
**SimpleGraph.Embedding.refl** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Embedding`
。
形式化陈述：refl : G ↪g G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity embedding from a graph to itself.
-/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
/-
**SimpleGraph.Embedding.toHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Embedding
`。
形式化陈述：toHom : G ->g G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding of graphs gives rise to a homomorphism of graphs.
-/
abbrev toHom : G →g G' :=
  f.toRelHom
/-
**SimpleGraph.Embedding.coe_toHom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embeddi
ng`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} (f
 : G ↪g H), ⇑f.toHom = ⇑f
参数：f : G ↪g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toHom (f : G ↪g H) : ⇑f.toHom = f := rfl
/-
**SimpleGraph.Embedding.map_adj_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embed
ding`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph W} (
f : G ↪g G') {v w : V},   G'.Adj (f v) (f w) ↔ G.Adj v w
参数：f : G ↪g G'；f v；f w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
@[simp] theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
/-
**SimpleGraph.Embedding.map_mem_edgeSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Embedding`。
形式化陈述：map_mem_edgeSet_iff {e : Sym2 V} : e.map f in G'.edgeSet ↔ e in G.edgeSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.Embedding.map_adj_iff`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {G' : SimpleGraph W} (f : G ↪g G') {v w : V},   G'.Adj (f v) (f w
) ↔ G.Adj v w
-/
theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e

@[simp]
/-
**SimpleGraph.Embedding.preimage_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Embedding`。
形式化陈述：preimage_edgeSet : Sym2.map f ⁻¹' G'.edgeSet = G.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SimpleGraph.Embedding.map_mem_edgeSet_iff`：map_mem_edgeSet_iff {e : Sym2
 V} : e.map f in G'.edgeSet ↔ e in G.edgeSet
-/
theorem preimage_edgeSet : Sym2.map f ⁻¹' G'.edgeSet = G.edgeSet :=
  Set.ext fun _ ↦ map_mem_edgeSet_iff f
/-
**SimpleGraph.Embedding.apply_mem_neighborSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Embedding`。
形式化陈述：apply_mem_neighborSet_iff {v w : V} : f w in G'.neighborSet (f v) ↔ w in G
.neighborSet v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Embedding.map_adj_iff`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {G' : SimpleGraph W} (f : G ↪g G') {v w : V},   G'.Adj (f v) (f w
) ↔ G.Adj v w
-/
theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f

variable (v) in
@[simp]
/-
**SimpleGraph.Embedding.preimage_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Embedding`。
形式化陈述：preimage_neighborSet : f ⁻¹' G'.neighborSet (f v) = G.neighborSet v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SimpleGraph.Embedding.apply_mem_neighborSet_iff`：apply_mem_neighborSet_i
ff {v w : V} : f w in G'.neighborSet (f v) ↔ w in G.neighborSet v
-/
theorem preimage_neighborSet : f ⁻¹' G'.neighborSet (f v) = G.neighborSet v :=
  Set.ext fun _ ↦ apply_mem_neighborSet_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
/-
**SimpleGraph.Embedding.mapEdgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedd
ing`。
形式化陈述：mapEdgeSet : G.edgeSet ↪ G'.edgeSet where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph embedding induces an embedding of edge sets.
-/
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f.toRelHom f.injective

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
/-
**SimpleGraph.Embedding.mapNeighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Em
bedding`。
形式化陈述：mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v) where toFu
n w
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph embedding induces an embedding of neighbor sets.
-/
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h

/-- A graph embedding induces a graph isomorphism between its domain and its range -/
/-
**SimpleGraph.Embedding.isoInduceRange** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Em
bedding`。
形式化陈述：isoInduceRange : G ≃g G'.induce (Set.range f) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph embedding induces a graph isomorphism between its domain and its range
-/
noncomputable def isoInduceRange : G ≃g G'.induce (Set.range f) where
  __ := Equiv.ofInjective f f.injective
  map_rel_iff' := by simp

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
-- Porting note: `@[simps]` does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
/-
**SimpleGraph.Embedding.comap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedding`。
形式化陈述：{V : Type u_1} → {W : Type u_2} → (f : V ↪ W) → (G : SimpleGraph W) → Simp
leGraph.comap (⇑f) G ↪g G
参数：f : V ↪ W；G : SimpleGraph W；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G where
  __ := f
  map_rel_iff' := by simp

@[simp]
/-
**SimpleGraph.Embedding.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embed
ding`。
形式化陈述：comap_apply (f : V ↪ W) (G : SimpleGraph W) (v : V) : SimpleGraph.Embeddin
g.comap f G v = f v
参数：f : V ↪ W；G : SimpleGraph W；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_apply (f : V ↪ W) (G : SimpleGraph W) (v : V) :
    SimpleGraph.Embedding.comap f G v = f v := rfl
/-
**SimpleGraph.Embedding.comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embeddin
g`。
形式化陈述：comap_eq (f : H ↪g G) : G.comap f = H
参数：f : H ↪g G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Embedding.map_adj_iff`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {G' : SimpleGraph W} (f : G ↪g G') {v w : V},   G'.Adj (f v) (f w
) ↔ G.Adj v w
-/
theorem comap_eq (f : H ↪g G) : G.comap f = H := by
  ext
  exact f.map_adj_iff

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
-- Porting note: `@[simps]` does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
/-
**SimpleGraph.Embedding.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedding`。
形式化陈述：{V : Type u_1} → {W : Type u_2} → (f : V ↪ W) → (G : SimpleGraph V) → G ↪g
 SimpleGraph.map (⇑f) G
参数：f : V ↪ W；G : SimpleGraph V；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f where
  __ := f
  map_rel_iff' := by simp

@[simp]
/-
**SimpleGraph.Embedding.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embeddi
ng`。
形式化陈述：map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) : Embedding.map f G v = 
f v
参数：f : V ↪ W；G : SimpleGraph V；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) : Embedding.map f G v = f v :=
  rfl

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
/-
**SimpleGraph.Embedding.induce** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedding`
。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → (s : Set V) → SimpleGraph.induce s 
G ↪g G
参数：s : Set V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the emb
edding of a
complete graph.
-/
protected abbrev induce (s : Set V) : G.induce s ↪g G :=
  .comap (.subtype _) G

/-- Graphs on a set of vertices embed in their `spanningCoe`. -/
/-
**SimpleGraph.Embedding.spanningCoe** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embed
ding`。
形式化陈述：{V : Type u_1} → {s : Set V} → (G : SimpleGraph ↑s) → G ↪g G.spanningCoe
参数：G : SimpleGraph ↑s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graphs on a set of vertices embed in their `spanningCoe`.
-/
protected abbrev spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  .map (.subtype _) G

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
/-
**SimpleGraph.Embedding.completeGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Emb
edding`。
形式化陈述：{α : Type u_5} → {β : Type u_6} → (α ↪ β) → SimpleGraph.completeGraph α ↪g
 SimpleGraph.completeGraph β
参数：α ↪ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embeddings of types induce embeddings of complete graphs on those types.
-/
protected def completeGraph {α β : Type*} (f : α ↪ β) : completeGraph α ↪g completeGraph β where
  __ := f
  map_rel_iff' := by simp
/-
**SimpleGraph.Embedding.coe_completeGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Embedding`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} (f : α ↪ β), ⇑(SimpleGraph.Embedding.compl
eteGraph f) = ⇑f
参数：f : α ↪ β；SimpleGraph.Embedding.completeGraph f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_completeGraph {α β : Type*} (f : α ↪ β) : ⇑(Embedding.completeGraph f) = f := rfl

variable {G'' : SimpleGraph X} {G''' : SimpleGraph Y}

/-- Composition of graph embeddings. -/
/-
**SimpleGraph.Embedding.comp** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Embedding`
。
形式化陈述：comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G''
参数：f' : G' ↪g G''；f : G ↪g G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of graph embeddings.
-/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'

@[simp]
/-
**SimpleGraph.Embedding.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embeddin
g`。
形式化陈述：coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f
参数：f' : G' ↪g G''；f : G ↪g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
/-
**SimpleGraph.Embedding.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embedd
ing`。
形式化陈述：comp_assoc (f : G'' ↪g G''') (g : G' ↪g G'') (h : G ↪g G') : f.comp (g.com
p h) = (f.comp g).comp h
参数：f : G'' ↪g G'''；g : G' ↪g G''；h : G ↪g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : G'' ↪g G''') (g : G' ↪g G'') (h : G ↪g G') :
    f.comp (g.comp h) = (f.comp g).comp h := rfl

@[simp]
/-
**SimpleGraph.Embedding.comp_refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embeddi
ng`。
形式化陈述：comp_refl (f : G ↪g G') : f.comp .refl = f
参数：f : G ↪g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_refl (f : G ↪g G') : f.comp .refl = f := rfl

@[simp]
/-
**SimpleGraph.Embedding.refl_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embeddi
ng`。
形式化陈述：refl_comp (f : G ↪g G') : .comp .refl f = f
参数：f : G ↪g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_comp (f : G ↪g G') : .comp .refl f = f := rfl

/-- Graph embeddings from `G` to `H` are the same thing as graph embeddings from `Gᶜ` to `Hᶜ`. -/
/-
**SimpleGraph.Embedding.complEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedd
ing`。
形式化陈述：complEquiv : G ↪g H ≃ Gᶜ ↪g Hᶜ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graph embeddings from `G` to `H` are the same thing as graph embeddings from `Gᶜ
` to `Hᶜ`.
-/
def complEquiv : G ↪g H ≃ Gᶜ ↪g Hᶜ where
  toFun f := ⟨f.toEmbedding, by simp⟩
  invFun f := ⟨f.toEmbedding, fun {v w} ↦ by
    obtain rfl | hvw := eq_or_ne v w
    · simp
    · simpa [hvw, not_iff_not] using f.map_adj_iff (v := v) (w := w)⟩

end Embedding

section induceHom

variable {G G'} {G'' : SimpleGraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G →g G') (φst : Set.MapsTo φ s t) (ψ : G' →g G'') (ψtr : Set.MapsTo ψ t r)

/-- The restriction of a morphism of graphs to induced subgraphs. -/
/-
**SimpleGraph.induceHom** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：induceHom : G.induce s ->g G'.induce t where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a morphism of graphs to induced subgraphs.
-/
def induceHom : G.induce s →g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'
/-
**SimpleGraph.coe_induceHom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph W} {
s : Set V} {t : Set W} (φ : G →g G')   (φst : Set.MapsTo (⇑φ) s t), ⇑(SimpleGrap
h.induceHom φ φst) = Set.MapsTo.restrict (⇑φ) s t φst
参数：φ : G →g G'；φst : Set.MapsTo (⇑φ) s t；SimpleGraph.induceHom φ φst；⇑φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_induceHom : ⇑(induceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl
/-
**SimpleGraph.induceHom_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (s : Set V), SimpleGraph.induceHom Si
mpleGraph.Hom.id ⋯ = SimpleGraph.Hom.id
参数：G : SimpleGraph V；s : Set V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.ext`：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
@[simp] lemma induceHom_id (G : SimpleGraph V) (s) :
    induceHom (Hom.id : G →g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl
/-
**SimpleGraph.induceHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {X : Type u_3} {G : SimpleGraph V} {G' : S
impleGraph W} {G'' : SimpleGraph X}   {s : Set V} {t : Set W} {r : Set X} (φ : G
 →g G') (φst : Set.MapsTo (⇑φ) s t) (ψ : G' →g G'')   (ψtr : Set.MapsTo (⇑ψ) t r
),   (SimpleGraph.induceHom ψ ψtr).comp (SimpleGraph.induceHom φ φst) = SimpleGr
aph.induceHom (ψ.comp φ) ⋯
参数：φ : G →g G'；φst : Set.MapsTo (⇑φ) s t；ψ : G' →g G''；ψtr : Set.MapsTo (⇑ψ) t r
；SimpleGraph.induceHom ψ ψtr；SimpleGraph.induceHom φ φst；ψ.comp φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.ext`：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
@[simp] lemma induceHom_comp :
    (induceHom ψ ψtr).comp (induceHom φ φst) = induceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl
/-
**SimpleGraph.induceHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：induceHom_injective (hi : Set.InjOn φ s) : Function.Injective (induceHom φ
 φst)
参数：hi : Set.InjOn φ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma induceHom_injective (hi : Set.InjOn φ s) :
    Function.Injective (induceHom φ φst) := by
  simpa [Set.MapsTo.restrict_inj]

end induceHom

section induceHomLE
variable {s s' : Set V} (h : s ≤ s')

/-- Given an inclusion of vertex subsets, the induced embedding on induced graphs.
This is not an abbreviation for `induceHom` since we get an embedding in this case. -/
/-
**SimpleGraph.induceHomOfLE** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：induceHomOfLE (h : s <= s') : G.induce s ↪g G.induce s' where toEmbedding
参数：h : s <= s'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an inclusion of vertex subsets, the induced embedding on induced graphs.
This is not an abbreviation for `induceHom` since we get an embedding in this ca
se.
-/
def induceHomOfLE (h : s ≤ s') : G.induce s ↪g G.induce s' where
  toEmbedding := Set.embeddingOfSubset s s' h
  map_rel_iff' := by simp
/-
**SimpleGraph.induceHomOfLE_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) {s s' : Set V} (h : s ⊆ s') (v : ↑s),
 (G.induceHomOfLE h) v = Set.inclusion h v
参数：G : SimpleGraph V；h : s ⊆ s'；v : ↑s；G.induceHomOfLE h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma induceHomOfLE_apply (v : s) : (G.induceHomOfLE h) v = Set.inclusion h v := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.induceHomOfLE_toHom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) {s s' : Set V} (h : s ⊆ s'),   (G.ind
uceHomOfLE h).toHom = SimpleGraph.induceHom SimpleGraph.Hom.id ⋯
参数：G : SimpleGraph V；h : s ⊆ s'；G.induceHomOfLE h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.ext`：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma induceHomOfLE_toHom :
    (G.induceHomOfLE h).toHom = induceHom (.id : G →g G) ((Set.mapsTo_id s).mono_right h) := by
  ext; simp

end induceHomLE

namespace Iso

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
/-
**SimpleGraph.Iso.refl** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：refl : G ≃g G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity isomorphism of a graph with itself.
-/
abbrev refl : G ≃g G :=
  RelIso.refl _

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
/-
**SimpleGraph.Iso.toEmbedding** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：toEmbedding : G ↪g G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of graphs gives rise to an embedding of graphs.
-/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
/-
**SimpleGraph.Iso.toHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：toHom : G ->g G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of graphs gives rise to a homomorphism of graphs.
-/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom

/-- The inverse of a graph isomorphism. -/
/-
**SimpleGraph.Iso.symm** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：symm : G' ≃g G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a graph isomorphism.
-/
abbrev symm : G' ≃g G :=
  RelIso.symm f
/-
**SimpleGraph.Iso.map_adj_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
-/
theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff
/-
**SimpleGraph.Iso.map_mem_edgeSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso
`。
形式化陈述：map_mem_edgeSet_iff {e : Sym2 V} : e.map f in G'.edgeSet ↔ e in G.edgeSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `SimpleGraph.Iso.map_adj_iff`：map_adj_iff {v w : V} : G'.Adj (f v) (f w) 
↔ G.Adj v w
-/
theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f ∈ G'.edgeSet ↔ e ∈ G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e
/-
**SimpleGraph.Iso.apply_mem_neighborSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Iso`。
形式化陈述：apply_mem_neighborSet_iff {v w : V} : f w in G'.neighborSet (f v) ↔ w in G
.neighborSet v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Iso.map_adj_iff`：map_adj_iff {v w : V} : G'.Adj (f v) (f w) 
↔ G.Adj v w
-/
theorem apply_mem_neighborSet_iff {v w : V} : f w ∈ G'.neighborSet (f v) ↔ w ∈ G.neighborSet v :=
  map_adj_iff f
/-
**SimpleGraph.Iso.image_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：image_neighborSet : f '' G.neighborSet v = G'.neighborSet (f v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Embedding.preimage_neighborSet`：preimage_neighborSet : f ⁻¹'
 G'.neighborSet (f v) = G.neighborSet v
· 使用定理 `Equiv.image_preimage`：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '
' e ⁻¹' s = s
-/
theorem image_neighborSet : f '' G.neighborSet v = G'.neighborSet (f v) := by
  rw [← f.toEmbedding.preimage_neighborSet]
  apply Equiv.image_preimage

@[simp]
/-
**SimpleGraph.Iso.symm_toHom_comp_toHom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
so`。
形式化陈述：symm_toHom_comp_toHom : f.symm.toHom.comp f.toHom = Hom.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.ext`：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelHom.comp_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α
 → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (g : s →r t)   (f : r →r s) (
x : α),…
· 使用定理 `RelIso.symm_apply_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : α), e.symm (e x) = x
· 使用定理 `RelHom.id_apply`：∀ {α : Type u_1} (r : α → α → Prop) (x : α), (RelHom.id
 r) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_toHom_comp_toHom : f.symm.toHom.comp f.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.symm_apply_apply, RelHom.id_apply]

@[simp]
/-
**SimpleGraph.Iso.toHom_comp_symm_toHom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
so`。
形式化陈述：toHom_comp_symm_toHom : f.toHom.comp f.symm.toHom = Hom.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.ext`：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelHom.comp_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α
 → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (g : s →r t)   (f : r →r s) (
x : α),…
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
· 使用定理 `RelHom.id_apply`：∀ {α : Type u_1} (r : α → α → Prop) (x : α), (RelHom.id
 r) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toHom_comp_symm_toHom : f.toHom.comp f.symm.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.apply_symm_apply, RelHom.id_apply]

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
/-
**SimpleGraph.Iso.mapEdgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：mapEdgeSet : G.edgeSet ≃ G'.edgeSet where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of graphs induces an equivalence of edge sets.
-/
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Sym2.map_map, comp_apply, Subtype.mk.injEq]
    convert! congr_fun Sym2.map_id e
    exact RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Sym2.map_map, comp_apply, Subtype.mk.injEq]
    convert! congr_fun Sym2.map_id e
    exact RelIso.apply_symm_apply _ _

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
/-
**SimpleGraph.Iso.mapNeighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v) where toFu
n w
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph isomorphism induces an equivalence of neighbor sets.
-/
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

include f in
/-
**SimpleGraph.Iso.card_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：card_eq [Fintype V] [Fintype W] : Fintype.card V = Fintype.card W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
-/
theorem card_eq [Fintype V] [Fintype W] : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert! rfl

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
/-
**SimpleGraph.Iso.comap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{V : Type u_1} → {W : Type u_2} → (f : V ≃ W) → (G : SimpleGraph W) → Simp
leGraph.comap (⇑f) G ≃g G
参数：f : V ≃ W；G : SimpleGraph W；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f ≃g G where
  __ := f
  map_rel_iff' := by simp

@[simp]
/-
**SimpleGraph.Iso.comap_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：comap_apply (f : V ≃ W) (G : SimpleGraph W) (v : V) : Iso.comap f G v = f 
v
参数：f : V ≃ W；G : SimpleGraph W；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_apply (f : V ≃ W) (G : SimpleGraph W) (v : V) : Iso.comap f G v = f v := rfl

-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
@[simp]
/-
**SimpleGraph.Iso.comap_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：comap_symm_apply (f : V ≃ W) (G : SimpleGraph W) (w : W) : (Iso.comap f G)
.symm w = f.symm w
参数：f : V ≃ W；G : SimpleGraph W；w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_symm_apply (f : V ≃ W) (G : SimpleGraph W) (w : W) :
    (Iso.comap f G).symm w = f.symm w := rfl

/-- Given a bijective function, there is an isomorphism from a graph into the mapped graph. -/
/-
**SimpleGraph.Iso.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{V : Type u_1} → {W : Type u_2} → (f : V ≃ W) → (G : SimpleGraph V) → G ≃g
 SimpleGraph.map (⇑f) G
参数：f : V ≃ W；G : SimpleGraph V；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a bijective function, there is an isomorphism from a graph into the mapped
 graph.
-/
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f where
  __ := f
  map_rel_iff' := by aesop (add simp map_adj')

@[simp]
/-
**SimpleGraph.Iso.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：map_apply (f : V ≃ W) (G : SimpleGraph V) (v : V) : Iso.map f G v = f v
参数：f : V ≃ W；G : SimpleGraph V；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply (f : V ≃ W) (G : SimpleGraph V) (v : V) : Iso.map f G v = f v := rfl

@[simp]
/-
**SimpleGraph.Iso.map_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：map_symm_apply (f : V ≃ W) (G : SimpleGraph V) (w : W) : (Iso.map f G).sym
m w = f.symm w
参数：f : V ≃ W；G : SimpleGraph V；w : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_symm_apply (f : V ≃ W) (G : SimpleGraph V) (w : W) :
    (Iso.map f G).symm w = f.symm w := rfl

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
/-
**SimpleGraph.Iso.completeGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{α : Type u_5} → {β : Type u_6} → α ≃ β → SimpleGraph.completeGraph α ≃g S
impleGraph.completeGraph β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalences of types induce isomorphisms of complete graphs on those types.
-/
protected def completeGraph {α β : Type*} (f : α ≃ β) : completeGraph α ≃g completeGraph β where
  __ := f
  map_rel_iff' := by simp
/-
**SimpleGraph.Iso.toEmbedding_completeGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Iso`。
形式化陈述：toEmbedding_completeGraph {α β : Type*} (f : α ≃ β) : (Iso.completeGraph f
).toEmbedding = Embedding.completeGraph f.toEmbedding
参数：f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEmbedding_completeGraph {α β : Type*} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl

variable {G'' : SimpleGraph X} {G''' : SimpleGraph Y}

/-- Equivalence of homomorphisms induced by isomorphisms of graphs. -/
/-
**SimpleGraph.Iso.homCongr** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：homCongr (f' : G'' ≃g G''') : G ->g G'' ≃ G' ->g G'''
参数：f' : G'' ≃g G'''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence of homomorphisms induced by isomorphisms of graphs.
-/
abbrev homCongr (f' : G'' ≃g G''') : G →g G'' ≃ G' →g G''' := RelIso.relHomCongr f f'

/-- Composition of graph isomorphisms. -/
/-
**SimpleGraph.Iso.comp** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G''
参数：f' : G' ≃g G''；f : G ≃g G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of graph isomorphisms.
-/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'

@[simp]
/-
**SimpleGraph.Iso.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f
参数：f' : G' ≃g G''；f : G ≃g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl
/-
**SimpleGraph.Iso.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：comp_assoc (f : G'' ≃g G''') (g : G' ≃g G'') (h : G ≃g G') : f.comp (g.com
p h) = (f.comp g).comp h
参数：f : G'' ≃g G'''；g : G' ≃g G''；h : G ≃g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : G'' ≃g G''') (g : G' ≃g G'') (h : G ≃g G') :
    f.comp (g.comp h) = (f.comp g).comp h := rfl

@[simp]
/-
**SimpleGraph.Iso.comp_refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：comp_refl (f : G ≃g G') : f.comp .refl = f
参数：f : G ≃g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_refl (f : G ≃g G') : f.comp .refl = f := rfl

@[simp]
/-
**SimpleGraph.Iso.refl_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：refl_comp (f : G ≃g G') : .comp .refl f = f
参数：f : G ≃g G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_comp (f : G ≃g G') : .comp .refl f = f := rfl

section induce

variable {s : Set V} {t : Set W} {r : Set X}
         (φ : G ≃g G') (φst : Set.BijOn φ s t) (ψ : G' ≃g G'') (ψtr : Set.BijOn ψ t r)

/-- The restriction of an isomorphism of graphs to induced subgraphs. -/
/-
**SimpleGraph.Iso.induce** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{V : Type u_1} →   {W : Type u_2} →     {G : SimpleGraph V} →       {G' : 
SimpleGraph W} →         {s : Set V} →           {t : Set W} → (φ : G ≃g G') → S
et.BijOn (⇑φ) s t → SimpleGraph.induce s G ≃g SimpleGraph.induce t G'
参数：φ : G ≃g G'；⇑φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of an isomorphism of graphs to induced subgraphs.
-/
protected def induce : G.induce s ≃g G'.induce t where
  toFun v := ⟨φ v.val, φst.mapsTo v.property⟩
  invFun w := ⟨φ.symm w.val, (φ.bijOn_symm.mpr φst).mapsTo w.property⟩
  left_inv v := by simp
  right_inv w := by simp
  map_rel_iff' := by simp [map_adj_iff φ]

@[simp, norm_cast]
/-
**SimpleGraph.Iso.coe_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph W} {
s : Set V} {t : Set W} (φ : G ≃g G')   (φst : Set.BijOn (⇑φ) s t), ⇑(φ.induce φs
t) = Set.MapsTo.restrict (⇑φ) s t ⋯
参数：φ : G ≃g G'；φst : Set.BijOn (⇑φ) s t；φ.induce φst；⇑φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_induce :
    ⇑(φ.induce φst) = φst.mapsTo.restrict φ s t := rfl

@[simp]
/-
**SimpleGraph.Iso.induce_refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (s : Set V), SimpleGraph.Iso.refl.ind
uce ⋯ = SimpleGraph.Iso.refl
参数：G : SimpleGraph V；s : Set V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.bijOn_id`：bijOn_id (s : Set α) : BijOn id s s
-/
protected lemma induce_refl (G : SimpleGraph V) (s : Set V) :
    (.refl : G ≃g G).induce (Set.bijOn_id s) = .refl := rfl

@[simp]
/-
**SimpleGraph.Iso.induce_comp_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`
。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {X : Type u_3} {G : SimpleGraph V} {G' : S
impleGraph W} {G'' : SimpleGraph X}   {s : Set V} {t : Set W} {r : Set X} (φ : G
 ≃g G') (φst : Set.BijOn (⇑φ) s t) (ψ : G' ≃g G'')   (ψtr : Set.BijOn (⇑ψ) t r),
 (ψ.induce ψtr).comp (φ.induce φst) = (ψ.comp φ).induce ⋯
参数：φ : G ≃g G'；φst : Set.BijOn (⇑φ) s t；ψ : G' ≃g G''；ψtr : Set.BijOn (⇑ψ) t r；ψ
.induce ψtr；φ.induce φst；ψ.comp φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma induce_comp_induce :
    (ψ.induce ψtr).comp (φ.induce φst) = (ψ.comp φ).induce (ψtr.comp φst) := by
  rfl

end induce

end Iso

/-
**SimpleGraph.neighborSet_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_comap (f : V -> W) (v : V) : (G'.comap f).neighborSet v = f ⁻¹
' G'.neighborSet (f v)
参数：f : V -> W；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neighborSet_comap (f : V → W) (v : V) :
    (G'.comap f).neighborSet v = f ⁻¹' G'.neighborSet (f v) :=
  rfl
/-
**SimpleGraph.neighborSet_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_induce (s : Set V) (v : s) : (G.induce s).neighborSet v = (↑) 
⁻¹' G.neighborSet v
参数：s : Set V；v : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.neighborSet_comap`：neighborSet_comap (f : V -> W) (v : V) : 
(G'.comap f).neighborSet v = f ⁻¹' G'.neighborSet (f v)
-/
theorem neighborSet_induce (s : Set V) (v : s) :
    (G.induce s).neighborSet v = (↑) ⁻¹' G.neighborSet v :=
  G.neighborSet_comap _ v
/-
**SimpleGraph.neighborSet_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_map_equiv (e : V ≃ W) (w : W) : (G.map e).neighborSet w = e.sy
mm ⁻¹' G.neighborSet (e.symm w)
参数：e : V ≃ W；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Embedding.preimage_neighborSet`：preimage_neighborSet : f ⁻¹'
 G'.neighborSet (f v) = G.neighborSet v
-/
theorem neighborSet_map_equiv (e : V ≃ W) (w : W) :
    (G.map e).neighborSet w = e.symm ⁻¹' G.neighborSet (e.symm w) :=
  Iso.map e G |>.symm.toEmbedding.preimage_neighborSet w |>.symm

set_option backward.isDefEq.respectTransparency false in
/-- The graph induced on `Set.univ` is isomorphic to the original graph. -/
@[simps!]
/-
**SimpleGraph.induceUnivIso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：induceUnivIso (G : SimpleGraph V) : G.induce Set.univ ≃g G where toEquiv
参数：G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph induced on `Set.univ` is isomorphic to the original graph.
-/
def induceUnivIso (G : SimpleGraph V) : G.induce Set.univ ≃g G where
  toEquiv := Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
                                implies_true]

/-- The isomorphism between `completeBipartiteGraph V₁ W₁` and
`completeBipartiteGraph V₂ W₂` where `V₁ ≃ V₂` and `W₁ ≃ W₂`. -/
@[simps!]
/-
**SimpleGraph.completeBipartiteGraphCongr** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
`。
形式化陈述：completeBipartiteGraphCongr {V₁ V₂ W₁ W₂ : Type*} (hV : V₁ ≃ V₂) (hW : W₁ 
≃ W₂) : completeBipartiteGraph V₁ W₁ ≃g completeBipartiteGraph V₂ W₂ where __
参数：hV : V₁ ≃ V₂；hW : W₁ ≃ W₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `completeBipartiteGraph V₁ W₁` and
`completeBipartiteGraph V₂ W₂` where `V₁ ≃ V₂` and `W₁ ≃ W₂`.
-/
def completeBipartiteGraphCongr {V₁ V₂ W₁ W₂ : Type*} (hV : V₁ ≃ V₂) (hW : W₁ ≃ W₂) :
    completeBipartiteGraph V₁ W₁ ≃g completeBipartiteGraph V₂ W₂ where
  __ := hV.sumCongr hW
  map_rel_iff' := by simp

section Finite

variable [Fintype V] {n : ℕ}

/-- Given a graph over a finite vertex type `V` and a proof `hc` that `Fintype.card V = n`,
`G.overFin n` is an isomorphic (as shown in `overFinIso`) graph over `Fin n`. -/
/-
**SimpleGraph.overFin** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：overFin (hc : Fintype.card V = n) : SimpleGraph (Fin n)
参数：hc : Fintype.card V = n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a graph over a finite vertex type `V` and a proof `hc` that `Fintype.card 
V = n`,
`G.overFin n` is an isomorphic (as shown in `overFinIso`) graph over `Fin n`.
-/
noncomputable def overFin (hc : Fintype.card V = n) : SimpleGraph (Fin n) :=
  G.comap (Fintype.equivFinOfCardEq hc).symm

/-- The isomorphism between `G` and `G.overFin hc`. -/
/-
**SimpleGraph.overFinIso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：overFinIso (hc : Fintype.card V = n) : G ≃g G.overFin hc
参数：hc : Fintype.card V = n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The isomorphism between `G` and `G.overFin hc`.
-/
noncomputable def overFinIso (hc : Fintype.card V = n) : G ≃g G.overFin hc :=
  .symm <| .comap ..

end Finite

end SimpleGraph

