/-
Copyright (c) 2022 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Disjoint sum of graphs

This file defines the disjoint sum of graphs. The disjoint sum of `G : SimpleGraph V` and
`H : SimpleGraph W` is a graph on `V ⊕ W` where `u` and `v` are adjacent if and only if they are
both in `G` and adjacent in `G`, or they are both in `H` and adjacent in `H`.

## Main declarations

* `SimpleGraph.Sum`: The disjoint sum of graphs.

## Notation

* `G ⊕g H`: The disjoint sum of `G` and `H`.
-/

@[expose] public section

namespace SimpleGraph
variable {U U' V V' W W' γ : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph U}
  {G' : SimpleGraph V'} {H' : SimpleGraph W'} {I' : SimpleGraph U'} {v v' : V} {w w' : W}

/-- Disjoint sum of `G` and `H`. -/
@[simps!]
/-
**SimpleGraph.sum** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_3} → {W : Type u_5} → SimpleGraph V → SimpleGraph W → SimpleGr
aph (V ⊕ W)
参数：V ⊕ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Disjoint sum of `G` and `H`.
-/
protected def sum (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => false
  symm.symm
    | Sum.inl u, Sum.inl v => G.adj_symm
    | Sum.inr u, Sum.inr v => H.adj_symm
    | Sum.inl _, Sum.inr _ | Sum.inr _, Sum.inl _ => id

@[inherit_doc] infixl:60 " ⊕g " => SimpleGraph.sum
/-
**SimpleGraph.sum_adj_inl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sum_adj_inl : (G oplusg H).Adj (.inl v) (.inl v') ↔ G.Adj v v'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.sum_adj`：∀ {V : Type u_3} {W : Type u_5} (G : SimpleGraph V)
 (H : SimpleGraph W) (x x_1 : V ⊕ W),   (G ⊕g H).Adj x x_1 =     match x, x_1 wi
th     | …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sum_adj_inl : (G ⊕g H).Adj (.inl v) (.inl v') ↔ G.Adj v v' := by
  simp
/-
**SimpleGraph.sum_adj_inr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sum_adj_inr : (G oplusg H).Adj (.inr w) (.inr w') ↔ H.Adj w w'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.sum_adj`：∀ {V : Type u_3} {W : Type u_5} (G : SimpleGraph V)
 (H : SimpleGraph W) (x x_1 : V ⊕ W),   (G ⊕g H).Adj x x_1 =     match x, x_1 wi
th     | …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sum_adj_inr : (G ⊕g H).Adj (.inr w) (.inr w') ↔ H.Adj w w' := by
  simp

/-- The disjoint sum is commutative up to isomorphism. `Iso.sumComm` as a graph isomorphism. -/
@[simps!]
/-
**SimpleGraph.Iso.sumComm** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{V : Type u_3} → {W : Type u_5} → {G : SimpleGraph V} → {H : SimpleGraph W
} → G ⊕g H ≃g H ⊕g G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The disjoint sum is commutative up to isomorphism. `Iso.sumComm` as a graph isom
orphism.
-/
def Iso.sumComm : G ⊕g H ≃g H ⊕g G := ⟨Equiv.sumComm V W, by
  rintro (u | u) (v | v) <;> simp⟩

/-- The disjoint sum is associative up to isomorphism. `Iso.sumAssoc` as a graph isomorphism. -/
@[simps!]
/-
**SimpleGraph.Iso.sumAssoc** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{U : Type u_1} →   {V : Type u_3} →     {W : Type u_5} → {G : SimpleGraph 
V} → {H : SimpleGraph W} → {I : SimpleGraph U} → G ⊕g H ⊕g I ≃g G ⊕g (H ⊕g I)
参数：H ⊕g I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The disjoint sum is associative up to isomorphism. `Iso.sumAssoc` as a graph iso
morphism.
-/
def Iso.sumAssoc : (G ⊕g H) ⊕g I ≃g G ⊕g (H ⊕g I) where
  toEquiv := .sumAssoc ..
  map_rel_iff' := by rintro ((u | u) | u) ((v | v) | v) <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The embedding of `G` into `G ⊕g H`. -/
@[simps]
/-
**SimpleGraph.Embedding.sumInl** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedding`
。
形式化陈述：{V : Type u_3} → {W : Type u_5} → {G : SimpleGraph V} → {H : SimpleGraph W
} → G ↪g G ⊕g H
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of `G` into `G ⊕g H`.
-/
def Embedding.sumInl : G ↪g G ⊕g H where
  toFun u := _root_.Sum.inl u
  inj' u v := by simp
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The embedding of `H` into `G ⊕g H`. -/
@[simps]
/-
**SimpleGraph.Embedding.sumInr** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedding`
。
形式化陈述：{V : Type u_3} → {W : Type u_5} → {G : SimpleGraph V} → {H : SimpleGraph W
} → H ↪g G ⊕g H
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of `H` into `G ⊕g H`.
-/
def Embedding.sumInr : H ↪g G ⊕g H where
  toFun u := _root_.Sum.inr u
  inj' u v := by simp
  map_rel_iff' := by simp

/-- Given homomorphisms `f : G →g G'` and `g : H →g H'`, returns a homomorphism from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps]
/-
**SimpleGraph.Hom.sum** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：{V : Type u_3} →   {V' : Type u_4} →     {W : Type u_5} →       {W' : Type
 u_6} →         {G : SimpleGraph V} →           {H : SimpleGraph W} → {G' : Simp
leGraph V'} → {H' : SimpleGraph W'} → G →g G' → H →g H' → G ⊕g H →g G' ⊕g H'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given homomorphisms `f : G →g G'` and `g : H →g H'`, returns a homomorphism from
 `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component
.
-/
def Hom.sum (f : G →g G') (g : H →g H') : G ⊕g H →g G' ⊕g H' where
  toFun := Sum.map f g
  map_rel' {u v} := by cases u <;> cases v <;> simp_all [f.map_rel, g.map_rel]
/-
**SimpleGraph.Hom.sum_comp_sumComm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Hom`。
形式化陈述：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_5} {W' : Type u_6} {G : Simpl
eGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V'} {H' : SimpleGraph W'} (f :
 G →g G') (g : H →g H'),   (f.sum g).comp SimpleGraph.Iso.sumComm.toHom = Simple
Graph.Iso.sumComm.toHom.comp (g.sum f)
参数：f : G →g G'；g : H →g H'；f.sum g；g.sum f。
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
· 使用定理 `SimpleGraph.Iso.sumComm_apply`：∀ {V : Type u_3} {W : Type u_5} {G : Simp
leGraph V} {H : SimpleGraph W} (a : V ⊕ W), SimpleGraph.Iso.sumComm a = a.swap
· 使用定理 `SimpleGraph.Hom.sum_apply`：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_
5} {W' : Type u_6} {G : SimpleGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V
'} {H' : Simple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.sum_comp_sumComm (f : G →g G') (g : H →g H') :
    comp (sum f g) Iso.sumComm.toHom = comp Iso.sumComm.toHom (sum g f) := by
  ext (v | w) <;> simp
/-
**SimpleGraph.Hom.sum_sum_comp_sumAssoc** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.H
om`。
形式化陈述：∀ {U : Type u_1} {U' : Type u_2} {V : Type u_3} {V' : Type u_4} {W : Type 
u_5} {W' : Type u_6} {G : SimpleGraph V}   {H : SimpleGraph W} {I : SimpleGraph 
U} {G' : SimpleGraph V'} {H' : SimpleGraph W'} {I' : SimpleGraph U'}   (f : G →g
 G') (g : H →g H') (h : I →g I'),   (f.sum (g.sum h)).comp SimpleGraph.Iso.sumAs
soc.toHom = SimpleGraph.Iso.sumAssoc.toHom.comp ((f.sum g).sum h)
参数：f : G →g G'；g : H →g H'；h : I →g I'；f.sum (g.sum h)；(f.sum g).sum h。
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
· 使用定理 `SimpleGraph.Iso.sumAssoc_apply`：∀ {U : Type u_1} {V : Type u_3} {W : Typ
e u_5} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph U}   (a : (V ⊕ W
) ⊕ U), SimpleGraph.…
· 使用定理 `SimpleGraph.Hom.sum_apply`：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_
5} {W' : Type u_6} {G : SimpleGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V
'} {H' : Simple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.sum_sum_comp_sumAssoc (f : G →g G') (g : H →g H') (h : I →g I') :
    comp (sum f (sum g h)) Iso.sumAssoc.toHom = comp Iso.sumAssoc.toHom (sum (sum f g) h) := by
  ext ((v | w) | u) <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Given embeddings `f : G ↪g G'` and `g : H ↪g H'`, returns an embedding from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps]
/-
**SimpleGraph.Embedding.sum** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Embedding`。
形式化陈述：{V : Type u_3} →   {V' : Type u_4} →     {W : Type u_5} →       {W' : Type
 u_6} →         {G : SimpleGraph V} →           {H : SimpleGraph W} → {G' : Simp
leGraph V'} → {H' : SimpleGraph W'} → G ↪g G' → H ↪g H' → G ⊕g H ↪g G' ⊕g H'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given embeddings `f : G ↪g G'` and `g : H ↪g H'`, returns an embedding from `G ⊕
g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component
.
-/
def Embedding.sum (f : G ↪g G') (g : H ↪g H') : G ⊕g H ↪g G' ⊕g H' where
  toFun := Sum.map f g
  inj' u v := by cases u <;> cases v <;> simp
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp
/-
**SimpleGraph.Embedding.toHom_sum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Embeddi
ng`。
形式化陈述：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_5} {W' : Type u_6} {G : Simpl
eGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V'} {H' : SimpleGraph W'} (f :
 G ↪g G') (g : H ↪g H'), (f.sum g).toHom = f.toHom.sum g.toHom
参数：f : G ↪g G'；g : H ↪g H'；f.sum g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Embedding.toHom_sum (f : G ↪g G') (g : H ↪g H') :
    (Embedding.sum f g).toHom = Hom.sum f.toHom g.toHom := rfl
/-
**SimpleGraph.Embedding.sum_comp_sumComm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Embedding`。
形式化陈述：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_5} {W' : Type u_6} {G : Simpl
eGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V'} {H' : SimpleGraph W'} (f :
 G ↪g G') (g : H ↪g H'),   (g.sum f).comp SimpleGraph.Iso.sumComm.toEmbedding = 
SimpleGraph.Iso.sumComm.toEmbedding.comp (f.sum g)
参数：f : G ↪g G'；g : H ↪g H'；g.sum f；f.sum g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Iso.sumComm_apply`：∀ {V : Type u_3} {W : Type u_5} {G : Simp
leGraph V} {H : SimpleGraph W} (a : V ⊕ W), SimpleGraph.Iso.sumComm a = a.swap
· 使用定理 `SimpleGraph.Embedding.sum_apply`：∀ {V : Type u_3} {V' : Type u_4} {W : T
ype u_5} {W' : Type u_6} {G : SimpleGraph V} {H : SimpleGraph W}   {G' : SimpleG
raph V'} {H' : Simple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Embedding.sum_comp_sumComm (f : G ↪g G') (g : H ↪g H') :
    comp (sum g f) Iso.sumComm.toEmbedding = comp Iso.sumComm.toEmbedding (sum f g) := by
  ext (v | w) <;> simp
/-
**SimpleGraph.Embedding.sum_sum_comp_sumAssoc** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Embedding`。
形式化陈述：∀ {U : Type u_1} {U' : Type u_2} {V : Type u_3} {V' : Type u_4} {W : Type 
u_5} {W' : Type u_6} {G : SimpleGraph V}   {H : SimpleGraph W} {I : SimpleGraph 
U} {G' : SimpleGraph V'} {H' : SimpleGraph W'} {I' : SimpleGraph U'}   (f : G ↪g
 G') (g : H ↪g H') (h : I ↪g I'),   (f.sum (g.sum h)).comp SimpleGraph.Iso.sumAs
soc.toEmbedding =     SimpleGraph.Iso.sumAssoc.toEmbedding.comp ((f.sum g).sum h
)
参数：f : G ↪g G'；g : H ↪g H'；h : I ↪g I'；f.sum (g.sum h)；(f.sum g).sum h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Iso.sumAssoc_apply`：∀ {U : Type u_1} {V : Type u_3} {W : Typ
e u_5} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph U}   (a : (V ⊕ W
) ⊕ U), SimpleGraph.…
· 使用定理 `SimpleGraph.Embedding.sum_apply`：∀ {V : Type u_3} {V' : Type u_4} {W : T
ype u_5} {W' : Type u_6} {G : SimpleGraph V} {H : SimpleGraph W}   {G' : SimpleG
raph V'} {H' : Simple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Embedding.sum_sum_comp_sumAssoc (f : G ↪g G') (g : H ↪g H') (h : I ↪g I') :
    comp (sum f (sum g h)) Iso.sumAssoc.toEmbedding =
      comp Iso.sumAssoc.toEmbedding (sum (sum f g) h) := by
  ext ((v | w) | u) <;> simp

/-- Given isomorphisms `f : G ≃g G'` and `g : H ≃g H'`, returns an isomorphism from `G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component. -/
@[simps!, simps toEquiv]
/-
**SimpleGraph.Iso.sumCongr** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{V : Type u_3} →   {V' : Type u_4} →     {W : Type u_5} →       {W' : Type
 u_6} →         {G : SimpleGraph V} →           {H : SimpleGraph W} → {G' : Simp
leGraph V'} → {H' : SimpleGraph W'} → G ≃g G' → H ≃g H' → G ⊕g H ≃g G' ⊕g H'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given isomorphisms `f : G ≃g G'` and `g : H ≃g H'`, returns an isomorphism from 
`G ⊕g H` to
`G' ⊕g H'` that applies `f` to the left component and `g` to the right component
.
-/
def Iso.sumCongr (f : G ≃g G') (g : H ≃g H') : G ⊕g H ≃g G' ⊕g H' where
  toEquiv := f.toEquiv.sumCongr g.toEquiv
  map_rel_iff' {u v} := by cases u <;> cases v <;> simp [f.map_rel_iff, g.map_rel_iff]
/-
**SimpleGraph.Iso.toHom_sumCongr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_5} {W' : Type u_6} {G : Simpl
eGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V'} {H' : SimpleGraph W'} (f :
 G ≃g G') (g : H ≃g H'), (f.sumCongr g).toHom = f.toHom.sum g.toHom
参数：f : G ≃g G'；g : H ≃g H'；f.sumCongr g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iso.toHom_sumCongr (f : G ≃g G') (g : H ≃g H') :
    (Iso.sumCongr f g).toHom = Hom.sum f.toHom g.toHom := rfl
/-
**SimpleGraph.Iso.toEmbedding_sumCongr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
o`。
形式化陈述：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_5} {W' : Type u_6} {G : Simpl
eGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V'} {H' : SimpleGraph W'} (f :
 G ≃g G') (g : H ≃g H'),   (f.sumCongr g).toEmbedding = f.toEmbedding.sum g.toEm
bedding
参数：f : G ≃g G'；g : H ≃g H'；f.sumCongr g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Iso.toEmbedding_sumCongr (f : G ≃g G') (g : H ≃g H') :
    (Iso.sumCongr f g).toEmbedding = Embedding.sum f.toEmbedding g.toEmbedding := rfl
/-
**SimpleGraph.Iso.sumComm_comp_sumCongr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
so`。
形式化陈述：∀ {V : Type u_3} {V' : Type u_4} {W : Type u_5} {W' : Type u_6} {G : Simpl
eGraph V} {H : SimpleGraph W}   {G' : SimpleGraph V'} {H' : SimpleGraph W'} (f :
 G ≃g G') (g : H ≃g H'),   SimpleGraph.Iso.sumComm.comp (f.sumCongr g) = (g.sumC
ongr f).comp SimpleGraph.Iso.sumComm
参数：f : G ≃g G'；g : H ≃g H'；f.sumCongr g；g.sumCongr f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ext`：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.trans_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : 
α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f₁ : r ≃r s)   (f₂ : s ≃r t
) (a : α…
· 使用定理 `SimpleGraph.Iso.sumCongr_apply`：∀ {V : Type u_3} {V' : Type u_4} {W : Ty
pe u_5} {W' : Type u_6} {G : SimpleGraph V} {H : SimpleGraph W}   {G' : SimpleGr
aph V'} {H' : Simple…
· 使用定理 `SimpleGraph.Iso.sumComm_apply`：∀ {V : Type u_3} {W : Type u_5} {G : Simp
leGraph V} {H : SimpleGraph W} (a : V ⊕ W), SimpleGraph.Iso.sumComm a = a.swap
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Iso.sumComm_comp_sumCongr (f : G ≃g G') (g : H ≃g H') :
    comp sumComm (sumCongr f g) = comp (sumCongr g f) sumComm := by
  ext (v | w) <;> simp
/-
**SimpleGraph.Iso.sumAssoc_comp_sumCongr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Iso`。
形式化陈述：∀ {U : Type u_1} {U' : Type u_2} {V : Type u_3} {V' : Type u_4} {W : Type 
u_5} {W' : Type u_6} {G : SimpleGraph V}   {H : SimpleGraph W} {I : SimpleGraph 
U} {G' : SimpleGraph V'} {H' : SimpleGraph W'} {I' : SimpleGraph U'}   (f : G ≃g
 G') (g : H ≃g H') (h : I ≃g I'),   SimpleGraph.Iso.sumAssoc.comp ((f.sumCongr g
).sumCongr h) = (f.sumCongr (g.sumCongr h)).comp SimpleGraph.Iso.sumAssoc
参数：f : G ≃g G'；g : H ≃g H'；h : I ≃g I'；(f.sumCongr g).sumCongr h；f.sumCongr (g.s
umCongr h)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ext`：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.trans_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : 
α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f₁ : r ≃r s)   (f₂ : s ≃r t
) (a : α…
· 使用定理 `SimpleGraph.Iso.sumCongr_apply`：∀ {V : Type u_3} {V' : Type u_4} {W : Ty
pe u_5} {W' : Type u_6} {G : SimpleGraph V} {H : SimpleGraph W}   {G' : SimpleGr
aph V'} {H' : Simple…
· 使用定理 `SimpleGraph.Iso.sumAssoc_apply`：∀ {U : Type u_1} {V : Type u_3} {W : Typ
e u_5} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph U}   (a : (V ⊕ W
) ⊕ U), SimpleGraph.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Iso.sumAssoc_comp_sumCongr (f : G ≃g G') (g : H ≃g H') (h : I ≃g I') :
    comp sumAssoc (sumCongr (sumCongr f g) h) = comp (sumCongr f (sumCongr g h)) sumAssoc := by
  ext ((v | w) | u) <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The edges of the disjoint sum of `G` and `H` are in bijection with
the disjoint sum of the edges of `G` and the edges of `H` -/
/-
**SimpleGraph.edgeSetSumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSetSumEquiv : (G oplusg H).edgeSet ≃ G.edgeSet oplus H.edgeSet where t
oFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj

--- 原说明 ---
The edges of the disjoint sum of `G` and `H` are in bijection with
the disjoint sum of the edges of `G` and the edges of `H`
-/
def edgeSetSumEquiv : (G ⊕g H).edgeSet ≃ G.edgeSet ⊕ H.edgeSet where
  toFun :=
    fun ⟨e, he⟩ ↦ e.fromRelNdrec (sym := symm _) he (fun
      | Sum.inl u, Sum.inl v, h => .inl ⟨s(u, v), h⟩
      | Sum.inr u, Sum.inr v, h => .inr ⟨s(u, v), h⟩
      | Sum.inl u, Sum.inr v, h => by contradiction
      | Sum.inr u, Sum.inl v, h => by contradiction
    ) (by grind)
  invFun
    | Sum.inl ⟨e, he⟩ =>
      e.fromRelNdrec (sym := G.symm) he (fun u v h ↦ ⟨s(.inl u, .inl v), h⟩) <| by simp
    | Sum.inr ⟨e, he⟩ =>
      e.fromRelNdrec (sym := H.symm) he (fun u v h ↦ ⟨s(.inr u, .inr v), h⟩) <| by simp
  left_inv := by rintro ⟨⟨u | u, v | v⟩, h⟩ <;> first | contradiction | rfl
  right_inv := by rintro (⟨⟨u, v⟩, h⟩ | ⟨⟨u, v⟩, h⟩) <;> rfl
/-
**SimpleGraph.not_adj_sum_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_adj_sum_inl_inr (v w) : ¬(G oplusg H).Adj (.inl v) (.inr w)
参数：v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.sum_adj`：∀ {V : Type u_3} {W : Type u_5} (G : SimpleGraph V)
 (H : SimpleGraph W) (x x_1 : V ⊕ W),   (G ⊕g H).Adj x x_1 =     match x, x_1 wi
th     | …
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_adj_sum_inl_inr (v w) : ¬(G ⊕g H).Adj (.inl v) (.inr w) := by simp
/-
**SimpleGraph.not_reachable_sum_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_reachable_sum_inl_inr (v w) : ¬(G oplusg H).Reachable (.inl v) (.inr w
)
参数：v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `SimpleGraph.Walk.exists_boundary_dart`：exists_boundary_dart {u v : V} (p
 : G.Walk u v) (S : Set V) (uS : u in S) (vS : v ∉ S) : exists d : G.Dart, d in 
p.darts ∧ d.fst in S ∧ d.sn…
· 使用引理 `SimpleGraph.not_adj_sum_inl_inr`：not_adj_sum_inl_inr (v w) : ¬(G oplusg 
H).Adj (.inl v) (.inr w)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma not_reachable_sum_inl_inr (v w) : ¬(G ⊕g H).Reachable (.inl v) (.inr w) := by
  rintro ⟨p⟩
  have hs : ∀ x : V ⊕ W, x ∉ Set.range .inl ↔ x ∈ Set.range .inr := by simp
  obtain ⟨⟨d, hadj⟩, _, hd1, hd2⟩ := p.exists_boundary_dart (Set.range .inl) (by simp) (by simp)
  simp only [hs] at hadj hd1 hd2
  obtain ⟨v', hv'⟩ := hd1
  obtain ⟨w', hw'⟩ := hd2
  rw [← hv', ← hw'] at hadj
  exact not_adj_sum_inl_inr _ _ hadj
/-
**SimpleGraph.not_preconnected_sum** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_preconnected_sum [Nonempty V] [Nonempty W] : ¬(G oplusg H).Preconnecte
d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.not_reachable_sum_inl_inr`：not_reachable_sum_inl_inr (v w) :
 ¬(G oplusg H).Reachable (.inl v) (.inr w)
-/
lemma not_preconnected_sum [Nonempty V] [Nonempty W] : ¬(G ⊕g H).Preconnected :=
  fun h ↦ not_reachable_sum_inl_inr (Classical.arbitrary _) (Classical.arbitrary _) (h ..)
/-
**SimpleGraph.not_connected_sum** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_connected_sum [Nonempty V] [Nonempty W] : ¬(G oplusg H).Connected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_connected_sum [Nonempty V] [Nonempty W] : ¬(G ⊕g H).Connected := by
  simp [connected_iff, not_preconnected_sum]
/-
**SimpleGraph.Reachable.sum_sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reac
hable`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {G : SimpleGraph V} {H : SimpleGraph W} {v
 v' : V} {w w' : W},   G.Reachable v v' →     H.Reachable w w' → ((G ⊕g H) ⊔ Sim
pleGraph.edge (Sum.inl v) (Sum.inr w)).Reachable (Sum.inl v') (Sum.inr w')
参数：(G ⊕g H) ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr w)；Sum.inl v'；Sum.inr w'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Embedding.sumInl_apply`：∀ {V : Type u_3} {W : Type u_5} {G :
 SimpleGraph V} {H : SimpleGraph W} (u : V),   SimpleGraph.Embedding.sumInl u = 
Sum.inl u
· 使用定理 `SimpleGraph.Embedding.sumInr_apply`：∀ {V : Type u_3} {W : Type u_5} {G :
 SimpleGraph V} {H : SimpleGraph W} (u : W),   SimpleGraph.Embedding.sumInr u = 
Sum.inr u
· 使用定理 `SimpleGraph.sum_adj`：∀ {V : Type u_3} {W : Type u_5} (G : SimpleGraph V)
 (H : SimpleGraph W) (x x_1 : V ⊕ W),   (G ⊕g H).Adj x x_1 =     match x, x_1 wi
th     | …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma Reachable.sum_sup_edge (hv : G.Reachable v v') (hw : H.Reachable w w') :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Reachable (.inl v') (.inr w') :=
  ((hv.symm.map Embedding.sumInl.toHom).mono le_sup_left).trans <| .trans
    (Adj.reachable <| by simp [edge]) <| (hw.map Embedding.sumInr.toHom).mono le_sup_left
/-
**SimpleGraph.Preconnected.sum_sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.P
reconnected`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {G : SimpleGraph V} {H : SimpleGraph W} {v
 : V} {w : W},   G.Preconnected → H.Preconnected → ((G ⊕g H) ⊔ SimpleGraph.edge 
(Sum.inl v) (Sum.inr w)).Preconnected
参数：(G ⊕g H) ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `SimpleGraph.Reachable.sum_sup_edge`：∀ {V : Type u_3} {W : Type u_5} {G :
 SimpleGraph V} {H : SimpleGraph W} {v v' : V} {w w' : W},   G.Reachable v v' → 
    H.Reachable w w' → (…
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
-/
lemma Preconnected.sum_sup_edge (hG : G.Preconnected) (hH : H.Preconnected) :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Preconnected := by
  rintro (v₁ | w₁) (v₂ | w₂)
  · exact ((hG v₁ v₂).map Embedding.sumInl.toHom).mono le_sup_left
  · exact (hG ..).sum_sup_edge (hH ..)
  · exact ((hG ..).sum_sup_edge (hH ..)).symm
  · exact ((hH w₁ w₂).map Embedding.sumInr.toHom).mono le_sup_left
/-
**SimpleGraph.Connected.sum_sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Conn
ected`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {G : SimpleGraph V} {H : SimpleGraph W} {v
 : V} {w : W},   G.Connected → H.Connected → ((G ⊕g H) ⊔ SimpleGraph.edge (Sum.i
nl v) (Sum.inr w)).Connected
参数：(G ⊕g H) ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.sum_sup_edge`：∀ {V : Type u_3} {W : Type u_5} {
G : SimpleGraph V} {H : SimpleGraph W} {v : V} {w : W},   G.Preconnected → H.Pre
connected → ((G ⊕g H) ⊔ Sim…
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `Sum.nonemptyLeft`：∀ {α : Type u} {β : Type v} [h : Nonempty α], Nonempty
 (α ⊕ β)
-/
lemma Connected.sum_sup_edge (hG : G.Connected) (hH : H.Connected) :
    (G.sum H ⊔ edge (.inl v) (.inr w)).Connected := by
  obtain ⟨hG⟩ := hG; exact ⟨hG.sum_sup_edge hH.preconnected⟩

/-- Color `G ⊕g H` with colorings of `G` and `H` -/
/-
**SimpleGraph.Coloring.sum** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`。
形式化陈述：{V : Type u_3} →   {W : Type u_5} →     {γ : Type u_7} → {G : SimpleGraph 
V} → {H : SimpleGraph W} → G.Coloring γ → H.Coloring γ → (G ⊕g H).Coloring γ
参数：G ⊕g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Color `G ⊕g H` with colorings of `G` and `H`
-/
def Coloring.sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (G ⊕g H).Coloring γ where
  toFun := Sum.elim cG cH
  map_rel' {u v} huv := by cases u <;> cases v <;> simp_all [cG.valid, cH.valid]

/-- Get coloring of `G` from coloring of `G ⊕g H` -/
/-
**SimpleGraph.Coloring.sumLeft** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`。
形式化陈述：{V : Type u_3} →   {W : Type u_5} → {γ : Type u_7} → {G : SimpleGraph V} →
 {H : SimpleGraph W} → (G ⊕g H).Coloring γ → G.Coloring γ
参数：G ⊕g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get coloring of `G` from coloring of `G ⊕g H`
-/
def Coloring.sumLeft (c : (G ⊕g H).Coloring γ) : G.Coloring γ := c.comp Embedding.sumInl.toHom

/-- Get coloring of `H` from coloring of `G ⊕g H` -/
/-
**SimpleGraph.Coloring.sumRight** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`
。
形式化陈述：{V : Type u_3} →   {W : Type u_5} → {γ : Type u_7} → {G : SimpleGraph V} →
 {H : SimpleGraph W} → (G ⊕g H).Coloring γ → H.Coloring γ
参数：G ⊕g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get coloring of `H` from coloring of `G ⊕g H`
-/
def Coloring.sumRight (c : (G ⊕g H).Coloring γ) : H.Coloring γ := c.comp Embedding.sumInr.toHom

@[simp]
/-
**SimpleGraph.Coloring.sumLeft_sum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colori
ng`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {γ : Type u_7} {G : SimpleGraph V} {H : Si
mpleGraph W} (cG : G.Coloring γ)   (cH : H.Coloring γ), (cG.sum cH).sumLeft = cG
参数：cG : G.Coloring γ；cH : H.Coloring γ；cG.sum cH。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Coloring.sumLeft_sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (cG.sum cH).sumLeft = cG :=
  rfl

@[simp]
/-
**SimpleGraph.Coloring.sumRight_sum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Color
ing`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {γ : Type u_7} {G : SimpleGraph V} {H : Si
mpleGraph W} (cG : G.Coloring γ)   (cH : H.Coloring γ), (cG.sum cH).sumRight = c
H
参数：cG : G.Coloring γ；cH : H.Coloring γ；cG.sum cH。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Coloring.sumRight_sum (cG : G.Coloring γ) (cH : H.Coloring γ) : (cG.sum cH).sumRight = cH :=
  rfl

@[simp]
/-
**SimpleGraph.Coloring.sum_sumLeft_sumRight** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Coloring`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {γ : Type u_7} {G : SimpleGraph V} {H : Si
mpleGraph W} (c : (G ⊕g H).Coloring γ),   c.sumLeft.sum c.sumRight = c
参数：c : (G ⊕g H).Coloring γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.ext`：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
-/
theorem Coloring.sum_sumLeft_sumRight (c : (G ⊕g H).Coloring γ) : c.sumLeft.sum c.sumRight = c := by
  ext (u | u) <;> rfl

/-- Bijection between `(G ⊕g H).Coloring γ` and `G.Coloring γ × H.Coloring γ` -/
/-
**SimpleGraph.Coloring.sumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`
。
形式化陈述：{V : Type u_3} →   {W : Type u_5} →     {γ : Type u_7} → {G : SimpleGraph 
V} → {H : SimpleGraph W} → (G ⊕g H).Coloring γ ≃ G.Coloring γ × H.Coloring γ
参数：G ⊕g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between `(G ⊕g H).Coloring γ` and `G.Coloring γ × H.Coloring γ`
-/
def Coloring.sumEquiv : (G ⊕g H).Coloring γ ≃ G.Coloring γ × H.Coloring γ where
  toFun c := ⟨c.sumLeft, c.sumRight⟩
  invFun p := p.1.sum p.2
  left_inv c := by simp [sum_sumLeft_sumRight c]

/-- Color `G ⊕g H` with `Fin (n + m)` given a coloring of `G` with `Fin n` and a coloring of `H`
with `Fin m` -/
/-
**SimpleGraph.Coloring.sumFin** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`。
形式化陈述：{V : Type u_3} →   {W : Type u_5} →     {G : SimpleGraph V} →       {H : S
impleGraph W} → {n m : ℕ} → G.Coloring (Fin n) → H.Coloring (Fin m) → (G ⊕g H).C
oloring (Fin (max n m))
参数：Fin n；Fin m；G ⊕g H；Fin (max n m)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_max_left`：∀ (a b : ℕ), a ≤ max a b
· 使用定理 `Nat.le_max_right`：∀ (a b : ℕ), b ≤ max a b

--- 原说明 ---
Color `G ⊕g H` with `Fin (n + m)` given a coloring of `G` with `Fin n` and a col
oring of `H`
with `Fin m`
-/
def Coloring.sumFin {n m : ℕ} (cG : G.Coloring (Fin n)) (cH : H.Coloring (Fin m)) :
    (G ⊕g H).Coloring (Fin (max n m)) := sum
  (G.recolorOfEmbedding (Fin.castLEEmb (n.le_max_left m)) cG)
  (H.recolorOfEmbedding (Fin.castLEEmb (n.le_max_right m)) cH)
/-
**SimpleGraph.Colorable.sum_max** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colorable
`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {G : SimpleGraph V} {H : SimpleGraph W} {n
 m : ℕ},   G.Colorable n → H.Colorable m → (G ⊕g H).Colorable (max n m)
参数：G ⊕g H；max n m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colorable.sum_max {n m : ℕ} (hG : G.Colorable n) (hH : H.Colorable m) :
    (G ⊕g H).Colorable (max n m) := Nonempty.intro (hG.some.sumFin hH.some)
/-
**SimpleGraph.Colorable.of_sum_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Color
able`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {G : SimpleGraph V} {H : SimpleGraph W} {n
 : ℕ}, (G ⊕g H).Colorable n → G.Colorable n
参数：G ⊕g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colorable.of_sum_left {n : ℕ} (h : (G ⊕g H).Colorable n) : G.Colorable n :=
  Nonempty.intro (h.some.sumLeft)
/-
**SimpleGraph.Colorable.of_sum_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colo
rable`。
形式化陈述：∀ {V : Type u_3} {W : Type u_5} {G : SimpleGraph V} {H : SimpleGraph W} {n
 : ℕ}, (G ⊕g H).Colorable n → H.Colorable n
参数：G ⊕g H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colorable.of_sum_right {n : ℕ} (h : (G ⊕g H).Colorable n) : H.Colorable n :=
  Nonempty.intro (h.some.sumRight)

@[simp]
/-
**SimpleGraph.colorable_sum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：colorable_sum {n : Nat} : (G oplusg H).Colorable n ↔ G.Colorable n ∧ H.Col
orable n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Colorable.of_sum_left`：∀ {V : Type u_3} {W : Type u_5} {G : 
SimpleGraph V} {H : SimpleGraph W} {n : ℕ}, (G ⊕g H).Colorable n → G.Colorable n
· 使用定理 `SimpleGraph.Colorable.of_sum_right`：∀ {V : Type u_3} {W : Type u_5} {G :
 SimpleGraph V} {H : SimpleGraph W} {n : ℕ}, (G ⊕g H).Colorable n → H.Colorable 
n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.max_self`：∀ (a : ℕ), max a a = a
· 使用定理 `SimpleGraph.Colorable.sum_max`：∀ {V : Type u_3} {W : Type u_5} {G : Simp
leGraph V} {H : SimpleGraph W} {n m : ℕ},   G.Colorable n → H.Colorable m → (G ⊕
g H).Colorable (max…
-/
theorem colorable_sum {n : ℕ} : (G ⊕g H).Colorable n ↔ G.Colorable n ∧ H.Colorable n :=
  ⟨fun cGH => ⟨cGH.of_sum_left, cGH.of_sum_right⟩,
    fun ⟨cG, cH⟩ => by rw [← n.max_self]; exact cG.sum_max cH⟩
/-
**SimpleGraph.chromaticNumber_le_sum_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：chromaticNumber_le_sum_left : G.chromaticNumber <= (G oplusg H).chromaticN
umber
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.chromaticNumber_le_of_forall_imp`：chromaticNumber_le_of_fora
ll_imp {V' : Type*} {G' : SimpleGraph V'} (h : forall n, G'.Colorable n -> G.Col
orable n) : G.chromaticNumber <= G…
· 使用定理 `SimpleGraph.Colorable.of_sum_left`：∀ {V : Type u_3} {W : Type u_5} {G : 
SimpleGraph V} {H : SimpleGraph W} {n : ℕ}, (G ⊕g H).Colorable n → G.Colorable n
-/
theorem chromaticNumber_le_sum_left : G.chromaticNumber ≤ (G ⊕g H).chromaticNumber :=
  chromaticNumber_le_of_forall_imp (fun _ h ↦ h.of_sum_left)
/-
**SimpleGraph.chromaticNumber_le_sum_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：chromaticNumber_le_sum_right : H.chromaticNumber <= (G oplusg H).chromatic
Number
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.chromaticNumber_le_of_forall_imp`：chromaticNumber_le_of_fora
ll_imp {V' : Type*} {G' : SimpleGraph V'} (h : forall n, G'.Colorable n -> G.Col
orable n) : G.chromaticNumber <= G…
· 使用定理 `SimpleGraph.Colorable.of_sum_right`：∀ {V : Type u_3} {W : Type u_5} {G :
 SimpleGraph V} {H : SimpleGraph W} {n : ℕ}, (G ⊕g H).Colorable n → H.Colorable 
n
-/
theorem chromaticNumber_le_sum_right : H.chromaticNumber ≤ (G ⊕g H).chromaticNumber :=
  chromaticNumber_le_of_forall_imp (fun _ h ↦ h.of_sum_right)

@[simp]
/-
**SimpleGraph.chromaticNumber_sum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_sum : (G oplusg H).chromaticNumber = max G.chromaticNumber
 H.chromaticNumber
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_max`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → (∀ {d : α}, a ≤ d → b ≤ d → c ≤ d) → c = max a b
· 使用定理 `SimpleGraph.chromaticNumber_le_sum_left`：chromaticNumber_le_sum_left : G
.chromaticNumber <= (G oplusg H).chromaticNumber
· 使用定理 `SimpleGraph.chromaticNumber_le_sum_right`：chromaticNumber_le_sum_right :
 H.chromaticNumber <= (G oplusg H).chromaticNumber
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem chromaticNumber_sum :
    (G ⊕g H).chromaticNumber = max G.chromaticNumber H.chromaticNumber := by
  refine eq_max chromaticNumber_le_sum_left chromaticNumber_le_sum_right fun {d} hG hH => ?_
  cases d with
  | top => simp
  | coe n =>
    let cG : G.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hG).some
    let cH : H.Coloring (Fin n) := (chromaticNumber_le_iff_colorable.mp hH).some
    exact chromaticNumber_le_iff_colorable.mpr (Nonempty.intro (cG.sum cH))
/-
**SimpleGraph.neighborSet_sum_inl** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_sum_inl (v : V) : (G oplusg H).neighborSet (.inl v) = Sum.inl 
'' G.neighborSet v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.sum_adj`：∀ {V : Type u_3} {W : Type u_5} (G : SimpleGraph V)
 (H : SimpleGraph W) (x x_1 : V ⊕ W),   (G ⊕g H).Adj x x_1 =     match x, x_1 wi
th     | …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma neighborSet_sum_inl (v : V) : (G ⊕g H).neighborSet (.inl v) = Sum.inl '' G.neighborSet v := by
  ext (v' | w') <;> simp
/-
**SimpleGraph.neighborSet_sum_inr** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_sum_inr (w : W) : (G oplusg H).neighborSet (.inr w) = Sum.inr 
'' H.neighborSet w
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.sum_adj`：∀ {V : Type u_3} {W : Type u_5} (G : SimpleGraph V)
 (H : SimpleGraph W) (x x_1 : V ⊕ W),   (G ⊕g H).Adj x x_1 =     match x, x_1 wi
th     | …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
lemma neighborSet_sum_inr (w : W) : (G ⊕g H).neighborSet (.inr w) = Sum.inr '' H.neighborSet w := by
  ext (v' | w') <;> simp
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq V] [DecidableEq W] [LocallyFinite G] [LocallyFinite H] :
    LocallyFinite (G ⊕g H) := by
  rintro (v | w) <;> simp only [neighborSet_sum_inl, neighborSet_sum_inr] <;>
    infer_instance

end SimpleGraph

