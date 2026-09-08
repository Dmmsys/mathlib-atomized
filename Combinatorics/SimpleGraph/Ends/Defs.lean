/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finite.Set

/-!
# Ends

This file contains a definition of the ends of a simple graph, as sections of the inverse system
assigning, to each finite set of vertices, the connected components of its complement.
-/

@[expose] public section


universe u

variable {V : Type u} (G : SimpleGraph V) (K L M : Set V)

namespace SimpleGraph

/-- The components outside a given set of vertices `K` -/
/-
**SimpleGraph.ComponentCompl** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：ComponentCompl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The components outside a given set of vertices `K`
-/
abbrev ComponentCompl :=
  (G.induce Kᶜ).ConnectedComponent

variable {G} {K L M}

/-- The connected component of `v` in `G.induce Kᶜ`. -/
/-
**SimpleGraph.componentComplMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：componentComplMk (G : SimpleGraph V) {v : V} (vK : v ∉ K) : G.ComponentCom
pl K
参数：G : SimpleGraph V；vK : v ∉ K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connected component of `v` in `G.induce Kᶜ`.
-/
abbrev componentComplMk (G : SimpleGraph V) {v : V} (vK : v ∉ K) : G.ComponentCompl K :=
  connectedComponentMk (G.induce Kᶜ) ⟨v, vK⟩

/-- The set of vertices of `G` making up the connected component `C` -/
/-
**SimpleGraph.ComponentCompl.supp** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Compone
ntCompl`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {K : Set V} → G.ComponentCompl K → Se
t V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of vertices of `G` making up the connected component `C`
-/
def ComponentCompl.supp (C : G.ComponentCompl K) : Set V :=
  { v : V | ∃ h : v ∉ K, G.componentComplMk h = C }

@[ext]
/-
**SimpleGraph.ComponentCompl.supp_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.ComponentCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V}, Function.Injective SimpleG
raph.ComponentCompl.supp
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind₂`：∀ {V : Type u} {G : SimpleGraph V} 
{β : G.ConnectedComponent → G.ConnectedComponent → Prop},   (∀ (v w : V), β (G.c
onnectedComponentMk v) (G…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
-/
theorem ComponentCompl.supp_injective :
    Function.Injective (ComponentCompl.supp : G.ComponentCompl K → Set V) := by
  refine ConnectedComponent.ind₂ ?_
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  simp only [Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq, ComponentCompl.supp] at h ⊢
  exact ((h v).mp ⟨hv, Reachable.refl _⟩).choose_spec
/-
**SimpleGraph.ComponentCompl.supp_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Com
ponentCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V} {C D : G.ComponentCompl K},
 C.supp = D.supp ↔ C = D
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SimpleGraph.ComponentCompl.supp_injective`：∀ {V : Type u} {G : SimpleGra
ph V} {K : Set V}, Function.Injective SimpleGraph.ComponentCompl.supp
-/
theorem ComponentCompl.supp_inj {C D : G.ComponentCompl K} : C.supp = D.supp ↔ C = D :=
  ComponentCompl.supp_injective.eq_iff
/-
**SimpleGraph.ComponentCompl.setLike** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Comp
onentCompl`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {K : Set V} → SetLike (G.ComponentCom
pl K) V
参数：G.ComponentCompl K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ComponentCompl.setLike : SetLike (G.ComponentCompl K) V where
  coe := ComponentCompl.supp
  coe_injective _ _ := ComponentCompl.supp_inj.mp
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (G.ComponentCompl K) := .ofSetLike (G.ComponentCompl K) V

@[simp]
/-
**SimpleGraph.ComponentCompl.mem_supp_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.ComponentCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V} {v : V} {C : G.ComponentCom
pl K},   v ∈ C ↔ ∃ (vK : v ∉ K), G.componentComplMk vK = C
参数：vK : v ∉ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ComponentCompl.mem_supp_iff {v : V} {C : ComponentCompl G K} :
    v ∈ C ↔ ∃ vK : v ∉ K, G.componentComplMk vK = C :=
  Iff.rfl
/-
**SimpleGraph.componentComplMk_mem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：componentComplMk_mem (G : SimpleGraph V) {v : V} (vK : v ∉ K) : v in G.com
ponentComplMk vK
参数：G : SimpleGraph V；vK : v ∉ K。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem componentComplMk_mem (G : SimpleGraph V) {v : V} (vK : v ∉ K) : v ∈ G.componentComplMk vK :=
  ⟨vK, rfl⟩
/-
**SimpleGraph.componentComplMk_eq_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：componentComplMk_eq_of_adj (G : SimpleGraph V) {v w : V} (vK : v ∉ K) (wK 
: w ∉ K) (a : G.Adj v w) : G.componentComplMk vK = G.componentComplMk wK
参数：G : SimpleGraph V；vK : v ∉ K；wK : w ∉ K；a : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.ConnectedComponent.eq`：∀ {V : Type u} {G : SimpleGraph V} {v
 w : V}, G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
theorem componentComplMk_eq_of_adj (G : SimpleGraph V) {v w : V} (vK : v ∉ K) (wK : w ∉ K)
    (a : G.Adj v w) : G.componentComplMk vK = G.componentComplMk wK := by
  rw [ConnectedComponent.eq]
  apply Adj.reachable
  exact a

/-- In an infinite graph, the set of components out of a finite set is nonempty. -/
/-
**SimpleGraph.componentCompl_nonempty_of_infinite** 是 Mathlib 中的一个实例，位于命名空间 `Sim
pleGraph`。
形式化陈述：componentCompl_nonempty_of_infinite (G : SimpleGraph V) [Infinite V] (K : 
Finset V) : Nonempty (G.ComponentCompl K)
参数：G : SimpleGraph V；K : Finset V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.nonempty`：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonemp
ty
· 使用定理 `Set.Finite.infinite_compl`：∀ {α : Type u} [Infinite α] {s : Set α}, s.Fi
nite → sᶜ.Infinite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
In an infinite graph, the set of components out of a finite set is nonempty.
-/
instance componentCompl_nonempty_of_infinite (G : SimpleGraph V) [Infinite V] (K : Finset V) :
    Nonempty (G.ComponentCompl K) :=
  let ⟨_, kK⟩ := K.finite_toSet.infinite_compl.nonempty
  ⟨componentComplMk _ kK⟩

namespace ComponentCompl

/-- A `ComponentCompl` specialization of `Quot.lift`, where soundness has to be proved only
for adjacent vertices.
-/
/-
**SimpleGraph.ComponentCompl.lift** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Compone
ntCompl`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} →     {K : Set V} →       {β : Sort u
_1} →         (f : ⦃v : V⦄ → v ∉ K → β) →           (∀ ⦃v w : V⦄ (hv : v ∉ K) (h
w : w ∉ K), G.Adj v w → f hv = f hw) → G.ComponentCompl K → β
参数：f : ⦃v : V⦄ → v ∉ K → β；∀ ⦃v w : V⦄ (hv : v ∉ K) (hw : w ∉ K), G.Adj v w → f 
hv = f hw。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `ComponentCompl` specialization of `Quot.lift`, where soundness has to be prov
ed only
for adjacent vertices.
-/
protected def lift {β : Sort*} (f : ∀ ⦃v⦄ (_ : v ∉ K), β)
    (h : ∀ ⦃v w⦄ (hv : v ∉ K) (hw : w ∉ K), G.Adj v w → f hv = f hw) : G.ComponentCompl K → β :=
  ConnectedComponent.lift (fun vv => f vv.prop) fun v w p => by
    induction p with
    | nil => rintro _; rfl
    | cons a q ih => rename_i u v w; rintro h'; exact (h u.prop v.prop a).trans (ih h'.of_cons)

@[elab_as_elim]
/-
**SimpleGraph.ComponentCompl.ind** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Componen
tCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V} {β : G.ComponentCompl K → P
rop},   (∀ ⦃v : V⦄ (hv : v ∉ K), β (G.componentComplMk hv)) → ∀ (C : G.Component
Compl K), β C
参数：∀ ⦃v : V⦄ (hv : v ∉ K), β (G.componentComplMk hv)；C : G.ComponentCompl K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind`：∀ {V : Type u} {G : SimpleGraph V} {
β : G.ConnectedComponent → Prop},   (∀ (v : V), β (G.connectedComponentMk v)) → 
∀ (c : G.ConnectedCompon…
-/
protected theorem ind {β : G.ComponentCompl K → Prop}
    (f : ∀ ⦃v⦄ (hv : v ∉ K), β (G.componentComplMk hv)) : ∀ C : G.ComponentCompl K, β C := by
  apply ConnectedComponent.ind
  exact fun ⟨v, vnK⟩ => f vnK

/-- The induced graph on the vertices `C`. -/
/-
**SimpleGraph.ComponentCompl.coeGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Com
ponentCompl`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {K : Set V} → (C : G.ComponentCompl K
) → SimpleGraph ↥C
参数：C : G.ComponentCompl K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced graph on the vertices `C`.
-/
protected abbrev coeGraph (C : ComponentCompl G K) : SimpleGraph C :=
  G.induce (C : Set V)
/-
**SimpleGraph.ComponentCompl.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Comp
onentCompl`。
形式化陈述：coe_inj {C D : G.ComponentCompl K} : (C : Set V) = (D : Set V) ↔ C = D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
theorem coe_inj {C D : G.ComponentCompl K} : (C : Set V) = (D : Set V) ↔ C = D :=
  SetLike.coe_set_eq

@[simp]
/-
**SimpleGraph.ComponentCompl.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Com
ponentCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V} (C : G.ComponentCompl K), (
↑C).Nonempty
参数：C : G.ComponentCompl K；↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ComponentCompl.ind`：∀ {V : Type u} {G : SimpleGraph V} {K : 
Set V} {β : G.ComponentCompl K → Prop},   (∀ ⦃v : V⦄ (hv : v ∉ K), β (G.componen
tComplMk hv)) → ∀ (C…
-/
protected theorem nonempty (C : G.ComponentCompl K) : (C : Set V).Nonempty :=
  C.ind fun v vnK => ⟨v, vnK, rfl⟩
/-
**SimpleGraph.ComponentCompl.exists_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.ComponentCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V} (C : G.ComponentCompl K), ∃
 v, ∃ (h : v ∉ K), G.componentComplMk h = C
参数：C : G.ComponentCompl K；h : v ∉ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ComponentCompl.nonempty`：∀ {V : Type u} {G : SimpleGraph V} 
{K : Set V} (C : G.ComponentCompl K), (↑C).Nonempty
-/
protected theorem exists_eq_mk (C : G.ComponentCompl K) :
    ∃ (v : _) (h : v ∉ K), G.componentComplMk h = C :=
  C.nonempty
/-
**SimpleGraph.ComponentCompl.disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.ComponentCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V} (C : G.ComponentCompl K), D
isjoint K ↑C
参数：C : G.ComponentCompl K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
-/
protected theorem disjoint_right (C : G.ComponentCompl K) : Disjoint K C := by
  rw [Set.disjoint_iff]
  exact fun v ⟨vK, vC⟩ => vC.choose vK
/-
**SimpleGraph.ComponentCompl.notMem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.ComponentCompl`。
形式化陈述：notMem_of_mem {C : G.ComponentCompl K} {c : V} (cC : c in C) : c ∉ K
参数：cC : c in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `SimpleGraph.ComponentCompl.disjoint_right`：∀ {V : Type u} {G : SimpleGra
ph V} {K : Set V} (C : G.ComponentCompl K), Disjoint K ↑C
-/
theorem notMem_of_mem {C : G.ComponentCompl K} {c : V} (cC : c ∈ C) : c ∉ K := fun cK =>
  Set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩
/-
**SimpleGraph.ComponentCompl.pairwise_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.ComponentCompl`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {K : Set V}, Pairwise fun C D => Disjoi
nt ↑C ↑D
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected theorem pairwise_disjoint :
    Pairwise fun C D : G.ComponentCompl K => Disjoint (C : Set V) (D : Set V) := by
  rintro C D ne
  rw [Set.disjoint_iff]
  exact fun u ⟨uC, uD⟩ => ne (uC.choose_spec.symm.trans uD.choose_spec)

/-- Any vertex adjacent to a vertex of `C` and not lying in `K` must lie in `C`.
-/
/-
**SimpleGraph.ComponentCompl.mem_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.C
omponentCompl`。
形式化陈述：mem_of_adj : forall {C : G.ComponentCompl K} (c d : V), c in C -> d ∉ K ->
 G.Adj c d -> d in C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ConnectedComponent.eq`：∀ {V : Type u} {G : SimpleGraph V} {v
 w : V}, G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u

--- 原说明 ---
Any vertex adjacent to a vertex of `C` and not lying in `K` must lie in `C`.
-/
theorem mem_of_adj : ∀ {C : G.ComponentCompl K} (c d : V), c ∈ C → d ∉ K → G.Adj c d → d ∈ C :=
  fun {C} c d ⟨cnK, h⟩ dnK cd =>
  ⟨dnK, by
    rw [← h, ConnectedComponent.eq]
    exact Adj.reachable cd.symm⟩

/--
Assuming `G` is preconnected and `K` not empty, given any connected component `C` outside of `K`,
there exists a vertex `k ∈ K` adjacent to a vertex `v ∈ C`.
-/
/-
**SimpleGraph.ComponentCompl.exists_adj_boundary_pair** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.ComponentCompl`。
形式化陈述：exists_adj_boundary_pair (Gc : G.Preconnected) (hK : K.Nonempty) : forall 
C : G.ComponentCompl K, exists ck : V × V, ck.1 in C ∧ ck.2 in K ∧ G.Adj ck.1 ck
.2
参数：Gc : G.Preconnected；hK : K.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ComponentCompl.ind`：∀ {V : Type u} {G : SimpleGraph V} {K : 
Set V} {β : G.ComponentCompl K → Prop},   (∀ ⦃v : V⦄ (hv : v ∉ K), β (G.componen
tComplMk hv)) → ∀ (C…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `SimpleGraph.ComponentCompl.disjoint_right`：∀ {V : Type u} {G : SimpleGra
ph V} {K : Set V} (C : G.ComponentCompl K), Disjoint K ↑C
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `SimpleGraph.Walk.exists_boundary_dart`：exists_boundary_dart {u v : V} (p
 : G.Walk u v) (S : Set V) (uS : u in S) (vS : v ∉ S) : exists d : G.Dart, d in 
p.darts ∧ d.fst in S ∧ d.sn…
· 使用定理 `SimpleGraph.componentComplMk_mem`：componentComplMk_mem (G : SimpleGraph 
V) {v : V} (vK : v ∉ K) : v in G.componentComplMk vK
· 使用定理 `SimpleGraph.ComponentCompl.mem_of_adj`：mem_of_adj : forall {C : G.Compon
entCompl K} (c d : V), c in C -> d ∉ K -> G.Adj c d -> d in C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Assuming `G` is preconnected and `K` not empty, given any connected component `C
` outside of `K`,
there exists a vertex `k ∈ K` adjacent to a vertex `v ∈ C`.
-/
theorem exists_adj_boundary_pair (Gc : G.Preconnected) (hK : K.Nonempty) :
    ∀ C : G.ComponentCompl K, ∃ ck : V × V, ck.1 ∈ C ∧ ck.2 ∈ K ∧ G.Adj ck.1 ck.2 := by
  refine ComponentCompl.ind fun v vnK => ?_
  let C : G.ComponentCompl K := G.componentComplMk vnK
  let dis := Set.disjoint_iff.mp C.disjoint_right
  by_contra! h
  suffices Set.univ = (C : Set V) by exact dis ⟨hK.choose_spec, this ▸ Set.mem_univ hK.some⟩
  symm
  rw [Set.eq_univ_iff_forall]
  rintro u
  by_contra unC
  obtain ⟨p⟩ := Gc v u
  obtain ⟨⟨⟨x, y⟩, xy⟩, -, xC, ynC⟩ :=
    p.exists_boundary_dart (C : Set V) (G.componentComplMk_mem vnK) unC
  exact ynC (mem_of_adj x y xC (fun yK : y ∈ K => h ⟨x, y⟩ xC yK xy) xy)

/--
If `K ⊆ L`, the components outside of `L` are all contained in a single component outside of `K`.
-/
/-
**SimpleGraph.ComponentCompl.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Compon
entCompl`。
形式化陈述：hom (h : K subseteq L) (C : G.ComponentCompl L) : G.ComponentCompl K
参数：h : K subseteq L；C : G.ComponentCompl L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K ⊆ L`, the components outside of `L` are all contained in a single componen
t outside of `K`.
-/
abbrev hom (h : K ⊆ L) (C : G.ComponentCompl L) : G.ComponentCompl K :=
  C.map <| induceHom Hom.id <| Set.compl_subset_compl.2 h
/-
**SimpleGraph.ComponentCompl.subset_hom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.C
omponentCompl`。
形式化陈述：subset_hom (C : G.ComponentCompl L) (h : K subseteq L) : (C : Set V) subse
teq (C.hom h : Set V)
参数：C : G.ComponentCompl L；h : K subseteq L。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_hom (C : G.ComponentCompl L) (h : K ⊆ L) : (C : Set V) ⊆ (C.hom h : Set V) := by
  rintro c ⟨cL, rfl⟩
  exact ⟨fun h' => cL (h h'), rfl⟩
/-
**SimpleGraph.ComponentCompl._root_.SimpleGraph.componentComplMk_mem_hom** 是 Mat
hlib 中的一个定理，位于命名空间 `SimpleGraph.ComponentCompl`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.componentComplMk_mem_hom
    (G : SimpleGraph V) {v : V} (vK : v ∉ K) (h : L ⊆ K) :
    v ∈ (G.componentComplMk vK).hom h :=
  subset_hom (G.componentComplMk vK) h (G.componentComplMk_mem vK)
/-
**SimpleGraph.ComponentCompl.hom_eq_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.ComponentCompl`。
形式化陈述：hom_eq_iff_le (C : G.ComponentCompl L) (h : K subseteq L) (D : G.Component
Compl K) : C.hom h = D ↔ (C : Set V) subseteq (D : Set V)
参数：C : G.ComponentCompl L；h : K subseteq L；D : G.ComponentCompl K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ComponentCompl.subset_hom`：subset_hom (C : G.ComponentCompl 
L) (h : K subseteq L) : (C : Set V) subseteq (C.hom h : Set V)
· 使用定理 `SimpleGraph.ComponentCompl.ind`：∀ {V : Type u} {G : SimpleGraph V} {K : 
Set V} {β : G.ComponentCompl K → Prop},   (∀ ⦃v : V⦄ (hv : v ∉ K), β (G.componen
tComplMk hv)) → ∀ (C…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem hom_eq_iff_le (C : G.ComponentCompl L) (h : K ⊆ L) (D : G.ComponentCompl K) :
    C.hom h = D ↔ (C : Set V) ⊆ (D : Set V) :=
  ⟨fun h' => h' ▸ C.subset_hom h, C.ind fun _ vnL vD => (vD ⟨vnL, rfl⟩).choose_spec⟩
/-
**SimpleGraph.ComponentCompl.hom_eq_iff_not_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.ComponentCompl`。
形式化陈述：hom_eq_iff_not_disjoint (C : G.ComponentCompl L) (h : K subseteq L) (D : G
.ComponentCompl K) : C.hom h = D ↔ ¬Disjoint (C : Set V) (D : Set V)
参数：C : G.ComponentCompl L；h : K subseteq L；D : G.ComponentCompl K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `SimpleGraph.ComponentCompl.ind`：∀ {V : Type u} {G : SimpleGraph V} {K : 
Set V} {β : G.ComponentCompl K → Prop},   (∀ ⦃v : V⦄ (hv : v ∉ K), β (G.componen
tComplMk hv)) → ∀ (C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hom_eq_iff_not_disjoint (C : G.ComponentCompl L) (h : K ⊆ L) (D : G.ComponentCompl K) :
    C.hom h = D ↔ ¬Disjoint (C : Set V) (D : Set V) := by
  rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    refine C.ind fun x xnL => ?_
    exact ⟨x, ⟨xnL, rfl⟩, ⟨fun xK => xnL (h xK), rfl⟩⟩
  · refine C.ind fun x xnL => ?_
    rintro ⟨x, ⟨_, e₁⟩, _, rfl⟩
    rw [← e₁]
    rfl
/-
**SimpleGraph.ComponentCompl.hom_refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Com
ponentCompl`。
形式化陈述：hom_refl (C : G.ComponentCompl L) : C.hom (subset_refl L) = C
参数：C : G.ComponentCompl L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_refl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] (a : α), a ⊆ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s
· 使用定理 `SimpleGraph.induceHom_id`：∀ {V : Type u_1} (G : SimpleGraph V) (s : Set 
V), SimpleGraph.induceHom SimpleGraph.Hom.id ⋯ = SimpleGraph.Hom.id
· 使用定理 `SimpleGraph.ConnectedComponent.map_id`：map_id (C : ConnectedComponent G)
 : C.map Hom.id = C
-/
theorem hom_refl (C : G.ComponentCompl L) : C.hom (subset_refl L) = C := by
  change C.map _ = C
  rw [induceHom_id G Lᶜ, ConnectedComponent.map_id]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.ComponentCompl.hom_trans** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Co
mponentCompl`。
形式化陈述：hom_trans (C : G.ComponentCompl L) (h : K subseteq L) (h' : M subseteq K) 
: C.hom (h'.trans h) = (C.hom h).hom h'
参数：C : G.ComponentCompl L；h : K subseteq L；h' : M subseteq K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.ConnectedComponent.map_comp`：map_comp (C : G.ConnectedCompon
ent) (φ : G ->g G') (ψ : G' ->g G'') : (C.map φ).map ψ = C.map (ψ.comp φ)
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `SimpleGraph.induceHom_comp`：∀ {V : Type u_1} {W : Type u_2} {X : Type u_
3} {G : SimpleGraph V} {G' : SimpleGraph W} {G'' : SimpleGraph X}   {s : Set V} 
{t : Set W} {r :…
-/
theorem hom_trans (C : G.ComponentCompl L) (h : K ⊆ L) (h' : M ⊆ K) :
    C.hom (h'.trans h) = (C.hom h).hom h' := by
  change C.map _ = (C.map _).map _
  rw [ConnectedComponent.map_comp, induceHom_comp]
  rfl
/-
**SimpleGraph.ComponentCompl.hom_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Compo
nentCompl`。
形式化陈述：hom_mk {v : V} (vnL : v ∉ L) (h : K subseteq L) : (G.componentComplMk vnL)
.hom h = G.componentComplMk (Set.notMem_subset h vnL)
参数：vnL : v ∉ L；h : K subseteq L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_mk {v : V} (vnL : v ∉ L) (h : K ⊆ L) :
    (G.componentComplMk vnL).hom h = G.componentComplMk (Set.notMem_subset h vnL) :=
  rfl
/-
**SimpleGraph.ComponentCompl.hom_infinite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.ComponentCompl`。
形式化陈述：hom_infinite (C : G.ComponentCompl L) (h : K subseteq L) (Cinf : (C : Set 
V).Infinite) : (C.hom h : Set V).Infinite
参数：C : G.ComponentCompl L；h : K subseteq L；Cinf : (C : Set V).Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `SimpleGraph.ComponentCompl.subset_hom`：subset_hom (C : G.ComponentCompl 
L) (h : K subseteq L) : (C : Set V) subseteq (C.hom h : Set V)
-/
theorem hom_infinite (C : G.ComponentCompl L) (h : K ⊆ L) (Cinf : (C : Set V).Infinite) :
    (C.hom h : Set V).Infinite :=
  Set.Infinite.mono (C.subset_hom h) Cinf
/-
**SimpleGraph.ComponentCompl.infinite_iff_in_all_ranges** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.ComponentCompl`。
形式化陈述：infinite_iff_in_all_ranges {K : Finset V} (C : G.ComponentCompl K) : C.sup
p.Infinite ↔ forall (L) (h : K subseteq L), exists D : G.ComponentCompl L, D.hom
 h = C
参数：C : G.ComponentCompl K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.nonempty`：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonemp
ty
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `SimpleGraph.ComponentCompl.nonempty`：∀ {V : Type u} {G : SimpleGraph V} 
{K : Set V} (C : G.ComponentCompl K), (↑C).Nonempty
· 使用定理 `SimpleGraph.ComponentCompl.disjoint_right`：∀ {V : Type u} {G : SimpleGra
ph V} {K : Set V} (C : G.ComponentCompl K), Disjoint K ↑C
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.ComponentCompl.hom_eq_iff_le`：hom_eq_iff_le (C : G.Component
Compl L) (h : K subseteq L) (D : G.ComponentCompl K) : C.hom h = D ↔ (C : Set V)
 subseteq (D : Set V)
-/
theorem infinite_iff_in_all_ranges {K : Finset V} (C : G.ComponentCompl K) :
    C.supp.Infinite ↔ ∀ (L) (h : K ⊆ L), ∃ D : G.ComponentCompl L, D.hom h = C := by
  classical
    constructor
    · rintro Cinf L h
      obtain ⟨v, ⟨vK, rfl⟩, vL⟩ := Set.Infinite.nonempty (Set.Infinite.sdiff Cinf L.finite_toSet)
      exact ⟨componentComplMk _ vL, rfl⟩
    · rintro h Cfin
      obtain ⟨D, e⟩ := h (K ∪ Cfin.toFinset) Finset.subset_union_left
      obtain ⟨v, vD⟩ := D.nonempty
      let Ddis := D.disjoint_right
      simp_rw [Finset.coe_union, Set.Finite.coe_toFinset, Set.disjoint_union_left,
        Set.disjoint_iff] at Ddis
      exact Ddis.right ⟨(ComponentCompl.hom_eq_iff_le _ _ _).mp e vD, vD⟩

end ComponentCompl

/-- For a locally finite preconnected graph, the number of components outside of any finite set
is finite. -/
/-
**SimpleGraph.componentCompl_finite** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：componentCompl_finite [LocallyFinite G] [Gpc : Fact G.Preconnected] (K : F
inset V) : Finite (G.ComponentCompl K)
参数：K : Finset V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `SimpleGraph.Preconnected.subsingleton_connectedComponent`：∀ {V : Type u}
 {G : SimpleGraph V}, G.Preconnected → Subsingleton G.ConnectedComponent
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ComponentCompl.exists_adj_boundary_pair`：exists_adj_boundary
_pair (Gc : G.Preconnected) (hK : K.Nonempty) : forall C : G.ComponentCompl K, e
xists ck : V × V, ck.1 in C ∧ ck.2 in K ∧…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {a b : α}, Pairwise r →
 ¬r a b → a = b
· 使用定理 `SimpleGraph.ComponentCompl.pairwise_disjoint`：∀ {V : Type u} {G : Simple
Graph V} {K : Set V}, Pairwise fun C D => Disjoint ↑C ↑D
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.Finite.ofFinset`：∀ {α : Type u} {p : Set α} (s : Finset α), (∀ (x : 
α), x ∈ s ↔ x ∈ p) → p.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finite.of_injective_finite_range`：Finite.of_injective_finite_range {f : 
ι -> α} (hf : Function.Injective f) [Finite (range f)] : Finite ι

--- 原说明 ---
For a locally finite preconnected graph, the number of components outside of any
 finite set
is finite.
-/
instance componentCompl_finite [LocallyFinite G] [Gpc : Fact G.Preconnected] (K : Finset V) :
    Finite (G.ComponentCompl K) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | h
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  · dsimp [ComponentCompl]
    rw [Finset.coe_empty, Set.compl_empty]
    have := Gpc.out.subsingleton_connectedComponent
    exact Finite.of_equiv _ (induceUnivIso G).connectedComponentEquiv.symm
  -- Otherwise, we consider the function `touch` mapping a connected component to one of its
  -- vertices adjacent to `K`.
  · let touch (C : G.ComponentCompl K) : {v : V | ∃ k : V, k ∈ K ∧ G.Adj k v} :=
      let p := C.exists_adj_boundary_pair Gpc.out h
      ⟨p.choose.1, p.choose.2, p.choose_spec.2.1, p.choose_spec.2.2.symm⟩
    -- `touch` is injective
    have touch_inj : touch.Injective := fun C D h' => ComponentCompl.pairwise_disjoint.eq
      (Set.not_disjoint_iff.mpr ⟨touch C, (C.exists_adj_boundary_pair Gpc.out h).choose_spec.1,
                                 h'.symm ▸ (D.exists_adj_boundary_pair Gpc.out h).choose_spec.1⟩)
    -- `touch` has finite range
    have : Finite (Set.range touch) := by
      refine @Subtype.finite _ (Set.Finite.to_subtype ?_) _
      apply Set.Finite.ofFinset (K.biUnion (fun v => G.neighborFinset v))
      simp only [Finset.mem_biUnion, mem_neighborFinset, Set.mem_ofPred_eq, implies_true]
    -- hence `touch` has a finite domain
    apply Finite.of_injective_finite_range touch_inj

section Ends

variable (G)

open CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/--
The functor assigning, to a finite set in `V`, the set of connected components in its complement.
-/
@[simps]
/-
**SimpleGraph.componentComplFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：componentComplFunctor : (Finset V)ᵒᵖ ⥤ Type u where obj K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor assigning, to a finite set in `V`, the set of connected components i
n its complement.
-/
def componentComplFunctor : (Finset V)ᵒᵖ ⥤ Type u where
  obj K := G.ComponentCompl K.unop
  map f := ↾(ComponentCompl.hom (le_of_op_hom f))
  map_id _ := by
    ext
    simp [ComponentCompl.hom_refl]
  map_comp {_ Y Z} h h' := by
    ext C
    simp

/-- The end of a graph, defined as the sections of the functor `component_compl_functor` . -/
/-
**SimpleGraph.** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The end of a graph, defined as the sections of the functor `component_compl_func
tor` .
-/
protected def «end» :=
  (componentComplFunctor G).sections
/-
**SimpleGraph.end_hom_mk_of_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：end_hom_mk_of_mk {s} (sec : s in G.end) {K L : (Finset V)ᵒᵖ} (h : L ⟶ K) {
v : V} (vnL : v ∉ L.unop) (hs : s L = G.componentComplMk vnL) : s K = G.componen
tComplMk (Set.notMem_subset (le_of_op_hom h) vnL)
参数：sec : s in G.end；Finset V；h : L ⟶ K；vnL : v ∉ L.unop；hs : s L = G.componentCo
mplMk vnL。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `CategoryTheory.le_of_op_hom`：le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop
 y <= unop x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ComponentCompl.hom_mk`：hom_mk {v : V} (vnL : v ∉ L) (h : K s
ubseteq L) : (G.componentComplMk vnL).hom h = G.componentComplMk (Set.notMem_sub
set h vnL)
-/
theorem end_hom_mk_of_mk {s} (sec : s ∈ G.end) {K L : (Finset V)ᵒᵖ} (h : L ⟶ K) {v : V}
    (vnL : v ∉ L.unop) (hs : s L = G.componentComplMk vnL) :
    s K = G.componentComplMk (Set.notMem_subset (le_of_op_hom h) vnL) := by
  rw [← sec h, hs]
  apply ComponentCompl.hom_mk _ (le_of_op_hom h)
/-
**SimpleGraph.infinite_iff_in_eventualRange** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：infinite_iff_in_eventualRange {K : (Finset V)ᵒᵖ} (C : G.componentComplFunc
tor.obj K) : C.supp.Infinite ↔ C in G.componentComplFunctor.eventualRange K
参数：Finset V；C : G.componentComplFunctor.obj K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.ComponentCompl.infinite_iff_in_all_ranges`：infinite_iff_in_a
ll_ranges {K : Finset V} (C : G.ComponentCompl K) : C.supp.Infinite ↔ forall (L)
 (h : K subseteq L), exists D : G.Component…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.componentComplFunctor_map`：∀ {V : Type u} (G : SimpleGraph V
) {X Y : (Finset V)ᵒᵖ} (f : X ⟶ Y),   G.componentComplFunctor.map f = TypeCat.of
Hom (SimpleGraph.ComponentC…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.le_of_op_hom`：le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop
 y <= unop x
-/
theorem infinite_iff_in_eventualRange {K : (Finset V)ᵒᵖ} (C : G.componentComplFunctor.obj K) :
    C.supp.Infinite ↔ C ∈ G.componentComplFunctor.eventualRange K := by
  simp only [C.infinite_iff_in_all_ranges, CategoryTheory.Functor.eventualRange, Set.mem_iInter,
    Set.mem_range, componentComplFunctor_map]
  exact
    ⟨fun h Lop KL => h Lop.unop (le_of_op_hom KL), fun h L KL =>
      h (Opposite.op L) (opHomOfLE KL)⟩

end Ends

end SimpleGraph

