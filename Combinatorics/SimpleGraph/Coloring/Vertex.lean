/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Order.Antichain
public import Mathlib.Order.Lattice.Nat

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper colorings in the literature).
A graph coloring is the attribution of "colors" to all of its vertices such that adjacent vertices
have different colors.
A coloring can be represented as a homomorphism into a complete graph, whose vertices represent
the colors.

## Main definitions

* `G.Coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.Colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromaticNumber` is the minimal `n` such that `G` is `n`-colorable,
  or `⊤` if it cannot be colored with finitely many colors.
  (Cardinal-valued chromatic numbers are more niche, so we stick to `ℕ∞`.)
  We write `G.chromaticNumber ≠ ⊤` to mean a graph is colorable with finitely many colors.

* `C.colorClass c` is the set of vertices colored by `c : α` in the coloring `C : G.Coloring α`.

* `C.colorClasses` is the set containing all color classes.

## TODO

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.Coloring α`)
-/

@[expose] public section

assert_not_exists Field

open Fintype Function

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
/-
**SimpleGraph.Coloring** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：Coloring (α : Type v)
参数：α : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete
 graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g completeGraph α

variable {G}
variable {ι α β : Type*} (C : G.Coloring α)
/-
**SimpleGraph.Coloring.valid** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) {v w 
: V}, G.Adj v w → C v ≠ C w
参数：C : G.Coloring α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.map_rel`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : 
β → β → Prop} (f : r →r s) {a b : α}, r a b → s (f a) (f b)
-/
theorem Coloring.valid {v w : V} (h : G.Adj v w) : C v ≠ C w :=
  C.map_rel h
/-
**SimpleGraph.Coloring.injective_comp_of_pairwise_adj** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {ι : Type u_1} {α : Type u_2} (C : G.Co
loring α) (f : ι → V),   (Pairwise fun i j => G.Adj (f i) (f j)) → Function.Inje
ctive (⇑C ∘ f)
参数：C : G.Coloring α；f : ι → V；Pairwise fun i j => G.Adj (f i) (f j)；⇑C ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.injective_iff_pairwise_ne`：Function.injective_iff_pairwise_ne :
 Injective f ↔ Pairwise ((· != ·) on f)
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
-/
lemma Coloring.injective_comp_of_pairwise_adj (C : G.Coloring α) (f : ι → V)
    (hf : Pairwise fun i j ↦ G.Adj (f i) (f j)) : (C ∘ f).Injective :=
  Function.injective_iff_pairwise_ne.2 <| hf.mono fun _ _ ↦ C.valid

/-- Construct a term of `SimpleGraph.Coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `SimpleGraph.Hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[match_pattern]
/-
**SimpleGraph.Coloring.mk** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} → {α : Type u_2} → (color : V → α) → 
(∀ {v w : V}, G.Adj v w → color v ≠ color w) → G.Coloring α
参数：color : V → α；∀ {v w : V}, G.Adj v w → color v ≠ color w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a term of `SimpleGraph.Coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `SimpleGraph.Hom`,
but with a syntactically better proper coloring hypothesis.)
-/
def Coloring.mk (color : V → α) (valid : ∀ {v w : V}, G.Adj v w → color v ≠ color w) :
    G.Coloring α :=
  ⟨color, @valid⟩

/-- The color class of a given color.
-/
/-
**SimpleGraph.Coloring.colorClass** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Colorin
g`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {α : Type u_2} → G.Coloring α → α → S
et V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The color class of a given color.
-/
def Coloring.colorClass (c : α) : Set V := { v : V | C v = c }

/-- The set containing all color classes. -/
/-
**SimpleGraph.Coloring.colorClasses** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Color
ing`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {α : Type u_2} → G.Coloring α → Set (
Set V)
参数：Set V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set containing all color classes.
-/
def Coloring.colorClasses : Set (Set V) := (Setoid.ker C).classes
/-
**SimpleGraph.Coloring.mem_colorClass** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Col
oring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) (v : 
V), v ∈ C.colorClass (C v)
参数：C : G.Coloring α；v : V；C v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Coloring.mem_colorClass (v : V) : v ∈ C.colorClass (C v) := rfl
/-
**SimpleGraph.Coloring.colorClasses_isPartition** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α), Seto
id.IsPartition C.colorClasses
参数：C : G.Coloring α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.isPartition_classes`：isPartition_classes (r : Setoid α) : IsParti
tion r.classes
-/
theorem Coloring.colorClasses_isPartition : Setoid.IsPartition C.colorClasses :=
  Setoid.isPartition_classes (Setoid.ker C)
/-
**SimpleGraph.Coloring.mem_colorClasses** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.C
oloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) {v : 
V}, C.colorClass (C v) ∈ C.colorClasses
参数：C : G.Coloring α；C v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Coloring.mem_colorClasses {v : V} : C.colorClass (C v) ∈ C.colorClasses :=
  ⟨v, rfl⟩
/-
**SimpleGraph.Coloring.colorClasses_finite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) [Fini
te α], C.colorClasses.Finite
参数：C : G.Coloring α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.finite_classes_ker`：finite_classes_ker {α β : Type*} [Finite β] (
f : α -> β) : (Setoid.ker f).classes.Finite
-/
theorem Coloring.colorClasses_finite [Finite α] : C.colorClasses.Finite :=
  Setoid.finite_classes_ker _
/-
**SimpleGraph.Coloring.card_colorClasses_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) [inst
 : Fintype α]   [inst_1 : Fintype ↑C.colorClasses], Fintype.card ↑C.colorClasses
 ≤ Fintype.card α
参数：C : G.Coloring α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Setoid.card_classes_ker_le`：card_classes_ker_le {α β : Type*} [Fintype β
] (f : α -> β) [Fintype (Setoid.ker f).classes] : Fintype.card (Setoid.ker f).cl
asses <= Fintype…
-/
theorem Coloring.card_colorClasses_le [Fintype α] [Fintype C.colorClasses] :
    Fintype.card C.colorClasses ≤ Fintype.card α := by
  simp only [colorClasses]
  convert! Setoid.card_classes_ker_le C
/-
**SimpleGraph.Coloring.not_adj_of_mem_colorClass** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) {c : 
α} {v w : V},   v ∈ C.colorClass c → w ∈ C.colorClass c → ¬G.Adj v w
参数：C : G.Coloring α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Coloring.not_adj_of_mem_colorClass {c : α} {v w : V} (hv : v ∈ C.colorClass c)
    (hw : w ∈ C.colorClass c) : ¬G.Adj v w := fun h => C.valid h (Eq.trans hv (Eq.symm hw))
/-
**SimpleGraph.Coloring.isIndepSet_colorClass** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) (c : 
α), G.IsIndepSet (C.colorClass c)
参数：C : G.Coloring α；c : α；C.colorClass c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.not_adj_of_mem_colorClass`：∀ {V : Type u} {G : Simp
leGraph V} {α : Type u_2} (C : G.Coloring α) {c : α} {v w : V},   v ∈ C.colorCla
ss c → w ∈ C.colorClass c → ¬G.Adj v…
-/
theorem Coloring.isIndepSet_colorClass (c : α) : G.IsIndepSet <| C.colorClass c :=
  fun _ hv _ hw _ ↦ C.not_adj_of_mem_colorClass hv hw

@[deprecated isIndepSet_colorClass (since := "2026-02-07")]
/-
**SimpleGraph.Coloring.color_classes_independent** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} (C : G.Coloring α) (c : 
α), IsAntichain G.Adj (C.colorClass c)
参数：C : G.Coloring α；c : α；C.colorClass c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.isIndepSet_colorClass`：∀ {V : Type u} {G : SimpleGr
aph V} {α : Type u_2} (C : G.Coloring α) (c : α), G.IsIndepSet (C.colorClass c)
-/
theorem Coloring.color_classes_independent (c : α) : IsAntichain G.Adj (C.colorClass c) :=
  C.isIndepSet_colorClass c

/-- Coloring induced from a homomorphism to a colored graph. -/
/-
**SimpleGraph.Coloring.comap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} →     {V' : Type u_4} → {G' : SimpleG
raph V'} → {α : Type u_5} → G'.Coloring α → G →g G' → G.Coloring α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coloring induced from a homomorphism to a colored graph.
-/
abbrev Coloring.comap {V' : Type*} {G' : SimpleGraph V'} {α : Type*} (C : G'.Coloring α)
    (f : G →g G') : G.Coloring α :=
  C.comp f

-- TODO make this computable
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Fintype V] [Fintype α] : Fintype (Coloring G α) := by
  classical
  change Fintype (RelHom G.Adj (completeGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] {c : α} :
    DecidablePred (· ∈ C.colorClass c) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | C v = c })
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty <| G.Coloring α] [Nontrivial α] [Nonempty V] : Nontrivial <| G.Coloring α := by
  classical
  have ⟨C⟩ := ‹Nonempty <| G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
  have ⟨c, hc⟩ := nontrivial_iff_exists_ne (C v) |>.mp inferInstance
  refine ⟨(Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C, C, fun h ↦ hc ?_⟩
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [Iso.completeGraph] at this
  grind
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty <| G.Coloring α] [Infinite α] [Nonempty V] : Infinite <| G.Coloring α := by
  classical
  have ⟨C⟩ := ‹Nonempty <| G.Coloring α›
  have ⟨v⟩ := ‹Nonempty V›
  let f c := (Iso.completeGraph <| Equiv.swap (C v) c).toHom.comp C
  refine Infinite.of_injective f fun a b h ↦ ?_
  have := congrFun (congrArg RelHom.toFun h) v
  dsimp [f, Iso.completeGraph] at this
  grind

variable (G) in
/-- Whether a graph can be colored by at most `n` colors. -/
/-
**SimpleGraph.Colorable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：Colorable (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether a graph can be colored by at most `n` colors.
-/
def Colorable (n : ℕ) : Prop := Nonempty (G.Coloring (Fin n))

/-- The coloring of an empty graph. -/
/-
**SimpleGraph.Coloring.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring
`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {α : Type u_2} → [IsEmpty V] → G.Colo
ring α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coloring of an empty graph.
-/
def Coloring.ofIsEmpty [IsEmpty V] : G.Coloring α := .mk isEmptyElim fun {v} => isEmptyElim v
/-
**SimpleGraph.Colorable.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colora
ble`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [IsEmpty V] (n : ℕ), G.Colorable n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colorable.of_isEmpty [IsEmpty V] (n : ℕ) : G.Colorable n := ⟨.ofIsEmpty⟩

@[deprecated (since := "2026-01-03")] alias coloringOfIsEmpty := Coloring.ofIsEmpty
@[deprecated (since := "2026-01-03")] alias colorableOfIsEmpty := Colorable.of_isEmpty

@[simp]
/-
**SimpleGraph.colorable_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：colorable_zero_iff : G.Colorable 0 ↔ IsEmpty V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `SimpleGraph.Colorable.of_isEmpty`：∀ {V : Type u} {G : SimpleGraph V} [Is
Empty V] (n : ℕ), G.Colorable n
-/
lemma colorable_zero_iff : G.Colorable 0 ↔ IsEmpty V :=
  ⟨fun ⟨C⟩ ↦ Function.isEmpty C, fun _ ↦ .of_isEmpty 0⟩

alias ⟨Colorable.isEmpty, _⟩ := colorable_zero_iff

@[deprecated (since := "2026-04-24")] alias isEmpty_of_colorable_zero := Colorable.isEmpty

@[simp]
/-
**SimpleGraph.colorable_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：colorable_one_iff : G.Colorable 1 ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.eq_bot_iff_forall_not_adj`：eq_bot_iff_forall_not_adj : G = ⊥
 ↔ forall a b : V, ¬G.Adj a b
· 使用定理 `RelHom.map_rel`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : 
β → β → Prop} (f : r →r s) {a b : α}, r a b → s (f a) (f b)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem colorable_one_iff : G.Colorable 1 ↔ G = ⊥ := by
  refine ⟨fun ⟨C⟩ ↦ eq_bot_iff_forall_not_adj.mpr fun u v h ↦ ?_, fun h ↦ h ▸ ⟨0, by simp⟩⟩
  exact C.map_rel h <| Subsingleton.elim ..

/-- A coloring of a graph `G` is a homomorphism from it to the mapped graph.
This is `Hom.map` spelled using colorings. The mapped graph `G.map f` can be thought of as taking
the original graph `G` and considering every color class (independent set) as a single vertex. -/
/-
**SimpleGraph.Coloring.homMap** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Coloring`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {α : Type u_4} → (f : G.Coloring α) →
 G →g SimpleGraph.map (⇑f) G
参数：f : G.Coloring α；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coloring of a graph `G` is a homomorphism from it to the mapped graph.
This is `Hom.map` spelled using colorings. The mapped graph `G.map f` can be tho
ught of as taking
the original graph `G` and considering every color class (independent set) as a 
single vertex.
-/
abbrev Coloring.homMap {α : Type*} (f : G.Coloring α) : G →g G.map f :=
  .map f G f.map_adj

/-- If `G` is `n`-colorable, then mapping the vertices of `G` produces an `n`-colorable simple
graph. -/
/-
**SimpleGraph.Colorable.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colorable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} {β : Type u_3} (f : V ↪ β) [NeZ
ero n],   G.Colorable n → (SimpleGraph.map (⇑f) G).Colorable n
参数：f : V ↪ β；SimpleGraph.map (⇑f) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w

--- 原说明 ---
If `G` is `n`-colorable, then mapping the vertices of `G` produces an `n`-colora
ble simple
graph.
-/
theorem Colorable.map (f : V ↪ β) [NeZero n] (hc : G.Colorable n) : (G.map f).Colorable n := by
  obtain ⟨C⟩ := hc
  use extend f C (const β default)
  intro a b ⟨_, _, _, hadj, ha, hb⟩
  rw [← ha, f.injective.extend_apply, ← hb, f.injective.extend_apply]
  exact C.valid hadj
/-
**SimpleGraph.Colorable.card_le_of_pairwise_adj** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Colorable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} {ι : Type u_1},   G.Colorable n
 → ∀ (f : ι → V), (Pairwise fun i j => G.Adj (f i) (f j)) → Nat.card ι ≤ n
参数：f : ι → V；Pairwise fun i j => G.Adj (f i) (f j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SimpleGraph.Coloring.injective_comp_of_pairwise_adj`：∀ {V : Type u} {G :
 SimpleGraph V} {ι : Type u_1} {α : Type u_2} (C : G.Coloring α) (f : ι → V),   
(Pairwise fun i j => G.Adj (f i) (f j)) →…
-/
lemma Colorable.card_le_of_pairwise_adj (hG : G.Colorable n) (f : ι → V)
    (hf : Pairwise fun i j ↦ G.Adj (f i) (f j)) : Nat.card ι ≤ n := by
  obtain ⟨C⟩ := hG
  simpa using Nat.card_le_card_of_injective _ (C.injective_comp_of_pairwise_adj f hf)

variable (G) in
/-- The "tautological" coloring of a graph, using the vertices of the graph as colors. -/
/-
**SimpleGraph.selfColoring** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：selfColoring : G.Coloring V
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b

--- 原说明 ---
The "tautological" coloring of a graph, using the vertices of the graph as color
s.
-/
def selfColoring : G.Coloring V := Coloring.mk id fun {_ _} => G.ne_of_adj

variable (G) in
/-- The chromatic number of a graph is the minimal number of colors needed to color it.
This is `⊤` (infinity) iff `G` isn't colorable with finitely many colors.

If `G` is colorable, then `ENat.toNat G.chromaticNumber` is the `ℕ`-valued chromatic number. -/
/-
**SimpleGraph.chromaticNumber** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber : Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chromatic number of a graph is the minimal number of colors needed to color 
it.
This is `⊤` (infinity) iff `G` isn't colorable with finitely many colors.

If `G` is colorable, then `ENat.toNat G.chromaticNumber` is the `ℕ`-valued chrom
atic number.
-/
noncomputable def chromaticNumber : ℕ∞ := ⨅ n ∈ Set.ofPred G.Colorable, (n : ℕ∞)
/-
**SimpleGraph.le_chromaticNumber_iff_colorable** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：le_chromaticNumber_iff_colorable : n <= G.chromaticNumber ↔ forall m, G.Co
lorable m -> n <= m
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_chromaticNumber_iff_colorable : n ≤ G.chromaticNumber ↔ ∀ m, G.Colorable m → n ≤ m := by
  simp [chromaticNumber]
/-
**SimpleGraph.le_chromaticNumber_iff_coloring** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph`。
形式化陈述：le_chromaticNumber_iff_coloring : n <= G.chromaticNumber ↔ forall m, G.Col
oring (Fin m) -> n <= m
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_chromaticNumber_iff_coloring :
    n ≤ G.chromaticNumber ↔ ∀ m, G.Coloring (Fin m) → n ≤ m := by
  simp [le_chromaticNumber_iff_colorable, Colorable]
/-
**SimpleGraph.le_chromaticNumber_of_pairwise_adj** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph`。
形式化陈述：le_chromaticNumber_of_pairwise_adj (hn : n <= Nat.card ι) (f : ι -> V) (hf
 : Pairwise fun i j => G.Adj (f i) (f j)) : n <= G.chromaticNumber
参数：hn : n <= Nat.card ι；f : ι -> V；hf : Pairwise fun i j => G.Adj (f i) (f j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.le_chromaticNumber_iff_colorable`：le_chromaticNumber_iff_col
orable : n <= G.chromaticNumber ↔ forall m, G.Colorable m -> n <= m
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SimpleGraph.Colorable.card_le_of_pairwise_adj`：∀ {V : Type u} {G : Simpl
eGraph V} {n : ℕ} {ι : Type u_1},   G.Colorable n → ∀ (f : ι → V), (Pairwise fun
 i j => G.Adj (f i) (f j)) → Nat.ca…
-/
lemma le_chromaticNumber_of_pairwise_adj (hn : n ≤ Nat.card ι) (f : ι → V)
    (hf : Pairwise fun i j ↦ G.Adj (f i) (f j)) : n ≤ G.chromaticNumber :=
  le_chromaticNumber_iff_colorable.2 fun _m hm ↦ hn.trans <| hm.card_le_of_pairwise_adj f hf

variable (G) in
/-
**SimpleGraph.chromaticNumber_eq_biInf** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_eq_biInf : G.chromaticNumber = ⨅ n in Set.ofPred G.Colorab
le, (n : Nat∞)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma chromaticNumber_eq_biInf : G.chromaticNumber = ⨅ n ∈ Set.ofPred G.Colorable, (n : ℕ∞) := rfl

variable (G) in
/-
**SimpleGraph.chromaticNumber_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_eq_iInf : G.chromaticNumber = ⨅ n : {m | G.Colorable m}, (
n : Nat∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber.eq_1`：∀ {V : Type u} (G : SimpleGraph V), G.
chromaticNumber = ⨅ n ∈ Set.ofPred G.Colorable, ↑n
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
-/
lemma chromaticNumber_eq_iInf : G.chromaticNumber = ⨅ n : {m | G.Colorable m}, (n : ℕ∞) := by
  rw [chromaticNumber, iInf_subtype]
/-
**SimpleGraph.Colorable.chromaticNumber_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Colorable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {n : ℕ}, G.Colorable n → G.chromaticNum
ber = ↑(sInf {n' | G.Colorable n'})
参数：sInf {n' | G.Colorable n'}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.natCast_sInf`：natCast_sInf (hs : s.Nonempty) : ↑(sInf s) = ⨅ a in s
, (a : Nat∞)
· 使用定理 `SimpleGraph.chromaticNumber.eq_1`：∀ {V : Type u} (G : SimpleGraph V), G.
chromaticNumber = ⨅ n ∈ Set.ofPred G.Colorable, ↑n
-/
lemma Colorable.chromaticNumber_eq_sInf (h : G.Colorable n) :
    G.chromaticNumber = sInf {n' : ℕ | G.Colorable n'} := by
  rw [ENat.natCast_sInf, chromaticNumber]
  exact ⟨_, h⟩

variable (G) in
/-- Given an embedding, there is an induced embedding of colorings. -/
/-
**SimpleGraph.recolorOfEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：recolorOfEmbedding {α β : Type*} (f : α ↪ β) : G.Coloring α ↪ G.Coloring β
 where toFun C
参数：f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding, there is an induced embedding of colorings.
-/
def recolorOfEmbedding {α β : Type*} (f : α ↪ β) : G.Coloring α ↪ G.Coloring β where
  toFun C := (Embedding.completeGraph f).toHom.comp C
  inj' C C' h := RelHom.mk.injEq C _ C' _ |>.mpr <| f.injective.comp_left <| RelHom.mk.inj h

variable (G) in
/-
**SimpleGraph.coe_recolorOfEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {α : Type u_2} {β : Type u_3} (f : α ↪ 
β),   ⇑(G.recolorOfEmbedding f) = (SimpleGraph.Embedding.completeGraph f).toHom.
comp
参数：G : SimpleGraph V；f : α ↪ β；G.recolorOfEmbedding f；SimpleGraph.Embedding.comp
leteGraph f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_recolorOfEmbedding (f : α ↪ β) :
    ⇑(G.recolorOfEmbedding f) = (Embedding.completeGraph f).toHom.comp := rfl

variable (G) in
/-- Given an equivalence, there is an induced equivalence between colorings. -/
/-
**SimpleGraph.recolorOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：recolorOfEquiv {α β : Type*} (f : α ≃ β) : G.Coloring α ≃ G.Coloring β whe
re toFun
参数：f : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an equivalence, there is an induced equivalence between colorings.
-/
def recolorOfEquiv {α β : Type*} (f : α ≃ β) : G.Coloring α ≃ G.Coloring β where
  toFun := G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv C := by
    ext v
    apply Equiv.symm_apply_apply
  right_inv C := by
    ext v
    apply Equiv.apply_symm_apply

variable (G) in
/-
**SimpleGraph.coe_recolorOfEquiv** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {α : Type u_2} {β : Type u_3} (f : α ≃ 
β),   ⇑(G.recolorOfEquiv f) = (SimpleGraph.Embedding.completeGraph f.toEmbedding
).toHom.comp
参数：G : SimpleGraph V；f : α ≃ β；G.recolorOfEquiv f；SimpleGraph.Embedding.complete
Graph f.toEmbedding。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_recolorOfEquiv (f : α ≃ β) :
    ⇑(G.recolorOfEquiv f) = (Embedding.completeGraph f).toHom.comp := rfl

variable (G) in
/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
/-
**SimpleGraph.recolorOfCardLE** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：recolorOfCardLE {α β : Type*} [Fintype α] [Fintype β] (hn : Fintype.card α
 <= Fintype.card β) : G.Coloring α ↪ G.Coloring β
参数：hn : Fintype.card α <= Fintype.card β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.nonempty_of_card_le`：nonempty_of_card_le [Fintype α] 
[Fintype β] (h : Fintype.card α <= Fintype.card β) : Nonempty (α ↪ β)

--- 原说明 ---
There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`.
-/
noncomputable def recolorOfCardLE {α β : Type*} [Fintype α] [Fintype β]
    (hn : Fintype.card α ≤ Fintype.card β) : G.Coloring α ↪ G.Coloring β :=
  G.recolorOfEmbedding <| (Function.Embedding.nonempty_of_card_le hn).some

variable (G) in
/-
**SimpleGraph.coe_recolorOfCardLE** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {α : Type u_2} {β : Type u_3} [inst : F
intype α] [inst_1 : Fintype β]   (hαβ : Fintype.card α ≤ Fintype.card β),   ⇑(G.
recolorOfCardLE hαβ) = (SimpleGraph.Embedding.completeGraph ⋯.some).toHom.comp
参数：G : SimpleGraph V；hαβ : Fintype.card α ≤ Fintype.card β；G.recolorOfCardLE hαβ
；SimpleGraph.Embedding.completeGraph ⋯.some。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_recolorOfCardLE [Fintype α] [Fintype β] (hαβ : card α ≤ card β) :
    ⇑(G.recolorOfCardLE hαβ) =
      (Embedding.completeGraph (Embedding.nonempty_of_card_le hαβ).some).toHom.comp := rfl
/-
**SimpleGraph.Colorable.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colorable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {n m : ℕ}, n ≤ m → G.Colorable n → G.Co
lorable m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem Colorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.Colorable n) : G.Colorable m :=
  ⟨G.recolorOfCardLE (by simp [h]) hc.some⟩
/-
**SimpleGraph.Coloring.colorable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Coloring
`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} [inst : Fintype α] (C : 
G.Coloring α), G.Colorable (Fintype.card α)
参数：C : G.Coloring α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem Coloring.colorable [Fintype α] (C : G.Coloring α) : G.Colorable (Fintype.card α) :=
  ⟨G.recolorOfCardLE (by simp) C⟩
/-
**SimpleGraph.colorable_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable (Fintyp
e.card V)
参数：G : SimpleGraph V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
-/
theorem colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable (Fintype.card V) :=
  G.selfColoring.colorable

/-- Noncomputably get a coloring from colorability. -/
/-
**SimpleGraph.Colorable.toColoring** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Colora
ble`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} →     {α : Type u_2} → [inst : Fintyp
e α] → {n : ℕ} → G.Colorable n → n ≤ Fintype.card α → G.Coloring α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputably get a coloring from colorability.
-/
noncomputable def Colorable.toColoring [Fintype α] {n : ℕ} (hc : G.Colorable n)
    (hn : n ≤ Fintype.card α) : G.Coloring α := by
  rw [← Fintype.card_fin n] at hn
  exact G.recolorOfCardLE hn hc.some
/-
**SimpleGraph.Colorable.of_hom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colorable`
。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {V' : Type u_4} {G' : SimpleGraph V'} {
n : ℕ} (f : G →g G'),   G'.Colorable n → G.Colorable n
参数：f : G →g G'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colorable.of_hom {V' : Type*} {G' : SimpleGraph V'} {n : ℕ} (f : G →g G')
    (h : G'.Colorable n) : G.Colorable n :=
  ⟨h.some.comap f⟩
/-
**SimpleGraph.colorable_iff_exists_bdd_nat_coloring** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：colorable_iff_exists_bdd_nat_coloring (n : Nat) : G.Colorable n ↔ exists C
 : G.Coloring Nat, forall v, C v < n
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
-/
theorem colorable_iff_exists_bdd_nat_coloring (n : ℕ) :
    G.Colorable n ↔ ∃ C : G.Coloring ℕ, ∀ v, C v < n := by
  constructor
  · rintro hc
    have C : G.Coloring (Fin n) := hc.toColoring (by simp)
    let f := Embedding.completeGraph (@Fin.valEmbedding n)
    use f.toHom.comp C
    intro v
    exact Fin.is_lt (C.1 v)
  · rintro ⟨C, Cf⟩
    refine ⟨Coloring.mk ?_ ?_⟩
    · exact fun v => ⟨C v, Cf v⟩
    · rintro v w hvw
      simp only [Fin.mk_eq_mk, Ne]
      exact C.valid hvw
/-
**SimpleGraph.colorable_iff_forall_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：colorable_iff_forall_connectedComponent {n : Nat} : G.Colorable n ↔ forall
 c : G.ConnectedComponent, (c.toSimpleGraph).Colorable n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
-/
theorem colorable_iff_forall_connectedComponent {n : ℕ} :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (c.toSimpleGraph).Colorable n :=
  ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v, fun h h1 ↦ C.valid h h1⟩,
   fun h ↦ ⟨G.homOfConnectedComponents (fun c ↦ (h c).some)⟩⟩

@[deprecated (since := "2026-07-12")]
alias colorable_iff_forall_connectedComponents := colorable_iff_forall_connectedComponent
/-
**SimpleGraph.colorable_set_nonempty_of_colorable** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：colorable_set_nonempty_of_colorable {n : Nat} (hc : G.Colorable n) : { n :
 Nat | G.Colorable n }.Nonempty
参数：hc : G.Colorable n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colorable_set_nonempty_of_colorable {n : ℕ} (hc : G.Colorable n) :
    { n : ℕ | G.Colorable n }.Nonempty :=
  ⟨n, hc⟩
/-
**SimpleGraph.chromaticNumber_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_bddBelow : BddBelow { n : Nat | G.Colorable n }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem chromaticNumber_bddBelow : BddBelow { n : ℕ | G.Colorable n } :=
  ⟨0, fun _ _ => zero_le⟩
/-
**SimpleGraph.Colorable.chromaticNumber_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Colorable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {n : ℕ}, G.Colorable n → G.chromaticNum
ber ≤ ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_eq_sInf`：∀ {V : Type u} {G : Simpl
eGraph V} {n : ℕ}, G.Colorable n → G.chromaticNumber = ↑(sInf {n' | G.Colorable 
n'})
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `SimpleGraph.chromaticNumber_bddBelow`：chromaticNumber_bddBelow : BddBelo
w { n : Nat | G.Colorable n }
-/
theorem Colorable.chromaticNumber_le {n : ℕ} (hc : G.Colorable n) : G.chromaticNumber ≤ n := by
  rw [hc.chromaticNumber_eq_sInf]
  norm_cast
  apply csInf_le chromaticNumber_bddBelow
  exact hc
/-
**SimpleGraph.chromaticNumber_ne_top_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：chromaticNumber_ne_top_iff_exists : G.chromaticNumber != ⊤ ↔ exists n, G.C
olorable n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber.eq_1`：∀ {V : Type u} (G : SimpleGraph V), G.
chromaticNumber = ⨅ n ∈ Set.ofPred G.Colorable, ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem chromaticNumber_ne_top_iff_exists : G.chromaticNumber ≠ ⊤ ↔ ∃ n, G.Colorable n := by
  rw [chromaticNumber]
  simp
/-
**SimpleGraph.chromaticNumber_le_iff_colorable** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：chromaticNumber_le_iff_colorable {n : Nat} : G.chromaticNumber <= n ↔ G.Co
lorable n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `ENat.natCast_lt_top`：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber_ne_top_iff_exists`：chromaticNumber_ne_top_if
f_exists : G.chromaticNumber != ⊤ ↔ exists n, G.Colorable n
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `SimpleGraph.Colorable.mono`：∀ {V : Type u} {G : SimpleGraph V} {n m : ℕ}
, n ≤ m → G.Colorable n → G.Colorable m
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_eq_sInf`：∀ {V : Type u} {G : Simpl
eGraph V} {n : ℕ}, G.Colorable n → G.chromaticNumber = ↑(sInf {n' | G.Colorable 
n'})
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
-/
theorem chromaticNumber_le_iff_colorable {n : ℕ} : G.chromaticNumber ≤ n ↔ G.Colorable n := by
  refine ⟨fun h ↦ ?_, Colorable.chromaticNumber_le⟩
  have : G.chromaticNumber ≠ ⊤ := (trans h (ENat.natCast_lt_top n)).ne
  rw [chromaticNumber_ne_top_iff_exists] at this
  obtain ⟨m, hm⟩ := this
  rw [hm.chromaticNumber_eq_sInf, Nat.cast_le] at h
  have := Nat.sInf_mem (⟨m, hm⟩ : {n' | G.Colorable n'}.Nonempty)
  rw [Set.mem_ofPred_eq] at this
  exact this.mono h

/-- If the chromatic number of `G` is `n + 1`, then `G` is colorable in no fewer than `n + 1`
colors. -/
/-
**SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_eq_iff_colorable_not_colorable : G.chromaticNumber = n + 1
 ↔ G.Colorable (n + 1) ∧ ¬G.Colorable n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If the chromatic number of `G` is `n + 1`, then `G` is colorable in no fewer tha
n `n + 1`
colors.
-/
theorem chromaticNumber_eq_iff_colorable_not_colorable :
    G.chromaticNumber = n + 1 ↔ G.Colorable (n + 1) ∧ ¬G.Colorable n := by
  rw [eq_iff_le_not_lt, not_lt, ENat.add_one_le_iff (ENat.natCast_ne_top n), ← not_le,
    chromaticNumber_le_iff_colorable, ← Nat.cast_add_one, chromaticNumber_le_iff_colorable]
/-
**SimpleGraph.colorable_chromaticNumber** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：colorable_chromaticNumber {m : Nat} (hc : G.Colorable m) : G.Colorable (EN
at.toNat G.chromaticNumber)
参数：hc : G.Colorable m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_eq_sInf`：∀ {V : Type u} {G : Simpl
eGraph V} {n : ℕ}, G.Colorable n → G.chromaticNumber = ↑(sInf {n' | G.Colorable 
n'})
· 使用定理 `SimpleGraph.colorable_set_nonempty_of_colorable`：colorable_set_nonempty_
of_colorable {n : Nat} (hc : G.Colorable n) : { n : Nat | G.Colorable n }.Nonemp
ty
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem colorable_chromaticNumber {m : ℕ} (hc : G.Colorable m) :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  classical
  rw [hc.chromaticNumber_eq_sInf, Nat.sInf_def]
  · apply Nat.find_spec
  · exact colorable_set_nonempty_of_colorable hc
/-
**SimpleGraph.colorable_chromaticNumber_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：colorable_chromaticNumber_of_fintype (G : SimpleGraph V) [Finite V] : G.Co
lorable (ENat.toNat G.chromaticNumber)
参数：G : SimpleGraph V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `SimpleGraph.colorable_chromaticNumber`：colorable_chromaticNumber {m : Na
t} (hc : G.Colorable m) : G.Colorable (ENat.toNat G.chromaticNumber)
· 使用定理 `SimpleGraph.colorable_of_fintype`：colorable_of_fintype (G : SimpleGraph 
V) [Fintype V] : G.Colorable (Fintype.card V)
-/
theorem colorable_chromaticNumber_of_fintype (G : SimpleGraph V) [Finite V] :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  cases nonempty_fintype V
  exact colorable_chromaticNumber G.colorable_of_fintype
/-
**SimpleGraph.chromaticNumber_le_one_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：chromaticNumber_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V
] : G.chromaticNumber <= 1
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem chromaticNumber_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V] :
    G.chromaticNumber ≤ 1 := by
  rw [← Nat.cast_one, chromaticNumber_le_iff_colorable]
  refine ⟨Coloring.mk (fun _ => 0) ?_⟩
  intro v w
  cases Subsingleton.elim v w
  simp
/-
**SimpleGraph.Colorable.chromaticNumber_pos** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Colorable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [Nonempty V] {n : ℕ}, G.Colorable n → 0
 < G.chromaticNumber
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_eq_sInf`：∀ {V : Type u} {G : Simpl
eGraph V} {n : ℕ}, G.Colorable n → G.chromaticNumber = ↑(sInf {n' | G.Colorable 
n'})
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `SimpleGraph.colorable_set_nonempty_of_colorable`：colorable_set_nonempty_
of_colorable {n : Nat} (hc : G.Colorable n) : { n : Nat | G.Colorable n }.Nonemp
ty
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Nat.not_lt_zero`：∀ (n : ℕ), ¬n < 0
-/
theorem Colorable.chromaticNumber_pos [Nonempty V] {n : ℕ} (hc : G.Colorable n) :
    0 < G.chromaticNumber := by
  rw [hc.chromaticNumber_eq_sInf, Nat.cast_pos]
  apply le_csInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_le] at h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  have h₁ : i < 0 := lt_of_lt_of_le hi (Nat.le_of_lt_succ h')
  exact Nat.not_lt_zero _ h₁

@[deprecated (since := "2026-05-20")] alias chromaticNumber_pos := Colorable.chromaticNumber_pos
/-
**SimpleGraph.colorable_of_chromaticNumber_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：colorable_of_chromaticNumber_ne_top (h : G.chromaticNumber != ⊤) : G.Color
able (ENat.toNat G.chromaticNumber)
参数：h : G.chromaticNumber != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber_ne_top_iff_exists`：chromaticNumber_ne_top_if
f_exists : G.chromaticNumber != ⊤ ↔ exists n, G.Colorable n
· 使用定理 `SimpleGraph.colorable_chromaticNumber`：colorable_chromaticNumber {m : Na
t} (hc : G.Colorable m) : G.Colorable (ENat.toNat G.chromaticNumber)
-/
theorem colorable_of_chromaticNumber_ne_top (h : G.chromaticNumber ≠ ⊤) :
    G.Colorable (ENat.toNat G.chromaticNumber) := by
  rw [chromaticNumber_ne_top_iff_exists] at h
  obtain ⟨n, hn⟩ := h
  exact colorable_chromaticNumber hn
/-
**SimpleGraph.Colorable.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colorab
le`。
形式化陈述：∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G' → ∀ {n : ℕ}, G'.Colorable n 
→ G.Colorable n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Colorable.mono_left {G' : SimpleGraph V} (h : G ≤ G') {n : ℕ} (hc : G'.Colorable n) :
    G.Colorable n :=
  ⟨hc.some.comp (.ofLE h)⟩
/-
**SimpleGraph.chromaticNumber_le_of_forall_imp** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：chromaticNumber_le_of_forall_imp {V' : Type*} {G' : SimpleGraph V'} (h : f
orall n, G'.Colorable n -> G.Colorable n) : G.chromaticNumber <= G'.chromaticNum
ber
参数：h : forall n, G'.Colorable n -> G.Colorable n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber.eq_1`：∀ {V : Type u} (G : SimpleGraph V), G.
chromaticNumber = ⨅ n ∈ Set.ofPred G.Colorable, ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
-/
theorem chromaticNumber_le_of_forall_imp {V' : Type*} {G' : SimpleGraph V'}
    (h : ∀ n, G'.Colorable n → G.Colorable n) :
    G.chromaticNumber ≤ G'.chromaticNumber := by
  rw [chromaticNumber, chromaticNumber]
  simp only [Set.mem_ofPred_eq, le_iInf_iff]
  intro m hc
  have := h _ hc
  rw [← chromaticNumber_le_iff_colorable] at this
  exact this
/-
**SimpleGraph.chromaticNumber_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_mono (G' : SimpleGraph V) (h : G <= G') : G.chromaticNumbe
r <= G'.chromaticNumber
参数：G' : SimpleGraph V；h : G <= G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.chromaticNumber_le_of_forall_imp`：chromaticNumber_le_of_fora
ll_imp {V' : Type*} {G' : SimpleGraph V'} (h : forall n, G'.Colorable n -> G.Col
orable n) : G.chromaticNumber <= G…
· 使用定理 `SimpleGraph.Colorable.mono_left`：∀ {V : Type u} {G G' : SimpleGraph V}, 
G ≤ G' → ∀ {n : ℕ}, G'.Colorable n → G.Colorable n
-/
theorem chromaticNumber_mono (G' : SimpleGraph V)
    (h : G ≤ G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  chromaticNumber_le_of_forall_imp fun _ => Colorable.mono_left h
/-
**SimpleGraph.chromaticNumber_mono_of_hom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：chromaticNumber_mono_of_hom {V' : Type*} {G' : SimpleGraph V'} (f : G ->g 
G') : G.chromaticNumber <= G'.chromaticNumber
参数：f : G ->g G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.chromaticNumber_le_of_forall_imp`：chromaticNumber_le_of_fora
ll_imp {V' : Type*} {G' : SimpleGraph V'} (h : forall n, G'.Colorable n -> G.Col
orable n) : G.chromaticNumber <= G…
· 使用定理 `SimpleGraph.Colorable.of_hom`：∀ {V : Type u} {G : SimpleGraph V} {V' : T
ype u_4} {G' : SimpleGraph V'} {n : ℕ} (f : G →g G'),   G'.Colorable n → G.Color
able n
-/
theorem chromaticNumber_mono_of_hom {V' : Type*} {G' : SimpleGraph V'} (f : G →g G') :
    G.chromaticNumber ≤ G'.chromaticNumber :=
  chromaticNumber_le_of_forall_imp fun _ hc => hc.of_hom f
/-
**SimpleGraph.card_le_chromaticNumber_iff_forall_surjective** 是 Mathlib 中的一个引理，位
于命名空间 `SimpleGraph`。
形式化陈述：card_le_chromaticNumber_iff_forall_surjective [Fintype α] : card α <= G.ch
romaticNumber ↔ forall C : G.Coloring α, Surjective C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.notMem_of_lt_sInf`：notMem_of_lt_sInf {s : Set Nat} {m : Nat} (hm : m
 < sInf s) : m ∉ s
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.sub_one_lt_of_lt`：∀ {n m : ℕ}, m < n → n - 1 < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_eq_sInf`：∀ {V : Type u} {G : Simpl
eGraph V} {n : ℕ}, G.Colorable n → G.chromaticNumber = ↑(sInf {n' | G.Colorable 
n'})
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 35 条，此处仅展示前 30 条）
-/
lemma card_le_chromaticNumber_iff_forall_surjective [Fintype α] :
    card α ≤ G.chromaticNumber ↔ ∀ C : G.Coloring α, Surjective C := by
  refine ⟨fun h C ↦ ?_, fun h ↦ ?_⟩
  · rw [C.colorable.chromaticNumber_eq_sInf, Nat.cast_le] at h
    intro i
    by_contra! hi
    let D : G.Coloring {a // a ≠ i} := ⟨fun v ↦ ⟨C v, hi v⟩, (C.valid · <| congr_arg Subtype.val ·)⟩
    classical
    exact Nat.notMem_of_lt_sInf ((Nat.sub_one_lt_of_lt <| card_pos_iff.2 ⟨i⟩).trans_le h)
      ⟨G.recolorOfEquiv (equivOfCardEq <| by simp) D⟩
  · simp only [chromaticNumber, Set.mem_ofPred_eq, le_iInf_iff, Nat.cast_le]
    rintro i ⟨C⟩
    contrapose! h
    refine ⟨G.recolorOfCardLE (by simpa using h.le) C, fun hC ↦ ?_⟩
    dsimp at hC
    simpa [h.not_ge] using Fintype.card_le_of_surjective _ hC.of_comp
/-
**SimpleGraph.le_chromaticNumber_iff_forall_surjective** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph`。
形式化陈述：le_chromaticNumber_iff_forall_surjective : n <= G.chromaticNumber ↔ forall
 C : G.Coloring (Fin n), Surjective C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_chromaticNumber_iff_forall_surjective :
    n ≤ G.chromaticNumber ↔ ∀ C : G.Coloring (Fin n), Surjective C := by
  simp [← card_le_chromaticNumber_iff_forall_surjective]
/-
**SimpleGraph.chromaticNumber_eq_card_iff_forall_surjective** 是 Mathlib 中的一个引理，位
于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_eq_card_iff_forall_surjective [Fintype α] (hG : G.Colorabl
e (card α)) : G.chromaticNumber = card α ↔ forall C : G.Coloring α, Surjective C
参数：hG : G.Colorable (card α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用引理 `SimpleGraph.card_le_chromaticNumber_iff_forall_surjective`：card_le_chrom
aticNumber_iff_forall_surjective [Fintype α] : card α <= G.chromaticNumber ↔ for
all C : G.Coloring α, Surjective C
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma chromaticNumber_eq_card_iff_forall_surjective [Fintype α] (hG : G.Colorable (card α)) :
    G.chromaticNumber = card α ↔ ∀ C : G.Coloring α, Surjective C := by
  rw [← hG.chromaticNumber_le.ge_iff_eq, card_le_chromaticNumber_iff_forall_surjective]
/-
**SimpleGraph.chromaticNumber_eq_iff_forall_surjective** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph`。
形式化陈述：chromaticNumber_eq_iff_forall_surjective (hG : G.Colorable n) : G.chromati
cNumber = n ↔ forall C : G.Coloring (Fin n), Surjective C
参数：hG : G.Colorable n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用引理 `SimpleGraph.le_chromaticNumber_iff_forall_surjective`：le_chromaticNumber
_iff_forall_surjective : n <= G.chromaticNumber ↔ forall C : G.Coloring (Fin n),
 Surjective C
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma chromaticNumber_eq_iff_forall_surjective (hG : G.Colorable n) :
    G.chromaticNumber = n ↔ ∀ C : G.Coloring (Fin n), Surjective C := by
  rw [← hG.chromaticNumber_le.ge_iff_eq, le_chromaticNumber_iff_forall_surjective]
/-
**SimpleGraph.chromaticNumber_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_pos`：∀ {V : Type u} {G : SimpleGra
ph V} [Nonempty V] {n : ℕ}, G.Colorable n → 0 < G.chromaticNumber
-/
theorem chromaticNumber_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1 :=
  have : (⊥ : SimpleGraph V).Colorable 1 := by simp
  this.chromaticNumber_le.antisymm <| Order.one_le_iff_pos.2 this.chromaticNumber_pos

@[simp]
/-
**SimpleGraph.chromaticNumber_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_top [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fi
ntype.card V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.chromaticNumber_eq_card_iff_forall_surjective`：chromaticNumb
er_eq_card_iff_forall_surjective [Fintype α] (hG : G.Colorable (card α)) : G.chr
omaticNumber = card α ↔ forall C : G.Coloring α…
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SimpleGraph.Hom.injective_of_top_hom`：injective_of_top_hom (f : (⊤ : Sim
pleGraph V) ->g G') : Function.Injective f
-/
theorem chromaticNumber_top [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V := by
  rw [chromaticNumber_eq_card_iff_forall_surjective (selfColoring _).colorable]
  intro C
  rw [← Finite.injective_iff_surjective]
  exact Hom.injective_of_top_hom C

@[simp]
/-
**SimpleGraph.chromaticNumber_top_eq_top_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：chromaticNumber_top_eq_top_of_infinite (V : Type*) [Infinite V] : (⊤ : Sim
pleGraph V).chromaticNumber = ⊤
参数：V : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber_ne_top_iff_exists`：chromaticNumber_ne_top_if
f_exists : G.chromaticNumber != ⊤ ↔ exists n, G.Colorable n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_injective_infinite_finite`：not_injective_infinite_finite {α β} [Infi
nite α] [Finite β] (f : α -> β) : ¬Injective f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SimpleGraph.Hom.injective_of_top_hom`：injective_of_top_hom (f : (⊤ : Sim
pleGraph V) ->g G') : Function.Injective f
-/
theorem chromaticNumber_top_eq_top_of_infinite (V : Type*) [Infinite V] :
    (⊤ : SimpleGraph V).chromaticNumber = ⊤ := by
  by_contra hc
  rw [← Ne, chromaticNumber_ne_top_iff_exists] at hc
  obtain ⟨n, ⟨hn⟩⟩ := hc
  exact not_injective_infinite_finite _ hn.injective_of_top_hom

@[simp]
/-
**SimpleGraph.chromaticNumber_top_eq_enat_card** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：chromaticNumber_top_eq_enat_card : (⊤ : SimpleGraph V).chromaticNumber = E
Nat.card V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber_top`：chromaticNumber_top [Fintype V] : (⊤ : 
SimpleGraph V).chromaticNumber = Fintype.card V
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.chromaticNumber_top_eq_top_of_infinite`：chromaticNumber_top_
eq_top_of_infinite (V : Type*) [Infinite V] : (⊤ : SimpleGraph V).chromaticNumbe
r = ⊤
· 使用定理 `ENat.card_eq_top_of_infinite`：card_eq_top_of_infinite [Infinite α] : car
d α = ⊤
-/
theorem chromaticNumber_top_eq_enat_card : (⊤ : SimpleGraph V).chromaticNumber = ENat.card V := by
  cases finite_or_infinite V
  · have := Fintype.ofFinite ‹_›
    simp
  · simp
/-
**SimpleGraph.eq_top_of_chromaticNumber_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：eq_top_of_chromaticNumber_eq_card [Fintype V] (h : G.chromaticNumber = Fin
type.card V) : G = ⊤
参数：h : G.chromaticNumber = Fintype.card V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.ne_top_iff_exists_not_adj`：ne_top_iff_exists_not_adj : G != 
⊤ ↔ exists a b : V, a != b ∧ ¬G.Adj a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `SimpleGraph.nontrivial_iff`：∀ {V : Type u}, Nontrivial (SimpleGraph V) ↔
 Nontrivial V
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_sub`：natCast_sub (m n : Nat) : ↑(m - n) = (m - n : Nat∞)
· 使用定理 `ENat.natCast_one`：natCast_one : ((1 : Nat) : Nat∞) = 1
-/
theorem eq_top_of_chromaticNumber_eq_card [Fintype V]
    (h : G.chromaticNumber = Fintype.card V) : G = ⊤ := by
  classical
  by_contra! hh
  have : G.chromaticNumber ≤ Fintype.card V - 1 := by
    obtain ⟨a, b, hne, _⟩ := ne_top_iff_exists_not_adj.mp hh
    apply chromaticNumber_le_iff_colorable.mpr
    suffices G.Coloring (Finset.univ.erase b) by simpa using Coloring.colorable this
    apply Coloring.mk (fun x ↦ if h' : x ≠ b then ⟨x, by simp [h']⟩ else ⟨a, by simp [hne]⟩)
    grind [Adj.ne', adj_symm]
  rw [h, ← ENat.natCast_one, ← ENat.natCast_sub, ENat.natCast_le_natCast] at this
  have := Fintype.one_lt_card_iff_nontrivial.mpr <| SimpleGraph.nontrivial_iff.mp ⟨_, _, hh⟩
  grind
/-
**SimpleGraph.chromaticNumber_eq_card_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：chromaticNumber_eq_card_iff [Fintype V] : G.chromaticNumber = Fintype.card
 V ↔ G = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.eq_top_of_chromaticNumber_eq_card`：eq_top_of_chromaticNumber
_eq_card [Fintype V] (h : G.chromaticNumber = Fintype.card V) : G = ⊤
· 使用定理 `SimpleGraph.chromaticNumber_top`：chromaticNumber_top [Fintype V] : (⊤ : 
SimpleGraph V).chromaticNumber = Fintype.card V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem chromaticNumber_eq_card_iff [Fintype V] :
    G.chromaticNumber = Fintype.card V ↔ G = ⊤ :=
  ⟨eq_top_of_chromaticNumber_eq_card, fun h ↦ h ▸ chromaticNumber_top⟩
/-
**SimpleGraph.chromaticNumber_le_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_le_card [Fintype V] : G.chromaticNumber <= Fintype.card V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.chromaticNumber_top`：chromaticNumber_top [Fintype V] : (⊤ : 
SimpleGraph V).chromaticNumber = Fintype.card V
· 使用定理 `SimpleGraph.chromaticNumber_mono_of_hom`：chromaticNumber_mono_of_hom {V'
 : Type*} {G' : SimpleGraph V'} (f : G ->g G') : G.chromaticNumber <= G'.chromat
icNumber
-/
theorem chromaticNumber_le_card [Fintype V] : G.chromaticNumber ≤ Fintype.card V := by
  rw [← chromaticNumber_top]
  exact chromaticNumber_mono_of_hom G.selfColoring
/-
**SimpleGraph.two_le_chromaticNumber_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：two_le_chromaticNumber_of_adj {u v : V} (hadj : G.Adj u v) : 2 <= G.chroma
ticNumber
参数：hadj : G.Adj u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用定理 `Order.le_of_lt_add_one`：le_of_lt_add_one (h : x < y + 1) : x <= y
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
-/
theorem two_le_chromaticNumber_of_adj {u v : V} (hadj : G.Adj u v) : 2 ≤ G.chromaticNumber := by
  refine le_of_not_gt fun h ↦ ?_
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  exact c.valid hadj (Subsingleton.elim (c u) (c v))

@[simp]
/-
**SimpleGraph.chromaticNumber_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：chromaticNumber_eq_zero_iff : G.chromaticNumber = 0 ↔ IsEmpty V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用引理 `SimpleGraph.colorable_zero_iff`：colorable_zero_iff : G.Colorable 0 ↔ IsE
mpty V
-/
theorem chromaticNumber_eq_zero_iff : G.chromaticNumber = 0 ↔ IsEmpty V :=
  nonpos_iff_eq_zero.symm.trans <| chromaticNumber_le_iff_colorable.trans colorable_zero_iff

@[simp]
/-
**SimpleGraph.chromaticNumber_eq_zero_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：chromaticNumber_eq_zero_of_isEmpty [IsEmpty V] : G.chromaticNumber = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem chromaticNumber_eq_zero_of_isEmpty [IsEmpty V] : G.chromaticNumber = 0 := by
  simpa

@[deprecated (since := "2026-04-24")]
alias ⟨isEmpty_of_chromaticNumber_eq_zero, _⟩ := chromaticNumber_eq_zero_iff
/-
**SimpleGraph.chromaticNumber_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：chromaticNumber_eq_one_iff : G.chromaticNumber = 1 ↔ G = ⊥ ∧ Nonempty V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `Order.lt_one_iff_nonpos`：lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEO
neClass α] [NeZero (1 : α)] [SuccAddOrder α] : x < 1 ↔ x <= 0
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `SimpleGraph.chromaticNumber_le_iff_colorable`：chromaticNumber_le_iff_col
orable {n : Nat} : G.chromaticNumber <= n ↔ G.Colorable n
· 使用定理 `SimpleGraph.colorable_one_iff`：colorable_one_iff : G.Colorable 1 ↔ G = ⊥
· 使用引理 `SimpleGraph.colorable_zero_iff`：colorable_zero_iff : G.Colorable 0 ↔ IsE
mpty V
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem chromaticNumber_eq_one_iff : G.chromaticNumber = 1 ↔ G = ⊥ ∧ Nonempty V := by
  rw [eq_iff_le_not_lt, Order.lt_one_iff_nonpos, ← not_isEmpty_iff, ← Nat.cast_one, ← Nat.cast_zero,
    chromaticNumber_le_iff_colorable, chromaticNumber_le_iff_colorable, colorable_one_iff,
    colorable_zero_iff]
/-
**SimpleGraph.two_le_chromaticNumber_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：two_le_chromaticNumber_iff_ne_bot : 2 <= G.chromaticNumber ↔ G != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber_eq_zero_of_isEmpty`：chromaticNumber_eq_zero_
of_isEmpty [IsEmpty V] : G.chromaticNumber = 0
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.chromaticNumber_eq_one_iff`：chromaticNumber_eq_one_iff : G.c
hromaticNumber = 1 ↔ G = ⊥ ∧ Nonempty V
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.ne_bot_iff_exists_adj`：ne_bot_iff_exists_adj : G != ⊥ ↔ exis
ts a b : V, G.Adj a b
· 使用定理 `SimpleGraph.two_le_chromaticNumber_of_adj`：two_le_chromaticNumber_of_adj
 {u v : V} (hadj : G.Adj u v) : 2 <= G.chromaticNumber
-/
theorem two_le_chromaticNumber_iff_ne_bot : 2 ≤ G.chromaticNumber ↔ G ≠ ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    by_cases h' : IsEmpty V
    · simp [chromaticNumber_eq_zero_of_isEmpty]
    · simp [chromaticNumber_eq_one_iff.mpr ⟨h, by simpa using h'⟩]
  · obtain ⟨_, _, h⟩ := ne_bot_iff_exists_adj.mp h
    exact two_le_chromaticNumber_of_adj h

/-- The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right. -/
/-
**SimpleGraph.CompleteBipartiteGraph.bicoloring** 是 Mathlib 中的一个定义，位于命名空间 `Simpl
eGraph.CompleteBipartiteGraph`。
形式化陈述：(V : Type u_4) → (W : Type u_5) → (completeBipartiteGraph V W).Coloring Bo
ol
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right.
-/
def CompleteBipartiteGraph.bicoloring (V W : Type*) : (completeBipartiteGraph V W).Coloring Bool :=
  Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp)
/-
**SimpleGraph.CompleteBipartiteGraph.chromaticNumber** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.CompleteBipartiteGraph`。
形式化陈述：∀ {V : Type u_4} {W : Type u_5} [Nonempty V] [Nonempty W], (completeBipart
iteGraph V W).chromaticNumber = 2
参数：completeBipartiteGraph V W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用引理 `SimpleGraph.chromaticNumber_eq_iff_forall_surjective`：chromaticNumber_eq
_iff_forall_surjective (hG : G.Colorable n) : G.chromaticNumber = n ↔ forall C :
 G.Coloring (Fin n), Surjective C
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `completeBipartiteGraph_adj`：∀ (V : Type u_1) (W : Type u_2) (v w : V ⊕ W
),   (completeBipartiteGraph V W).Adj v w = (v.isLeft = true ∧ w.isRight = true 
∨ v.isRight = tr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.two_lt_card_iff`：∀ {α : Type u_1} [inst : Fintype α], 2 < Fintyp
e.card α ↔ ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
-/
theorem CompleteBipartiteGraph.chromaticNumber {V W : Type*} [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 := by
  rw [← Nat.cast_two, chromaticNumber_eq_iff_forall_surjective
    (by simpa using (CompleteBipartiteGraph.bicoloring V W).colorable)]
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
  by_cases he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
  by_cases he' : C (Sum.inr w) = b
  · exact ⟨_, he'⟩
  · simpa using two_lt_card_iff.2 ⟨_, _, _, C.valid h, he, he'⟩

/-! ### Cliques -/

/-
**SimpleGraph.IsClique.card_le_of_colorable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.IsClique`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} {s : Finset V}, G.IsClique ↑s →
 G.Colorable n → s.card ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `SimpleGraph.Colorable.card_le_of_pairwise_adj`：∀ {V : Type u} {G : Simpl
eGraph V} {n : ℕ} {ι : Type u_1},   G.Colorable n → ∀ (f : ι → V), (Pairwise fun
 i j => G.Adj (f i) (f j)) → Nat.ca…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…

--- 原说明 ---
### Cliques
-/
theorem IsClique.card_le_of_colorable {s : Finset V} (h : G.IsClique s) (hc : G.Colorable n) :
    s.card ≤ n := by
  simpa using! hc.card_le_of_pairwise_adj (Subtype.val : s → V) <| by simpa [Pairwise] using! h
/-
**SimpleGraph.IsClique.card_le_of_coloring** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsClique`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} {s : Finset V},   G.IsCl
ique ↑s → ∀ [inst : Fintype α] (C : G.Coloring α), s.card ≤ Fintype.card α
参数：C : G.Coloring α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsClique.card_le_of_colorable`：∀ {V : Type u} {G : SimpleGra
ph V} {n : ℕ} {s : Finset V}, G.IsClique ↑s → G.Colorable n → s.card ≤ n
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
-/
theorem IsClique.card_le_of_coloring {s : Finset V} (h : G.IsClique s) [Fintype α]
    (C : G.Coloring α) : s.card ≤ Fintype.card α := h.card_le_of_colorable C.colorable
/-
**SimpleGraph.IsClique.card_le_chromaticNumber** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.IsClique`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {s : Finset V}, G.IsClique ↑s → ↑s.card
 ≤ G.chromaticNumber
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.le_chromaticNumber_of_pairwise_adj`：le_chromaticNumber_of_pa
irwise_adj (hn : n <= Nat.card ι) (f : ι -> V) (hf : Pairwise fun i j => G.Adj (
f i) (f j)) : n <= G.chromaticNumber
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem IsClique.card_le_chromaticNumber {s : Finset V} (h : G.IsClique s) :
    s.card ≤ G.chromaticNumber :=
  le_chromaticNumber_of_pairwise_adj (by simp) (Subtype.val : s → V) <| by simpa [Pairwise] using! h
/-
**SimpleGraph.cliqueNum_le_chromaticNumber** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：cliqueNum_le_chromaticNumber : G.cliqueNum <= G.chromaticNumber
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isNClique_cliqueNum`：exists_isNClique_cliqueNum : exi
sts s, G.IsNClique G.cliqueNum s
· 使用定理 `SimpleGraph.IsClique.card_le_chromaticNumber`：∀ {V : Type u} {G : Simple
Graph V} {s : Finset V}, G.IsClique ↑s → ↑s.card ≤ G.chromaticNumber
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
theorem cliqueNum_le_chromaticNumber : G.cliqueNum ≤ G.chromaticNumber := by
  have ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  exact hs.card_eq ▸ hs.isClique.card_le_chromaticNumber
/-
**SimpleGraph.Colorable.cliqueFree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Colora
ble`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {n m : ℕ}, G.Colorable n → n < m → G.Cl
iqueFree m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.lt_le_asymm`：∀ {a b : ℕ}, a < b → ¬b ≤ a
· 使用定理 `SimpleGraph.IsClique.card_le_of_colorable`：∀ {V : Type u} {G : SimpleGra
ph V} {n : ℕ} {s : Finset V}, G.IsClique ↑s → G.Colorable n → s.card ≤ n
-/
protected theorem Colorable.cliqueFree {n m : ℕ} (hc : G.Colorable n) (hm : n < m) :
    G.CliqueFree m := by
  by_contra h
  simp only [CliqueFree, isNClique_iff, not_forall, Classical.not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_asymm hm (h.card_le_of_colorable hc)
/-
**SimpleGraph.cliqueFree_of_chromaticNumber_lt** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：cliqueFree_of_chromaticNumber_lt {n : Nat} (hc : G.chromaticNumber < n) : 
G.CliqueFree n
参数：hc : G.chromaticNumber < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.chromaticNumber_ne_top_iff_exists`：chromaticNumber_ne_top_if
f_exists : G.chromaticNumber != ⊤ ↔ exists n, G.Colorable n
· 使用定理 `SimpleGraph.colorable_chromaticNumber`：colorable_chromaticNumber {m : Na
t} (hc : G.Colorable m) : G.Colorable (ENat.toNat G.chromaticNumber)
· 使用定理 `SimpleGraph.Colorable.cliqueFree`：∀ {V : Type u} {G : SimpleGraph V} {n 
m : ℕ}, G.Colorable n → n < m → G.CliqueFree m
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_toNat_eq_self`：natCast_toNat_eq_self : ENat.toNat n = n ↔ n
 != ⊤
-/
theorem cliqueFree_of_chromaticNumber_lt {n : ℕ} (hc : G.chromaticNumber < n) :
    G.CliqueFree n := by
  have hne : G.chromaticNumber ≠ ⊤ := hc.ne_top
  obtain ⟨m, hc'⟩ := chromaticNumber_ne_top_iff_exists.mp hne
  have := colorable_chromaticNumber hc'
  refine this.cliqueFree ?_
  rw [← ENat.natCast_toNat_eq_self] at hne
  rw [← hne] at hc
  simpa using hc

/--
Given a coloring `α` of `G`, and a clique of size at least the number of colors, the clique
contains a vertex of each color.
-/
/-
**SimpleGraph.Coloring.surjOn_of_card_le_isClique** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Coloring`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {α : Type u_2} [inst : Fintype α] {s : 
Finset V},   G.IsClique ↑s → Fintype.card α ≤ s.card → ∀ (C : G.Coloring α), Set
.SurjOn (⇑C) (↑s) Set.univ
参数：C : G.Coloring α；⇑C；↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.card_le_chromaticNumber_iff_forall_surjective`：card_le_chrom
aticNumber_iff_forall_surjective [Fintype α] : card α <= G.chromaticNumber ↔ for
all C : G.Coloring α, Surjective C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.chromaticNumber_top`：chromaticNumber_top [Fintype V] : (⊤ : 
SimpleGraph V).chromaticNumber = Fintype.card V
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S

--- 原说明 ---
Given a coloring `α` of `G`, and a clique of size at least the number of colors,
 the clique
contains a vertex of each color.
-/
lemma Coloring.surjOn_of_card_le_isClique [Fintype α] {s : Finset V} (h : G.IsClique s)
    (hc : Fintype.card α ≤ s.card) (C : G.Coloring α) : Set.SurjOn C s Set.univ := by
  intro _ _
  obtain ⟨_, hx⟩ := card_le_chromaticNumber_iff_forall_surjective.mp
                    (by simp_all [← induce_eq_top]) (C.comp (Embedding.induce s).toHom) _
  exact ⟨_, Subtype.coe_prop _, hx⟩

namespace completeMultipartiteGraph

variable {ι : Type*} (V : ι → Type*)

/-- The canonical `ι`-coloring of a `completeMultipartiteGraph` with parts indexed by `ι` -/
/-
**SimpleGraph.completeMultipartiteGraph.coloring** 是 Mathlib 中的一个定义，位于命名空间 `Simp
leGraph.completeMultipartiteGraph`。
形式化陈述：coloring : (completeMultipartiteGraph V).Coloring ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `ι`-coloring of a `completeMultipartiteGraph` with parts indexed b
y `ι`
-/
def coloring : (completeMultipartiteGraph V).Coloring ι := Coloring.mk (fun v ↦ v.1) (by simp)
/-
**SimpleGraph.completeMultipartiteGraph.colorable** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph.completeMultipartiteGraph`。
形式化陈述：colorable [Fintype ι] : (completeMultipartiteGraph V).Colorable (Fintype.c
ard ι)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
-/
lemma colorable [Fintype ι] : (completeMultipartiteGraph V).Colorable (Fintype.card ι) :=
  (coloring V).colorable
/-
**SimpleGraph.completeMultipartiteGraph.chromaticNumber** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.completeMultipartiteGraph`。
形式化陈述：chromaticNumber [Fintype ι] (f : forall (i : ι), V i) : (completeMultipart
iteGraph V).chromaticNumber = Fintype.card ι
参数：f : forall (i : ι), V i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.Colorable.chromaticNumber_le`：∀ {V : Type u} {G : SimpleGrap
h V} {n : ℕ}, G.Colorable n → G.chromaticNumber ≤ ↑n
· 使用引理 `SimpleGraph.completeMultipartiteGraph.colorable`：colorable [Fintype ι] :
 (completeMultipartiteGraph V).Colorable (Fintype.card ι)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_le_card`：not_cli
queFree_of_le_card [Fintype ι] (f : forall (i : ι), V i) (hc : n <= card ι) : ¬ 
(completeMultipartiteGraph V).CliqueFree n
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `SimpleGraph.cliqueFree_of_chromaticNumber_lt`：cliqueFree_of_chromaticNum
ber_lt {n : Nat} (hc : G.chromaticNumber < n) : G.CliqueFree n
-/
theorem chromaticNumber [Fintype ι] (f : ∀ (i : ι), V i) :
    (completeMultipartiteGraph V).chromaticNumber = Fintype.card ι := by
  apply le_antisymm (colorable V).chromaticNumber_le
  by_contra! h
  exact not_cliqueFree_of_le_card V f le_rfl <| cliqueFree_of_chromaticNumber_lt h
/-
**SimpleGraph.completeMultipartiteGraph.colorable_of_cliqueFree** 是 Mathlib 中的一个
定理，位于命名空间 `SimpleGraph.completeMultipartiteGraph`。
形式化陈述：colorable_of_cliqueFree (f : forall (i : ι), V i) (hc : (completeMultipart
iteGraph V).CliqueFree n) : (completeMultipartiteGraph V).Colorable (n - 1)
参数：f : forall (i : ι), V i；hc : (completeMultipartiteGraph V).CliqueFree n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.not_cliqueFree_zero`：∀ {α : Type u_1} {G : SimpleGraph α}, ¬
G.CliqueFree 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_infinite`：not_cl
iqueFree_of_infinite [Infinite ι] (f : forall (i : ι), V i) : ¬ (completeMultipa
rtiteGraph V).CliqueFree n
· 使用定理 `SimpleGraph.Colorable.mono`：∀ {V : Type u} {G : SimpleGraph V} {n m : ℕ}
, n ≤ m → G.Colorable n → G.Colorable m
· 使用定理 `SimpleGraph.Coloring.colorable`：∀ {V : Type u} {G : SimpleGraph V} {α : 
Type u_2} [inst : Fintype α] (C : G.Coloring α), G.Colorable (Fintype.card α)
· 使用定理 `SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_le_card`：not_cli
queFree_of_le_card [Fintype ι] (f : forall (i : ι), V i) (hc : n <= card ι) : ¬ 
(completeMultipartiteGraph V).CliqueFree n
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.CliqueFree.mono`：∀ {α : Type u_1} {G : SimpleGraph α} {m n :
 ℕ}, m ≤ n → G.CliqueFree m → G.CliqueFree n
-/
theorem colorable_of_cliqueFree (f : ∀ (i : ι), V i)
    (hc : (completeMultipartiteGraph V).CliqueFree n) :
    (completeMultipartiteGraph V).Colorable (n - 1) := by
  cases n with
  | zero => exact absurd hc not_cliqueFree_zero
  | succ n =>
  have : Fintype ι := fintypeOfNotInfinite
    fun hinf ↦ not_cliqueFree_of_infinite V f hc
  apply (coloring V).colorable.mono
  have := not_cliqueFree_of_le_card V f le_rfl
  contrapose! this
  exact hc.mono this

end completeMultipartiteGraph

variable {W : Type*} {H : SimpleGraph W}

/-- If `H` is not `n`-colorable and `G` is `n`-colorable, then `G` is `H.Free`. -/
/-
**SimpleGraph.free_of_colorable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：free_of_colorable (nhc : ¬H.Colorable n) (hc : G.Colorable n) : H.Free G
参数：nhc : ¬H.Colorable n；hc : G.Colorable n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `SimpleGraph.Colorable.of_hom`：∀ {V : Type u} {G : SimpleGraph V} {V' : T
ype u_4} {G' : SimpleGraph V'} {n : ℕ} (f : G →g G'),   G'.Colorable n → G.Color
able n

--- 原说明 ---
If `H` is not `n`-colorable and `G` is `n`-colorable, then `G` is `H.Free`.
-/
theorem free_of_colorable (nhc : ¬H.Colorable n) (hc : G.Colorable n) : H.Free G := by
  contrapose! nhc with hc'
  exact hc.of_hom hc'.some.toHom

/-! ### Isomorphisms -/

/-- Equivalence of colorings induced by isomorphisms of graphs and equivalence of colors. -/
/-
**SimpleGraph.coloringCongr** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：coloringCongr (f : G ≃g H) (g : α ≃ β) : G.Coloring α ≃ H.Coloring β
参数：f : G ≃g H；g : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence of colorings induced by isomorphisms of graphs and equivalence of co
lors.
-/
def coloringCongr (f : G ≃g H) (g : α ≃ β) : G.Coloring α ≃ H.Coloring β :=
  f.homCongr (Iso.completeGraph g)
/-
**SimpleGraph.colorable_congr** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：colorable_congr (f : G ≃g H) : G.Colorable n ↔ H.Colorable n
参数：f : G ≃g H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Colorable.of_hom`：∀ {V : Type u} {G : SimpleGraph V} {V' : T
ype u_4} {G' : SimpleGraph V'} {n : ℕ} (f : G →g G'),   G'.Colorable n → G.Color
able n
-/
lemma colorable_congr (f : G ≃g H) : G.Colorable n ↔ H.Colorable n :=
  ⟨fun hc ↦ hc.of_hom f.symm.toHom, fun hc ↦ hc.of_hom f.toHom⟩
/-
**SimpleGraph.chromaticNumber_congr** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：chromaticNumber_congr (f : G ≃g H) : G.chromaticNumber = H.chromaticNumber
参数：f : G ≃g H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.chromaticNumber_mono_of_hom`：chromaticNumber_mono_of_hom {V'
 : Type*} {G' : SimpleGraph V'} (f : G ->g G') : G.chromaticNumber <= G'.chromat
icNumber
-/
lemma chromaticNumber_congr (f : G ≃g H) : G.chromaticNumber = H.chromaticNumber :=
  le_antisymm (chromaticNumber_mono_of_hom f.toHom) (chromaticNumber_mono_of_hom f.symm.toHom)

end SimpleGraph

