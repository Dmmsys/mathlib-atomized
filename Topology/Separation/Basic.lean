/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Separation.SeparatedNhds
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Bases
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Separation properties of topological spaces

This file defines some of the weaker separation axioms (under the Kolmogorov classification),
notably T₀, R₀, T₁ and R₁ spaces. For T₂ (Hausdorff) spaces and other stronger
conditions, see the file `Mathlib/Topology/Separation/Hausdorff.lean`.

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `HasSeparatingCover`: A set has a countable cover that can be used with
  `hasSeparatingCovers_iff_separatedNhds` to witness when two `Set`s have `SeparatedNhds`.
* `T0Space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `R0Space`: An R₀ space (sometimes called a *symmetric space*) is a topological space
  such that the `Specializes` relation is symmetric.
* `T1Space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1Space_iff_exists_open` shows that these conditions are equivalent.)
  T₁ iff T₀ and R₀.
* `R1Space`: An R₁/preregular space is a space where any two topologically distinguishable points
  have disjoint neighbourhoods. R₁ implies R₀.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### T₀ spaces

* `IsClosed.exists_closed_singleton`: Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_isOpen_singleton_of_isOpen_finite`: Given an open finite set `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `isClosedMap_const`: The constant map is a closed map.
* `Finite.instDiscreteTopology`: A finite T₁ space must have the discrete topology.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]
-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- A T₀ space, also known as a Kolmogorov space, is a topological space such that for every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the definition in terms
of the `Inseparable` relation. -/
@[stacks 004X "(2)"]
/-
**T0Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₀ space, also known as a Kolmogorov space, is a topological space such that f
or every pair
`x ≠ y`, there is an open set containing one but not the other. We formulate the
 definition in terms
of the `Inseparable` relation.
-/
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two inseparable points in a T₀ space are equal. -/
  t0 : ∀ ⦃x y : X⦄, Inseparable x y → x = y
/-
**t0Space_iff_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_inseparable (X : Type u) [TopologicalSpace X] : T0Space X ↔ fo
rall x y : X, Inseparable x y -> x = y
参数：X : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem t0Space_iff_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ ∀ x y : X, Inseparable x y → x = y :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
/-
**t0Space_iff_not_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_not_inseparable (X : Type u) [TopologicalSpace X] : T0Space X 
↔ Pairwise fun x y : X => ¬Inseparable x y
参数：X : Type u。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t0Space_iff_not_inseparable (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y : X => ¬Inseparable x y := by
  simp only [t0Space_iff_inseparable, Ne, not_imp_not, Pairwise]
/-
**Inseparable.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x y) : x = y
参数：h : Inseparable x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T0Space.t0`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T0Space X
] ⦃x y : X⦄, Inseparable x y → x = y
-/
theorem Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x y) : x = y :=
  T0Space.t0 h

/-- A topology inducing map from a T₀ space is injective. -/
/-
**Topology.IsInducing.injective** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T0Space X] {f : X → Y},   Topology.IsInducing f → Function.Inje
ctive f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.inseparable_iff`：Topology.IsInducing.inseparable_iff
 (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y)
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y

--- 原说明 ---
A topology inducing map from a T₀ space is injective.
-/
protected theorem Topology.IsInducing.injective [TopologicalSpace Y] [T0Space X] {f : X → Y}
    (hf : IsInducing f) : Injective f := fun _ _ h =>
  (hf.inseparable_iff.1 <| .of_eq h).eq

/-- A topology inducing map from a T₀ space is a topological embedding. -/
/-
**Topology.IsInducing.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing
`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T0Space X] {f : X → Y},   Topology.IsInducing f → Topology.IsEm
bedding f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space X] {f : X → Y},   Topo
logy.IsInducing f →…

--- 原说明 ---
A topology inducing map from a T₀ space is a topological embedding.
-/
protected theorem Topology.IsInducing.isEmbedding [TopologicalSpace Y] [T0Space X] {f : X → Y}
    (hf : IsInducing f) : IsEmbedding f :=
  ⟨hf, hf.injective⟩
/-
**isEmbedding_iff_isInducing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isEmbedding_iff_isInducing [TopologicalSpace Y] [T0Space X] {f : X -> Y} :
 IsEmbedding f ↔ IsInducing f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Topology.IsInducing.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space X] {f : X → Y},   To
pology.IsInducing f →…
-/
lemma isEmbedding_iff_isInducing [TopologicalSpace Y] [T0Space X] {f : X → Y} :
    IsEmbedding f ↔ IsInducing f :=
  ⟨IsEmbedding.isInducing, IsInducing.isEmbedding⟩
/-
**t0Space_iff_nhds_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_nhds_injective (X : Type u) [TopologicalSpace X] : T0Space X ↔
 Injective (𝓝 : X -> Filter X)
参数：X : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t0Space_iff_inseparable`：t0Space_iff_inseparable (X : Type u) [Topologic
alSpace X] : T0Space X ↔ forall x y : X, Inseparable x y -> x = y
-/
theorem t0Space_iff_nhds_injective (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Injective (𝓝 : X → Filter X) :=
  t0Space_iff_inseparable X
/-
**nhds_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_injective [T0Space X] : Injective (𝓝 : X -> Filter X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t0Space_iff_nhds_injective`：t0Space_iff_nhds_injective (X : Type u) [Top
ologicalSpace X] : T0Space X ↔ Injective (𝓝 : X -> Filter X)
-/
theorem nhds_injective [T0Space X] : Injective (𝓝 : X → Filter X) :=
  (t0Space_iff_nhds_injective X).1 ‹_›
/-
**inseparable_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_iff_eq [T0Space X] {x y : X} : Inseparable x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `nhds_injective`：nhds_injective [T0Space X] : Injective (𝓝 : X -> Filter 
X)
-/
theorem inseparable_iff_eq [T0Space X] {x y : X} : Inseparable x y ↔ x = y :=
  nhds_injective.eq_iff

@[simp]
/-
**nhds_eq_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_eq_nhds_iff [T0Space X] {a b : X} : 𝓝 a = 𝓝 b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `nhds_injective`：nhds_injective [T0Space X] : Injective (𝓝 : X -> Filter 
X)
-/
theorem nhds_eq_nhds_iff [T0Space X] {a b : X} : 𝓝 a = 𝓝 b ↔ a = b :=
  nhds_injective.eq_iff

@[simp]
/-
**inseparable_eq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inseparable_eq_eq [T0Space X] : Inseparable = @Eq X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `inseparable_iff_eq`：inseparable_iff_eq [T0Space X] {x y : X} : Inseparab
le x y ↔ x = y
-/
theorem inseparable_eq_eq [T0Space X] : Inseparable = @Eq X :=
  funext₂ fun _ _ => propext inseparable_iff_eq
/-
**TopologicalSpace.IsTopologicalBasis.inseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：TopologicalSpace.IsTopologicalBasis.inseparable_iff {b : Set (Set X)} (hb 
: IsTopologicalBasis b) {x y : X} : Inseparable x y ↔ forall s in b, (x in s ↔ y
 in s)
参数：Set X；hb : IsTopologicalBasis b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inseparable_iff_forall_isOpen`：inseparable_iff_forall_isOpen : (x ~ᵢ y) 
↔ forall s : Set X, IsOpen s -> (x in s ↔ y in s)
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `TopologicalSpace.IsTopologicalBasis.nhds_hasBasis`：∀ {α : Type u} [t : T
opologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis b → 
∀ {a : α}, (nhds a).HasBasis (fun t => …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
-/
theorem TopologicalSpace.IsTopologicalBasis.inseparable_iff {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : Inseparable x y ↔ ∀ s ∈ b, (x ∈ s ↔ y ∈ s) :=
  ⟨fun h _ hs ↦ inseparable_iff_forall_isOpen.1 h _ (hb.isOpen hs),
    fun h ↦ hb.nhds_hasBasis.eq_of_same_basis <| by
      convert! hb.nhds_hasBasis using 2
      exact and_congr_right (h _)⟩
/-
**TopologicalSpace.IsTopologicalBasis.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TopologicalSpace.IsTopologicalBasis.eq_iff [T0Space X] {b : Set (Set X)} (
hb : IsTopologicalBasis b) {x y : X} : x = y ↔ forall s in b, (x in s ↔ y in s)
参数：Set X；hb : IsTopologicalBasis b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `inseparable_iff_eq`：inseparable_iff_eq [T0Space X] {x y : X} : Inseparab
le x y ↔ x = y
· 使用定理 `TopologicalSpace.IsTopologicalBasis.inseparable_iff`：TopologicalSpace.Is
TopologicalBasis.inseparable_iff {b : Set (Set X)} (hb : IsTopologicalBasis b) {
x y : X} : Inseparable x y ↔ forall s in …
-/
theorem TopologicalSpace.IsTopologicalBasis.eq_iff [T0Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} : x = y ↔ ∀ s ∈ b, (x ∈ s ↔ y ∈ s) :=
  inseparable_iff_eq.symm.trans hb.inseparable_iff
/-
**t0Space_iff_exists_isOpen_xor_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_exists_isOpen_xor_mem (X : Type u) [TopologicalSpace X] : T0Sp
ace X ↔ Pairwise fun x y => exists U : Set X, IsOpen U ∧ Xor (x in U) (y in U)
参数：X : Type u。
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t0Space_iff_exists_isOpen_xor_mem (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun x y => ∃ U : Set X, IsOpen U ∧ Xor (x ∈ U) (y ∈ U) := by
  simp only [t0Space_iff_not_inseparable, xor_iff_not_iff, not_forall, exists_prop,
    inseparable_iff_forall_isOpen, Pairwise]

@[deprecated (since := "2026-04-04")]
alias t0Space_iff_exists_isOpen_xor'_mem := t0Space_iff_exists_isOpen_xor_mem
/-
**exists_isOpen_xor_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isOpen_xor_mem [T0Space X] {x y : X} (h : x != y) : exists U : Set 
X, IsOpen U ∧ Xor (x in U) (y in U)
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t0Space_iff_exists_isOpen_xor_mem`：t0Space_iff_exists_isOpen_xor_mem (X 
: Type u) [TopologicalSpace X] : T0Space X ↔ Pairwise fun x y => exists U : Set 
X, IsOpen U ∧ Xor (x in…
-/
theorem exists_isOpen_xor_mem [T0Space X] {x y : X} (h : x ≠ y) :
    ∃ U : Set X, IsOpen U ∧ Xor (x ∈ U) (y ∈ U) :=
  (t0Space_iff_exists_isOpen_xor_mem X).1 ‹_› h

@[deprecated (since := "2026-04-04")] alias exists_isOpen_xor'_mem := exists_isOpen_xor_mem

/-- Specialization forms a partial order on a t0 topological space. -/
@[instance_reducible]
/-
**specializationOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：specializationOrder (X) [TopologicalSpace X] [T0Space X] : PartialOrder X
参数：X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_injective`：nhds_injective [T0Space X] : Injective (𝓝 : X -> Filter 
X)
· 使用定理 `PartialOrder.le_antisymm`：∀ {α : Type u_2} [self : PartialOrder α] (a b 
: α), a ≤ b → b ≤ a → a = b

--- 原说明 ---
Specialization forms a partial order on a t0 topological space.
-/
def specializationOrder (X) [TopologicalSpace X] [T0Space X] : PartialOrder X :=
  { specializationPreorder X, PartialOrder.lift (OrderDual.toDual ∘ 𝓝) nhds_injective with }
/-
**SeparationQuotient.instT0Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.instT0Space : T0Space (SeparationQuotient X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.inseparable_iff`：Topology.IsInducing.inseparable_iff
 (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y)
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
-/
instance SeparationQuotient.instT0Space : T0Space (SeparationQuotient X) :=
  ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ h =>
    SeparationQuotient.mk_eq_mk.2 <| SeparationQuotient.isInducing_mk.inseparable_iff.1 h⟩
/-
**minimal_nonempty_closed_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_nonempty_closed_subsingleton [T0Space X] {s : Set X} (hs : IsClose
d s) (hmin : forall t, t subseteq s -> t.Nonempty -> IsClosed t -> t = s) : s.Su
bsingleton
参数：hs : IsClosed s；hmin : forall t, t subseteq s -> t.Nonempty -> IsClosed t -> 
t = s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `exists_isOpen_xor_mem`：exists_isOpen_xor_mem [T0Space X] {x y : X} (h : 
x != y) : exists U : Set X, IsOpen U ∧ Xor (x in U) (y in U)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `IsClosed.sdiff`：IsClosed.sdiff (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClo
sed (s \ t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
theorem minimal_nonempty_closed_subsingleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hmin : ∀ t, t ⊆ s → t.Nonempty → IsClosed t → t = s) : s.Subsingleton := by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x ∈ U ∧ y ∉ U
  · refine this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s \ U = s := hmin (s \ U) sdiff_subset ⟨y, hy, hyU⟩ (hs.sdiff hUo)
  exact (this.symm.subset hx).2 hxU
/-
**minimal_nonempty_closed_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_nonempty_closed_eq_singleton [T0Space X] {s : Set X} (hs : IsClose
d s) (hne : s.Nonempty) (hmin : forall t, t subseteq s -> t.Nonempty -> IsClosed
 t -> t = s) : exists x, s = {x}
参数：hs : IsClosed s；hne : s.Nonempty；hmin : forall t, t subseteq s -> t.Nonempty 
-> IsClosed t -> t = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_eq_singleton_iff_nonempty_subsingleton`：exists_eq_singleton_i
ff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton
· 使用定理 `minimal_nonempty_closed_subsingleton`：minimal_nonempty_closed_subsinglet
on [T0Space X] {s : Set X} (hs : IsClosed s) (hmin : forall t, t subseteq s -> t
.Nonempty -> IsClosed t ->…
-/
theorem minimal_nonempty_closed_eq_singleton [T0Space X] {s : Set X} (hs : IsClosed s)
    (hne : s.Nonempty) (hmin : ∀ t, t ⊆ s → t.Nonempty → IsClosed t → t = s) : ∃ x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2
    ⟨hne, minimal_nonempty_closed_subsingleton hs hmin⟩

/-- Given a closed set `S` in a compact T₀ space, there is some `x ∈ S` such that `{x}` is
closed. -/
/-
**IsClosed.exists_closed_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.exists_closed_singleton [T0Space X] [CompactSpace X] {S : Set X} 
(hS : IsClosed S) (hne : S.Nonempty) : exists x : X, x in S ∧ IsClosed ({x} : Se
t X)
参数：hS : IsClosed S；hne : S.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.exists_minimal_nonempty_closed_subset`：IsClosed.exists_minimal_
nonempty_closed_subset [CompactSpace X] {S : Set X} (hS : IsClosed S) (hne : S.N
onempty) : exists V : Set X, V subse…
· 使用定理 `minimal_nonempty_closed_eq_singleton`：minimal_nonempty_closed_eq_singlet
on [T0Space X] {s : Set X} (hs : IsClosed s) (hne : s.Nonempty) (hmin : forall t
, t subseteq s -> t.Nonemp…
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a closed set `S` in a compact T₀ space, there is some `x ∈ S` such that `{
x}` is
closed.
-/
theorem IsClosed.exists_closed_singleton [T0Space X] [CompactSpace X] {S : Set X}
    (hS : IsClosed S) (hne : S.Nonempty) : ∃ x : X, x ∈ S ∧ IsClosed ({x} : Set X) := by
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne
  rcases minimal_nonempty_closed_eq_singleton Vcls Vne hV with ⟨x, rfl⟩
  exact ⟨x, Vsub (mem_singleton x), Vcls⟩
/-
**minimal_nonempty_open_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_nonempty_open_subsingleton [T0Space X] {s : Set X} (hs : IsOpen s)
 (hmin : forall t, t subseteq s -> t.Nonempty -> IsOpen t -> t = s) : s.Subsingl
eton
参数：hs : IsOpen s；hmin : forall t, t subseteq s -> t.Nonempty -> IsOpen t -> t = 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `exists_isOpen_xor_mem`：exists_isOpen_xor_mem [T0Space X] {x y : X} (h : 
x != y) : exists U : Set X, IsOpen U ∧ Xor (x in U) (y in U)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
theorem minimal_nonempty_open_subsingleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hmin : ∀ t, t ⊆ s → t.Nonempty → IsOpen t → t = s) : s.Subsingleton := by
  refine fun x hx y hy => of_not_not fun hxy => ?_
  rcases exists_isOpen_xor_mem hxy with ⟨U, hUo, hU⟩
  wlog h : x ∈ U ∧ y ∉ U
  · exact this hs hmin y hy x hx (Ne.symm hxy) U hUo hU.symm (hU.resolve_left h)
  obtain ⟨hxU, hyU⟩ := h
  have : s ∩ U = s := hmin (s ∩ U) inter_subset_left ⟨x, hx, hxU⟩ (hs.inter hUo)
  exact hyU (this.symm.subset hy).2
/-
**minimal_nonempty_open_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：minimal_nonempty_open_eq_singleton [T0Space X] {s : Set X} (hs : IsOpen s)
 (hne : s.Nonempty) (hmin : forall t, t subseteq s -> t.Nonempty -> IsOpen t -> 
t = s) : exists x, s = {x}
参数：hs : IsOpen s；hne : s.Nonempty；hmin : forall t, t subseteq s -> t.Nonempty ->
 IsOpen t -> t = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_eq_singleton_iff_nonempty_subsingleton`：exists_eq_singleton_i
ff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton
· 使用定理 `minimal_nonempty_open_subsingleton`：minimal_nonempty_open_subsingleton [
T0Space X] {s : Set X} (hs : IsOpen s) (hmin : forall t, t subseteq s -> t.Nonem
pty -> IsOpen t -> t = s…
-/
theorem minimal_nonempty_open_eq_singleton [T0Space X] {s : Set X} (hs : IsOpen s)
    (hne : s.Nonempty) (hmin : ∀ t, t ⊆ s → t.Nonempty → IsOpen t → t = s) : ∃ x, s = {x} :=
  exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hne, minimal_nonempty_open_subsingleton hs hmin⟩

/-- Given an open finite set `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
/-
**exists_isOpen_singleton_of_isOpen_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isOpen_singleton_of_isOpen_finite [T0Space X] {s : Set X} (hfin : s
.Finite) (hne : s.Nonempty) (ho : IsOpen s) : exists x in s, IsOpen ({x} : Set X
)
参数：hfin : s.Finite；hne : s.Nonempty；ho : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `minimal_nonempty_open_eq_singleton`：minimal_nonempty_open_eq_singleton [
T0Space X] {s : Set X} (hs : IsOpen s) (hne : s.Nonempty) (hmin : forall t, t su
bseteq s -> t.Nonempty -…
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ssubset_iff_subset_ne`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [ins
t : PartialOrder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ a ≠ b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given an open finite set `S` in a T₀ space, there is some `x ∈ S` such that `{x}
` is open.
-/
theorem exists_isOpen_singleton_of_isOpen_finite [T0Space X] {s : Set X} (hfin : s.Finite)
    (hne : s.Nonempty) (ho : IsOpen s) : ∃ x ∈ s, IsOpen ({x} : Set X) := by
  lift s to Finset X using hfin
  induction s using Finset.strongInductionOn
  rename_i s ihs
  rcases em (∃ t, t ⊂ s ∧ t.Nonempty ∧ IsOpen (t : Set X)) with (⟨t, hts, htne, hto⟩ | ht)
  · rcases ihs t hts htne hto with ⟨x, hxt, hxo⟩
    exact ⟨x, hts.1 hxt, hxo⟩
  · -- Porting note: was `rcases minimal_nonempty_open_eq_singleton ho hne _ with ⟨x, hx⟩`
    --               https://github.com/leanprover-community/batteries/issues/116
    rsuffices ⟨x, hx⟩ : ∃ x, (s : Set X) = {x}
    · exact ⟨x, hx.symm ▸ rfl, hx ▸ ho⟩
    refine minimal_nonempty_open_eq_singleton ho hne ?_
    refine fun t hts htne hto => of_not_not fun hts' => ht ?_
    lift t to Finset X using s.finite_toSet.subset hts
    exact ⟨t, ssubset_iff_subset_ne.2 ⟨hts, mt Finset.coe_inj.2 hts'⟩, htne, hto⟩
/-
**exists_open_singleton_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_open_singleton_of_finite [T0Space X] [Finite X] [Nonempty X] : exis
ts x : X, IsOpen ({x} : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isOpen_singleton_of_isOpen_finite`：exists_isOpen_singleton_of_isO
pen_finite [T0Space X] {s : Set X} (hfin : s.Finite) (hne : s.Nonempty) (ho : Is
Open s) : exists x in s, IsOpe…
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem exists_open_singleton_of_finite [T0Space X] [Finite X] [Nonempty X] :
    ∃ x : X, IsOpen ({x} : Set X) :=
  let ⟨x, _, h⟩ := exists_isOpen_singleton_of_isOpen_finite (Set.toFinite _)
    univ_nonempty isOpen_univ
  ⟨x, h⟩
/-
**t0Space_of_injective_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_of_injective_of_continuous [TopologicalSpace Y] {f : X -> Y} (hf :
 Function.Injective f) (hf' : Continuous f) [T0Space Y] : T0Space X
参数：hf : Function.Injective f；hf' : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
-/
theorem t0Space_of_injective_of_continuous [TopologicalSpace Y] {f : X → Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T0Space Y] : T0Space X :=
  ⟨fun _ _ h => hf <| (h.map hf').eq⟩
/-
**Topology.IsEmbedding.t0Space** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T0Space Y] {f : X → Y},   Topology.IsEmbedding f → T0Space X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t0Space_of_injective_of_continuous`：t0Space_of_injective_of_continuous [
TopologicalSpace Y] {f : X -> Y} (hf : Function.Injective f) (hf' : Continuous f
) [T0Space Y] : T0Space …
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
-/
protected theorem Topology.IsEmbedding.t0Space [TopologicalSpace Y] [T0Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T0Space X :=
  t0Space_of_injective_of_continuous hf.injective hf.continuous
/-
**Homeomorph.t0Space** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T0Space X] (h : X ≃ₜ Y),   T0Space Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
protected theorem Homeomorph.t0Space [TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y) : T0Space Y :=
  h.symm.isEmbedding.t0Space

@[stacks 0B31 "part 1"]
/-
**Subtype.t0Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.t0Space [T0Space X] {p : X -> Prop} : T0Space (Subtype p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
instance Subtype.t0Space [T0Space X] {p : X → Prop} : T0Space (Subtype p) :=
  IsEmbedding.subtypeVal.t0Space
/-
**t0Space_iff_or_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t0Space_iff_or_notMem_closure (X : Type u) [TopologicalSpace X] : T0Space 
X ↔ Pairwise fun a b : X => a ∉ closure ({b} : Set X) ∨ b ∉ closure ({a} : Set X
)
参数：X : Type u。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t0Space_iff_or_notMem_closure (X : Type u) [TopologicalSpace X] :
    T0Space X ↔ Pairwise fun a b : X => a ∉ closure ({b} : Set X) ∨ b ∉ closure ({a} : Set X) := by
  simp only [t0Space_iff_not_inseparable, inseparable_iff_mem_closure, not_and_or]
/-
**Prod.instT0Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instT0Space [TopologicalSpace Y] [T0Space X] [T0Space Y] : T0Space (X
 × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
instance Prod.instT0Space [TopologicalSpace Y] [T0Space X] [T0Space Y] : T0Space (X × Y) :=
  ⟨fun _ _ h => Prod.ext (h.map continuous_fst).eq (h.map continuous_snd).eq⟩
/-
**Pi.instT0Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instT0Space {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X
 i)] [forall i, T0Space (X i)] : T0Space (forall i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
instance Pi.instT0Space {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T0Space (X i)] :
    T0Space (∀ i, X i) :=
  ⟨fun _ _ h => funext fun i => (h.map (continuous_apply i)).eq⟩
/-
**ULift.instT0Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instT0Space [T0Space X] : T0Space (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用引理 `Topology.IsEmbedding.uliftDown`：Topology.IsEmbedding.uliftDown [Topologi
calSpace X] : IsEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.instT0Space [T0Space X] : T0Space (ULift X) := IsEmbedding.uliftDown.t0Space
/-
**T0Space.of_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：T0Space.of_cover (h : forall x y, Inseparable x y -> exists s : Set X, x i
n s ∧ y in s ∧ T0Space s) : T0Space X
参数：h : forall x y, Inseparable x y -> exists s : Set X, x in s ∧ y in s ∧ T0Spac
e s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subtype_inseparable_iff`：subtype_inseparable_iff {p : X -> Prop} (x y : 
Subtype p) : (x ~ᵢ y) ↔ ((x : X) ~ᵢ y)
-/
theorem T0Space.of_cover (h : ∀ x y, Inseparable x y → ∃ s : Set X, x ∈ s ∧ y ∈ s ∧ T0Space s) :
    T0Space X := by
  refine ⟨fun x y hxy => ?_⟩
  rcases h x y hxy with ⟨s, hxs, hys, hs⟩
  lift x to s using hxs; lift y to s using hys
  rw [← subtype_inseparable_iff] at hxy
  exact congr_arg Subtype.val hxy.eq
/-
**T0Space.of_open_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：T0Space.of_open_cover (h : forall x, exists s : Set X, x in s ∧ IsOpen s ∧
 T0Space s) : T0Space X
参数：h : forall x, exists s : Set X, x in s ∧ IsOpen s ∧ T0Space s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T0Space.of_cover`：T0Space.of_cover (h : forall x y, Inseparable x y -> e
xists s : Set X, x in s ∧ y in s ∧ T0Space s) : T0Space X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
-/
theorem T0Space.of_open_cover (h : ∀ x, ∃ s : Set X, x ∈ s ∧ IsOpen s ∧ T0Space s) : T0Space X :=
  T0Space.of_cover fun x _ hxy =>
    let ⟨s, hxs, hso, hs⟩ := h x
    ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩

/-- A topological space is called an R₀ space, if `Specializes` relation is symmetric.

In other words, given two points `x y : X`,
if every neighborhood of `y` contains `x`, then every neighborhood of `x` contains `y`. -/
@[mk_iff]
/-
**R0Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is called an R₀ space, if `Specializes` relation is symmetri
c.

In other words, given two points `x y : X`,
if every neighborhood of `y` contains `x`, then every neighborhood of `x` contai
ns `y`.
-/
class R0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- In an R₀ space, the `Specializes` relation is symmetric. -/
  specializes_symm : Std.Symm (Specializes : X → X → Prop)

export R0Space (specializes_symm)

@[deprecated (since := "2026-06-10")]
alias R0Space.specializes_symmetric := R0Space.specializes_symm

export R0Space (specializes_symmetric)

section R0Space

variable [R0Space X] {x y : X}

/-- In an R₀ space, the `Specializes` relation is symmetric, dot notation version. -/
/-
**Specializes.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.symm (h : x ⤳ y) : y ⤳ x
参数：h : x ⤳ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `R0Space.specializes_symm`：∀ {X : Type u} {inst : TopologicalSpace X} [se
lf : R0Space X], Std.Symm Specializes

--- 原说明 ---
In an R₀ space, the `Specializes` relation is symmetric, dot notation version.
-/
theorem Specializes.symm (h : x ⤳ y) : y ⤳ x :=
  specializes_symm.symm x y h

/-- In an R₀ space, the `Specializes` relation is symmetric, `Iff` version. -/
/-
**specializes_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_comm : x ⤳ y ↔ y ⤳ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.symm`：Specializes.symm (h : x ⤳ y) : y ⤳ x

--- 原说明 ---
In an R₀ space, the `Specializes` relation is symmetric, `Iff` version.
-/
theorem specializes_comm : x ⤳ y ↔ y ⤳ x := ⟨Specializes.symm, Specializes.symm⟩

/-- In an R₀ space, `Specializes` is equivalent to `Inseparable`. -/
/-
**specializes_iff_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_inseparable : x ⤳ y ↔ Inseparable x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.antisymm`：Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x
 ~ᵢ y
· 使用定理 `Specializes.symm`：Specializes.symm (h : x ⤳ y) : y ⤳ x
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y

--- 原说明 ---
In an R₀ space, `Specializes` is equivalent to `Inseparable`.
-/
theorem specializes_iff_inseparable : x ⤳ y ↔ Inseparable x y :=
  ⟨fun h ↦ h.antisymm h.symm, Inseparable.specializes⟩

/-- In an R₀ space, `Specializes` implies `Inseparable`. -/
alias ⟨Specializes.inseparable, _⟩ := specializes_iff_inseparable

/-
**Topology.IsInducing.r0Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.r0Space [TopologicalSpace Y] {f : Y -> X} (hf : IsIndu
cing f) : R0Space Y where specializes_symm.symm a b
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
· 使用定理 `Specializes.symm`：Specializes.symm (h : x ⤳ y) : y ⤳ x
-/
theorem Topology.IsInducing.r0Space [TopologicalSpace Y] {f : Y → X} (hf : IsInducing f) :
    R0Space Y where
  specializes_symm.symm a b := by
    simpa only [← hf.specializes_iff] using Specializes.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : X → Prop} : R0Space {x // p x} := IsInducing.subtypeVal.r0Space
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace Y] [R0Space Y] : R0Space (X × Y) where
  specializes_symm.symm _ _ h := h.fst.symm.prod h.snd.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, R0Space (X i)] :
    R0Space (∀ i, X i) where
  specializes_symm.symm _ _ h := specializes_pi.2 fun i ↦ (specializes_pi.1 h i).symm
/-
**R0Space.closure_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：R0Space.closure_singleton (x : X) : closure {x} = (𝓝 x).ker
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ker_nhds_eq_specializes`：ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ 
x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma R0Space.closure_singleton (x : X) : closure {x} = (𝓝 x).ker := by
  ext; simp [ker_nhds_eq_specializes, ← specializes_iff_mem_closure, specializes_comm]

/-- In an R₀ space, the closure of a singleton is a compact set. -/
/-
**isCompact_closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_closure_singleton : IsCompact (closure {x})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_of_finite_subcover`：isCompact_of_finite_subcover (h : forall {
ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) 
-> exists t : Fins…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `specializes_comm`：specializes_comm : x ⤳ y ↔ y ⤳ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)

--- 原说明 ---
In an R₀ space, the closure of a singleton is a compact set.
-/
theorem isCompact_closure_singleton : IsCompact (closure {x}) := by
  refine isCompact_of_finite_subcover fun U hUo hxU ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := mem_iUnion.1 <| hxU <| subset_closure rfl
  refine ⟨{i}, fun y hy ↦ ?_⟩
  rw [← specializes_iff_mem_closure, specializes_comm] at hy
  simpa using hy.mem_open (hUo i) hi
/-
**Filter.coclosedCompact_le_cofinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.coclosedCompact_le_cofinite : coclosedCompact X <= cofinite
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_cofinite_iff_compl_singleton_mem`：le_cofinite_iff_compl_single
ton_mem : l <= cofinite ↔ forall x, {x}ᶜ in l
· 使用定理 `Filter.compl_mem_coclosedCompact`：compl_mem_coclosedCompact : sᶜ in cocl
osedCompact X ↔ IsCompact (closure s)
· 使用定理 `isCompact_closure_singleton`：isCompact_closure_singleton : IsCompact (cl
osure {x})
-/
theorem Filter.coclosedCompact_le_cofinite : coclosedCompact X ≤ cofinite :=
  le_cofinite_iff_compl_singleton_mem.2 fun _ ↦
    compl_mem_coclosedCompact.2 isCompact_closure_singleton

variable (X) in
/-- In an R₀ space, relatively compact sets form a bornology.
Its cobounded filter is `Filter.coclosedCompact`.
See also `Bornology.inCompact` the bornology of sets contained in a compact set. -/
@[instance_reducible]
/-
**Bornology.relativelyCompact** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Bornology.relativelyCompact : Bornology X where cobounded
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.coclosedCompact_le_cofinite`：Filter.coclosedCompact_le_cofinite :
 coclosedCompact X <= cofinite

--- 原说明 ---
In an R₀ space, relatively compact sets form a bornology.
Its cobounded filter is `Filter.coclosedCompact`.
See also `Bornology.inCompact` the bornology of sets contained in a compact set.
-/
def Bornology.relativelyCompact : Bornology X where
  cobounded := Filter.coclosedCompact X
  le_cofinite := Filter.coclosedCompact_le_cofinite
/-
**Bornology.relativelyCompact.isBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.relativelyCompact.isBounded_iff {s : Set X} : @Bornology.IsBound
ed _ (Bornology.relativelyCompact X) s ↔ IsCompact (closure s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.compl_mem_coclosedCompact`：compl_mem_coclosedCompact : sᶜ in cocl
osedCompact X ↔ IsCompact (closure s)
-/
theorem Bornology.relativelyCompact.isBounded_iff {s : Set X} :
    @Bornology.IsBounded _ (Bornology.relativelyCompact X) s ↔ IsCompact (closure s) :=
  compl_mem_coclosedCompact

/-- In an R₀ space, the closure of a finite set is a compact set. -/
/-
**Set.Finite.isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.isCompact_closure {s : Set X} (hs : s.Finite) : IsCompact (clos
ure s)
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bornology.relativelyCompact.isBounded_iff`：Bornology.relativelyCompact.i
sBounded_iff {s : Set X} : @Bornology.IsBounded _ (Bornology.relativelyCompact X
) s ↔ IsCompact (closure s)
· 使用定理 `Set.Finite.isBounded`：Set.Finite.isBounded [Bornology α] {s : Set α} (hs
 : s.Finite) : IsBounded s

--- 原说明 ---
In an R₀ space, the closure of a finite set is a compact set.
-/
theorem Set.Finite.isCompact_closure {s : Set X} (hs : s.Finite) : IsCompact (closure s) :=
  let _ : Bornology X := .relativelyCompact X
  Bornology.relativelyCompact.isBounded_iff.1 hs.isBounded

end R0Space

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
/-
**T1Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`.
-/
class T1Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- A singleton in a T₁ space is a closed set. -/
  t1 : ∀ x, IsClosed ({x} : Set X)

@[closedness .]
/-
**isClosed_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
-/
theorem isClosed_singleton [T1Space X] {x : X} : IsClosed ({x} : Set X) :=
  T1Space.t1 x
/-
**isOpen_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_compl_singleton [T1Space X] {x : X} : IsOpen ({x}ᶜ : Set X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
theorem isOpen_compl_singleton [T1Space X] {x : X} : IsOpen ({x}ᶜ : Set X) :=
  isClosed_singleton.isOpen_compl
/-
**isOpen_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
-/
theorem isOpen_ne [T1Space X] {x : X} : IsOpen { y | y ≠ x } :=
  isOpen_compl_singleton

@[to_additive]
/-
**Continuous.isOpen_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.isOpen_mulSupport [T1Space X] [One X] [TopologicalSpace Y] {f :
 Y -> X} (hf : Continuous f) : IsOpen (mulSupport f)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
-/
theorem Continuous.isOpen_mulSupport [T1Space X] [One X] [TopologicalSpace Y] {f : Y → X}
    (hf : Continuous f) : IsOpen (mulSupport f) :=
  isOpen_ne.preimage hf
/-
**Ne.nhdsWithin_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.nhdsWithin_compl_singleton [T1Space X] {x y : X} (h : x != y) : 𝓝[{y}ᶜ]
 x = 𝓝 x
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
-/
theorem Ne.nhdsWithin_compl_singleton [T1Space X] {x y : X} (h : x ≠ y) : 𝓝[{y}ᶜ] x = 𝓝 x :=
  isOpen_ne.nhdsWithin_eq h
/-
**Ne.nhdsWithin_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.nhdsWithin_sdiff_singleton [T1Space X] {x y : X} (h : x != y) (s : Set 
X) : 𝓝[s \ {y}] x = 𝓝[s] x
参数：h : x != y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
-/
theorem Ne.nhdsWithin_sdiff_singleton [T1Space X] {x y : X} (h : x ≠ y) (s : Set X) :
    𝓝[s \ {y}] x = 𝓝[s] x := by
  rw [sdiff_eq, inter_comm, nhdsWithin_inter_of_mem]
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)

@[deprecated (since := "2026-06-03")]
alias Ne.nhdsWithin_diff_singleton := Ne.nhdsWithin_sdiff_singleton
/-
**nhdsWithin_compl_singleton_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsWithin_compl_singleton_le [T1Space X] (x y : X) : 𝓝[{x}ᶜ] x <= 𝓝[{y}ᶜ]
 x
参数：x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.nhdsWithin_compl_singleton`：Ne.nhdsWithin_compl_singleton [T1Space X]
 {x y : X} (h : x != y) : 𝓝[{y}ᶜ] x = 𝓝 x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma nhdsWithin_compl_singleton_le [T1Space X] (x y : X) : 𝓝[{x}ᶜ] x ≤ 𝓝[{y}ᶜ] x := by
  rcases eq_or_ne x y with rfl | hy
  · exact Eq.le rfl
  · rw [Ne.nhdsWithin_compl_singleton hy]
    exact nhdsWithin_le_nhds
/-
**isOpen_setOfPred_eventually_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_setOfPred_eventually_nhdsWithin [T1Space X] {p : X -> Prop} : IsOpe
n { x | forallᶠ y in 𝓝[!=] x, p y }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_nhds_nhdsWithin`：eventually_nhds_nhdsWithin {a : α} {s : Set 
α} {p : α -> Prop} : (forallᶠ y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in
 𝓝[s] a, p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.nhdsWithin_compl_singleton`：Ne.nhdsWithin_compl_singleton [T1Space X]
 {x y : X} (h : x != y) : 𝓝[{y}ᶜ] x = 𝓝 x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem isOpen_setOfPred_eventually_nhdsWithin [T1Space X] {p : X → Prop} :
    IsOpen { x | ∀ᶠ y in 𝓝[≠] x, p y } := by
  refine isOpen_iff_mem_nhds.mpr fun a ha => ?_
  filter_upwards [eventually_nhds_nhdsWithin.mpr ha] with b hb
  rcases eq_or_ne a b with rfl | h
  · exact hb
  · rw [h.symm.nhdsWithin_compl_singleton] at hb
    exact hb.filter_mono nhdsWithin_le_nhds

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_eventually_nhdsWithin := isOpen_setOfPred_eventually_nhdsWithin
/-
**Set.Finite.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X] {s : Set X}, s.Fi
nite → IsClosed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
@[simp] protected lemma Set.Finite.isClosed [T1Space X] {s : Set X} (hs : s.Finite) :
    IsClosed s := by
  rw [← biUnion_of_singleton s]
  exact hs.isClosed_biUnion fun i _ => isClosed_singleton
/-
**TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne [T1Space X] {b : Set 
(Set X)} (hb : IsTopologicalBasis b) {x y : X} (h : x != y) : exists a in b, x i
n a ∧ y ∉ a
参数：Set X；hb : IsTopologicalBasis b；h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen_iff`：∀ {α : Type u} [t : Topo
logicalSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalB
asis b → (IsOpen s ↔ ∀ a ∈ s, ∃ t ∈ …
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
-/
theorem TopologicalSpace.IsTopologicalBasis.exists_mem_of_ne [T1Space X] {b : Set (Set X)}
    (hb : IsTopologicalBasis b) {x y : X} (h : x ≠ y) : ∃ a ∈ b, x ∈ a ∧ y ∉ a := by
  rcases hb.isOpen_iff.1 isOpen_ne x h with ⟨a, ab, xa, ha⟩
  exact ⟨a, ab, xa, fun h => ha h rfl⟩
/-
**Finset.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X] (s : Finset X), I
sClosed ↑s
参数：s : Finset X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Spa
ce X] {s : Set X}, s.Finite → IsClosed s
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
protected theorem Finset.isClosed [T1Space X] (s : Finset X) : IsClosed (s : Set X) :=
  s.finite_toSet.isClosed
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T1Space (CofiniteTopology X) where
  t1 x := CofiniteTopology.isClosed_iff.mpr <| by simp
/-
**t1Space_TFAE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE [T1Space X, for
all x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set X), Continuous (
@CofiniteTopology.of X), forall ⦃x y : X⦄, x != y -> {y}ᶜ in 𝓝 x, forall ⦃x y : 
X⦄, x != y -> exists s in 𝓝 x, y ∉ s, forall ⦃x y : X⦄, x != y -> exists U : Set
 X, IsOpen U ∧ x in U ∧ y ∉ U, forall ⦃x y : X⦄, x != y -> Disjoint (𝓝 x) (pure 
y), forall ⦃x y : X⦄, x != y -> Disjoint (pure x) (𝓝 y), forall ⦃x y : X⦄, x ⤳ y
 -> x = y, T0Space X ∧ R0S
参数：X : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Set.Finite.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Spa
ce X] {s : Set X}, s.Finite → IsClosed s
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.preimage_image`：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻
¹' e '' s = s
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `instT1SpaceCofiniteTopology`：∀ {X : Type u_1}, T1Space (CofiniteTopology
 X)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
（共 35 条，此处仅展示前 30 条）
-/
theorem t1Space_TFAE (X : Type u) [TopologicalSpace X] :
    List.TFAE [T1Space X,
      ∀ x, IsClosed ({ x } : Set X),
      ∀ x, IsOpen ({ x }ᶜ : Set X),
      Continuous (@CofiniteTopology.of X),
      ∀ ⦃x y : X⦄, x ≠ y → {y}ᶜ ∈ 𝓝 x,
      ∀ ⦃x y : X⦄, x ≠ y → ∃ s ∈ 𝓝 x, y ∉ s,
      ∀ ⦃x y : X⦄, x ≠ y → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ y ∉ U,
      ∀ ⦃x y : X⦄, x ≠ y → Disjoint (𝓝 x) (pure y),
      ∀ ⦃x y : X⦄, x ≠ y → Disjoint (pure x) (𝓝 y),
      ∀ ⦃x y : X⦄, x ⤳ y → x = y,
      T0Space X ∧ R0Space X] := by
  tfae_have 1 ↔ 2 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 ↔ 3 := by
    simp only [isOpen_compl_iff]
  tfae_have 5 ↔ 3 := by
    refine forall_comm.trans ?_
    simp only [isOpen_iff_mem_nhds, mem_compl_iff, mem_singleton_iff]
  tfae_have 5 ↔ 6 := by
    simp only [← subset_compl_singleton_iff, exists_mem_subset_iff]
  tfae_have 5 ↔ 7 := by
    simp only [(nhds_basis_opens _).mem_iff, subset_compl_singleton_iff, and_assoc,
      and_left_comm]
  tfae_have 5 ↔ 8 := by
    simp only [← principal_singleton, disjoint_principal_right]
  tfae_have 8 ↔ 9 := forall_comm.trans (by simp only [disjoint_comm, ne_comm])
  tfae_have 1 → 4 := by
    simp only [continuous_def, CofiniteTopology.isOpen_iff']
    rintro H s (rfl | hs)
    · exact isOpen_empty
    · rw [← compl_compl s, preimage_compl]
      exact hs.preimage (Equiv.injective _).injOn |>.isClosed.isOpen_compl
  tfae_have 4 → 2 := by
    intro h x
    rw [← CofiniteTopology.of.preimage_image {x}]
    exact (Set.Finite.isClosed <| by simp) |>.preimage h
  tfae_have 2 ↔ 10 := by
    simp only [← closure_subset_iff_isClosed, specializes_iff_mem_closure, subset_def,
      mem_singleton_iff, eq_comm]
  tfae_have 10 ↔ 11 :=
    ⟨fun h => ⟨⟨fun _ _ h₂ => h h₂.specializes⟩, ⟨⟨fun _ _ h₂ => specializes_of_eq (h h₂).symm⟩⟩⟩,
      fun ⟨_, _⟩ _ _ h => (h.antisymm h.symm).eq⟩
  tfae_finish
/-
**t1Space_iff_continuous_cofinite_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_iff_continuous_cofinite_of : T1Space X ↔ Continuous (@CofiniteTopo
logy.of X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
-/
theorem t1Space_iff_continuous_cofinite_of : T1Space X ↔ Continuous (@CofiniteTopology.of X) :=
  (t1Space_TFAE X).out 0 3
/-
**CofiniteTopology.continuous_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CofiniteTopology.continuous_of [T1Space X] : Continuous (@CofiniteTopology
.of X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t1Space_iff_continuous_cofinite_of`：t1Space_iff_continuous_cofinite_of :
 T1Space X ↔ Continuous (@CofiniteTopology.of X)
-/
theorem CofiniteTopology.continuous_of [T1Space X] : Continuous (@CofiniteTopology.of X) :=
  t1Space_iff_continuous_cofinite_of.mp ‹_›
/-
**t1Space_iff_exists_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_iff_exists_open : T1Space X ↔ Pairwise fun x y => exists U : Set X
, IsOpen U ∧ x in U ∧ y ∉ U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
-/
theorem t1Space_iff_exists_open :
    T1Space X ↔ Pairwise fun x y => ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ y ∉ U :=
  (t1Space_TFAE X).out 0 6
/-
**t1Space_iff_disjoint_pure_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_iff_disjoint_pure_nhds : T1Space X ↔ forall ⦃x y : X⦄, x != y -> D
isjoint (pure x) (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
-/
theorem t1Space_iff_disjoint_pure_nhds : T1Space X ↔ ∀ ⦃x y : X⦄, x ≠ y → Disjoint (pure x) (𝓝 y) :=
  (t1Space_TFAE X).out 0 8
/-
**t1Space_iff_disjoint_nhds_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_iff_disjoint_nhds_pure : T1Space X ↔ forall ⦃x y : X⦄, x != y -> D
isjoint (𝓝 x) (pure y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
-/
theorem t1Space_iff_disjoint_nhds_pure : T1Space X ↔ ∀ ⦃x y : X⦄, x ≠ y → Disjoint (𝓝 x) (pure y) :=
  (t1Space_TFAE X).out 0 7
/-
**t1Space_iff_specializes_imp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_iff_specializes_imp_eq : T1Space X ↔ forall ⦃x y : X⦄, x ⤳ y -> x 
= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
-/
theorem t1Space_iff_specializes_imp_eq : T1Space X ↔ ∀ ⦃x y : X⦄, x ⤳ y → x = y :=
  (t1Space_TFAE X).out 0 9
/-
**t1Space_iff_t0Space_and_r0Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_iff_t0Space_and_r0Space : T1Space X ↔ T0Space X ∧ R0Space X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
-/
theorem t1Space_iff_t0Space_and_r0Space : T1Space X ↔ T0Space X ∧ R0Space X :=
  (t1Space_TFAE X).out 0 10
/-
**disjoint_pure_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_pure_nhds [T1Space X] {x y : X} (h : x != y) : Disjoint (pure x) 
(𝓝 y)
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t1Space_iff_disjoint_pure_nhds`：t1Space_iff_disjoint_pure_nhds : T1Space
 X ↔ forall ⦃x y : X⦄, x != y -> Disjoint (pure x) (𝓝 y)
-/
theorem disjoint_pure_nhds [T1Space X] {x y : X} (h : x ≠ y) : Disjoint (pure x) (𝓝 y) :=
  t1Space_iff_disjoint_pure_nhds.mp ‹_› h
/-
**disjoint_nhds_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_pure [T1Space X] {x y : X} (h : x != y) : Disjoint (𝓝 x) (pu
re y)
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t1Space_iff_disjoint_nhds_pure`：t1Space_iff_disjoint_nhds_pure : T1Space
 X ↔ forall ⦃x y : X⦄, x != y -> Disjoint (𝓝 x) (pure y)
-/
theorem disjoint_nhds_pure [T1Space X] {x y : X} (h : x ≠ y) : Disjoint (𝓝 x) (pure y) :=
  t1Space_iff_disjoint_nhds_pure.mp ‹_› h
/-
**Specializes.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y
参数：h : x ⤳ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t1Space_iff_specializes_imp_eq`：t1Space_iff_specializes_imp_eq : T1Space
 X ↔ forall ⦃x y : X⦄, x ⤳ y -> x = y
-/
theorem Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y :=
  t1Space_iff_specializes_imp_eq.1 ‹_› h
/-
**specializes_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.eq`：Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y
· 使用定理 `specializes_rfl`：specializes_rfl : x ⤳ x
-/
theorem specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x = y :=
  ⟨Specializes.eq, fun h => h ▸ specializes_rfl⟩
/-
**specializes_eq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X], (fun x1 x2 => x1
 ⤳ x2) = Eq
参数：fun x1 x2 => x1 ⤳ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `specializes_iff_eq`：specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x
 = y
-/
@[simp] theorem specializes_eq_eq [T1Space X] : (· ⤳ ·) = @Eq X :=
  funext₂ fun _ _ => propext specializes_iff_eq

@[simp]
/-
**pure_le_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pure_le_nhds_iff [T1Space X] {a b : X} : pure a <= 𝓝 b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `specializes_iff_pure`：specializes_iff_pure : x ⤳ y ↔ pure x <= 𝓝 y
· 使用定理 `specializes_iff_eq`：specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x
 = y
-/
theorem pure_le_nhds_iff [T1Space X] {a b : X} : pure a ≤ 𝓝 b ↔ a = b :=
  specializes_iff_pure.symm.trans specializes_iff_eq

@[simp]
/-
**nhds_le_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_le_nhds_iff [T1Space X] {a b : X} : 𝓝 a <= 𝓝 b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `specializes_iff_eq`：specializes_iff_eq [T1Space X] {x y : X} : x ⤳ y ↔ x
 = y
-/
theorem nhds_le_nhds_iff [T1Space X] {a b : X} : 𝓝 a ≤ 𝓝 b ↔ a = b :=
  specializes_iff_eq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [T1Space X] : R0Space X :=
  (t1Space_iff_t0Space_and_r0Space.mp ‹T1Space X›).right
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 80) [T0Space X] [R0Space X] : T1Space X :=
  t1Space_iff_t0Space_and_r0Space.mpr ⟨‹T0Space X›, ‹R0Space X›⟩
/-
**t1Space_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_antitone {X} : Antitone (@T1Space X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mono`：IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsCl
osed[t₁] s
· 使用定理 `T1Space.t1`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T1Space X
] (x : X), IsClosed {x}
-/
theorem t1Space_antitone {X} : Antitone (@T1Space X) := fun a _ h _ =>
  @T1Space.mk _ a fun x => (T1Space.t1 x).mono h
/-
**continuousWithinAt_update_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSp
ace Y] {f : X -> Y} {s : Set X} {x x' : X} {y : Y} (hne : x' != x) : ContinuousW
ithinAt (Function.update f x y) s x' ↔ ContinuousWithinAt f s x'
参数：hne : x' != x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.congr_continuousWithinAt`：Filter.EventuallyEq.congr_
continuousWithinAt (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) : ContinuousWithinAt f 
s x ↔ ContinuousWithinAt g s x
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem continuousWithinAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x x' : X} {y : Y} (hne : x' ≠ x) :
    ContinuousWithinAt (Function.update f x y) s x' ↔ ContinuousWithinAt f s x' :=
  EventuallyEq.congr_continuousWithinAt
    (mem_nhdsWithin_of_mem_nhds <| mem_of_superset (isOpen_ne.mem_nhds hne) fun _y' hy' =>
      Function.update_of_ne hy' _ _)
    (Function.update_of_ne hne ..)
/-
**continuousAt_update_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y]
 {f : X -> Y} {x x' : X} {y : Y} (hne : x' != x) : ContinuousAt (Function.update
 f x y) x' ↔ ContinuousAt f x'
参数：hne : x' != x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_update_of_ne`：continuousWithinAt_update_of_ne [T1Spac
e X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y} {s : Set X} {x x' : X} {y
 : Y} (hne : x' != x)…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_update_of_ne [T1Space X] [DecidableEq X] [TopologicalSpace Y]
    {f : X → Y} {x x' : X} {y : Y} (hne : x' ≠ x) :
    ContinuousAt (Function.update f x y) x' ↔ ContinuousAt f x' := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_update_of_ne hne]
/-
**continuousOn_update_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_update_iff [T1Space X] [DecidableEq X] [TopologicalSpace Y] {
f : X -> Y} {s : Set X} {x : X} {y : Y} : ContinuousOn (Function.update f x y) s
 ↔ ContinuousOn f (s \ {x}) ∧ (x in s -> Tendsto f (𝓝[s \ {x}] x) (𝓝 y))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_forall_ne`：and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔
 forall b, p b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `continuousWithinAt_update_of_ne`：continuousWithinAt_update_of_ne [T1Spac
e X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y} {s : Set X} {x x' : X} {y
 : Y} (hne : x' != x)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `ContinuousWithinAt.mono_of_mem_nhdsWithin`：ContinuousWithinAt.mono_of_me
m_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x) : ContinuousWithi
nAt f s x
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `continuousWithinAt_update_same`：continuousWithinAt_update_same [Decidabl
eEq α] {y : β} : ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x
) (𝓝 y)
-/
theorem continuousOn_update_iff [T1Space X] [DecidableEq X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x : X} {y : Y} :
    ContinuousOn (Function.update f x y) s ↔
      ContinuousOn f (s \ {x}) ∧ (x ∈ s → Tendsto f (𝓝[s \ {x}] x) (𝓝 y)) := by
  rw [ContinuousOn, ← and_forall_ne x, and_comm]
  refine and_congr ⟨fun H z hz => ?_, fun H z hzx hzs => ?_⟩ (forall_congr' fun _ => ?_)
  · specialize H z hz.2 hz.1
    rw [continuousWithinAt_update_of_ne hz.2] at H
    exact H.mono sdiff_subset
  · rw [continuousWithinAt_update_of_ne hzx]
    refine (H z ⟨hzs, hzx⟩).mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ ?_)
    exact isOpen_ne.mem_nhds hzx
  · exact continuousWithinAt_update_same
/-
**t1Space_of_injective_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t1Space_of_injective_of_continuous [TopologicalSpace Y] {f : X -> Y} (hf :
 Function.Injective f) (hf' : Continuous f) [T1Space Y] : T1Space X
参数：hf : Function.Injective f；hf' : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `t1Space_iff_specializes_imp_eq`：t1Space_iff_specializes_imp_eq : T1Space
 X ↔ forall ⦃x y : X⦄, x ⤳ y -> x = y
· 使用定理 `Specializes.eq`：Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
-/
theorem t1Space_of_injective_of_continuous [TopologicalSpace Y] {f : X → Y}
    (hf : Function.Injective f) (hf' : Continuous f) [T1Space Y] : T1Space X :=
  t1Space_iff_specializes_imp_eq.2 fun _ _ h => hf (h.map hf').eq
/-
**Topology.IsEmbedding.t1Space** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbedding`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T1Space Y] {f : X → Y},   Topology.IsEmbedding f → T1Space X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t1Space_of_injective_of_continuous`：t1Space_of_injective_of_continuous [
TopologicalSpace Y] {f : X -> Y} (hf : Function.Injective f) (hf' : Continuous f
) [T1Space Y] : T1Space …
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
-/
protected theorem Topology.IsEmbedding.t1Space [TopologicalSpace Y] [T1Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T1Space X :=
  t1Space_of_injective_of_continuous hf.injective hf.continuous
/-
**Homeomorph.t1Space** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T1Space X] (h : X ≃ₜ Y),   T1Space Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T1Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
protected theorem Homeomorph.t1Space [TopologicalSpace Y] [T1Space X] (h : X ≃ₜ Y) : T1Space Y :=
  h.symm.isEmbedding.t1Space
/-
**Subtype.t1Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.t1Space {X : Type u} [TopologicalSpace X] [T1Space X] {p : X -> Pr
op} : T1Space (Subtype p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T1Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
instance Subtype.t1Space {X : Type u} [TopologicalSpace X] [T1Space X] {p : X → Prop} :
    T1Space (Subtype p) :=
  IsEmbedding.subtypeVal.t1Space
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace Y] [T1Space X] [T1Space Y] : T1Space (X × Y) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ isClosed_singleton.prod isClosed_singleton⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)] :
    T1Space (∀ i, X i) :=
  ⟨fun f => univ_pi_singleton f ▸ isClosed_set_pi fun _ _ => isClosed_singleton⟩
/-
**ULift.instT1Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instT1Space [T1Space X] : T1Space (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t1Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T1Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用引理 `Topology.IsEmbedding.uliftDown`：Topology.IsEmbedding.uliftDown [Topologi
calSpace X] : IsEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.instT1Space [T1Space X] : T1Space (ULift X) :=
  IsEmbedding.uliftDown.t1Space

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) T1Space.t0Space [T1Space X] : T0Space X :=
  (t1Space_iff_t0Space_and_r0Space.mp ‹T1Space X›).left

@[simp]
/-
**compl_singleton_mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_singleton_mem_nhds_iff [T1Space X] {x y : X} : {x}ᶜ in 𝓝 y ↔ y != x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds_iff`：∀ {X : Type u} [inst : TopologicalSpace X] {x : X} 
{s : Set X}, IsOpen s → (s ∈ nhds x ↔ x ∈ s)
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
-/
theorem compl_singleton_mem_nhds_iff [T1Space X] {x y : X} : {x}ᶜ ∈ 𝓝 y ↔ y ≠ x :=
  isOpen_compl_singleton.mem_nhds_iff
/-
**compl_singleton_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_singleton_mem_nhds [T1Space X] {x y : X} (h : y != x) : {x}ᶜ in 𝓝 y
参数：h : y != x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `compl_singleton_mem_nhds_iff`：compl_singleton_mem_nhds_iff [T1Space X] {
x y : X} : {x}ᶜ in 𝓝 y ↔ y != x
-/
theorem compl_singleton_mem_nhds [T1Space X] {x y : X} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
  compl_singleton_mem_nhds_iff.mpr h

@[closedness =]
/-
**closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_singleton [T1Space X] {x : X} : closure ({x} : Set X) = {x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
theorem closure_singleton [T1Space X] {x : X} : closure ({x} : Set X) = {x} :=
  isClosed_singleton.closure_eq
/-
**Set.Subsingleton.isClosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isClosed [T1Space X] {s : Set X} (hs : s.Subsingleton) : 
IsClosed s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
-/
lemma Set.Subsingleton.isClosed [T1Space X] {s : Set X} (hs : s.Subsingleton) : IsClosed s := by
  rcases hs.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact isClosed_empty
  · exact isClosed_singleton
/-
**Set.Subsingleton.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.closure_eq [T1Space X] {s : Set X} (hs : s.Subsingleton) 
: closure s = s
参数：hs : s.Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用引理 `Set.Subsingleton.isClosed`：Set.Subsingleton.isClosed [T1Space X] {s : Se
t X} (hs : s.Subsingleton) : IsClosed s
-/
theorem Set.Subsingleton.closure_eq [T1Space X] {s : Set X} (hs : s.Subsingleton) :
    closure s = s :=
  hs.isClosed.closure_eq
/-
**Set.Subsingleton.closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.closure [T1Space X] {s : Set X} (hs : s.Subsingleton) : (
closure s).Subsingleton
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Subsingleton.closure_eq`：Set.Subsingleton.closure_eq [T1Space X] {s 
: Set X} (hs : s.Subsingleton) : closure s = s
-/
theorem Set.Subsingleton.closure [T1Space X] {s : Set X} (hs : s.Subsingleton) :
    (closure s).Subsingleton := by
  rwa [hs.closure_eq]

@[simp]
/-
**subsingleton_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_closure [T1Space X] {s : Set X} : (closure s).Subsingleton ↔ 
s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.Subsingleton.closure`：Set.Subsingleton.closure [T1Space X] {s : Set 
X} (hs : s.Subsingleton) : (closure s).Subsingleton
-/
theorem subsingleton_closure [T1Space X] {s : Set X} : (closure s).Subsingleton ↔ s.Subsingleton :=
  ⟨fun h => h.anti subset_closure, fun h => h.closure⟩

set_option backward.isDefEq.respectTransparency false in
/-
**isClosedMap_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_const {X Y} [TopologicalSpace X] [TopologicalSpace Y] [T1Space
 Y] {y : Y} : IsClosedMap (Function.const X y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.of_nonempty`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (s : Set X), IsClos
ed s → s.None…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem isClosedMap_const {X Y} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] {y : Y} :
    IsClosedMap (Function.const X y) :=
  IsClosedMap.of_nonempty fun s _ h2s => by simp_rw [const, h2s.image_const, isClosed_singleton]
/-
**isClosedMap_prodMk_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosedMap_prodMk_left [TopologicalSpace Y] [T1Space X] (x : X) : IsClose
dMap (fun y : Y => Prod.mk x y)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.prod`：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁
) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
-/
lemma isClosedMap_prodMk_left [TopologicalSpace Y] [T1Space X] (x : X) :
    IsClosedMap (fun y : Y ↦ Prod.mk x y) :=
  fun _K hK ↦ Set.singleton_prod ▸ isClosed_singleton.prod hK
/-
**isClosedMap_prodMk_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosedMap_prodMk_right [TopologicalSpace Y] [T1Space Y] (y : Y) : IsClos
edMap (fun x : X => Prod.mk x y)
参数：y : Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.prod`：IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁
) (h₂ : IsClosed s₂) : IsClosed (s₁ ×ˢ s₂)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `Set.prod_singleton`：prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, 
b)) '' s
-/
lemma isClosedMap_prodMk_right [TopologicalSpace Y] [T1Space Y] (y : Y) :
    IsClosedMap (fun x : X ↦ Prod.mk x y) :=
  fun _K hK ↦ Set.prod_singleton ▸ hK.prod isClosed_singleton
/-
**nhdsWithin_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {s : Set X} (hxy : x != y) :
 𝓝[insert y s] x = 𝓝[s] x
参数：hxy : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_def`：le_def : f <= g ↔ forall x in g, x in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `IsOpen.sdiff`：IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s
 \ t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_insert_of_notMem`：inter_insert_of_notMem (h : a ∉ s) : s inter
 insert a t = s inter t
· 使用定理 `Set.notMem_sdiff_of_mem`：notMem_sdiff_of_mem {s t : Set α} {x : α} (hx :
 x in t) : x ∉ s \ t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
-/
theorem nhdsWithin_insert_of_ne [T1Space X] {x y : X} {s : Set X} (hxy : x ≠ y) :
    𝓝[insert y s] x = 𝓝[s] x := by
  refine le_antisymm (Filter.le_def.2 fun t ht => ?_) (nhdsWithin_mono x <| subset_insert y s)
  obtain ⟨o, ho, hxo, host⟩ := mem_nhdsWithin.mp ht
  refine mem_nhdsWithin.mpr ⟨o \ {y}, ho.sdiff isClosed_singleton, ⟨hxo, hxy⟩, ?_⟩
  rw [inter_insert_of_notMem <| notMem_sdiff_of_mem (mem_singleton y)]
  exact (inter_subset_inter sdiff_subset Subset.rfl).trans host

/-- If `t` is a subset of `s`, except for one point,
then `insert x s` is a neighborhood of `x` within `t`. -/
/-
**insert_mem_nhdsWithin_of_subset_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：insert_mem_nhdsWithin_of_subset_insert [T1Space X] {x y : X} {s t : Set X}
 (hu : t subseteq insert y s) : insert x s in 𝓝[t] x
参数：hu : t subseteq insert y s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s

--- 原说明 ---
If `t` is a subset of `s`, except for one point,
then `insert x s` is a neighborhood of `x` within `t`.
-/
theorem insert_mem_nhdsWithin_of_subset_insert [T1Space X] {x y : X} {s t : Set X}
    (hu : t ⊆ insert y s) : insert x s ∈ 𝓝[t] x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact mem_of_superset self_mem_nhdsWithin hu
  refine nhdsWithin_mono x hu ?_
  rw [nhdsWithin_insert_of_ne h]
  exact mem_of_superset self_mem_nhdsWithin (subset_insert x s)
/-
**eventuallyEq_insert** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventuallyEq_insert [T1Space X] {s t : Set X} {x y : X} (h : s =ᶠ[𝓝[{y}ᶜ] 
x] t) : (insert x s : Set X) =ᶠ[𝓝 x] (insert x t : Set X)
参数：h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `nhdsWithin_compl_singleton_le`：nhdsWithin_compl_singleton_le [T1Space X]
 (x y : X) : 𝓝[{x}ᶜ] x <= 𝓝[{y}ᶜ] x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eventuallyEq_insert [T1Space X] {s t : Set X} {x y : X} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    (insert x s : Set X) =ᶠ[𝓝 x] (insert x t : Set X) := by
  simp_rw [eventuallyEq_set] at h ⊢
  simp_rw [← union_singleton, ← nhdsWithin_univ, ← compl_union_self {x},
    nhdsWithin_union, eventually_sup, nhdsWithin_singleton,
    eventually_pure, union_singleton, mem_insert_iff, true_or, and_true]
  filter_upwards [nhdsWithin_compl_singleton_le x y h] with y using or_congr (Iff.rfl)

@[simp]
/-
**ker_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x}
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ker_nhds_eq_specializes`：ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ 
x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `specializes_eq_eq`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space
 X], (fun x1 x2 => x1 ⤳ x2) = Eq
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x} := by
  simp [ker_nhds_eq_specializes]
/-
**biInter_basis_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biInter_basis_nhds [T1Space X] {ι : Sort*} {p : ι -> Prop} {s : ι -> Set X
} {x : X} (h : (𝓝 x).HasBasis p s) : ⋂ (i) (_ : p i), s i = {x}
参数：h : (𝓝 x).HasBasis p s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.HasBasis.ker`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {p :
 ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.ker = ⋂ i, ⋂ (_ : p i), s i
· 使用定理 `ker_nhds`：ker_nhds [T1Space X] (x : X) : (𝓝 x).ker = {x}
-/
theorem biInter_basis_nhds [T1Space X] {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : ⋂ (i) (_ : p i), s i = {x} := by
  rw [← h.ker, ker_nhds]

@[simp]
/-
**compl_singleton_mem_nhdsSet_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_singleton_mem_nhdsSet_iff [T1Space X] {x : X} {s : Set X} : {x}ᶜ in 
𝓝ˢ s ↔ x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用引理 `Set.subset_compl_singleton_iff`：subset_compl_singleton_iff : s subseteq 
{a}ᶜ ↔ a ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_singleton_mem_nhdsSet_iff [T1Space X] {x : X} {s : Set X} : {x}ᶜ ∈ 𝓝ˢ s ↔ x ∉ s := by
  rw [isOpen_compl_singleton.mem_nhdsSet, subset_compl_singleton_iff]

@[simp]
/-
**nhdsSet_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_le_iff [T1Space X] {s t : Set X} : 𝓝ˢ s <= 𝓝ˢ t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `monotone_nhdsSet`：monotone_nhdsSet : Monotone (𝓝ˢ : Set X -> Filter X)
-/
theorem nhdsSet_le_iff [T1Space X] {s t : Set X} : 𝓝ˢ s ≤ 𝓝ˢ t ↔ s ⊆ t := by
  refine ⟨?_, fun h => monotone_nhdsSet h⟩
  simp_rw [Filter.le_def]; intro h x hx
  specialize h {x}ᶜ
  simp_rw [compl_singleton_mem_nhdsSet_iff] at h
  by_contra hxt
  exact h hxt hx

@[simp]
/-
**nhdsSet_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_inj_iff [T1Space X] {s t : Set X} : 𝓝ˢ s = 𝓝ˢ t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `nhdsSet_le_iff`：nhdsSet_le_iff [T1Space X] {s t : Set X} : 𝓝ˢ s <= 𝓝ˢ t 
↔ s subseteq t
-/
theorem nhdsSet_inj_iff [T1Space X] {s t : Set X} : 𝓝ˢ s = 𝓝ˢ t ↔ s = t := by
  simp_rw [le_antisymm_iff]
  exact and_congr nhdsSet_le_iff nhdsSet_le_iff
/-
**injective_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_nhdsSet [T1Space X] : Function.Injective (𝓝ˢ : Set X -> Filter X
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nhdsSet_inj_iff`：nhdsSet_inj_iff [T1Space X] {s t : Set X} : 𝓝ˢ s = 𝓝ˢ t
 ↔ s = t
-/
theorem injective_nhdsSet [T1Space X] : Function.Injective (𝓝ˢ : Set X → Filter X) := fun _ _ hst =>
  nhdsSet_inj_iff.mp hst
/-
**strictMono_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_nhdsSet [T1Space X] : StrictMono (𝓝ˢ : Set X -> Filter X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `monotone_nhdsSet`：monotone_nhdsSet : Monotone (𝓝ˢ : Set X -> Filter X)
· 使用定理 `injective_nhdsSet`：injective_nhdsSet [T1Space X] : Function.Injective (𝓝
ˢ : Set X -> Filter X)
-/
theorem strictMono_nhdsSet [T1Space X] : StrictMono (𝓝ˢ : Set X → Filter X) :=
  monotone_nhdsSet.strictMono_of_injective injective_nhdsSet

@[simp]
/-
**nhds_le_nhdsSet_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_le_nhdsSet_iff [T1Space X] {s : Set X} {x : X} : 𝓝 x <= 𝓝ˢ s ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `nhdsSet_le_iff`：nhdsSet_le_iff [T1Space X] {s t : Set X} : 𝓝ˢ s <= 𝓝ˢ t 
↔ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nhds_le_nhdsSet_iff [T1Space X] {s : Set X} {x : X} : 𝓝 x ≤ 𝓝ˢ s ↔ x ∈ s := by
  rw [← nhdsSet_singleton, nhdsSet_le_iff, singleton_subset_iff]

/-- Removing a non-isolated point from a dense set, one still obtains a dense set. -/
/-
**Dense.sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.sdiff_singleton [T1Space X] {s : Set X} (hs : Dense s) (x : X) [NeBo
t (𝓝[!=] x)] : Dense (s \ {x})
参数：hs : Dense s；x : X；𝓝[!=] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_of_isOpen_right`：Dense.inter_of_isOpen_right (hs : Dense s) 
(ht : Dense t) (hto : IsOpen t) : Dense (s inter t)
· 使用定理 `dense_compl_singleton`：dense_compl_singleton (x : X) [NeBot (𝓝[!=] x)] :
 Dense ({x}ᶜ : Set X)
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)

--- 原说明 ---
Removing a non-isolated point from a dense set, one still obtains a dense set.
-/
theorem Dense.sdiff_singleton [T1Space X] {s : Set X} (hs : Dense s) (x : X) [NeBot (𝓝[≠] x)] :
    Dense (s \ {x}) :=
  hs.inter_of_isOpen_right (dense_compl_singleton x) isOpen_compl_singleton

@[deprecated (since := "2026-06-03")] alias Dense.diff_singleton := Dense.sdiff_singleton

/-- Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set. -/
/-
**Dense.sdiff_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.sdiff_finset [T1Space X] [forall x : X, NeBot (𝓝[!=] x)] {s : Set X}
 (hs : Dense s) (t : Finset X) : Dense (s \ t)
参数：𝓝[!=] x；hs : Dense s；t : Finset X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
· 使用定理 `Dense.sdiff_singleton`：Dense.sdiff_singleton [T1Space X] {s : Set X} (hs
 : Dense s) (x : X) [NeBot (𝓝[!=] x)] : Dense (s \ {x})

--- 原说明 ---
Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set.
-/
theorem Dense.sdiff_finset [T1Space X] [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s)
    (t : Finset X) : Dense (s \ t) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hs
  | insert _ _ _ ih =>
    rw [Finset.coe_insert, ← union_singleton, ← sdiff_sdiff]
    exact ih.sdiff_singleton _

@[deprecated (since := "2026-06-03")] alias Dense.diff_finset := Dense.sdiff_finset

/-- Removing a finite set from a dense set in a space without isolated points, one still
obtains a dense set. -/
/-
**Dense.sdiff_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.sdiff_finite [T1Space X] [forall x : X, NeBot (𝓝[!=] x)] {s : Set X}
 (hs : Dense s) {t : Set X} (ht : t.Finite) : Dense (s \ t)
参数：𝓝[!=] x；hs : Dense s；ht : t.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Dense.sdiff_finset`：Dense.sdiff_finset [T1Space X] [forall x : X, NeBot 
(𝓝[!=] x)] {s : Set X} (hs : Dense s) (t : Finset X) : Dense (s \ t)

--- 原说明 ---
Removing a finite set from a dense set in a space without isolated points, one s
till
obtains a dense set.
-/
theorem Dense.sdiff_finite [T1Space X] [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s)
    {t : Set X} (ht : t.Finite) : Dense (s \ t) := by
  convert! hs.sdiff_finset ht.toFinset
  exact (Finite.coe_toFinset _).symm

@[deprecated (since := "2026-06-03")] alias Dense.diff_finite := Dense.sdiff_finite

/-- If a function to a `T1Space` tends to some limit `y` at some point `x`, then necessarily
`y = f x`. -/
/-
**eq_of_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {x : X} {
y : Y} (h : Tendsto f (𝓝 x) (𝓝 y)) : f x = y
参数：h : Tendsto f (𝓝 x) (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `compl_singleton_mem_nhds`：compl_singleton_mem_nhds [T1Space X] {x y : X}
 (h : y != x) : {x}ᶜ in 𝓝 y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)

--- 原说明 ---
If a function to a `T1Space` tends to some limit `y` at some point `x`, then nec
essarily
`y = f x`.
-/
theorem eq_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : f x = y :=
  by_contra fun hfa : f x ≠ y =>
    have fact₁ : {f x}ᶜ ∈ 𝓝 y := compl_singleton_mem_nhds hfa.symm
    have fact₂ : Tendsto f (pure x) (𝓝 y) := h.comp (tendsto_id'.2 <| pure_le_nhds x)
    fact₂ fact₁ (Eq.refl <| f x)
/-
**Filter.Tendsto.eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.eventually_ne {X} [TopologicalSpace Y] [T1Space Y] {g : X -
> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g l (𝓝 b₁)) (hb : b₁ != b₂) : fora
llᶠ z in l, g z != b₂
参数：hg : Tendsto g l (𝓝 b₁)；hb : b₁ != b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
-/
theorem Filter.Tendsto.eventually_ne {X} [TopologicalSpace Y] [T1Space Y] {g : X → Y}
    {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g l (𝓝 b₁)) (hb : b₁ ≠ b₂) : ∀ᶠ z in l, g z ≠ b₂ :=
  hg.eventually (isOpen_compl_singleton.eventually_mem hb)
/-
**ContinuousAt.eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.eventually_ne [TopologicalSpace Y] [T1Space Y] {g : X -> Y} {
x : X} {y : Y} (hg1 : ContinuousAt g x) (hg2 : g x != y) : forallᶠ z in 𝓝 x, g z
 != y
参数：hg1 : ContinuousAt g x；hg2 : g x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually_ne`：Filter.Tendsto.eventually_ne {X} [Topologi
calSpace Y] [T1Space Y] {g : X -> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g 
l (𝓝 b₁)) (hb : b₁…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
-/
theorem ContinuousAt.eventually_ne [TopologicalSpace Y] [T1Space Y] {g : X → Y} {x : X} {y : Y}
    (hg1 : ContinuousAt g x) (hg2 : g x ≠ y) : ∀ᶠ z in 𝓝 x, g z ≠ y :=
  hg1.tendsto.eventually_ne hg2
/-
**eventually_ne_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_ne_nhds [T1Space X] {a b : X} (h : a != b) : forallᶠ x in 𝓝 a, 
x != b
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
-/
theorem eventually_ne_nhds [T1Space X] {a b : X} (h : a ≠ b) : ∀ᶠ x in 𝓝 a, x ≠ b :=
  IsOpen.eventually_mem isOpen_ne h
/-
**eventually_ne_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_ne_nhdsWithin [T1Space X] {a b : X} {s : Set X} (h : a != b) : 
forallᶠ x in 𝓝[s] a, x != b
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `eventually_ne_nhds`：eventually_ne_nhds [T1Space X] {a b : X} (h : a != b
) : forallᶠ x in 𝓝 a, x != b
-/
theorem eventually_ne_nhdsWithin [T1Space X] {a b : X} {s : Set X} (h : a ≠ b) :
    ∀ᶠ x in 𝓝[s] a, x ≠ b :=
  Filter.Eventually.filter_mono nhdsWithin_le_nhds <| eventually_ne_nhds h
/-
**eventually_nhdsWithin_eventually_nhds_iff_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：eventually_nhdsWithin_eventually_nhds_iff_of_isOpen {s : Set X} {a : X} {p
 : X -> Prop} (hs : IsOpen s) : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝 y, p x) ↔ f
orallᶠ x in 𝓝[s] a, p x
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eventually_eventually_nhdsWithin`：eventually_eventually_nhdsWithin {a : 
α} {s : Set α} {p : α -> Prop} : (forallᶠ y in 𝓝[s] a, forallᶠ x in 𝓝[s] y, p x)
 ↔ forallᶠ x in 𝓝[s] a…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用定理 `IsOpen.nhdsWithin_eq`：IsOpen.nhdsWithin_eq {a : α} {s : Set α} (h : IsOp
en s) (ha : a in s) : 𝓝[s] a = 𝓝 a
-/
theorem eventually_nhdsWithin_eventually_nhds_iff_of_isOpen {s : Set X} {a : X} {p : X → Prop}
    (hs : IsOpen s) : (∀ᶠ y in 𝓝[s] a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝[s] a, p x := by
  nth_rw 2 [← eventually_eventually_nhdsWithin]
  constructor
  · intro h
    filter_upwards [h] with _ hy
    exact eventually_nhdsWithin_of_eventually_nhds hy
  · intro h
    filter_upwards [h, eventually_nhdsWithin_of_forall fun _ a ↦ a] with _ _ _
    simp_all [IsOpen.nhdsWithin_eq]

@[simp]
/-
**eventually_nhdsNE_eventually_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsNE_eventually_nhds_iff [T1Space X] {a : X} {p : X -> Prop} 
: (forallᶠ y in 𝓝[!=] a, forallᶠ x in 𝓝 y, p x) ↔ forallᶠ x in 𝓝[!=] a, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_nhdsWithin_eventually_nhds_iff_of_isOpen`：eventually_nhdsWith
in_eventually_nhds_iff_of_isOpen {s : Set X} {a : X} {p : X -> Prop} (hs : IsOpe
n s) : (forallᶠ y in 𝓝[s] a, forallᶠ x in…
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
-/
theorem eventually_nhdsNE_eventually_nhds_iff [T1Space X] {a : X} {p : X → Prop} :
    (∀ᶠ y in 𝓝[≠] a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝[≠] a, p x :=
  eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_ne
/-
**continuousWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_insert [TopologicalSpace Y] [T1Space X] {x y : X} {s : 
Set X} {f : X -> Y} : ContinuousWithinAt f (insert y s) x ↔ ContinuousWithinAt f
 s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `continuousWithinAt_insert_self`：continuousWithinAt_insert_self : Continu
ousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_insert [TopologicalSpace Y] [T1Space X]
    {x y : X} {s : Set X} {f : X → Y} :
    ContinuousWithinAt f (insert y s) x ↔ ContinuousWithinAt f s x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact continuousWithinAt_insert_self
  simp_rw [ContinuousWithinAt, nhdsWithin_insert_of_ne h]

alias ⟨ContinuousWithinAt.of_insert, ContinuousWithinAt.insert'⟩ := continuousWithinAt_insert

/-- See also `continuousWithinAt_sdiff_self` for the case `y = x` but not requiring `T1Space`. -/
/-
**continuousWithinAt_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_sdiff_singleton [TopologicalSpace Y] [T1Space X] {x y :
 X} {s : Set X} {f : X -> Y} : ContinuousWithinAt f (s \ {y}) x ↔ ContinuousWith
inAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_insert`：continuousWithinAt_insert [TopologicalSpace Y
] [T1Space X] {x y : X} {s : Set X} {f : X -> Y} : ContinuousWithinAt f (insert 
y s) x ↔ Contin…
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See also `continuousWithinAt_sdiff_self` for the case `y = x` but not requiring 
`T1Space`.
-/
theorem continuousWithinAt_sdiff_singleton [TopologicalSpace Y] [T1Space X]
    {x y : X} {s : Set X} {f : X → Y} :
    ContinuousWithinAt f (s \ {y}) x ↔ ContinuousWithinAt f s x := by
  rw [← continuousWithinAt_insert, insert_sdiff_singleton, continuousWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_singleton := continuousWithinAt_sdiff_singleton

/-- If two sets coincide locally around `x`, except maybe at `y`, then it is equivalent to be
continuous at `x` within one set or the other. -/
/-
**continuousWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_congr_set' [TopologicalSpace Y] [T1Space X] {x : X} {s 
t : Set X} {f : X -> Y} (y : X) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : ContinuousWithinAt f s
 x ↔ ContinuousWithinAt f t x
参数：y : X；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_insert_self`：continuousWithinAt_insert_self : Continu
ousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x
· 使用定理 `continuousWithinAt_congr_set`：continuousWithinAt_congr_set (h : s =ᶠ[𝓝 x
] t) : ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x
· 使用引理 `eventuallyEq_insert`：eventuallyEq_insert [T1Space X] {s t : Set X} {x y 
: X} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : (insert x s : Set X) =ᶠ[𝓝 x] (insert x t : Set X)

--- 原说明 ---
If two sets coincide locally around `x`, except maybe at `y`, then it is equival
ent to be
continuous at `x` within one set or the other.
-/
theorem continuousWithinAt_congr_set' [TopologicalSpace Y] [T1Space X]
    {x : X} {s t : Set X} {f : X → Y} (y : X) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x := by
  rw [← continuousWithinAt_insert_self (s := s), ← continuousWithinAt_insert_self (s := t)]
  exact continuousWithinAt_congr_set (eventuallyEq_insert h)
/-
**ContinuousWithinAt.eq_const_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.eq_const_of_mem_closure [TopologicalSpace Y] [T1Space Y
] {f : X -> Y} {s : Set X} {x : X} {c : Y} (h : ContinuousWithinAt f s x) (hx : 
x in closure s) (ht : forall y in s, f y = c) : f x = c
参数：h : ContinuousWithinAt f s x；hx : x in closure s；ht : forall y in s, f y = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `closure_singleton`：closure_singleton [T1Space X] {x : X} : closure ({x} 
: Set X) = {x}
· 使用定理 `ContinuousWithinAt.mem_closure`：ContinuousWithinAt.mem_closure {t : Set 
β} (h : ContinuousWithinAt f s x) (hx : x in closure s) (ht : MapsTo f s t) : f 
x in closure t
-/
theorem ContinuousWithinAt.eq_const_of_mem_closure [TopologicalSpace Y] [T1Space Y]
    {f : X → Y} {s : Set X} {x : X} {c : Y} (h : ContinuousWithinAt f s x) (hx : x ∈ closure s)
    (ht : ∀ y ∈ s, f y = c) : f x = c := by
  rw [← Set.mem_singleton_iff, ← closure_singleton]
  exact h.mem_closure hx ht
/-
**ContinuousWithinAt.eqOn_const_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.eqOn_const_closure [TopologicalSpace Y] [T1Space Y] {f 
: X -> Y} {s : Set X} {c : Y} (h : forall x in closure s, ContinuousWithinAt f s
 x) (ht : s.EqOn f (fun _ => c)) : (closure s).EqOn f (fun _ => c)
参数：h : forall x in closure s, ContinuousWithinAt f s x；ht : s.EqOn f (fun _ => c
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.eq_const_of_mem_closure`：ContinuousWithinAt.eq_const_
of_mem_closure [TopologicalSpace Y] [T1Space Y] {f : X -> Y} {s : Set X} {x : X}
 {c : Y} (h : ContinuousWithinAt…
-/
theorem ContinuousWithinAt.eqOn_const_closure [TopologicalSpace Y] [T1Space Y]
    {f : X → Y} {s : Set X} {c : Y} (h : ∀ x ∈ closure s, ContinuousWithinAt f s x)
    (ht : s.EqOn f (fun _ ↦ c)) : (closure s).EqOn f (fun _ ↦ c) := by
  intro x hx
  apply ContinuousWithinAt.eq_const_of_mem_closure (h x hx) hx ht

/-- To prove a function to a `T1Space` is continuous at some point `x`, it suffices to prove that
`f` admits *some* limit at `x`. -/
/-
**continuousAt_of_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X -> Y}
 {x : X} {y : Y} (h : Tendsto f (𝓝 x) (𝓝 y)) : ContinuousAt f x
参数：h : Tendsto f (𝓝 x) (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `eq_of_tendsto_nhds`：eq_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] 
{f : X -> Y} {x : X} {y : Y} (h : Tendsto f (𝓝 x) (𝓝 y)) : f x = y

--- 原说明 ---
To prove a function to a `T1Space` is continuous at some point `x`, it suffices 
to prove that
`f` admits *some* limit at `x`.
-/
theorem continuousAt_of_tendsto_nhds [TopologicalSpace Y] [T1Space Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝 x) (𝓝 y)) : ContinuousAt f x := by
  rwa [ContinuousAt, eq_of_tendsto_nhds h]

@[simp]
/-
**tendsto_const_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_nhds_iff [T1Space X] {l : Filter Y} [NeBot l] {c d : X} : Te
ndsto (fun _ => c) l (𝓝 d) ↔ c = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_const`：map_const [NeBot f] {c : β} : (f.map fun _ => c) = pur
e c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_const_nhds_iff [T1Space X] {l : Filter Y} [NeBot l] {c d : X} :
    Tendsto (fun _ => c) l (𝓝 d) ↔ c = d := by simp_rw [Tendsto, Filter.map_const, pure_le_nhds_iff]

/-- A point with a finite neighborhood has to be isolated. -/
/-
**isOpen_singleton_of_finite_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_singleton_of_finite_mem_nhds [T1Space X] (x : X) {s : Set X} (hs : 
s in 𝓝 x) (hsf : s.Finite) : IsOpen ({x} : Set X)
参数：x : X；hs : s in 𝓝 x；hsf : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Set.Finite.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Spa
ce X] {s : Set X}, s.Finite → IsClosed s
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `subset_interior_iff_isOpen`：subset_interior_iff_isOpen : s subseteq inte
rior s ↔ IsOpen s
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x

--- 原说明 ---
A point with a finite neighborhood has to be isolated.
-/
theorem isOpen_singleton_of_finite_mem_nhds [T1Space X] (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) (hsf : s.Finite) : IsOpen ({x} : Set X) := by
  have A : {x} ⊆ s := by simp only [singleton_subset_iff, mem_of_mem_nhds hs]
  have B : IsClosed (s \ {x}) := (hsf.subset sdiff_subset).isClosed
  have C : (s \ {x})ᶜ ∈ 𝓝 x := B.isOpen_compl.mem_nhds fun h => h.2 rfl
  have D : {x} ∈ 𝓝 x := by simpa only [← sdiff_eq, sdiff_sdiff_cancel_left A] using inter_mem hs C
  rwa [← mem_interior_iff_mem_nhds, ← singleton_subset_iff, subset_interior_iff_isOpen] at D

/-- If the punctured neighborhoods of a point form a nontrivial filter, then any neighborhood is
infinite. -/
/-
**infinite_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infinite_of_mem_nhds {X} [TopologicalSpace X] [T1Space X] (x : X) [hx : Ne
Bot (𝓝[!=] x)] {s : Set X} (hs : s in 𝓝 x) : Set.Infinite s
参数：x : X；𝓝[!=] x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.ne'`：∀ {α : Type u_1} {f : Filter α} [self : f.NeBot], f ≠ 
⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_singleton_iff_punctured_nhds`：isOpen_singleton_iff_punctured_nhds
 (x : X) : IsOpen ({x} : Set X) ↔ 𝓝[!=] x = ⊥
· 使用定理 `isOpen_singleton_of_finite_mem_nhds`：isOpen_singleton_of_finite_mem_nhds
 [T1Space X] (x : X) {s : Set X} (hs : s in 𝓝 x) (hsf : s.Finite) : IsOpen ({x} 
: Set X)

--- 原说明 ---
If the punctured neighborhoods of a point form a nontrivial filter, then any nei
ghborhood is
infinite.
-/
theorem infinite_of_mem_nhds {X} [TopologicalSpace X] [T1Space X] (x : X) [hx : NeBot (𝓝[≠] x)]
    {s : Set X} (hs : s ∈ 𝓝 x) : Set.Infinite s := by
  refine fun hsf => hx.1 ?_
  rw [← isOpen_singleton_iff_punctured_nhds]
  exact isOpen_singleton_of_finite_mem_nhds x hs hsf
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [DiscreteTopology X] : T1Space X where t1 _ := isClosed_discrete _
/-
**Finite.instDiscreteTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finite.instDiscreteTopology [T1Space X] [Finite X] : DiscreteTopology X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_forall_isClosed`：discreteTopology_iff_forall_isClos
ed [TopologicalSpace α] : DiscreteTopology α ↔ forall s : Set α, IsClosed s
· 使用定理 `Set.Finite.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Spa
ce X] {s : Set X}, s.Finite → IsClosed s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
instance Finite.instDiscreteTopology [T1Space X] [Finite X] : DiscreteTopology X :=
  discreteTopology_iff_forall_isClosed.mpr (·.toFinite.isClosed)
/-
**Set.Finite.isDiscrete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs : s.Finite) : IsDiscrete
 s
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
-/
lemma Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs : s.Finite) : IsDiscrete s :=
  ⟨@Finite.instDiscreteTopology _ _ _ hs.to_subtype⟩
/-
**Set.Finite.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.continuousOn [T1Space X] [TopologicalSpace Y] {s : Set X} (hs :
 s.Finite) (f : X -> Y) : ContinuousOn f s
参数：hs : s.Finite；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
-/
theorem Set.Finite.continuousOn [T1Space X] [TopologicalSpace Y] {s : Set X} (hs : s.Finite)
    (f : X → Y) : ContinuousOn f s := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : Finite s := hs
  fun_prop
/-
**SeparationQuotient.t1Space_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparationQuotient.t1Space_iff : T1Space (SeparationQuotient X) ↔ R0Space 
X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `r0Space_iff`：∀ (X : Type u) [inst : TopologicalSpace X], R0Space X ↔ Std
.Symm Specializes
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
· 使用定理 `specializes_refl`：specializes_refl (x : X) : x ⤳ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
· 使用定理 `inseparable_iff_specializes_and`：inseparable_iff_specializes_and : (x ~ᵢ
 y) ↔ x ⤳ y ∧ y ⤳ x
-/
theorem SeparationQuotient.t1Space_iff : T1Space (SeparationQuotient X) ↔ R0Space X := by
  rw [r0Space_iff, ((t1Space_TFAE (SeparationQuotient X)).out 0 9 :)]
  refine ⟨fun h ↦ ⟨fun x y xspecy ↦ ?_⟩, ?_⟩
  · rw [← IsInducing.specializes_iff isInducing_mk, h xspecy] at *
  · -- TODO is there are better way to do this,
    -- so the case split produces `SeparationQuotient.mk` directly, rather than `Quot.mk`?
    -- Currently we need the `change` statement to recover this.
    rintro h ⟨x⟩ ⟨y⟩ sxspecsy
    change mk _ = mk _
    have xspecy : x ⤳ y := isInducing_mk.specializes_iff.mp sxspecsy
    have yspecx : y ⤳ x := h.symm x y xspecy
    rw [mk_eq_mk, inseparable_iff_specializes_and]
    exact ⟨xspecy, yspecx⟩
/-
**isClosed_inter_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_inter_singleton [T1Space X] {A : Set X} {a : X} : IsClosed (A int
er {a})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Subsingleton.isClosed`：Set.Subsingleton.isClosed [T1Space X] {s : Se
t X} (hs : s.Subsingleton) : IsClosed s
· 使用定理 `Set.Subsingleton.inter_singleton`：∀ {α : Type u} {a : α} {s : Set α}, (s
 ∩ {a}).Subsingleton
-/
lemma isClosed_inter_singleton [T1Space X] {A : Set X} {a : X} : IsClosed (A ∩ {a}) :=
  Subsingleton.inter_singleton.isClosed
/-
**isClosed_singleton_inter** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_singleton_inter [T1Space X] {A : Set X} {a : X} : IsClosed ({a} i
nter A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Subsingleton.isClosed`：Set.Subsingleton.isClosed [T1Space X] {s : Se
t X} (hs : s.Subsingleton) : IsClosed s
· 使用定理 `Set.Subsingleton.singleton_inter`：∀ {α : Type u} {a : α} {s : Set α}, ({
a} ∩ s).Subsingleton
-/
lemma isClosed_singleton_inter [T1Space X] {A : Set X} {a : X} : IsClosed ({a} ∩ A) :=
  Subsingleton.singleton_inter.isClosed
/-
**singleton_mem_nhdsWithin_of_mem_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：singleton_mem_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {
x : X} (hx : x in s) : {x} in 𝓝[s] x
参数：hs : IsDiscrete s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用引理 `isDiscrete_iff_discreteTopology`：isDiscrete_iff_discreteTopology : IsDis
crete s ↔ DiscreteTopology s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `nhdsWithin_eq_map_subtype_coe`：nhdsWithin_eq_map_subtype_coe {s : Set α}
 {a : α} (h : a in s) : 𝓝[s] a = map ((↑) : s -> α) (𝓝 ⟨a, h⟩)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
-/
theorem singleton_mem_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x ∈ s) : {x} ∈ 𝓝[s] x := by
  rw [isDiscrete_iff_discreteTopology] at hs
  have : ({⟨x, hx⟩} : Set s) ∈ 𝓝 (⟨x, hx⟩ : s) := by simp [nhds_discrete]
  simpa only [nhdsWithin_eq_map_subtype_coe hx, image_singleton] using
    @image_mem_map _ _ _ ((↑) : s → X) _ this

/-- The neighbourhoods filter of `x` within `s`, under the discrete topology, is equal to
the pure `x` filter (which is the principal filter at the singleton `{x}`.) -/
/-
**nhdsWithin_of_mem_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x
 in s) : 𝓝[s] x = pure x
参数：hs : IsDiscrete s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_pure_iff`：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {
a} in f
· 使用定理 `singleton_mem_nhdsWithin_of_mem_discrete`：singleton_mem_nhdsWithin_of_me
m_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s) : {x} in 𝓝[s] x
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a

--- 原说明 ---
The neighbourhoods filter of `x` within `s`, under the discrete topology, is equ
al to
the pure `x` filter (which is the principal filter at the singleton `{x}`.)
-/
theorem nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x ∈ s) :
    𝓝[s] x = pure x :=
  (le_pure_iff.2 <| singleton_mem_nhdsWithin_of_mem_discrete hs hx).antisymm (pure_le_nhdsWithin hx)
/-
**Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p :
 ι -> Prop} {t : ι -> Set X} {s : Set X} (hs : IsDiscrete s) {x : X} (hb : (𝓝 x)
.HasBasis p t) (hx : x in s) : exists i, p i ∧ t i inter s = {x}
参数：hs : IsDiscrete s；hb : (𝓝 x).HasBasis p t；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `singleton_mem_nhdsWithin_of_mem_discrete`：singleton_mem_nhdsWithin_of_me
m_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s) : {x} in 𝓝[s] x
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
-/
theorem Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p : ι → Prop}
    {t : ι → Set X} {s : Set X} (hs : IsDiscrete s) {x : X} (hb : (𝓝 x).HasBasis p t)
    (hx : x ∈ s) : ∃ i, p i ∧ t i ∩ s = {x} := by
  rcases (nhdsWithin_hasBasis hb s).mem_iff.1 (singleton_mem_nhdsWithin_of_mem_discrete hs hx) with
    ⟨i, hi, hix⟩
  exact ⟨i, hi, hix.antisymm <| singleton_subset_iff.2 ⟨mem_of_mem_nhds <| hb.mem_of_mem hi, hx⟩⟩

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`. -/
/-
**nhds_inter_eq_singleton_of_mem_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x
 : X} (hx : x in s) : exists U in 𝓝 x, U inter s = {x}
参数：hs : IsDiscrete s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete`：Filter.HasBas
is.exists_inter_eq_singleton_of_mem_discrete {ι : Type*} {p : ι -> Prop} {t : ι 
-> Set X} {s : Set X} (hs : IsDiscrete s) {x : …
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id

--- 原说明 ---
A point `x` in a discrete subset `s` of a topological space admits a neighbourho
od
that only meets `s` at `x`.
-/
theorem nhds_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x ∈ s) : ∃ U ∈ 𝓝 x, U ∩ s = {x} := by
  simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hs hx

/-- Let `x` be a point in a discrete subset `s` of a topological space, then there exists an open
set that only meets `s` at `x`. -/
/-
**isOpen_inter_eq_singleton_of_mem_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) 
{x : X} (hx : x in s) : exists U : Set X, IsOpen U ∧ U inter s = {x}
参数：hs : IsDiscrete s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_inter_eq_singleton_of_mem_discrete`：nhds_inter_eq_singleton_of_mem_
discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s) : exists U in 𝓝 x
, U inter s = {x}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t

--- 原说明 ---
Let `x` be a point in a discrete subset `s` of a topological space, then there e
xists an open
set that only meets `s` at `x`.
-/
theorem isOpen_inter_eq_singleton_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X}
    (hx : x ∈ s) : ∃ U : Set X, IsOpen U ∧ U ∩ s = {x} := by
  obtain ⟨U, hU_nhds, hU_inter⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  obtain ⟨t, ht_sub, ht_open, ht_x⟩ := mem_nhds_iff.mp hU_nhds
  grind

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (i.e. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
/-
**disjoint_nhdsWithin_of_mem_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X
} (hx : x in s) : exists U in 𝓝[!=] x, Disjoint U s
参数：hs : IsDiscrete s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_inter_eq_singleton_of_mem_discrete`：nhds_inter_eq_singleton_of_mem_
discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x in s) : exists U in 𝓝 x
, U inter s = {x}
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅

--- 原说明 ---
For point `x` in a discrete subset `s` of a topological space, there is a set `U
`
such that
1. `U` is a punctured neighborhood of `x` (i.e. `U ∪ {x}` is a neighbourhood of 
`x`),
2. `U` is disjoint from `s`.
-/
theorem disjoint_nhdsWithin_of_mem_discrete {s : Set X} (hs : IsDiscrete s) {x : X} (hx : x ∈ s) :
    ∃ U ∈ 𝓝[≠] x, Disjoint U s :=
  let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hs hx
  ⟨{x}ᶜ ∩ V, inter_mem_nhdsWithin _ h,
    disjoint_iff_inter_eq_empty.mpr (by rw [inter_assoc, h', compl_inter_self])⟩
/-
**isClosedEmbedding_update** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedEmbedding_update {ι : Type*} {β : ι -> Type*} [DecidableEq ι] [(i 
: ι) -> TopologicalSpace (β i)] (x : (i : ι) -> β i) (i : ι) [(i : ι) -> T1Space
 (β i)] : IsClosedEmbedding (update x i)
参数：i : ι；β i；x : (i : ι) -> β i；i : ι；i : ι；β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap`：∀ {X : T
ype u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topolo
gicalSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `Continuous.update`：Continuous.update [DecidableEq ι] (hf : Continuous f)
 (i : ι) {g : X -> A i} (hg : Continuous g) : Continuous fun a => update (f a) i
 (g a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Function.update_injective`：update_injective (f : forall a, β a) (a' : α)
 : Injective (update f a')
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.update_image`：update_image [DecidableEq ι] (x : (i : ι) -> β i) (i :
 ι) (s : Set (β i)) : update x i '' s = Set.univ.pi (update (fun j => {x j}) i s
)
· 使用定理 `isClosed_set_pi`：isClosed_set_pi {i : Set ι} {s : forall a, Set (A a)} (
hs : forall a in i, IsClosed (s a)) : IsClosed (pi i s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isClosedEmbedding_update {ι : Type*} {β : ι → Type*}
    [DecidableEq ι] [(i : ι) → TopologicalSpace (β i)]
    (x : (i : ι) → β i) (i : ι) [(i : ι) → T1Space (β i)] :
    IsClosedEmbedding (update x i) := by
  refine .of_continuous_injective_isClosedMap (continuous_const.update i continuous_id)
    (update_injective x i) fun s hs ↦ ?_
  rw [update_image]
  apply isClosed_set_pi
  simp [forall_update_iff, hs]
/-
**nhdsNE_le_cofinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhdsNE_le_cofinite {α : Type*} [TopologicalSpace α] [T1Space α] (a : α) : 
𝓝[!=] a <= cofinite
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_cofinite_iff_compl_singleton_mem`：le_cofinite_iff_compl_single
ton_mem : l <= cofinite ↔ forall x, {x}ᶜ in l
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `eventually_ne_nhdsWithin`：eventually_ne_nhdsWithin [T1Space X] {a b : X}
 {s : Set X} (h : a != b) : forallᶠ x in 𝓝[s] a, x != b
-/
lemma nhdsNE_le_cofinite {α : Type*} [TopologicalSpace α] [T1Space α] (a : α) :
    𝓝[≠] a ≤ cofinite := by
  refine le_cofinite_iff_compl_singleton_mem.mpr fun x ↦ ?_
  rcases eq_or_ne a x with rfl | hx
  exacts [self_mem_nhdsWithin, eventually_ne_nhdsWithin hx]
/-
**Function.update_eventuallyEq_nhdsNE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.update_eventuallyEq_nhdsNE {α β : Type*} [TopologicalSpace α] [T1
Space α] [DecidableEq α] (f : α -> β) (a a' : α) (b : β) : Function.update f a b
 =ᶠ[𝓝[!=] a'] f
参数：f : α -> β；a a' : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用引理 `Function.update_eventuallyEq_cofinite`：Function.update_eventuallyEq_cofi
nite [DecidableEq α] (f : α -> β) (a : α) (b : β) : Function.update f a b =ᶠ[cof
inite] f
· 使用引理 `nhdsNE_le_cofinite`：nhdsNE_le_cofinite {α : Type*} [TopologicalSpace α] 
[T1Space α] (a : α) : 𝓝[!=] a <= cofinite
-/
lemma Function.update_eventuallyEq_nhdsNE
    {α β : Type*} [TopologicalSpace α] [T1Space α] [DecidableEq α] (f : α → β) (a a' : α) (b : β) :
    Function.update f a b =ᶠ[𝓝[≠] a'] f :=
  (Function.update_eventuallyEq_cofinite f a b).filter_mono (nhdsNE_le_cofinite a')

/-! ### R₁ (preregular) spaces -/

section R1Space

/-- A topological space is called a *preregular* (a.k.a. R₁) space,
if any two topologically distinguishable points have disjoint neighbourhoods. -/
@[mk_iff r1Space_iff_specializes_or_disjoint_nhds]
/-
**R1Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_3) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is called a *preregular* (a.k.a. R₁) space,
if any two topologically distinguishable points have disjoint neighbourhoods.
-/
class R1Space (X : Type*) [TopologicalSpace X] : Prop where
  specializes_or_disjoint_nhds (x y : X) : Specializes x y ∨ Disjoint (𝓝 x) (𝓝 y)

export R1Space (specializes_or_disjoint_nhds)

variable [R1Space X] {x y : X}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : R0Space X where
  specializes_symm.symm _ _ h := (specializes_or_disjoint_nhds _ _).resolve_right <| fun hd ↦
    h.not_disjoint hd.symm
/-
**disjoint_nhds_nhds_iff_not_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_nhds_iff_not_specializes : Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.not_disjoint`：Specializes.not_disjoint (h : x ⤳ y) : ¬Disjoi
nt (𝓝 x) (𝓝 y)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `R1Space.specializes_or_disjoint_nhds`：∀ {X : Type u_3} {inst : Topologic
alSpace X} [self : R1Space X] (x y : X), x ⤳ y ∨ Disjoint (nhds x) (nhds y)
-/
theorem disjoint_nhds_nhds_iff_not_specializes : Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y :=
  ⟨fun hd hspec ↦ hspec.not_disjoint hd, (specializes_or_disjoint_nhds _ _).resolve_left⟩
/-
**specializes_iff_not_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：specializes_iff_not_disjoint : x ⤳ y ↔ ¬Disjoint (𝓝 x) (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `disjoint_nhds_nhds_iff_not_specializes`：disjoint_nhds_nhds_iff_not_speci
alizes : Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y
-/
theorem specializes_iff_not_disjoint : x ⤳ y ↔ ¬Disjoint (𝓝 x) (𝓝 y) :=
  disjoint_nhds_nhds_iff_not_specializes.not_left.symm
/-
**disjoint_nhds_nhds_iff_not_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_nhds_iff_not_inseparable : Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparab
le x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_nhds_nhds_iff_not_specializes`：disjoint_nhds_nhds_iff_not_speci
alizes : Disjoint (𝓝 x) (𝓝 y) ↔ ¬x ⤳ y
· 使用定理 `specializes_iff_inseparable`：specializes_iff_inseparable : x ⤳ y ↔ Insep
arable x y
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_nhds_nhds_iff_not_inseparable : Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparable x y := by
  rw [disjoint_nhds_nhds_iff_not_specializes, specializes_iff_inseparable]
/-
**r1Space_iff_inseparable_or_disjoint_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：r1Space_iff_inseparable_or_disjoint_nhds {X : Type*} [TopologicalSpace X] 
: R1Space X ↔ forall x y : X, Inseparable x y ∨ Disjoint (𝓝 x) (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `Specializes.inseparable`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R
0Space X] {x y : X}, x ⤳ y → Inseparable x y
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `R1Space.specializes_or_disjoint_nhds`：∀ {X : Type u_3} {inst : Topologic
alSpace X} [self : R1Space X] (x y : X), x ⤳ y ∨ Disjoint (nhds x) (nhds y)
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
-/
theorem r1Space_iff_inseparable_or_disjoint_nhds {X : Type*} [TopologicalSpace X] :
    R1Space X ↔ ∀ x y : X, Inseparable x y ∨ Disjoint (𝓝 x) (𝓝 y) :=
  ⟨fun _h x y ↦ (specializes_or_disjoint_nhds x y).imp_left Specializes.inseparable, fun h ↦
    ⟨fun x y ↦ (h x y).imp_left Inseparable.specializes⟩⟩
/-
**Inseparable.of_nhds_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.of_nhds_neBot {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) : Inseparable 
x y
参数：h : NeBot (𝓝 x ⊓ 𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `r1Space_iff_inseparable_or_disjoint_nhds`：r1Space_iff_inseparable_or_dis
joint_nhds {X : Type*} [TopologicalSpace X] : R1Space X ↔ forall x y : X, Insepa
rable x y ∨ Disjoint (𝓝 x) (𝓝 …
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
-/
theorem Inseparable.of_nhds_neBot {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) :
    Inseparable x y :=
  (r1Space_iff_inseparable_or_disjoint_nhds.mp ‹_› _ _).resolve_right fun h' => h.ne h'.eq_bot
/-
**r1_separation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：r1_separation {x y : X} (h : ¬Inseparable x y) : exists u v : Set X, IsOpe
n u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
参数：h : ¬Inseparable x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `disjoint_nhds_nhds_iff_not_inseparable`：disjoint_nhds_nhds_iff_not_insep
arable : Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparable x y
-/
theorem r1_separation {x y : X} (h : ¬Inseparable x y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
  rw [← disjoint_nhds_nhds_iff_not_inseparable,
    (nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)] at h
  obtain ⟨u, ⟨hxu, hu⟩, v, ⟨hyv, hv⟩, huv⟩ := h
  exact ⟨u, v, hu, hv, hxu, hyv, huv⟩

/-- Limits are unique up to separability.

A weaker version of `tendsto_nhds_unique` for `R1Space`. -/
/-
**tendsto_nhds_unique_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_unique_inseparable {f : Y -> X} {l : Filter Y} {a b : X} [NeB
ot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : Inseparable a b
参数：ha : Tendsto f l (𝓝 a)；hb : Tendsto f l (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.of_nhds_neBot`：Inseparable.of_nhds_neBot {x y : X} (h : NeBo
t (𝓝 x ⊓ 𝓝 y)) : Inseparable x y
· 使用定理 `Filter.neBot_of_le`：neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f 
<= g) : NeBot g
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b

--- 原说明 ---
Limits are unique up to separability.

A weaker version of `tendsto_nhds_unique` for `R1Space`.
-/
theorem tendsto_nhds_unique_inseparable {f : Y → X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : Inseparable a b :=
  .of_nhds_neBot <| neBot_of_le <| le_inf ha hb
/-
**isClosed_setOfPred_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_specializes : IsClosed { p : X × X | p.1 ⤳ p.2 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isClosed_setOfPred_specializes : IsClosed { p : X × X | p.1 ⤳ p.2 } := by
  simp only [← isOpen_compl_iff, compl_ofPred, ← disjoint_nhds_nhds_iff_not_specializes,
    isOpen_setOfPred_disjoint_nhds_nhds]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_specializes := isClosed_setOfPred_specializes
/-
**isClosed_setOfPred_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_inseparable : IsClosed { p : X × X | Inseparable p.1 p.
2 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
-/
theorem isClosed_setOfPred_inseparable : IsClosed { p : X × X | Inseparable p.1 p.2 } := by
  simp only [← specializes_iff_inseparable, isClosed_setOfPred_specializes]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_inseparable := isClosed_setOfPred_inseparable

/-- In an R₁ space, a point belongs to the closure of a compact set `K`
if and only if it is topologically inseparable from some point of `K`. -/
/-
**IsCompact.mem_closure_iff_exists_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.mem_closure_iff_exists_inseparable {K : Set X} (hK : IsCompact K
) : y in closure K ↔ exists x in K, Inseparable x y
参数：hK : IsCompact K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCompact.disjoint_nhdsSet_right`：IsCompact.disjoint_nhdsSet_right {l : 
Filter X} (hs : IsCompact s) : Disjoint l (𝓝ˢ s) ↔ forall x in s, Disjoint l (𝓝 
x)
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `disjoint_nhds_nhds_iff_not_inseparable`：disjoint_nhds_nhds_iff_not_insep
arable : Disjoint (𝓝 x) (𝓝 y) ↔ ¬Inseparable x y
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `principal_le_nhdsSet`：principal_le_nhdsSet : 𝓟 s <= 𝓝ˢ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_closed_iff`：mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s
) : x in s ↔ y in s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
In an R₁ space, a point belongs to the closure of a compact set `K`
if and only if it is topologically inseparable from some point of `K`.
-/
theorem IsCompact.mem_closure_iff_exists_inseparable {K : Set X} (hK : IsCompact K) :
    y ∈ closure K ↔ ∃ x ∈ K, Inseparable x y := by
  refine ⟨fun hy ↦ ?_, fun ⟨x, hxK, hxy⟩ ↦
    (hxy.mem_closed_iff isClosed_closure).1 <| subset_closure hxK⟩
  contrapose! hy
  have : Disjoint (𝓝 y) (𝓝ˢ K) := hK.disjoint_nhdsSet_right.2 fun x hx ↦
    (disjoint_nhds_nhds_iff_not_inseparable.2 (hy x hx)).symm
  simpa only [disjoint_iff, notMem_closure_iff_nhdsWithin_eq_bot]
    using! this.mono_right principal_le_nhdsSet
/-
**IsCompact.closure_eq_biUnion_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closure_eq_biUnion_inseparable {K : Set X} (hK : IsCompact K) : 
closure K = ⋃ x in K, {y | Inseparable x y}
参数：hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.mem_closure_iff_exists_inseparable`：IsCompact.mem_closure_iff_
exists_inseparable {K : Set X} (hK : IsCompact K) : y in closure K ↔ exists x in
 K, Inseparable x y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsCompact.closure_eq_biUnion_inseparable {K : Set X} (hK : IsCompact K) :
    closure K = ⋃ x ∈ K, {y | Inseparable x y} := by
  ext; simp [hK.mem_closure_iff_exists_inseparable]

/-- In an R₁ space, the closure of a compact set is the union of the closures of its points. -/
/-
**IsCompact.closure_eq_biUnion_closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closure_eq_biUnion_closure_singleton {K : Set X} (hK : IsCompact
 K) : closure K = ⋃ x in K, closure {x}
参数：hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.closure_eq_biUnion_inseparable`：IsCompact.closure_eq_biUnion_i
nseparable {K : Set X} (hK : IsCompact K) : closure K = ⋃ x in K, {y | Inseparab
le x y}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In an R₁ space, the closure of a compact set is the union of the closures of its
 points.
-/
theorem IsCompact.closure_eq_biUnion_closure_singleton {K : Set X} (hK : IsCompact K) :
    closure K = ⋃ x ∈ K, closure {x} := by
  simp only [hK.closure_eq_biUnion_inseparable, ← specializes_iff_inseparable,
    specializes_iff_mem_closure, ofPred_mem_eq]

/-- In an R₁ space, if a compact set `K` is contained in an open set `U`,
then its closure is also contained in `U`. -/
/-
**IsCompact.closure_subset_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closure_subset_of_isOpen {K : Set X} (hK : IsCompact K) {U : Set
 X} (hU : IsOpen U) (hKU : K subseteq U) : closure K subseteq U
参数：hK : IsCompact K；hU : IsOpen U；hKU : K subseteq U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.closure_eq_biUnion_inseparable`：IsCompact.closure_eq_biUnion_i
nseparable {K : Set X} (hK : IsCompact K) : closure K = ⋃ x in K, {y | Inseparab
le x y}
· 使用定理 `Set.iUnion₂_subset_iff`：iUnion₂_subset_iff {s : forall i, κ i -> Set α} 
{t : Set α} : ⋃ (i) (j), s i j subseteq t ↔ forall i j, s i j subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s

--- 原说明 ---
In an R₁ space, if a compact set `K` is contained in an open set `U`,
then its closure is also contained in `U`.
-/
theorem IsCompact.closure_subset_of_isOpen {K : Set X} (hK : IsCompact K)
    {U : Set X} (hU : IsOpen U) (hKU : K ⊆ U) : closure K ⊆ U := by
  rw [hK.closure_eq_biUnion_inseparable, iUnion₂_subset_iff]
  exact fun x hx y hxy ↦ (hxy.mem_open_iff hU).1 (hKU hx)

/-- The closure of a compact set in an R₁ space is a compact set. -/
/-
**IsCompact.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X] {K : Set X}, IsCo
mpact K → IsCompact (closure K)
参数：closure K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_of_finite_subcover`：isCompact_of_finite_subcover (h : forall {
ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subseteq ⋃ i, U i) 
-> exists t : Fins…
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)

--- 原说明 ---
The closure of a compact set in an R₁ space is a compact set.
-/
protected theorem IsCompact.closure {K : Set X} (hK : IsCompact K) : IsCompact (closure K) := by
  refine isCompact_of_finite_subcover fun U hUo hKU ↦ ?_
  rcases hK.elim_finite_subcover U hUo (subset_closure.trans hKU) with ⟨t, ht⟩
  exact ⟨t, hK.closure_subset_of_isOpen (isOpen_biUnion fun _ _ ↦ hUo _) ht⟩
/-
**IsCompact.closure_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.closure_of_subset {s K : Set X} (hK : IsCompact K) (h : s subset
eq K) : IsCompact (closure s)
参数：hK : IsCompact K；h : s subseteq K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem IsCompact.closure_of_subset {s K : Set X} (hK : IsCompact K) (h : s ⊆ K) :
    IsCompact (closure s) :=
  hK.closure.of_isClosed_subset isClosed_closure (closure_mono h)

@[simp]
/-
**exists_isCompact_superset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isCompact_superset_iff {s : Set X} : (exists K, IsCompact K ∧ s sub
seteq K) ↔ IsCompact (closure s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem exists_isCompact_superset_iff {s : Set X} :
    (∃ K, IsCompact K ∧ s ⊆ K) ↔ IsCompact (closure s) :=
  ⟨fun ⟨_K, hK, hsK⟩ => hK.closure_of_subset hsK, fun h => ⟨closure s, h, subset_closure⟩⟩

/-- If `K` and `L` are disjoint compact sets in an R₁ topological space
and `L` is also closed, then `K` and `L` have disjoint neighborhoods. -/
/-
**SeparatedNhds.of_isCompact_isCompact_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparatedNhds.of_isCompact_isCompact_isClosed {K L : Set X} (hK : IsCompac
t K) (hL : IsCompact L) (h'L : IsClosed L) (hd : Disjoint K L) : SeparatedNhds K
 L
参数：hK : IsCompact K；hL : IsCompact L；h'L : IsClosed L；hd : Disjoint K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.disjoint_nhdsSet_left`：IsCompact.disjoint_nhdsSet_left {l : Fi
lter X} (hs : IsCompact s) : Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsCompact.disjoint_nhdsSet_right`：IsCompact.disjoint_nhdsSet_right {l : 
Filter X} (hs : IsCompact s) : Disjoint l (𝓝ˢ s) ↔ forall x in s, Disjoint l (𝓝 
x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Inseparable.mem_closed_iff`：mem_closed_iff (h : x ~ᵢ y) (hs : IsClosed s
) : x in s ↔ y in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t

--- 原说明 ---
If `K` and `L` are disjoint compact sets in an R₁ topological space
and `L` is also closed, then `K` and `L` have disjoint neighborhoods.
-/
theorem SeparatedNhds.of_isCompact_isCompact_isClosed {K L : Set X} (hK : IsCompact K)
    (hL : IsCompact L) (h'L : IsClosed L) (hd : Disjoint K L) : SeparatedNhds K L := by
  simp_rw [separatedNhds_iff_disjoint, hK.disjoint_nhdsSet_left, hL.disjoint_nhdsSet_right,
    disjoint_nhds_nhds_iff_not_inseparable]
  intro x hx y hy h
  exact absurd ((h.mem_closed_iff h'L).2 hy) <| disjoint_left.1 hd hx

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
/-
**IsCompact.binary_compact_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.binary_compact_cover {K U V : Set X} (hK : IsCompact K) (hU : Is
Open U) (hV : IsOpen V) (h2K : K subseteq U union V) : exists K₁ K₂ : Set X, IsC
ompact K₁ ∧ IsCompact K₂ ∧ K₁ subseteq U ∧ K₂ subseteq V ∧ K = K₁ union K₂
参数：hK : IsCompact K；hU : IsOpen U；hV : IsOpen V；h2K : K subseteq U union V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `SeparatedNhds.of_isCompact_isCompact_isClosed`：SeparatedNhds.of_isCompac
t_isCompact_isClosed {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (h'L : 
IsClosed L) (hd : Disjoint K L) : S…
· 使用定理 `IsCompact.diff`：IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCo
mpact (s \ t)
· 使用定理 `IsClosed.sdiff`：IsClosed.sdiff (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClo
sed (s \ t)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Set.sdiff_inter_sdiff`：sdiff_inter_sdiff : s \ t inter (s \ u) = s \ (t 
union u)
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `SeparatedNhds.mono`：mono (h : SeparatedNhds s₂ t₂) (hs : s₁ subseteq s₂)
 (ht : t₁ subseteq t₂) : SeparatedNhds s₁ t₁
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.sdiff_subset_comm`：sdiff_subset_comm {s t u : Set α} : s \ t subsete
q u ↔ s \ u subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_inter`：sdiff_inter {s t u : Set α} : s \ (t inter u) = s \ t u
nion s \ u
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s

--- 原说明 ---
If a compact set is covered by two open sets, then we can cover it by two compac
t subsets.
-/
theorem IsCompact.binary_compact_cover {K U V : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V) (h2K : K ⊆ U ∪ V) :
    ∃ K₁ K₂ : Set X, IsCompact K₁ ∧ IsCompact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ := by
  have hK' : IsCompact (closure K) := hK.closure
  have : SeparatedNhds (closure K \ U) (closure K \ V) := by
    apply SeparatedNhds.of_isCompact_isCompact_isClosed (hK'.diff hU) (hK'.diff hV)
      (isClosed_closure.sdiff hV)
    rw [disjoint_iff_inter_eq_empty, sdiff_inter_sdiff, sdiff_eq_empty]
    exact hK.closure_subset_of_isOpen (hU.union hV) h2K
  have : SeparatedNhds (K \ U) (K \ V) :=
    this.mono (sdiff_subset_sdiff_left (subset_closure)) (sdiff_subset_sdiff_left (subset_closure))
  rcases this with ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩
  exact ⟨K \ O₁, K \ O₂, hK.diff h1O₁, hK.diff h1O₂, sdiff_subset_comm.mp h2O₁,
    sdiff_subset_comm.mp h2O₂, by rw [← sdiff_inter, hO.inter_eq, sdiff_empty]⟩

/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
/-
**IsCompact.finite_compact_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.finite_compact_cover {s : Set X} (hs : IsCompact s) {ι : Type*} 
(t : Finset ι) (U : ι -> Set X) (hU : forall i in t, IsOpen (U i)) (hsC : s subs
eteq ⋃ i in t, U i) : exists K : ι -> Set X, (forall i, IsCompact (K i)) ∧ (fora
ll i, K i subseteq U i) ∧ s = ⋃ i in t, K i
参数：hs : IsCompact s；t : Finset ι；U : ι -> Set X；hU : forall i in t, IsOpen (U i)
；hsC : s subseteq ⋃ i in t, U i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.iUnion_false`：iUnion_false {s : False -> Set α} : iUnion s = ∅
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsCompact.binary_compact_cover`：IsCompact.binary_compact_cover {K U V : 
Set X} (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V) (h2K : K subseteq U un
ion V) : exists K₁ K…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `Finset.set_biUnion_insert`：set_biUnion_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.set_biUnion_insert_update`：set_biUnion_insert_update {x : α} {t :
 Finset α} (f : α -> Set β) {s : Set β} (hx : x ∉ t) : ⋃ i in insert x t, @updat
e _ _ _ f x s i = s un…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For every finite open cover `Uᵢ` of a compact set, there exists a compact cover 
`Kᵢ ⊆ Uᵢ`.
-/
theorem IsCompact.finite_compact_cover {s : Set X} (hs : IsCompact s) {ι : Type*}
    (t : Finset ι) (U : ι → Set X) (hU : ∀ i ∈ t, IsOpen (U i)) (hsC : s ⊆ ⋃ i ∈ t, U i) :
    ∃ K : ι → Set X, (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U i) ∧ s = ⋃ i ∈ t, K i := by
  classical
  induction t using Finset.induction generalizing U s with
  | empty =>
    refine ⟨fun _ => ∅, fun _ => isCompact_empty, fun i => empty_subset _, ?_⟩
    simpa only [subset_empty_iff, Finset.notMem_empty, iUnion_false, iUnion_empty] using hsC
  | insert x t hx ih =>
    simp only [Finset.set_biUnion_insert] at hsC
    simp only [Finset.forall_mem_insert] at hU
    have hU' : ∀ i ∈ t, IsOpen (U i) := fun i hi => hU.2 i hi
    rcases hs.binary_compact_cover hU.1 (isOpen_biUnion hU') hsC with
      ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩
    rcases ih h1K₂ U hU' h2K₂ with ⟨K, h1K, h2K, h3K⟩
    refine ⟨update K x K₁, ?_, ?_, ?_⟩
    · intro i
      rcases eq_or_ne i x with rfl | hi
      · simp only [update_self, h1K₁]
      · simp only [update_of_ne hi, h1K]
    · intro i
      rcases eq_or_ne i x with rfl | hi
      · simp only [update_self, h2K₁]
      · simp only [update_of_ne hi, h2K]
    · simp only [Finset.set_biUnion_insert_update _ hx, hK, h3K]
/-
**R1Space.of_continuous_specializes_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：R1Space.of_continuous_specializes_imp [TopologicalSpace Y] {f : Y -> X} (h
c : Continuous f) (hspec : forall x y, f x ⤳ f y -> x ⤳ y) : R1Space Y where spe
cializes_or_disjoint_nhds x y
参数：hc : Continuous f；hspec : forall x y, f x ⤳ f y -> x ⤳ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Filter.Tendsto.disjoint`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {la
₁ la₂ : Filter α} {lb₁ lb₂ : Filter β},   Filter.Tendsto f la₁ lb₁ → Disjoint lb
₁ lb₂ → Filte…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `R1Space.specializes_or_disjoint_nhds`：∀ {X : Type u_3} {inst : Topologic
alSpace X} [self : R1Space X] (x y : X), x ⤳ y ∨ Disjoint (nhds x) (nhds y)
-/
theorem R1Space.of_continuous_specializes_imp [TopologicalSpace Y] {f : Y → X} (hc : Continuous f)
    (hspec : ∀ x y, f x ⤳ f y → x ⤳ y) : R1Space Y where
  specializes_or_disjoint_nhds x y := (specializes_or_disjoint_nhds (f x) (f y)).imp (hspec x y) <|
    ((hc.tendsto _).disjoint · (hc.tendsto _))
/-
**Topology.IsInducing.r1Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.r1Space [TopologicalSpace Y] {f : Y -> X} (hf : IsIndu
cing f) : R1Space Y
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `R1Space.of_continuous_specializes_imp`：R1Space.of_continuous_specializes
_imp [TopologicalSpace Y] {f : Y -> X} (hc : Continuous f) (hspec : forall x y, 
f x ⤳ f y -> x ⤳ y) : R1Spa…
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
-/
theorem Topology.IsInducing.r1Space [TopologicalSpace Y] {f : Y → X} (hf : IsInducing f) :
    R1Space Y := .of_continuous_specializes_imp hf.continuous fun _ _ ↦ hf.specializes_iff.1
/-
**R1Space.induced** 是 Mathlib 中的一个定理，位于命名空间 `R1Space`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [R1Space X] (f
 : Y → X), R1Space Y
参数：f : Y → X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.r1Space`：Topology.IsInducing.r1Space [TopologicalSpa
ce Y] {f : Y -> X} (hf : IsInducing f) : R1Space Y
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
-/
protected theorem R1Space.induced (f : Y → X) : @R1Space Y (.induced f ‹_›) :=
  @IsInducing.r1Space _ _ _ _ (.induced f _) f (.induced f)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : X → Prop) : R1Space (Subtype p) := .induced _
/-
**R1Space.sInf** 是 Mathlib 中的一个定理，位于命名空间 `R1Space`。
形式化陈述：∀ {X : Type u_3} {T : Set (TopologicalSpace X)}, (∀ t ∈ T, R1Space X) → R1
Space X
参数：TopologicalSpace X；∀ t ∈ T, R1Space X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_sInf`：nhds_sInf {s : Set (TopologicalSpace α)} {a : α} : @nhds α (s
Inf s) a = ⨅ t in s, @nhds α t a
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `R1Space.specializes_or_disjoint_nhds`：∀ {X : Type u_3} {inst : Topologic
alSpace X} [self : R1Space X] (x y : X), x ⤳ y ∨ Disjoint (nhds x) (nhds y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
-/
protected theorem R1Space.sInf {X : Type*} {T : Set (TopologicalSpace X)}
    (hT : ∀ t ∈ T, @R1Space X t) : @R1Space X (sInf T) := by
  let _ := sInf T
  refine ⟨fun x y ↦ ?_⟩
  simp only [Specializes, nhds_sInf]
  by_cases! hTd : ∃ t ∈ T, Disjoint (@nhds X t x) (@nhds X t y)
  · rcases hTd with ⟨t, htT, htd⟩
    exact .inr <| htd.mono (iInf₂_le t htT) (iInf₂_le t htT)
  · exact .inl <| iInf₂_mono fun t ht ↦ ((hT t ht).1 x y).resolve_right (hTd t ht)
/-
**R1Space.iInf** 是 Mathlib 中的一个定理，位于命名空间 `R1Space`。
形式化陈述：∀ {ι : Type u_3} {X : Type u_4} {t : ι → TopologicalSpace X}, (∀ (i : ι), 
R1Space X) → R1Space X
参数：∀ (i : ι), R1Space X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `R1Space.sInf`：∀ {X : Type u_3} {T : Set (TopologicalSpace X)}, (∀ t ∈ T,
 R1Space X) → R1Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected theorem R1Space.iInf {ι X : Type*} {t : ι → TopologicalSpace X}
    (ht : ∀ i, @R1Space X (t i)) : @R1Space X (iInf t) :=
  .sInf <| forall_mem_range.2 ht

set_option backward.isDefEq.respectTransparency false in
/-
**R1Space.inf** 是 Mathlib 中的一个定理，位于命名空间 `R1Space`。
形式化陈述：∀ {X : Type u_3} {t₁ t₂ : TopologicalSpace X}, R1Space X → R1Space X → R1S
pace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用定理 `R1Space.iInf`：∀ {ι : Type u_3} {X : Type u_4} {t : ι → TopologicalSpace 
X}, (∀ (i : ι), R1Space X) → R1Space X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected theorem R1Space.inf {X : Type*} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @R1Space X t₁) (h₂ : @R1Space X t₂) : @R1Space X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  apply R1Space.iInf
  simp [*]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace Y] [R1Space Y] : R1Space (X × Y) :=
  .inf (.induced _) (.induced _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, R1Space (X i)] :
    R1Space (∀ i, X i) :=
  .iInf fun _ ↦ .induced _
/-
**exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds {X Y : Type*} [Topo
logicalSpace X] [TopologicalSpace Y] [R1Space Y] {f : X -> Y} {x : X} {K : Set X
} {s : Set Y} (hf : Continuous f) (hs : s in 𝓝 (f x)) (hKc : IsCompact K) (hKx :
 K in 𝓝 x) : exists L in 𝓝 x, IsCompact L ∧ MapsTo f L s
参数：hf : Continuous f；hs : s in 𝓝 (f x)；hKc : IsCompact K；hKx : K in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.diff`：IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCo
mpact (s \ t)
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `IsCompact.disjoint_nhdsSet_right`：IsCompact.disjoint_nhdsSet_right {l : 
Filter X} (hs : IsCompact s) : Disjoint l (𝓝ˢ s) ↔ forall x in s, Disjoint l (𝓝 
x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Filter.sdiff_mem`：sdiff_mem {s t : Set α} (hs : s in f) (ht : tᶜ in f) :
 s \ t in f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y] {f : X → Y} {x : X}
    {K : Set X} {s : Set Y} (hf : Continuous f) (hs : s ∈ 𝓝 (f x)) (hKc : IsCompact K)
    (hKx : K ∈ 𝓝 x) : ∃ L ∈ 𝓝 x, IsCompact L ∧ MapsTo f L s := by
  have hc : IsCompact (f '' K \ interior s) := (hKc.image hf).diff isOpen_interior
  obtain ⟨U, V, Uo, Vo, hxU, hV, hd⟩ : SeparatedNhds {f x} (f '' K \ interior s) := by
    simp_rw [separatedNhds_iff_disjoint, nhdsSet_singleton, hc.disjoint_nhdsSet_right,
      disjoint_nhds_nhds_iff_not_inseparable]
    rintro y ⟨-, hys⟩ hxy
    refine hys <| (hxy.mem_open_iff isOpen_interior).1 ?_
    rwa [mem_interior_iff_mem_nhds]
  refine ⟨K \ f ⁻¹' V, sdiff_mem hKx ?_, hKc.diff <| Vo.preimage hf, fun y hy ↦ ?_⟩
  · filter_upwards [hf.continuousAt <| Uo.mem_nhds (hxU rfl)] with x hx
      using Set.disjoint_left.1 hd hx
  · by_contra hys
    exact hy.2 (hV ⟨mem_image_of_mem _ hy.1, notMem_subset interior_subset hys⟩)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {X Y : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [TopologicalSpace Y] [R1Space Y] : LocallyCompactPair X Y where
  exists_mem_nhds_isCompact_mapsTo hf hs :=
    let ⟨_K, hKc, hKx⟩ := exists_compact_mem_nhds _
    exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds hf hs hKc hKx

/-- If a point in an R₁ space has a compact neighborhood,
then it has a basis of compact closed neighborhoods. -/
/-
**IsCompact.isCompact_isClosed_basis_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isCompact_isClosed_basis_nhds {x : X} {L : Set X} (hLc : IsCompa
ct L) (hxL : L in 𝓝 x) : (𝓝 x).HasBasis (fun K => K in 𝓝 x ∧ IsCompact K ∧ IsClo
sed K) (·)
参数：hLc : IsCompact L；hxL : L in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.hasBasis_self`：hasBasis_self {l : Filter α} {P : Set α -> Prop} :
 HasBasis l (fun s => s in l ∧ P s) id ↔ forall t in l, exists r in l, P r ∧ r s
ubseteq t
· 使用定理 `exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds`：exists_mem_nhds_
isCompact_mapsTo_of_isCompact_mem_nhds {X Y : Type*} [TopologicalSpace X] [Topol
ogicalSpace Y] [R1Space Y] {f : X -> Y} {x :…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `interior_mem_nhds`：interior_mem_nhds : interior s in 𝓝 x ↔ s in 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsCompact.closure_subset_of_isOpen`：IsCompact.closure_subset_of_isOpen {
K : Set X} (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K subseteq U) :
 closure K subseteq U
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
If a point in an R₁ space has a compact neighborhood,
then it has a basis of compact closed neighborhoods.
-/
theorem IsCompact.isCompact_isClosed_basis_nhds {x : X} {L : Set X} (hLc : IsCompact L)
    (hxL : L ∈ 𝓝 x) : (𝓝 x).HasBasis (fun K ↦ K ∈ 𝓝 x ∧ IsCompact K ∧ IsClosed K) (·) :=
  hasBasis_self.2 fun _U hU ↦
    let ⟨K, hKx, hKc, hKU⟩ := exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
      continuous_id (interior_mem_nhds.2 hU) hLc hxL
    ⟨closure K, mem_of_superset hKx subset_closure, ⟨hKc.closure, isClosed_closure⟩,
      (hKc.closure_subset_of_isOpen isOpen_interior hKU).trans interior_subset⟩

/-- In an R₁ space, the filters `coclosedCompact` and `cocompact` are equal. -/
@[simp]
/-
**Filter.coclosedCompact_eq_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.coclosedCompact_eq_cocompact : coclosedCompact X = cocompact X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Filter.cocompact_le_coclosedCompact`：cocompact_le_coclosedCompact : coco
mpact X <= coclosedCompact X

--- 原说明 ---
In an R₁ space, the filters `coclosedCompact` and `cocompact` are equal.
-/
theorem Filter.coclosedCompact_eq_cocompact : coclosedCompact X = cocompact X := by
  refine le_antisymm ?_ cocompact_le_coclosedCompact
  rw [hasBasis_coclosedCompact.le_basis_iff hasBasis_cocompact]
  exact fun K hK ↦ ⟨closure K, ⟨isClosed_closure, hK.closure⟩, compl_subset_compl.2 subset_closure⟩

/-- In an R₁ space, the bornologies `relativelyCompact` and `inCompact` are equal. -/
@[simp]
/-
**Bornology.relativelyCompact_eq_inCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.relativelyCompact_eq_inCompact : Bornology.relativelyCompact X =
 Bornology.inCompact X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Bornology.ext`：Bornology.ext (t t' : Bornology α) (h_cobounded : @Bornol
ogy.cobounded α t = @Bornology.cobounded α t') : t = t'
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `Filter.coclosedCompact_eq_cocompact`：Filter.coclosedCompact_eq_cocompact
 : coclosedCompact X = cocompact X

--- 原说明 ---
In an R₁ space, the bornologies `relativelyCompact` and `inCompact` are equal.
-/
theorem Bornology.relativelyCompact_eq_inCompact :
    Bornology.relativelyCompact X = Bornology.inCompact X :=
  Bornology.ext _ _ Filter.coclosedCompact_eq_cocompact

/-!
### Lemmas about a weakly locally compact R₁ space

In fact, a space with these properties is locally compact and regular.
Some lemmas are formulated using the latter assumptions below.
-/

variable [WeaklyLocallyCompactSpace X]

/-- In a (weakly) locally compact R₁ space, compact closed neighborhoods of a point `x`
form a basis of neighborhoods of `x`. -/
/-
**isCompact_isClosed_basis_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_isClosed_basis_nhds (x : X) : (𝓝 x).HasBasis (fun K => K in 𝓝 x 
∧ IsCompact K ∧ IsClosed K) (·)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `IsCompact.isCompact_isClosed_basis_nhds`：IsCompact.isCompact_isClosed_ba
sis_nhds {x : X} {L : Set X} (hLc : IsCompact L) (hxL : L in 𝓝 x) : (𝓝 x).HasBas
is (fun K => K in 𝓝 x ∧ IsCom…

--- 原说明 ---
In a (weakly) locally compact R₁ space, compact closed neighborhoods of a point 
`x`
form a basis of neighborhoods of `x`.
-/
theorem isCompact_isClosed_basis_nhds (x : X) :
    (𝓝 x).HasBasis (fun K => K ∈ 𝓝 x ∧ IsCompact K ∧ IsClosed K) (·) :=
  let ⟨_L, hLc, hLx⟩ := exists_compact_mem_nhds x
  hLc.isCompact_isClosed_basis_nhds hLx

/-- In a (weakly) locally compact R₁ space, each point admits a compact closed neighborhood. -/
/-
**exists_mem_nhds_isCompact_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_nhds_isCompact_isClosed (x : X) : exists K in 𝓝 x, IsCompact K 
∧ IsClosed K
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.ex_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} {
p : ι → Prop} {s : ι → Set α}, l.HasBasis p s → ∃ i, p i
· 使用定理 `isCompact_isClosed_basis_nhds`：isCompact_isClosed_basis_nhds (x : X) : (
𝓝 x).HasBasis (fun K => K in 𝓝 x ∧ IsCompact K ∧ IsClosed K) (·)

--- 原说明 ---
In a (weakly) locally compact R₁ space, each point admits a compact closed neigh
borhood.
-/
theorem exists_mem_nhds_isCompact_isClosed (x : X) : ∃ K ∈ 𝓝 x, IsCompact K ∧ IsClosed K :=
  (isCompact_isClosed_basis_nhds x).ex_mem

-- see Note [lower instance priority]
/-- A weakly locally compact R₁ space is locally compact. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weakly locally compact R₁ space is locally compact.
-/
instance (priority := 80) WeaklyLocallyCompactSpace.locallyCompactSpace : LocallyCompactSpace X :=
  .of_hasBasis isCompact_isClosed_basis_nhds fun _ _ ⟨_, h, _⟩ ↦ h

/-- In a weakly locally compact R₁ space,
every compact set has an open neighborhood with compact closure. -/
/-
**exists_isOpen_superset_and_isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isOpen_superset_and_isCompact_closure {K : Set X} (hK : IsCompact K
) : exists V, IsOpen V ∧ K subseteq V ∧ IsCompact (closure V)
参数：hK : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_compact_superset`：exists_compact_superset [WeaklyLocallyCompactSp
ace X] {K : Set X} (hK : IsCompact K) : exists K', IsCompact K' ∧ K subseteq int
erior K'
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
In a weakly locally compact R₁ space,
every compact set has an open neighborhood with compact closure.
-/
theorem exists_isOpen_superset_and_isCompact_closure {K : Set X} (hK : IsCompact K) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) := by
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩
  exact ⟨interior K', isOpen_interior, hKK', hK'.closure_of_subset interior_subset⟩

/-- In a weakly locally compact R₁ space,
every point has an open neighborhood with compact closure. -/
/-
**exists_isOpen_mem_isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isOpen_mem_isCompact_closure (x : X) : exists U : Set X, IsOpen U ∧
 x in U ∧ IsCompact (closure U)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_isOpen_superset_and_isCompact_closure`：exists_isOpen_superset_and
_isCompact_closure {K : Set X} (hK : IsCompact K) : exists V, IsOpen V ∧ K subse
teq V ∧ IsCompact (closure V)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)

--- 原说明 ---
In a weakly locally compact R₁ space,
every point has an open neighborhood with compact closure.
-/
theorem exists_isOpen_mem_isCompact_closure (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) := by
  simpa only [singleton_subset_iff]
    using exists_isOpen_superset_and_isCompact_closure isCompact_singleton

end R1Space

end Separation

