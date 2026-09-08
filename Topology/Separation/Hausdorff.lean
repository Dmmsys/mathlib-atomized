/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Separation.Basic

/-!
# T₂ and T₂.₅ spaces.

This file defines the T₂ (Hausdorff) condition, which is the most commonly-used among the various
separation axioms, and the related T₂.₅ condition.

## Main definitions

* `T2Space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`. T₂ implies T₁ and R₁.
* `T25Space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
  T₂.₅ implies T₂.

See `Mathlib/Topology/Separation/Regular.lean` for regular, T₃, etc. spaces; and
`Mathlib/Topology/Separation/GDelta.lean` for the definitions of `PerfectlyNormalSpace` and
`T6Space`.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_isClosed_diagonal`: A space is T₂ iff the `diagonal` of `X` (that is, the set of all
  points of the form `(a, a) : X × X`) is closed under the product topology.
* `separatedNhds_of_finset_finset`: Any two disjoint finsets are `SeparatedNhds`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `Topology.IsEmbedding.t2Space`)
* `Set.EqOn.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `IsCompact.isClosed`: All compact sets are closed.
* `WeaklyLocallyCompactSpace.locallyCompactSpace`: If a topological space is both
  weakly locally compact (i.e., each point has a compact neighbourhood)
  and is T₂, then it is locally compact.
* `totallySeparatedSpace_of_t1_of_basis_clopen`: If `X` has a clopen basis, then
  it is a `TotallySeparatedSpace`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.
* `T2Quotient`: the largest T2 quotient of a given topological space.

If the space is also compact:

* `normalOfCompactT2`: A compact T₂ space is a `NormalSpace`.
* `connectedComponent_eq_iInter_isClopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `TotallyDisconnectedSpace`
  is equivalent to being a `TotallySeparatedSpace`.
* `ConnectedComponents.t2`: `ConnectedComponents X` is T₂ for `X` T₂ and compact.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]

-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff]
/-
**T2Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms.
-/
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v

/-- Two different points can be separated by open sets. -/
/-
**t2_separation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2_separation [T2Space X] {x y : X} (h : x != y) : exists u v : Set X, IsO
pen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.t2`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T2Space X
],   Pairwise fun x y => ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u
…

--- 原说明 ---
Two different points can be separated by open sets.
-/
theorem t2_separation [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  T2Space.t2 h

-- todo: use this as a definition?
/-
**t2Space_iff_disjoint_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2Space_iff_disjoint_nhds : T2Space X ↔ Pairwise fun x y : X => Disjoint (
𝓝 x) (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `t2Space_iff`：∀ (X : Type u) [inst : TopologicalSpace X],   T2Space X ↔ P
airwise fun x y => ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t2Space_iff_disjoint_nhds : T2Space X ↔ Pairwise fun x y : X => Disjoint (𝓝 x) (𝓝 y) := by
  refine (t2Space_iff X).trans (forall₃_congr fun x y _ => ?_)
  simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y), ← exists_and_left,
    and_assoc, and_comm, and_left_comm]

@[simp]
/-
**disjoint_nhds_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint (𝓝 x) (𝓝 y) ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t2Space_iff_disjoint_nhds`：t2Space_iff_disjoint_nhds : T2Space X ↔ Pairw
ise fun x y : X => Disjoint (𝓝 x) (𝓝 y)
-/
theorem disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint (𝓝 x) (𝓝 y) ↔ x ≠ y :=
  ⟨fun hd he => by simp [he, nhds_neBot.ne] at hd, (t2Space_iff_disjoint_nhds.mp ‹_› ·)⟩
/-
**pairwise_disjoint_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwise_disjoint_nhds [T2Space X] : Pairwise (Disjoint on (𝓝 : X -> Filte
r X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_nhds_nhds`：disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint 
(𝓝 x) (𝓝 y) ↔ x != y
-/
theorem pairwise_disjoint_nhds [T2Space X] : Pairwise (Disjoint on (𝓝 : X → Filter X)) := fun _ _ =>
  disjoint_nhds_nhds.2
/-
**Set.pairwiseDisjoint_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X] (s : Set X), s.Pa
irwiseDisjoint nhds
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用定理 `pairwise_disjoint_nhds`：pairwise_disjoint_nhds [T2Space X] : Pairwise (D
isjoint on (𝓝 : X -> Filter X))
-/
protected theorem Set.pairwiseDisjoint_nhds [T2Space X] (s : Set X) : s.PairwiseDisjoint 𝓝 :=
  pairwise_disjoint_nhds.set_pairwise s

/-- Points of a finite set can be separated by open sets from each other. -/
/-
**Set.Finite.t2_separation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.t2_separation [T2Space X] {s : Set X} (hs : s.Finite) : exists 
U : X -> Set X, (forall x, x in U x ∧ IsOpen (U x)) ∧ s.PairwiseDisjoint U
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.exists_mem_filter_basis`：∀ {α : Type u_1} {I : Type
 u_6} {l : I → Filter α} {ι : I → Sort u_7} {p : (i : I) → ι i → Prop}   {s : (i
 : I) → ι i → Set α} {S : Set I}, …
· 使用定理 `Set.pairwiseDisjoint_nhds`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[T2Space X] (s : Set X), s.PairwiseDisjoint nhds
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s

--- 原说明 ---
Points of a finite set can be separated by open sets from each other.
-/
theorem Set.Finite.t2_separation [T2Space X] {s : Set X} (hs : s.Finite) :
    ∃ U : X → Set X, (∀ x, x ∈ U x ∧ IsOpen (U x)) ∧ s.PairwiseDisjoint U :=
  s.pairwiseDisjoint_nhds.exists_mem_filter_basis hs nhds_basis_opens

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) T2Space.t1Space [T2Space X] : T1Space X :=
  t1Space_iff_disjoint_pure_nhds.mpr fun _ _ hne =>
    (disjoint_nhds_nhds.2 hne).mono_left <| pure_le_nhds _

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) T2Space.r1Space [T2Space X] : R1Space X :=
  ⟨fun x y ↦ (eq_or_ne x y).imp specializes_of_eq disjoint_nhds_nhds.2⟩
/-
**SeparationQuotient.t2Space_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparationQuotient.t2Space_iff : T2Space (SeparationQuotient X) ↔ R1Space 
X
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.disjoint_comap_iff`：disjoint_comap_iff (h : Surjective m) : Disjo
int (comap m g₁) (comap m g₂) ↔ Disjoint g₁ g₂
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `SeparationQuotient.comap_mk_nhds_mk`：comap_mk_nhds_mk : comap mk (𝓝 (mk 
x)) = 𝓝 x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem SeparationQuotient.t2Space_iff : T2Space (SeparationQuotient X) ↔ R1Space X := by
  simp only [t2Space_iff_disjoint_nhds, Pairwise, surjective_mk.forall₂, ne_eq, mk_eq_mk,
    r1Space_iff_inseparable_or_disjoint_nhds, ← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk,
    ← or_iff_not_imp_left]
/-
**SeparationQuotient.t2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SeparationQuotient.t2Space [R1Space X] : T2Space (SeparationQuotient X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparationQuotient.t2Space_iff`：SeparationQuotient.t2Space_iff : T2Space
 (SeparationQuotient X) ↔ R1Space X
-/
instance SeparationQuotient.t2Space [R1Space X] : T2Space (SeparationQuotient X) :=
  t2Space_iff.2 ‹_›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 80) [R1Space X] [T0Space X] : T2Space X :=
  t2Space_iff_disjoint_nhds.2 fun _x _y hne ↦ disjoint_nhds_nhds_iff_not_inseparable.2 fun hxy ↦
    hne hxy.eq
/-
**R1Space.t2Space_iff_t0Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：R1Space.t2Space_iff_t0Space [R1Space X] : T2Space X ↔ T0Space X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `instT2SpaceOfR1SpaceOfT0Space`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [R1Space X] [T0Space X], T2Space X
-/
theorem R1Space.t2Space_iff_t0Space [R1Space X] : T2Space X ↔ T0Space X := by
  constructor <;> intro <;> infer_instance

/-- A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter. -/
/-
**t2_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2_iff_nhds : T2Space X ↔ forall {x y : X}, NeBot (𝓝 x ⊓ 𝓝 y) -> x = y
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A space is T₂ iff the neighbourhoods of distinct points generate the bottom filt
er.
-/
theorem t2_iff_nhds : T2Space X ↔ ∀ {x y : X}, NeBot (𝓝 x ⊓ 𝓝 y) → x = y := by
  simp only [t2Space_iff_disjoint_nhds, disjoint_iff, neBot_iff, Ne, not_imp_comm, Pairwise]
/-
**eq_of_nhds_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_nhds_neBot [T2Space X] {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) : x = y
参数：h : NeBot (𝓝 x ⊓ 𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t2_iff_nhds`：t2_iff_nhds : T2Space X ↔ forall {x y : X}, NeBot (𝓝 x ⊓ 𝓝 
y) -> x = y
-/
theorem eq_of_nhds_neBot [T2Space X] {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) : x = y :=
  t2_iff_nhds.mp ‹_› h
/-
**t2Space_iff_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2Space_iff_nhds : T2Space X ↔ Pairwise fun x y : X => exists U in 𝓝 x, ex
ists V in 𝓝 y, Disjoint U V
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t2Space_iff_nhds :
    T2Space X ↔ Pairwise fun x y : X => ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y, Disjoint U V := by
  simp only [t2Space_iff_disjoint_nhds, Filter.disjoint_iff, Pairwise]
/-
**t2_separation_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2_separation_nhds [T2Space X] {x y : X} (h : x != y) : exists u v, u in 𝓝
 x ∧ v in 𝓝 y ∧ Disjoint u v
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t2_separation`：t2_separation [T2Space X] {x y : X} (h : x != y) : exists
 u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem t2_separation_nhds [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ Disjoint u v :=
  let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h
  ⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩
/-
**t2_separation_compact_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2_separation_compact_nhds [LocallyCompactSpace X] [T2Space X] {x y : X} (
h : x != y) : exists u v, u in 𝓝 x ∧ v in 𝓝 y ∧ IsCompact u ∧ IsCompact v ∧ Disj
oint u v
参数：h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `compact_basis_nhds`：compact_basis_nhds [LocallyCompactSpace X] (x : X) :
 (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_nhds_nhds`：disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint 
(𝓝 x) (𝓝 y) ↔ x != y
-/
theorem t2_separation_compact_nhds [LocallyCompactSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ IsCompact u ∧ IsCompact v ∧ Disjoint u v := by
  simpa only [exists_prop, ← exists_and_left, and_comm, and_assoc, and_left_comm] using
    ((compact_basis_nhds x).disjoint_iff (compact_basis_nhds y)).1 (disjoint_nhds_nhds.2 h)
/-
**t2_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2_iff_ultrafilter : T2Space X ↔ forall {x y : X} (f : Ultrafilter X), ↑f 
<= 𝓝 x -> ↑f <= 𝓝 y -> x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `t2_iff_nhds`：t2_iff_nhds : T2Space X ↔ forall {x y : X}, NeBot (𝓝 x ⊓ 𝓝 
y) -> x = y
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
theorem t2_iff_ultrafilter :
    T2Space X ↔ ∀ {x y : X} (f : Ultrafilter X), ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y :=
  t2_iff_nhds.trans <| by simp only [← exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp]
/-
**t2_iff_isClosed_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2_iff_isClosed_diagonal : T2Space X ↔ IsClosed (diagonal X)
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem t2_iff_isClosed_diagonal : T2Space X ↔ IsClosed (diagonal X) := by
  simp only [t2Space_iff_disjoint_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds, Prod.forall,
    nhds_prod_eq, compl_diagonal_mem_prod, mem_compl_iff, mem_diagonal_iff, Pairwise]

@[closedness ., grind .]
/-
**isClosed_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `t2_iff_isClosed_diagonal`：t2_iff_isClosed_diagonal : T2Space X ↔ IsClose
d (diagonal X)
-/
theorem isClosed_diagonal [T2Space X] : IsClosed (diagonal X) :=
  t2_iff_isClosed_diagonal.mp ‹_›
/-
**t2Space_iff_of_isOpenQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2Space_iff_of_isOpenQuotientMap [TopologicalSpace Y] {π : X -> Y} (h : Is
OpenQuotientMap π) : T2Space Y ↔ IsClosed {q : X × X | π q.1 = π q.2}
参数：h : IsOpenQuotientMap π。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `t2_iff_isClosed_diagonal`：t2_iff_isClosed_diagonal : T2Space X ↔ IsClose
d (diagonal X)
· 使用定理 `IsOpenQuotientMap.prodMap`：IsOpenQuotientMap.prodMap {f : X -> Y} {g : Z
 -> W} (hf : IsOpenQuotientMap f) (hg : IsOpenQuotientMap g) : IsOpenQuotientMap
 (Prod.map f g)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `IsOpenQuotientMap.continuous`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Continuous f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `IsOpenQuotientMap.isOpenMap`：∀ {X : Type u} {Y : Type v} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f → 
IsOpenMap f
-/
theorem t2Space_iff_of_isOpenQuotientMap [TopologicalSpace Y] {π : X → Y}
    (h : IsOpenQuotientMap π) : T2Space Y ↔ IsClosed {q : X × X | π q.1 = π q.2} := by
  rw [t2_iff_isClosed_diagonal]
  replace h := IsOpenQuotientMap.prodMap h h
  refine ⟨fun H ↦ H.preimage h.continuous, fun H ↦ ?_⟩
  simp_rw [← isOpen_compl_iff] at H ⊢
  convert! h.isOpenMap _ H
  exact (h.surjective.image_preimage _).symm
/-
**tendsto_nhds_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : Filter Y} {a b : X} [NeB
ot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b
参数：ha : Tendsto f l (𝓝 a)；hb : Tendsto f l (𝓝 b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `tendsto_nhds_unique_inseparable`：tendsto_nhds_unique_inseparable {f : Y 
-> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto 
f l (𝓝 b)) : Insepara…
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
-/
theorem tendsto_nhds_unique [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  (tendsto_nhds_unique_inseparable ha hb).eq
/-
**tendsto_nhds_unique'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_unique' [T2Space X] {f : Y -> X} {l : Filter Y} {a b : X} (_ 
: NeBot l) (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b
参数：_ : NeBot l；ha : Tendsto f l (𝓝 a)；hb : Tendsto f l (𝓝 b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
-/
theorem tendsto_nhds_unique' [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} (_ : NeBot l)
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb
/-
**tendsto_nhds_unique_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_unique_of_eventuallyEq [T2Space X] {f g : Y -> X} {l : Filter
 Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg :
 f =ᶠ[l] g) : a = b
参数：ha : Tendsto f l (𝓝 a)；hb : Tendsto g l (𝓝 b)；hfg : f =ᶠ[l] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
-/
theorem tendsto_nhds_unique_of_eventuallyEq [T2Space X] {f g : Y → X} {l : Filter Y} {a b : X}
    [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) : a = b :=
  tendsto_nhds_unique (ha.congr' hfg) hb
/-
**tendsto_nhds_unique_of_frequently_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_unique_of_frequently_eq [T2Space X] {f g : Y -> X} {l : Filte
r Y} {a b : X} (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : existsᶠ 
x in l, f x = g x) : a = b
参数：ha : Tendsto f l (𝓝 a)；hb : Tendsto g l (𝓝 b)；hfg : existsᶠ x in l, f x = g x
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_diagonal`：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)
-/
theorem tendsto_nhds_unique_of_frequently_eq [T2Space X] {f g : Y → X} {l : Filter Y} {a b : X}
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : ∃ᶠ x in l, f x = g x) : a = b :=
  have : ∃ᶠ z : X × X in 𝓝 (a, b), z.1 = z.2 := (ha.prodMk_nhds hb).frequently hfg
  not_not.1 fun hne => this (isClosed_diagonal.isOpen_compl.mem_nhds hne)

/-- If `s` and `t` are compact sets in a T₂ space, then the set neighborhoods filter of `s ∩ t`
is the infimum of set neighborhoods filters for `s` and `t`.

For general sets, only the `≤` inequality holds, see `nhdsSet_inter_le`. -/
/-
**IsCompact.nhdsSet_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.nhdsSet_inter_eq [T2Space X] {s t : Set X} (hs : IsCompact s) (h
t : IsCompact t) : 𝓝ˢ (s inter t) = 𝓝ˢ s ⊓ 𝓝ˢ t
参数：hs : IsCompact s；ht : IsCompact t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `nhdsSet_inter_le`：nhdsSet_inter_le (s t : Set X) : 𝓝ˢ (s inter t) <= 𝓝ˢ 
s ⊓ 𝓝ˢ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.nhdsSet_inf_eq_biSup`：IsCompact.nhdsSet_inf_eq_biSup {K : Set 
X} (hK : IsCompact K) (l : Filter X) : (𝓝ˢ K) ⊓ l = ⨆ x in K, 𝓝 x ⊓ l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsCompact.inf_nhdsSet_eq_biSup`：IsCompact.inf_nhdsSet_eq_biSup {K : Set 
X} (hK : IsCompact K) (l : Filter X) : l ⊓ (𝓝ˢ K) = ⨆ x in K, l ⊓ 𝓝 x
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_nhds_nhds`：disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint 
(𝓝 x) (𝓝 y) ↔ x != y

--- 原说明 ---
If `s` and `t` are compact sets in a T₂ space, then the set neighborhoods filter
 of `s ∩ t`
is the infimum of set neighborhoods filters for `s` and `t`.

For general sets, only the `≤` inequality holds, see `nhdsSet_inter_le`.
-/
theorem IsCompact.nhdsSet_inter_eq [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s ∩ t) = 𝓝ˢ s ⊓ 𝓝ˢ t := by
  refine le_antisymm (nhdsSet_inter_le _ _) ?_
  simp_rw [hs.nhdsSet_inf_eq_biSup, ht.inf_nhdsSet_eq_biSup, nhdsSet, sSup_image]
  refine iSup₂_le fun x hxs ↦ iSup₂_le fun y hyt ↦ ?_
  rcases eq_or_ne x y with (rfl | hne)
  · exact le_iSup₂_of_le x ⟨hxs, hyt⟩ (inf_idem _).le
  · exact (disjoint_nhds_nhds.mpr hne).eq_bot ▸ bot_le

/-- In a `T2Space X`, for a compact set `t` and a point `x` outside `t`, there are open sets `U`,
`V` that separate `t` and `x`. -/
/-
**IsCompact.separation_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.separation_of_notMem {X : Type u_1} [TopologicalSpace X] [T2Spac
e X] {x : X} {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) : exists (U : Set X), e
xists (V : Set X), IsOpen U ∧ IsOpen V ∧ t subseteq U ∧ x in V ∧ Disjoint U V
参数：H1 : IsCompact t；H2 : x ∉ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SeparatedNhds.of_isCompact_isCompact_isClosed`：SeparatedNhds.of_isCompac
t_isCompact_isClosed {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (h'L : 
IsClosed L) (hd : Disjoint K L) : S…
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s

--- 原说明 ---
In a `T2Space X`, for a compact set `t` and a point `x` outside `t`, there are o
pen sets `U`,
`V` that separate `t` and `x`.
-/
lemma IsCompact.separation_of_notMem {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    ∃ (U : Set X), ∃ (V : Set X), IsOpen U ∧ IsOpen V ∧ t ⊆ U ∧ x ∈ V ∧ Disjoint U V := by
  simpa [SeparatedNhds] using SeparatedNhds.of_isCompact_isCompact_isClosed H1 isCompact_singleton
    isClosed_singleton <| disjoint_singleton_right.mpr H2

/-- In a `T2Space X`, for a compact set `t` and a point `x` outside `t`, `𝓝ˢ t` and `𝓝 x` are
disjoint. -/
/-
**IsCompact.disjoint_nhdsSet_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompact.disjoint_nhdsSet_nhds {X : Type u_1} [TopologicalSpace X] [T2Spa
ce X] {x : X} {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) : Disjoint (𝓝ˢ t) (𝓝 x
)
参数：H1 : IsCompact t；H2 : x ∉ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `SeparatedNhds.disjoint_nhdsSet`：∀ {X : Type u_1} [inst : TopologicalSpac
e X] {s t : Set X}, SeparatedNhds s t → Disjoint (nhdsSet s) (nhdsSet t)
· 使用定理 `SeparatedNhds.of_isCompact_isCompact_isClosed`：SeparatedNhds.of_isCompac
t_isCompact_isClosed {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (h'L : 
IsClosed L) (hd : Disjoint K L) : S…
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s

--- 原说明 ---
In a `T2Space X`, for a compact set `t` and a point `x` outside `t`, `𝓝ˢ t` and 
`𝓝 x` are
disjoint.
-/
lemma IsCompact.disjoint_nhdsSet_nhds {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    Disjoint (𝓝ˢ t) (𝓝 x) := by
  simpa using SeparatedNhds.disjoint_nhdsSet <| .of_isCompact_isCompact_isClosed H1
    isCompact_singleton isClosed_singleton <| disjoint_singleton_right.mpr H2

/-- If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on a neighborhood of this set. -/
/-
**Set.InjOn.exists_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.InjOn.exists_mem_nhdsSet {X Y : Type*} [TopologicalSpace X] [Topologic
alSpace Y] [T2Space Y] {f : X -> Y} {s : Set X} (inj : InjOn f s) (sc : IsCompac
t s) (fc : forall x in s, ContinuousAt f x) (loc : forall x in s, exists u in 𝓝 
x, InjOn f u) : exists t in 𝓝ˢ s, InjOn f t
参数：inj : InjOn f s；sc : IsCompact s；fc : forall x in s, ContinuousAt f x；loc : f
orall x in s, exists u in 𝓝 x, InjOn f u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `prod_mem_nhds`：prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx
 : s in 𝓝 x) (hy : t in 𝓝 y) : s ×ˢ t in 𝓝 (x, y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_prod_set`：forall_prod_set {p : α × β -> Prop} : (forall x in 
s ×ˢ t, p x) ↔ forall x in s, forall y in t, p (x, y)
· 使用定理 `ContinuousAt.prodMap'`：ContinuousAt.prodMap' {f : X -> Z} {g : Y -> W} {
x : X} {y : Y} (hf : ContinuousAt f x) (hg : ContinuousAt g y) : ContinuousAt (P
rod.map f g…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_diagonal`：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)
· 使用定理 `Set.InjOn.ne`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x
 y : α}, Set.InjOn f s → x ∈ s → y ∈ s → x ≠ y → f x ≠ f y
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_prod_self_iff`：eventually_prod_self_iff {r : α -> α ->
 Prop} : (forallᶠ x in la ×ˢ la, r x.1 x.2) ↔ exists t in la, forall x in t, for
all y in t, r x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.nhdsSet_prod_eq`：IsCompact.nhdsSet_prod_eq {t : Set Y} (hs : I
sCompact s) (ht : IsCompact t) : 𝓝ˢ (s ×ˢ t) = 𝓝ˢ s ×ˢ 𝓝ˢ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eventually_nhdsSet_iff_forall`：eventually_nhdsSet_iff_forall {p : X -> P
rop} : (forallᶠ x in 𝓝ˢ s, p x) ↔ forall x, x in s -> forallᶠ y in 𝓝 x, p y

--- 原说明 ---
If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on a neighborhood of this set.
-/
theorem Set.InjOn.exists_mem_nhdsSet {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : ∀ x ∈ s, ContinuousAt f x) (loc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn f u) :
    ∃ t ∈ 𝓝ˢ s, InjOn f t := by
  have : ∀ x ∈ s ×ˢ s, ∀ᶠ y in 𝓝 x, f y.1 = f y.2 → y.1 = y.2 := fun (x, y) ⟨hx, hy⟩ ↦ by
    rcases eq_or_ne x y with rfl | hne
    · rcases loc x hx with ⟨u, hu, hf⟩
      exact Filter.mem_of_superset (prod_mem_nhds hu hu) <| forall_prod_set.2 hf
    · suffices ∀ᶠ z in 𝓝 (x, y), f z.1 ≠ f z.2 from this.mono fun _ hne h ↦ absurd h hne
      refine (fc x hx).prodMap' (fc y hy) <| isClosed_diagonal.isOpen_compl.mem_nhds ?_
      exact inj.ne hx hy hne
  rw [← eventually_nhdsSet_iff_forall, sc.nhdsSet_prod_eq sc] at this
  exact eventually_prod_self_iff.1 this

/-- If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on an open neighborhood of this set. -/
/-
**Set.InjOn.exists_isOpen_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.InjOn.exists_isOpen_superset {X Y : Type*} [TopologicalSpace X] [Topol
ogicalSpace Y] [T2Space Y] {f : X -> Y} {s : Set X} (inj : InjOn f s) (sc : IsCo
mpact s) (fc : forall x in s, ContinuousAt f x) (loc : forall x in s, exists u i
n 𝓝 x, InjOn f u) : exists t, IsOpen t ∧ s subseteq t ∧ InjOn f t
参数：inj : InjOn f s；sc : IsCompact s；fc : forall x in s, ContinuousAt f x；loc : f
orall x in s, exists u in 𝓝 x, InjOn f u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.exists_mem_nhdsSet`：Set.InjOn.exists_mem_nhdsSet {X Y : Type*}
 [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f : X -> Y} {s : Set X} 
(inj : InjOn f s) …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_exists`：mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : 
Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁

--- 原说明 ---
If a function `f` is

- injective on a compact set `s`;
- continuous at every point of this set;
- injective on a neighborhood of each point of this set,

then it is injective on an open neighborhood of this set.
-/
theorem Set.InjOn.exists_isOpen_superset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : ∀ x ∈ s, ContinuousAt f x) (loc : ∀ x ∈ s, ∃ u ∈ 𝓝 x, InjOn f u) :
    ∃ t, IsOpen t ∧ s ⊆ t ∧ InjOn f t :=
  let ⟨_t, hst, ht⟩ := inj.exists_mem_nhdsSet sc fc loc
  let ⟨u, huo, hsu, hut⟩ := mem_nhdsSet_iff_exists.1 hst
  ⟨u, huo, hsu, ht.mono hut⟩

section limUnder

variable [T2Space X] {f : Filter X}

/-!
### Properties of `lim` and `limUnder`

In this section we use explicit `Nonempty X` instances for `lim` and `limUnder`. This way the lemmas
are useful without a `Nonempty X` instance.
-/


/-
**lim_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x
参数：h : f <= 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `le_nhds_lim`：le_nhds_lim {f : Filter X} (h : exists x, f <= 𝓝 x) : f <= 
𝓝 (@lim _ _ h.nonempty f)

--- 原说明 ---
### Properties of `lim` and `limUnder`

In this section we use explicit `Nonempty X` instances for `lim` and `limUnder`.
 This way the lemmas
are useful without a `Nonempty X` instance.
-/
theorem lim_eq {x : X} [NeBot f] (h : f ≤ 𝓝 x) : @lim _ _ ⟨x⟩ f = x :=
  tendsto_nhds_unique (le_nhds_lim ⟨x, h⟩) h
/-
**lim_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lim_eq_iff [NeBot f] (h : exists x : X, f <= 𝓝 x) {x} : @lim _ _ ⟨x⟩ f = x
 ↔ f <= 𝓝 x
参数：h : exists x : X, f <= 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_nhds_lim`：le_nhds_lim {f : Filter X} (h : exists x, f <= 𝓝 x) : f <= 
𝓝 (@lim _ _ h.nonempty f)
· 使用定理 `lim_eq`：lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x
-/
theorem lim_eq_iff [NeBot f] (h : ∃ x : X, f ≤ 𝓝 x) {x} : @lim _ _ ⟨x⟩ f = x ↔ f ≤ 𝓝 x :=
  ⟨fun c => c ▸ le_nhds_lim h, lim_eq⟩
/-
**Ultrafilter.lim_eq_iff_le_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ultrafilter.lim_eq_iff_le_nhds [CompactSpace X] {x : X} {F : Ultrafilter X
} : F.lim = x ↔ ↑F <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.le_nhds_lim`：∀ {X : Type u} [inst : TopologicalSpace X] [Com
pactSpace X] (F : Ultrafilter X), ↑F ≤ nhds F.lim
· 使用定理 `lim_eq`：lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x
-/
theorem Ultrafilter.lim_eq_iff_le_nhds [CompactSpace X] {x : X} {F : Ultrafilter X} :
    F.lim = x ↔ ↑F ≤ 𝓝 x :=
  ⟨fun h => h ▸ F.le_nhds_lim, lim_eq⟩
/-
**isOpen_iff_ultrafilter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_ultrafilter' [CompactSpace X] (U : Set X) : IsOpen U ↔ forall F
 : Ultrafilter X, F.lim in U -> U in F.1
参数：U : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_ultrafilter`：isOpen_iff_ultrafilter : IsOpen s ↔ forall x in 
s, forall (l : Ultrafilter X), ↑l <= 𝓝 x -> s in l
· 使用定理 `Ultrafilter.le_nhds_lim`：∀ {X : Type u} [inst : TopologicalSpace X] [Com
pactSpace X] (F : Ultrafilter X), ↑F ≤ nhds F.lim
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ultrafilter.lim_eq_iff_le_nhds`：Ultrafilter.lim_eq_iff_le_nhds [CompactS
pace X] {x : X} {F : Ultrafilter X} : F.lim = x ↔ ↑F <= 𝓝 x
-/
theorem isOpen_iff_ultrafilter' [CompactSpace X] (U : Set X) :
    IsOpen U ↔ ∀ F : Ultrafilter X, F.lim ∈ U → U ∈ F.1 := by
  rw [isOpen_iff_ultrafilter]
  refine ⟨fun h F hF => h F.lim hF F F.le_nhds_lim, ?_⟩
  intro cond x hx f h
  rw [← Ultrafilter.lim_eq_iff_le_nhds.2 h] at hx
  exact cond _ hx
/-
**Filter.Tendsto.limUnder_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.limUnder_eq {x : X} {f : Filter Y} [NeBot f] {g : Y -> X} (
h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g = x
参数：h : Tendsto g f (𝓝 x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lim_eq`：lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x
-/
theorem Filter.Tendsto.limUnder_eq {x : X} {f : Filter Y} [NeBot f] {g : Y → X}
    (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g = x :=
  lim_eq h
/-
**Filter.limUnder_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.limUnder_eq_iff {f : Filter Y} [NeBot f] {g : Y -> X} (h : exists x
, Tendsto g f (𝓝 x)) {x} : @limUnder _ _ _ ⟨x⟩ f g = x ↔ Tendsto g f (𝓝 x)
参数：h : exists x, Tendsto g f (𝓝 x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
-/
theorem Filter.limUnder_eq_iff {f : Filter Y} [NeBot f] {g : Y → X} (h : ∃ x, Tendsto g f (𝓝 x))
    {x} : @limUnder _ _ _ ⟨x⟩ f g = x ↔ Tendsto g f (𝓝 x) :=
  ⟨fun c => c ▸ tendsto_nhds_limUnder h, Filter.Tendsto.limUnder_eq⟩
/-
**Continuous.limUnder_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.limUnder_eq [TopologicalSpace Y] {f : Y -> X} (h : Continuous f
) (y : Y) : @limUnder _ _ _ ⟨f y⟩ (𝓝 y) f = f y
参数：h : Continuous f；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
theorem Continuous.limUnder_eq [TopologicalSpace Y] {f : Y → X} (h : Continuous f) (y : Y) :
    @limUnder _ _ _ ⟨f y⟩ (𝓝 y) f = f y :=
  (h.tendsto y).limUnder_eq

@[simp]
/-
**lim_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lim_nhds (x : X) : @lim _ _ ⟨x⟩ (𝓝 x) = x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lim_eq`：lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lim_nhds (x : X) : @lim _ _ ⟨x⟩ (𝓝 x) = x :=
  lim_eq le_rfl

@[simp]
/-
**limUnder_nhds_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limUnder_nhds_id (x : X) : @limUnder _ _ _ ⟨x⟩ (𝓝 x) id = x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lim_nhds`：lim_nhds (x : X) : @lim _ _ ⟨x⟩ (𝓝 x) = x
-/
theorem limUnder_nhds_id (x : X) : @limUnder _ _ _ ⟨x⟩ (𝓝 x) id = x :=
  lim_nhds x

@[simp]
/-
**lim_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lim_nhdsWithin {x : X} {s : Set X} (h : x in closure s) : @lim _ _ ⟨x⟩ (𝓝[
s] x) = x
参数：h : x in closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lim_eq`：lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem lim_nhdsWithin {x : X} {s : Set X} (h : x ∈ closure s) : @lim _ _ ⟨x⟩ (𝓝[s] x) = x :=
  haveI : NeBot (𝓝[s] x) := mem_closure_iff_clusterPt.1 h
  lim_eq inf_le_left

@[simp]
/-
**limUnder_nhdsWithin_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limUnder_nhdsWithin_id {x : X} {s : Set X} (h : x in closure s) : @limUnde
r _ _ _ ⟨x⟩ (𝓝[s] x) id = x
参数：h : x in closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lim_nhdsWithin`：lim_nhdsWithin {x : X} {s : Set X} (h : x in closure s) 
: @lim _ _ ⟨x⟩ (𝓝[s] x) = x
-/
theorem limUnder_nhdsWithin_id {x : X} {s : Set X} (h : x ∈ closure s) :
    @limUnder _ _ _ ⟨x⟩ (𝓝[s] x) id = x :=
  lim_nhdsWithin h

end limUnder

/-!
### `T2Space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : X` can be separated by open neighborhoods
  provided that there exists a continuous map `f : X → Y` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_isOpenEmbedding` says that for an open embedding `f : X → Y` of a Hausdorff space
  `X`, the images of two distinct points `x y : X`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteTopology.toT2Space
    [DiscreteTopology X] : T2Space X :=
  ⟨fun x y h => ⟨{x}, {y}, isOpen_discrete _, isOpen_discrete _, rfl, rfl, disjoint_singleton.2 h⟩⟩
/-
**separated_by_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separated_by_continuous [TopologicalSpace Y] [T2Space Y] {f : X -> Y} (hf 
: Continuous f) {x y : X} (h : f x != f y) : exists u v : Set X, IsOpen u ∧ IsOp
en v ∧ x in u ∧ y in v ∧ Disjoint u v
参数：hf : Continuous f；h : f x != f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t2_separation`：t2_separation [T2Space X] {x y : X} (h : x != y) : exists
 u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
-/
theorem separated_by_continuous [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {x y : X} (h : f x ≠ f y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv, uv.preimage _⟩
/-
**separated_by_isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separated_by_isOpenEmbedding [TopologicalSpace Y] [T2Space X] {f : X -> Y}
 (hf : IsOpenEmbedding f) {x y : X} (h : x != y) : exists u v : Set Y, IsOpen u 
∧ IsOpen v ∧ f x in u ∧ f y in v ∧ Disjoint u v
参数：hf : IsOpenEmbedding f；h : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t2_separation`：t2_separation [T2Space X] {x y : X} (h : x != y) : exists
 u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.disjoint_image_of_injective`：disjoint_image_of_injective (hf : Injec
tive f) {s t : Set α} (hd : Disjoint s t) : Disjoint (f '' s) (f '' t)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
-/
theorem separated_by_isOpenEmbedding [TopologicalSpace Y] [T2Space X]
    {f : X → Y} (hf : IsOpenEmbedding f) {x y : X} (h : x ≠ y) :
    ∃ u v : Set Y, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ f y ∈ v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.isOpenMap _ uo, hf.isOpenMap _ vo, mem_image_of_mem _ xu,
    mem_image_of_mem _ yv, disjoint_image_of_injective hf.injective uv⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : X → Prop} [T2Space X] : T2Space (Subtype p) := inferInstance
/-
**Prod.t2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.t2Space [T2Space X] [TopologicalSpace Y] [T2Space Y] : T2Space (X × Y
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instT2SpaceOfR1SpaceOfT0Space`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [R1Space X] [T0Space X], T2Space X
· 使用定理 `instR1SpaceProd`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpac
e X] [R1Space X] [inst_2 : TopologicalSpace Y] [R1Space Y],   R1Space (X × Y)
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
-/
instance Prod.t2Space [T2Space X] [TopologicalSpace Y] [T2Space Y] : T2Space (X × Y) :=
  inferInstance

/-- If the codomain of an injective continuous function is a Hausdorff space, then so is its
domain. -/
/-
**T2Space.of_injective_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：T2Space.of_injective_continuous [TopologicalSpace Y] [T2Space Y] {f : X ->
 Y} (hinj : Injective f) (hc : Continuous f) : T2Space X
参数：hinj : Injective f；hc : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `separated_by_continuous`：separated_by_continuous [TopologicalSpace Y] [T
2Space Y] {f : X -> Y} (hf : Continuous f) {x y : X} (h : f x != f y) : exists u
 v : Set X, I…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂

--- 原说明 ---
If the codomain of an injective continuous function is a Hausdorff space, then s
o is its
domain.
-/
theorem T2Space.of_injective_continuous [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hinj : Injective f) (hc : Continuous f) : T2Space X :=
  ⟨fun _ _ h => separated_by_continuous hc (hinj.ne h)⟩

/-- If the codomain of a topological embedding is a Hausdorff space, then so is its domain.
See also `T2Space.of_continuous_injective`. -/
/-
**Topology.IsEmbedding.t2Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.t2Space [TopologicalSpace Y] [T2Space Y] {f : X -> Y}
 (hf : IsEmbedding f) : T2Space X
参数：hf : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.of_injective_continuous`：T2Space.of_injective_continuous [Topolo
gicalSpace Y] [T2Space Y] {f : X -> Y} (hinj : Injective f) (hc : Continuous f) 
: T2Space X
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…

--- 原说明 ---
If the codomain of a topological embedding is a Hausdorff space, then so is its 
domain.
See also `T2Space.of_continuous_injective`.
-/
theorem Topology.IsEmbedding.t2Space [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T2Space X :=
  .of_injective_continuous hf.injective hf.continuous
/-
**Homeomorph.t2Space** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T2Space X] (h : X ≃ₜ Y),   T2Space Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
protected theorem Homeomorph.t2Space [TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y) : T2Space Y :=
  h.symm.isEmbedding.t2Space
/-
**ULift.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.instT2Space [T2Space X] : T2Space (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用引理 `Topology.IsEmbedding.uliftDown`：Topology.IsEmbedding.uliftDown [Topologi
calSpace X] : IsEmbedding (ULift.down : ULift.{v, u} X -> X)
-/
instance ULift.instT2Space [T2Space X] : T2Space (ULift X) :=
  IsEmbedding.uliftDown.t2Space
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space X] [TopologicalSpace Y] [T2Space Y] :
    T2Space (X ⊕ Y) := by
  constructor
  rintro (x | x) (y | y) h
  · exact separated_by_isOpenEmbedding .inl <| ne_of_apply_ne _ h
  · exact separated_by_continuous continuous_isLeft <| by simp
  · exact separated_by_continuous continuous_isLeft <| by simp
  · exact separated_by_isOpenEmbedding .inr <| ne_of_apply_ne _ h
/-
**Pi.t2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.t2Space {Y : X -> Type v} [forall a, TopologicalSpace (Y a)] [forall a,
 T2Space (Y a)] : T2Space (forall a, Y a)
参数：Y a；Y a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instT2SpaceOfR1SpaceOfT0Space`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [R1Space X] [T0Space X], T2Space X
· 使用定理 `instR1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), R1Space (X i)],   R1Space ((i : ι) → X i)
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
-/
instance Pi.t2Space {Y : X → Type v} [∀ a, TopologicalSpace (Y a)]
    [∀ a, T2Space (Y a)] : T2Space (∀ a, Y a) :=
  inferInstance
/-
**Sigma.t2Space** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sigma.t2Space {ι} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [for
all a, T2Space (X a)] : T2Space (Σ i, X i)
参数：X i；X a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `separated_by_isOpenEmbedding`：separated_by_isOpenEmbedding [TopologicalS
pace Y] [T2Space X] {f : X -> Y} (hf : IsOpenEmbedding f) {x y : X} (h : x != y)
 : exists u v : Se…
· 使用引理 `Topology.IsOpenEmbedding.sigmaMk`：Topology.IsOpenEmbedding.sigmaMk {i : 
ι} : IsOpenEmbedding (@Sigma.mk ι σ i)
· 使用定理 `separated_by_continuous`：separated_by_continuous [TopologicalSpace Y] [T
2Space Y] {f : X -> Y} (hf : Continuous f) {x y : X} (h : f x != f y) : exists u
 v : Set X, I…
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `isOpen_sigma_fst_preimage`：isOpen_sigma_fst_preimage (s : Set ι) : IsOpe
n (Sigma.fst ⁻¹' s : Set (Σ a, σ a))
-/
instance Sigma.t2Space {ι} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ a, T2Space (X a)] :
    T2Space (Σ i, X i) := by
  constructor
  rintro ⟨i, x⟩ ⟨j, y⟩ ne
  rcases eq_or_ne i j with (rfl | h)
  · replace ne : x ≠ y := ne_of_apply_ne _ ne
    exact separated_by_isOpenEmbedding .sigmaMk ne
  · let _ := (⊥ : TopologicalSpace ι); have : DiscreteTopology ι := ⟨rfl⟩
    exact separated_by_continuous (continuous_def.2 fun u _ => isOpen_sigma_fst_preimage u) h

section
variable (X)

/-- The smallest equivalence relation on a topological space giving a T2 quotient. -/
@[instance_reducible]
/-
**t2Setoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：t2Setoid : Setoid X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest equivalence relation on a topological space giving a T2 quotient.
-/
def t2Setoid : Setoid X := sInf {s | T2Space (Quotient s)}

/-- The largest T2 quotient of a topological space. This construction is left-adjoint to the
inclusion of T2 spaces into all topological spaces. -/
/-
**T2Quotient** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：T2Quotient
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The largest T2 quotient of a topological space. This construction is left-adjoin
t to the
inclusion of T2 spaces into all topological spaces.
-/
def T2Quotient := Quotient (t2Setoid X)

namespace T2Quotient
variable {X}

/-
**T2Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `T2Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (T2Quotient X) :=
  inferInstanceAs <| TopologicalSpace (Quotient _)

/-- The map from a topological space to its largest T2 quotient. -/
/-
**T2Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `T2Quotient`。
形式化陈述：mk : X -> T2Quotient X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from a topological space to its largest T2 quotient.
-/
def mk : X → T2Quotient X := Quotient.mk (t2Setoid X)
/-
**T2Quotient.mk_eq** 是 Mathlib 中的一个引理，位于命名空间 `T2Quotient`。
形式化陈述：mk_eq {x y : X} : mk x = mk y ↔ forall s : Setoid X, T2Space (Quotient s) 
-> s x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Setoid.quotient_mk_sInf_eq`：quotient_mk_sInf_eq {S : Set (Setoid α)} {x 
y : α} : Quotient.mk (sInf S) x = Quotient.mk (sInf S) y ↔ forall s in S, s x y
-/
lemma mk_eq {x y : X} : mk x = mk y ↔ ∀ s : Setoid X, T2Space (Quotient s) → s x y :=
  Setoid.quotient_mk_sInf_eq

variable (X)
/-
**T2Quotient.surjective_mk** 是 Mathlib 中的一个引理，位于命名空间 `T2Quotient`。
形式化陈述：surjective_mk : Surjective (mk : X -> T2Quotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
lemma surjective_mk : Surjective (mk : X → T2Quotient X) := Quotient.mk_surjective
/-
**T2Quotient.continuous_mk** 是 Mathlib 中的一个引理，位于命名空间 `T2Quotient`。
形式化陈述：continuous_mk : Continuous (mk : X -> T2Quotient X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
-/
lemma continuous_mk : Continuous (mk : X → T2Quotient X) :=
  continuous_quotient_mk'

variable {X}

@[elab_as_elim]
/-
**T2Quotient.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `T2Quotient`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {motive : T2Quotient X → Prop
} (q : T2Quotient X),   (∀ (x : X), motive (T2Quotient.mk x)) → motive q
参数：q : T2Quotient X；∀ (x : X), motive (T2Quotient.mk x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
protected lemma inductionOn {motive : T2Quotient X → Prop} (q : T2Quotient X)
    (h : ∀ x, motive (T2Quotient.mk x)) : motive q := Quotient.inductionOn q h

@[elab_as_elim]
/-
**T2Quotient.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `T2Quotient`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {motive : T2Quotient X → Prop
} (q : T2Quotient X),   (∀ (x : X), motive (T2Quotient.mk x)) → motive q
参数：q : T2Quotient X；∀ (x : X), motive (T2Quotient.mk x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
protected lemma inductionOn₂ [TopologicalSpace Y] {motive : T2Quotient X → T2Quotient Y → Prop}
    (q : T2Quotient X) (q' : T2Quotient Y) (h : ∀ x y, motive (mk x) (mk y)) : motive q q' :=
  Quotient.inductionOn₂ q q' h

/-- The largest T2 quotient of a topological space is indeed T2. -/
/-
**T2Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `T2Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The largest T2 quotient of a topological space is indeed T2.
-/
instance : T2Space (T2Quotient X) := by
  rw [t2Space_iff]
  rintro ⟨x⟩ ⟨y⟩ (h : ¬ T2Quotient.mk x = T2Quotient.mk y)
  obtain ⟨s, hs, hsxy⟩ : ∃ s, T2Space (Quotient s) ∧ Quotient.mk s x ≠ Quotient.mk s y := by
    simpa [T2Quotient.mk_eq, Quotient.eq] using h
  exact separated_by_continuous (continuous_map_sInf (by exact hs)) hsxy
/-
**T2Quotient.compatible** 是 Mathlib 中的一个引理，位于命名空间 `T2Quotient`。
形式化陈述：compatible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Spac
e Y] {f : X -> Y} (hf : Continuous f) : letI _
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `T2Space.of_injective_continuous`：T2Space.of_injective_continuous [Topolo
gicalSpace Y] [T2Space Y] {f : X -> Y} (hinj : Injective f) (hc : Continuous f) 
: T2Space X
· 使用定理 `Setoid.kerLift_injective`：kerLift_injective (f : α -> β) : Injective ker
Lift f
· 使用定理 `Continuous.quotient_lift`：Continuous.quotient_lift {f : X -> Y} (h : Con
tinuous f) (hs : forall a b, a ≈ b -> f a = f b) : Continuous (Quotient.lift f h
s : Quotient s…
-/
lemma compatible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : letI _ := t2Setoid X
    ∀ (a b : X), a ≈ b → f a = f b := by
  change t2Setoid X ≤ Setoid.ker f
  exact sInf_le <| .of_injective_continuous
    (Setoid.kerLift_injective _) (hf.quotient_lift fun _ _ ↦ id)

/-- The universal property of the largest T2 quotient of a topological space `X`: any continuous
map from `X` to a T2 space `Y` uniquely factors through `T2Quotient X`. This declaration builds the
factored map. Its continuity is `T2Quotient.continuous_lift`, the fact that it indeed factors the
original map is `T2Quotient.lift_mk` and uniqueness is `T2Quotient.unique_lift`. -/
/-
**T2Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `T2Quotient`。
形式化陈述：lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {
f : X -> Y} (hf : Continuous f) : T2Quotient X -> Y
参数：hf : Continuous f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `T2Quotient.compatible`：compatible {X Y : Type*} [TopologicalSpace X] [To
pologicalSpace Y] [T2Space Y] {f : X -> Y} (hf : Continuous f) : letI _

--- 原说明 ---
The universal property of the largest T2 quotient of a topological space `X`: an
y continuous
map from `X` to a T2 space `Y` uniquely factors through `T2Quotient X`. This dec
laration builds the
factored map. Its continuity is `T2Quotient.continuous_lift`, the fact that it i
ndeed factors the
original map is `T2Quotient.lift_mk` and uniqueness is `T2Quotient.unique_lift`.
-/
def lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : T2Quotient X → Y :=
  Quotient.lift f (T2Quotient.compatible hf)
/-
**T2Quotient.continuous_lift** 是 Mathlib 中的一个引理，位于命名空间 `T2Quotient`。
形式化陈述：continuous_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T
2Space Y] {f : X -> Y} (hf : Continuous f) : Continuous (T2Quotient.lift hf)
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
-/
lemma continuous_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : Continuous (T2Quotient.lift hf) :=
  continuous_coinduced_dom.mpr hf

@[simp]
/-
**T2Quotient.lift_mk** 是 Mathlib 中的一个引理，位于命名空间 `T2Quotient`。
形式化陈述：lift_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y
] {f : X -> Y} (hf : Continuous f) (x : X) : lift hf (mk x) = f x
参数：hf : Continuous f；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.lift_mk`：Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : fora
ll a b : α, a ≈ b -> f a = f b) (x : α) : Quotient.lift f h (Quotient.mk s x) = 
f x
· 使用引理 `T2Quotient.compatible`：compatible {X Y : Type*} [TopologicalSpace X] [To
pologicalSpace Y] [T2Space Y] {f : X -> Y} (hf : Continuous f) : letI _
-/
lemma lift_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (x : X) : lift hf (mk x) = f x :=
  Quotient.lift_mk (s := t2Setoid X) f (T2Quotient.compatible hf) x
/-
**T2Quotient.unique_lift** 是 Mathlib 中的一个引理，位于命名空间 `T2Quotient`。
形式化陈述：unique_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Spa
ce Y] {f : X -> Y} (hf : Continuous f) {g : T2Quotient X -> Y} (hfg : g ∘ mk = f
) : g = lift hf
参数：hf : Continuous f；hfg : g ∘ mk = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.right_cancellable`：∀ {α : Sort u_1} {β : Sort u_2} {
γ : Sort u_3} {f : α → β},   Function.Surjective f → ∀ {g₁ g₂ : β → γ}, g₁ ∘ f =
 g₂ ∘ f ↔ g₁ = g₂
· 使用引理 `T2Quotient.surjective_mk`：surjective_mk : Surjective (mk : X -> T2Quotie
nt X)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `T2Quotient.lift.congr_simp`：∀ {X : Type u_3} {Y : Type u_4} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] [inst_2 : T2Space Y]   {f f_1 : X 
→ Y} (e_f : f = …
· 使用引理 `T2Quotient.lift_mk`：lift_mk {X Y : Type*} [TopologicalSpace X] [Topologi
calSpace Y] [T2Space Y] {f : X -> Y} (hf : Continuous f) (x : X) : lift hf (mk x
) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma unique_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {g : T2Quotient X → Y} (hfg : g ∘ mk = f) :
    g = lift hf := by
  apply surjective_mk X |>.right_cancellable |>.mp <| funext _
  simp [← hfg]

end T2Quotient
end

variable {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-
**isClosed_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) (hg : Continuou
s g) : IsClosed { y : Y | f y = g y }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `isClosed_diagonal`：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)
-/
theorem isClosed_eq [T2Space X] {f g : Y → X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { y : Y | f y = g y } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_diagonal

/-- If functions `f` and `g` are continuous on a closed set `s`,
then the set of points `x ∈ s` such that `f x = g x` is a closed set. -/
@[closedness .]
/-
**IsClosed.isClosed_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T2Space Y] {f g : X → Y}   {s : Set X}, IsClosed s → Continuous
On f s → ContinuousOn g s → IsClosed {x | x ∈ s ∧ f x = g x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.preimage_isClosed_of_isClosed`：ContinuousOn.preimage_isClos
ed_of_isClosed {t : Set β} (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClo
sed t) : IsClosed (s inter f ⁻¹'…
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `isClosed_diagonal`：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)

--- 原说明 ---
If functions `f` and `g` are continuous on a closed set `s`,
then the set of points `x ∈ s` such that `f x = g x` is a closed set.
-/
protected theorem IsClosed.isClosed_eq [T2Space Y] {f g : X → Y} {s : Set X} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed {x ∈ s | f x = g x} :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hs isClosed_diagonal
/-
**isOpen_ne_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_ne_fun [T2Space X] {f g : Y -> X} (hf : Continuous f) (hg : Continu
ous g) : IsOpen { y : Y | f y != g y }
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
-/
theorem isOpen_ne_fun [T2Space X] {f g : Y → X} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { y : Y | f y ≠ g y } :=
  isOpen_compl_iff.mpr <| isClosed_eq hf hg

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. See also
`Set.EqOn.of_subset_closure` for a more general version. -/
/-
**Set.EqOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [T2Space X] {s : Set Y}   {f g : Y → X}, Set.EqOn f g s → Contin
uous f → Continuous g → Set.EqOn f g (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }

--- 原说明 ---
If two continuous maps are equal on `s`, then they are equal on the closure of `
s`. See also
`Set.EqOn.of_subset_closure` for a more general version.
-/
protected theorem Set.EqOn.closure [T2Space X] {s : Set Y} {f g : Y → X} (h : EqOn f g s)
    (hf : Continuous f) (hg : Continuous g) : EqOn f g (closure s) :=
  closure_minimal h (isClosed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
/-
**Continuous.ext_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense s) {f g : Y -> X} (h
f : Continuous f) (hg : Continuous g) (h : EqOn f g s) : f = g
参数：hs : Dense s；hf : Continuous f；hg : Continuous g；h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.EqOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [T2Space X] {s : Set Y}   {f g : Y → X}, Set
.EqOn …

--- 原说明 ---
If two continuous functions are equal on a dense set, then they are equal.
-/
theorem Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense s) {f g : Y → X} (hf : Continuous f)
    (hg : Continuous g) (h : EqOn f g s) : f = g :=
  funext fun x => h.closure hf hg (hs x)
/-
**eqOn_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqOn_closure₂' [T2Space Z] {s : Set X} {t : Set Y} {f g : X → Y → Z}
    (h : ∀ x ∈ s, ∀ y ∈ t, f x y = g x y) (hf₁ : ∀ x, Continuous (f x))
    (hf₂ : ∀ y, Continuous fun x => f x y) (hg₁ : ∀ x, Continuous (g x))
    (hg₂ : ∀ y, Continuous fun x => g x y) : ∀ x ∈ closure s, ∀ y ∈ closure t, f x y = g x y :=
  suffices closure s ⊆ ⋂ y ∈ closure t, { x | f x y = g x y } by simpa only [subset_def, mem_iInter]
  (closure_minimal fun x hx => mem_iInter₂.2 <| Set.EqOn.closure (h x hx) (hf₁ _) (hg₁ _)) <|
    isClosed_biInter fun _ _ => isClosed_eq (hf₂ _) (hg₂ _)
/-
**eqOn_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqOn_closure₂ [T2Space Z] {s : Set X} {t : Set Y} {f g : X → Y → Z}
    (h : ∀ x ∈ s, ∀ y ∈ t, f x y = g x y) (hf : Continuous (uncurry f))
    (hg : Continuous (uncurry g)) : ∀ x ∈ closure s, ∀ y ∈ closure t, f x y = g x y :=
  eqOn_closure₂' h hf.uncurry_left hf.uncurry_right hg.uncurry_left hg.uncurry_right

/-- If `f x = g x` for all `x ∈ s` and `f`, `g` are continuous on `t`, `s ⊆ t ⊆ closure s`, then
`f x = g x` for all `x ∈ t`. See also `Set.EqOn.closure`. -/
/-
**Set.EqOn.of_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.EqOn.of_subset_closure [T2Space Y] {s t : Set X} {f g : X -> Y} (h : E
qOn f g s) (hf : ContinuousOn f t) (hg : ContinuousOn g t) (hst : s subseteq t) 
(hts : t subseteq closure s) : EqOn f g t
参数：h : EqOn f g s；hf : ContinuousOn f t；hg : ContinuousOn g t；hst : s subseteq t
；hts : t subseteq closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a

--- 原说明 ---
If `f x = g x` for all `x ∈ s` and `f`, `g` are continuous on `t`, `s ⊆ t ⊆ clos
ure s`, then
`f x = g x` for all `x ∈ t`. See also `Set.EqOn.closure`.
-/
theorem Set.EqOn.of_subset_closure [T2Space Y] {s t : Set X} {f g : X → Y} (h : EqOn f g s)
    (hf : ContinuousOn f t) (hg : ContinuousOn g t) (hst : s ⊆ t) (hts : t ⊆ closure s) :
    EqOn f g t := by
  intro x hx
  have : (𝓝[s] x).NeBot := mem_closure_iff_clusterPt.mp (hts hx)
  exact
    tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono_left <| nhdsWithin_mono _ hst)
      ((hg x hx).mono_left <| nhdsWithin_mono _ hst) (h.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- Retract subspaces of Hausdorff spaces are closed. -/
/-
**Function.LeftInverse.isClosed_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.LeftInverse.isClosed_range [T2Space X] {f : X -> Y} {g : Y -> X} 
(h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClose
d (range g)
参数：h : Function.LeftInverse f g；hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace Y] [T2Space X] {s : Set Y}   {f g : Y → X}, Set
.EqOn …
· 使用定理 `Set.RightInvOn.eqOn`：eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t
· 使用定理 `Function.LeftInverse.rightInvOn_range`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {g : β → α}, Function.LeftInverse f g → Set.RightInvOn f g (Set.range
 g)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s

--- 原说明 ---
Retract subspaces of Hausdorff spaces are closed.
-/
theorem Function.LeftInverse.isClosed_range [T2Space X] {f : X → Y} {g : Y → X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClosed (range g) :=
  have : EqOn (g ∘ f) id (closure <| range g) :=
    h.rightInvOn_range.eqOn.closure (hg.comp hf) continuous_id
  isClosed_of_closure_subset fun x hx => ⟨f x, this hx⟩
/-
**Function.LeftInverse.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.LeftInverse.isClosedEmbedding [T2Space X] {f : X -> Y} {g : Y -> 
X} (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsCl
osedEmbedding g
参数：h : Function.LeftInverse f g；hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_leftInverse`：∀ {X : Type u_1} {Y : Type u_2} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {g : Y → X}, 
  Function.LeftInverse f …
· 使用定理 `Function.LeftInverse.isClosed_range`：Function.LeftInverse.isClosed_range
 [T2Space X] {f : X -> Y} {g : Y -> X} (h : Function.LeftInverse f g) (hf : Cont
inuous f) (hg : Continuou…
-/
theorem Function.LeftInverse.isClosedEmbedding [T2Space X] {f : X → Y} {g : Y → X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClosedEmbedding g :=
  ⟨.of_leftInverse h hf hg, h.isClosed_range hf hg⟩
/-
**SeparatedNhds.of_isCompact_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparatedNhds.of_isCompact_isCompact [T2Space X] {s t : Set X} (hs : IsCom
pact s) (ht : IsCompact t) (hst : Disjoint s t) : SeparatedNhds s t
参数：hs : IsCompact s；ht : IsCompact t；hst : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.prod_subset_compl_diagonal_iff_disjoint`：prod_subset_compl_diagonal_
iff_disjoint : s ×ˢ t subseteq (diagonal α)ᶜ ↔ Disjoint s t
· 使用定理 `generalized_tube_lemma`：generalized_tube_lemma (hs : IsCompact s) {t : S
et Y} (ht : IsCompact t) {n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t subseteq
 n) : exists…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_diagonal`：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)
-/
theorem SeparatedNhds.of_isCompact_isCompact [T2Space X] {s t : Set X} (hs : IsCompact s)
    (ht : IsCompact t) (hst : Disjoint s t) : SeparatedNhds s t := by
  simp only [SeparatedNhds, prod_subset_compl_diagonal_iff_disjoint.symm] at hst ⊢
  exact generalized_tube_lemma hs ht isClosed_diagonal.isOpen_compl hst

/-- In a `R1Space X`, for disjoint closed sets `s t` such that `closure sᶜ` is compact,
there are neighbourhoods that separate `s` and `t`. -/
/-
**SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed [R1Space X] {s 
: Set X} {t : Set X} (H1 : IsClosed s) (H2 : IsCompact (closure sᶜ)) (H3 : IsClo
sed t) (H4 : Disjoint s t) : SeparatedNhds s t
参数：H1 : IsClosed s；H2 : IsCompact (closure sᶜ)；H3 : IsClosed t；H4 : Disjoint s t
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `SeparatedNhds.union_left`：union_left : SeparatedNhds s u -> SeparatedNhd
s t u -> SeparatedNhds (s union t) u
· 使用定理 `IsClosed.frontier_eq`：IsClosed.frontier_eq (hs : IsClosed s) : frontier 
s = s \ interior s
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `SeparatedNhds.of_isCompact_isCompact_isClosed`：SeparatedNhds.of_isCompac
t_isCompact_isClosed {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (h'L : 
IsClosed L) (hd : Disjoint K L) : S…
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ

--- 原说明 ---
In a `R1Space X`, for disjoint closed sets `s t` such that `closure sᶜ` is compa
ct,
there are neighbourhoods that separate `s` and `t`.
-/
lemma SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed [R1Space X] {s : Set X}
    {t : Set X} (H1 : IsClosed s) (H2 : IsCompact (closure sᶜ)) (H3 : IsClosed t)
    (H4 : Disjoint s t) : SeparatedNhds s t := by
  -- Since `t` is a closed subset of the compact set `closure sᶜ`, it is compact.
  have ht : IsCompact t := .of_isClosed_subset H2 H3 <| H4.subset_compl_left.trans subset_closure
  -- we split `s` into its frontier and its interior.
  rw [← sdiff_union_of_subset (interior_subset (s := s))]
  -- since `t ⊆ sᶜ`, which is open, and `interior s` is open, we have
  -- `SeparatedNhds (interior s) t`, which leaves us only with the frontier.
  refine .union_left ?_ ⟨interior s, sᶜ, isOpen_interior, H1.isOpen_compl, le_rfl,
    H4.subset_compl_left, disjoint_compl_right.mono_left interior_subset⟩
  -- Since the frontier of `s` is compact (as it is a subset of `closure sᶜ`), we simply apply
  -- `SeparatedNhds_of_isCompact_isCompact`.
  rw [← H1.frontier_eq, frontier_eq_closure_inter_closure, H1.closure_eq]
  refine .of_isCompact_isCompact_isClosed ?_ ht H3 (disjoint_of_subset_left inter_subset_left H4)
  exact H2.of_isClosed_subset (H1.inter isClosed_closure) inter_subset_right

section SeparatedFinset

/-
**SeparatedNhds.of_finset_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparatedNhds.of_finset_finset [T2Space X] (s t : Finset X) (h : Disjoint 
s t) : SeparatedNhds (s : Set X) t
参数：s t : Finset X；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatedNhds.of_isCompact_isCompact`：SeparatedNhds.of_isCompact_isCompa
ct [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) (hst : Disjoi
nt s t) : SeparatedNhds s …
· 使用定理 `Set.Finite.isCompact`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Finite → IsCompact s
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem SeparatedNhds.of_finset_finset [T2Space X] (s t : Finset X) (h : Disjoint s t) :
    SeparatedNhds (s : Set X) t :=
  .of_isCompact_isCompact s.finite_toSet.isCompact t.finite_toSet.isCompact <| mod_cast h
/-
**SeparatedNhds.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparatedNhds.of_finite [T2Space X] {s t : Set X} (hs : s.Finite) (ht : t.
Finite) (h : Disjoint s t) : SeparatedNhds s t
参数：hs : s.Finite；ht : t.Finite；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `SeparatedNhds.of_finset_finset`：SeparatedNhds.of_finset_finset [T2Space 
X] (s t : Finset X) (h : Disjoint s t) : SeparatedNhds (s : Set X) t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.disjoint_toFinset`：∀ {α : Type u} {s t : Set α} {hs : s.Finit
e} {ht : t.Finite}, Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t
-/
theorem SeparatedNhds.of_finite [T2Space X] {s t : Set X} (hs : s.Finite) (ht : t.Finite)
    (h : Disjoint s t) : SeparatedNhds s t := by
  rw [← hs.coe_toFinset, ← ht.coe_toFinset]
  exact SeparatedNhds.of_finset_finset _ _ (Finite.disjoint_toFinset.2 h)
/-
**SeparatedNhds.of_singleton_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeparatedNhds.of_singleton_finset [T2Space X] {x : X} {s : Finset X} (h : 
x ∉ s) : SeparatedNhds ({x} : Set X) s
参数：h : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `SeparatedNhds.of_finset_finset`：SeparatedNhds.of_finset_finset [T2Space 
X] (s t : Finset X) (h : Disjoint s t) : SeparatedNhds (s : Set X) t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_left`：disjoint_singleton_left : Disjoint (sing
leton a) s ↔ a ∉ s
-/
theorem SeparatedNhds.of_singleton_finset [T2Space X] {x : X} {s : Finset X} (h : x ∉ s) :
    SeparatedNhds ({x} : Set X) s :=
  mod_cast .of_finset_finset {x} s (Finset.disjoint_singleton_left.mpr h)

end SeparatedFinset

/-- In a `T2Space`, every compact set is closed. -/
@[aesop 50% apply, grind ←, closedness .]
/-
**IsCompact.isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isClosed_iff_forall_filter`：isClosed_iff_forall_filter : IsClosed s ↔ fo
rall x, forall F : Filter X, F.NeBot -> F <= 𝓟 s -> F <= 𝓝 x -> x in s
· 使用引理 `IsCompact.exists_clusterPt`：IsCompact.exists_clusterPt (hs : IsCompact s
) {f : Filter X} [NeBot f] (hf : f <= 𝓟 s) : exists x in s, ClusterPt x f
· 使用定理 `Set.mem_of_eq_of_mem`：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y
) (h : y in s) : x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_nhds_neBot`：eq_of_nhds_neBot [T2Space X] {x y : X} (h : NeBot (𝓝 x
 ⊓ 𝓝 y)) : x = y
· 使用定理 `ClusterPt.neBot`：ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : Ne
Bot (𝓝 x ⊓ F)
· 使用定理 `ClusterPt.mono`：ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h :
 f <= g) : ClusterPt x g

--- 原说明 ---
In a `T2Space`, every compact set is closed.
-/
theorem IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s :=
  isClosed_iff_forall_filter.2 fun _x _f _ hfs hfx =>
    let ⟨_y, hy, hfy⟩ := hs.exists_clusterPt hfs
    mem_of_eq_of_mem (eq_of_nhds_neBot (hfy.mono hfx).neBot).symm hy

@[compactness .]
/-
**IsCompact.preimage_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.preimage_continuous [CompactSpace X] [T2Space Y] {f : X -> Y} {s
 : Set Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f ⁻¹' s)
参数：hs : IsCompact s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
-/
theorem IsCompact.preimage_continuous [CompactSpace X] [T2Space Y] {f : X → Y} {s : Set Y}
    (hs : IsCompact s) (hf : Continuous f) : IsCompact (f ⁻¹' s) :=
  (hs.isClosed.preimage hf).isCompact
/-
**Pi.isCompact_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.isCompact_iff {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace 
(X i)] [forall i, T2Space (X i)] {s : Set (Π i, X i)} : IsCompact s ↔ IsClosed s
 ∧ forall i, IsCompact (eval i '' s)
参数：X i；X i；Π i, X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_pi_eval_image`：subset_pi_eval_image (s : Set ι) (u : Set (for
all i, α i)) : u subseteq pi s fun i => eval i '' u
-/
lemma Pi.isCompact_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, T2Space (X i)] {s : Set (Π i, X i)} :
    IsCompact s ↔ IsClosed s ∧ ∀ i, IsCompact (eval i '' s) := by
  constructor <;> intro H
  · exact ⟨H.isClosed, fun i ↦ H.image <| continuous_apply i⟩
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H.2) H.1 (subset_pi_eval_image univ s)
/-
**Pi.isCompact_closure_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.isCompact_closure_iff {ι : Type*} {X : ι -> Type*} [forall i, Topologic
alSpace (X i)] [forall i, R1Space (X i)] {s : Set (Π i, X i)} : IsCompact (closu
re s) ↔ forall i, IsCompact (closure <| eval i '' s)
参数：X i；X i；Π i, X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instR1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), R1Space (X i)],   R1Space ((i : ι) → X i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Pi.isCompact_closure_iff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, R1Space (X i)] {s : Set (Π i, X i)} :
    IsCompact (closure s) ↔ ∀ i, IsCompact (closure <| eval i '' s) := by
  simp_rw [← exists_isCompact_superset_iff, Pi.exists_compact_superset_iff, image_subset_iff]

/-- If `V : ι → Set X` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhds_of_isCompact'` where we
don't need to assume each `V i` closed because it follows from compactness since `X` is
assumed to be Hausdorff. -/
/-
**exists_subset_nhds_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_nhds_of_isCompact [T2Space X] {ι : Type*} [Nonempty ι] {V : 
ι -> Set X} (hV : Directed (· ⊇ ·) V) (hV_cpct : forall i, IsCompact (V i)) {U :
 Set X} (hU : forall x in ⋂ i, V i, U in 𝓝 x) : exists i, V i subseteq U
参数：hV : Directed (· ⊇ ·) V；hV_cpct : forall i, IsCompact (V i)；hU : forall x in 
⋂ i, V i, U in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_nhds_of_isCompact'`：exists_subset_nhds_of_isCompact' [None
mpty ι] {V : ι -> Set X} (hV : Directed (· ⊇ ·) V) (hV_cpct : forall i, IsCompac
t (V i)) (hV_closed : …
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s

--- 原说明 ---
If `V : ι → Set X` is a decreasing family of compact sets then any neighborhood 
of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhds_of_isCo
mpact'` where we
don't need to assume each `V i` closed because it follows from compactness since
 `X` is
assumed to be Hausdorff.
-/
theorem exists_subset_nhds_of_isCompact [T2Space X] {ι : Type*} [Nonempty ι] {V : ι → Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : ∀ i, IsCompact (V i)) {U : Set X}
    (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhds_of_isCompact' hV hV_cpct (fun i => (hV_cpct i).isClosed) hU
/-
**CompactExhaustion.isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactExhaustion.isClosed [T2Space X] (K : CompactExhaustion X) (n : Nat)
 : IsClosed (K n)
参数：K : CompactExhaustion X；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `CompactExhaustion.isCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X
] (K : CompactExhaustion X) (n : ℕ), IsCompact (K n)
-/
theorem CompactExhaustion.isClosed [T2Space X] (K : CompactExhaustion X) (n : ℕ) : IsClosed (K n) :=
  (K.isCompact n).isClosed

@[compactness .]
/-
**IsCompact.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.inter [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompa
ct t) : IsCompact (s inter t)
参数：hs : IsCompact s；ht : IsCompact t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
-/
theorem IsCompact.inter [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ∩ t) :=
  hs.inter_right <| ht.isClosed
/-
**image_closure_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_closure_of_isCompact [T2Space Y] {s : Set X} (hs : IsCompact (closur
e s)) {f : X -> Y} (hf : ContinuousOn f (closure s)) : f '' closure s = closure 
(f '' s)
参数：hs : IsCompact (closure s)；hf : ContinuousOn f (closure s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `ContinuousOn.image_closure`：ContinuousOn.image_closure (hf : ContinuousO
n f (closure s)) : f '' closure s subseteq closure (f '' s)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
-/
theorem image_closure_of_isCompact [T2Space Y] {s : Set X} (hs : IsCompact (closure s)) {f : X → Y}
    (hf : ContinuousOn f (closure s)) : f '' closure s = closure (f '' s) :=
  Subset.antisymm hf.image_closure <|
    closure_minimal (image_mono subset_closure) (hs.image_of_continuousOn hf).isClosed

/-- Two continuous maps into a Hausdorff space disagree at a point iff they disagree in a
neighborhood. -/
/-
**ContinuousAt.ne_iff_eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.ne_iff_eventually_ne [T2Space Y] {x : X} {f g : X -> Y} (hf :
 ContinuousAt f x) (hg : ContinuousAt g x) : f x != g x ↔ forallᶠ x in 𝓝 x, f x 
!= g x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `t2_separation`：t2_separation [T2Space X] {x y : X} (h : x != y) : exists
 u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t

--- 原说明 ---
Two continuous maps into a Hausdorff space disagree at a point iff they disagree
 in a
neighborhood.
-/
theorem ContinuousAt.ne_iff_eventually_ne [T2Space Y] {x : X} {f g : X → Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x ≠ g x ↔ ∀ᶠ x in 𝓝 x, f x ≠ g x := by
  constructor <;> intro hfg
  · obtain ⟨Uf, Ug, h₁U, h₂U, h₃U, h₄U, h₅U⟩ := t2_separation hfg
    rw [Set.disjoint_iff_inter_eq_empty] at h₅U
    filter_upwards [inter_mem
      (hf.preimage_mem_nhds (IsOpen.mem_nhds h₁U h₃U))
      (hg.preimage_mem_nhds (IsOpen.mem_nhds h₂U h₄U))]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    by_contra H
    rw [H] at hx
    have : g x ∈ Uf ∩ Ug := hx
    simp [h₅U] at this
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 hfg
    exact h₁t x h₃t

/-- **Local identity principle** for continuous maps: Two continuous maps into a Hausdorff space
agree in a punctured neighborhood of a non-isolated point iff they agree in a neighborhood. -/
/-
**ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X}
 {f g : X -> Y} (hf : ContinuousAt f x) (hg : ContinuousAt g x) [(𝓝[!=] x).NeBot
] : f =ᶠ[𝓝[!=] x] g ↔ f =ᶠ[𝓝 x] g
参数：hf : ContinuousAt f x；hg : ContinuousAt g x；𝓝[!=] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`：eventuallyEq_nhds_of_eventuall
yEq_nhdsNE {f g : α -> β} {a : α} (h₁ : f =ᶠ[𝓝[!=] a] g) (h₂ : f a = g a) : f =ᶠ
[𝓝 a] g
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousAt.ne_iff_eventually_ne`：ContinuousAt.ne_iff_eventually_ne [T2
Space Y] {x : X} {f g : X -> Y} (hf : ContinuousAt f x) (hg : ContinuousAt g x) 
: f x != g x ↔ forallᶠ …
· 使用定理 `Filter.empty_notMem`：empty_notMem (f : Filter α) [NeBot f] : ∅ ∉ f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a

--- 原说明 ---
**Local identity principle** for continuous maps: Two continuous maps into a Hau
sdorff space
agree in a punctured neighborhood of a non-isolated point iff they agree in a ne
ighborhood.
-/
theorem ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X} {f g : X → Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) [(𝓝[≠] x).NeBot] :
    f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor <;> intro hfg
  · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg
    by_contra hCon
    obtain ⟨a, ha⟩ : {x | f x ≠ g x ∧ f x = g x}.Nonempty := by
      have h₁ := (eventually_nhdsWithin_of_eventually_nhds
        ((hf.ne_iff_eventually_ne hg).1 hCon)).and hfg
      have h₂ : ∅ ∉ 𝓝[≠] x := by exact empty_notMem (𝓝[≠] x)
      simp_all
    simp at ha
  · exact hfg.filter_mono nhdsWithin_le_nhds

/-- A continuous map from a compact space to a Hausdorff space is a closed map. -/
/-
**Continuous.isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X → Y}, Continuous f → IsClo
sedMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s

--- 原说明 ---
A continuous map from a compact space to a Hausdorff space is a closed map.
-/
protected theorem Continuous.isClosedMap [CompactSpace X] [T2Space Y] {f : X → Y}
    (h : Continuous f) : IsClosedMap f := fun _s hs => (hs.isCompact.image h).isClosed

/-- A continuous injective map from a compact space to a Hausdorff space is a closed embedding. -/
/-
**Continuous.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.isClosedEmbedding [CompactSpace X] [T2Space Y] {f : X -> Y} (h 
: Continuous f) (hf : Function.Injective f) : IsClosedEmbedding f
参数：h : Continuous f；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap`：∀ {X : T
ype u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topolo
gicalSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…

--- 原说明 ---
A continuous injective map from a compact space to a Hausdorff space is a closed
 embedding.
-/
theorem Continuous.isClosedEmbedding [CompactSpace X] [T2Space Y] {f : X → Y} (h : Continuous f)
    (hf : Function.Injective f) : IsClosedEmbedding f :=
  .of_continuous_injective_isClosedMap h hf h.isClosedMap

/-- A continuous surjective map from a compact space to a Hausdorff space is a quotient map. -/
/-
**Topology.IsQuotientMap.of_surjective_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsQuotientMap.of_surjective_continuous [CompactSpace X] [T2Space 
Y] {f : X -> Y} (hsurj : Surjective f) (hcont : Continuous f) : IsQuotientMap f
参数：hsurj : Surjective f；hcont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → Cont
inuous f → Func…
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…

--- 原说明 ---
A continuous surjective map from a compact space to a Hausdorff space is a quoti
ent map.
-/
theorem Topology.IsQuotientMap.of_surjective_continuous [CompactSpace X] [T2Space Y] {f : X → Y}
    (hsurj : Surjective f) (hcont : Continuous f) : IsQuotientMap f :=
  hcont.isClosedMap.isQuotientMap hcont hsurj
/-
**isPreirreducible_iff_forall_mem_subset_closure_singleton** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：isPreirreducible_iff_forall_mem_subset_closure_singleton [R1Space X] {S : 
Set X} : IsPreirreducible S ↔ forall x in S, S subseteq closure {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `r1_separation`：r1_separation {x y : X} (h : ¬Inseparable x y) : exists u
 v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v
· 使用定理 `Specializes.mem_closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x
 y : X}, x ⤳ y → y ∈ closure {x}
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Set.Nonempty.not_disjoint`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempt
y → ¬Disjoint s t
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
-/
theorem isPreirreducible_iff_forall_mem_subset_closure_singleton [R1Space X] {S : Set X} :
    IsPreirreducible S ↔ ∀ x ∈ S, S ⊆ closure {x} := by
  constructor
  · intro h x hx y hy
    by_contra e
    obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := r1_separation fun h => e h.specializes.mem_closure
    exact ((h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩).mono inter_subset_right).not_disjoint h'
  · intro h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
    exact ⟨x, hxs, hxu, (specializes_iff_mem_closure.mpr (h x hxs hys)).mem_open hv hyv⟩
/-
**isPreirreducible_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreirreducible_iff_subsingleton [T2Space X] {S : Set X} : IsPreirreducib
le S ↔ S.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPreirreducible_iff_subsingleton [T2Space X] {S : Set X} :
    IsPreirreducible S ↔ S.Subsingleton := by
  simp [isPreirreducible_iff_forall_mem_subset_closure_singleton, Set.Subsingleton, eq_comm]

-- todo: use `alias` + `attribute [protected]` once we get `attribute [protected]`
/-
**IsPreirreducible.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsPreirreducible`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X] {S : Set X}, IsPr
eirreducible S → S.Subsingleton
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPreirreducible_iff_subsingleton`：isPreirreducible_iff_subsingleton [T2
Space X] {S : Set X} : IsPreirreducible S ↔ S.Subsingleton
-/
protected lemma IsPreirreducible.subsingleton [T2Space X] {S : Set X} (h : IsPreirreducible S) :
    S.Subsingleton :=
  isPreirreducible_iff_subsingleton.1 h
/-
**isIrreducible_iff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIrreducible_iff_singleton [T2Space X] {S : Set X} : IsIrreducible S ↔ ex
ists x, S = {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIrreducible.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Se
t X), IsIrreducible s = (s.Nonempty ∧ IsPreirreducible s)
· 使用定理 `isPreirreducible_iff_subsingleton`：isPreirreducible_iff_subsingleton [T2
Space X] {S : Set X} : IsPreirreducible S ↔ S.Subsingleton
· 使用定理 `Set.exists_eq_singleton_iff_nonempty_subsingleton`：exists_eq_singleton_i
ff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIrreducible_iff_singleton [T2Space X] {S : Set X} : IsIrreducible S ↔ ∃ x, S = {x} := by
  rw [IsIrreducible, isPreirreducible_iff_subsingleton,
    exists_eq_singleton_iff_nonempty_subsingleton]

/-- There does not exist a nontrivial preirreducible T₂ space. -/
/-
**not_preirreducible_nontrivial_t2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_preirreducible_nontrivial_t2 (X) [TopologicalSpace X] [PreirreducibleS
pace X] [Nontrivial X] [T2Space X] : False
参数：X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.not_nontrivial`：∀ {α : Type u} {s : Set α}, s.Subsingle
ton → ¬s.Nontrivial
· 使用定理 `IsPreirreducible.subsingleton`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [T2Space X] {S : Set X}, IsPreirreducible S → S.Subsingleton
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
· 使用定理 `Set.nontrivial_univ`：nontrivial_univ [Nontrivial α] : (univ : Set α).Non
trivial

--- 原说明 ---
There does not exist a nontrivial preirreducible T₂ space.
-/
theorem not_preirreducible_nontrivial_t2 (X) [TopologicalSpace X] [PreirreducibleSpace X]
    [Nontrivial X] [T2Space X] : False :=
  (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton.not_nontrivial nontrivial_univ
/-
**t2Space_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：t2Space_antitone {X : Type*} : Antitone (@T2Space X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.of_injective_continuous`：T2Space.of_injective_continuous [Topolo
gicalSpace Y] [T2Space Y] {f : X -> Y} (hinj : Injective f) (hc : Continuous f) 
: T2Space X
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `continuous_id_of_le`：continuous_id_of_le {t t' : TopologicalSpace α} (h 
: t <= t') : Continuous[t, t'] id
-/
theorem t2Space_antitone {X : Type*} : Antitone (@T2Space X) :=
  fun inst₁ inst₂ h_top h_t2 ↦ @T2Space.of_injective_continuous _ _ inst₁ inst₂
    h_t2 _ Function.injective_id <| continuous_id_of_le h_top

end Separation

