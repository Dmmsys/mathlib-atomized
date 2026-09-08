/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Topology.Algebra.Group.Compact

/-!
# Haar measure

In this file we prove the existence of Haar measure for a locally compact Hausdorff topological
group.

We follow the write-up by Jonathan Gleason, *Existence and Uniqueness of Haar Measure*.
This is essentially the same argument as in
https://en.wikipedia.org/wiki/Haar_measure#A_construction_using_compact_subsets.

We construct the Haar measure first on compact sets. For this we define `(K : U)` as the (smallest)
number of left-translates of `U` that are needed to cover `K` (`index` in the formalization).
Then we define a function `h` on compact sets as `lim_U (K : U) / (K₀ : U)`,
where `U` becomes a smaller and smaller open neighborhood of `1`, and `K₀` is a fixed compact set
with nonempty interior. This function is `chaar` in the formalization, and we define the limit
formally using Tychonoff's theorem.

This function `h` forms a content, which we can extend to an outer measure and then a measure
(`haarMeasure`).
We normalize the Haar measure so that the measure of `K₀` is `1`.

Note that `μ` need not coincide with `h` on compact sets, according to
[halmos1950measure, ch. X, §53 p.233]. However, we know that `h(K)` lies between `μ(Kᵒ)` and `μ(K)`,
where `ᵒ` denotes the interior.

We also give a form of uniqueness of Haar measure, for σ-finite measures on second-countable
locally compact groups. For more involved statements not assuming second-countability, see
the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.

## Main Declarations

* `haarMeasure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.
* `haarMeasure_self`: the Haar measure is normalized.
* `isMulLeftInvariant_haarMeasure`: the Haar measure is left invariant.
* `regular_haarMeasure`: the Haar measure is a regular measure.
* `isHaarMeasure_haarMeasure`: the Haar measure satisfies the `IsHaarMeasure` typeclass, i.e.,
  it is invariant and gives finite mass to compact sets and positive mass to nonempty open sets.
* `haar` : some choice of a Haar measure, on a locally compact Hausdorff group, constructed as
  `haarMeasure K` where `K` is some arbitrary choice of a compact set with nonempty interior.
* `haarMeasure_unique`: Every σ-finite left invariant measure on a second-countable locally compact
  Hausdorff group is a scalar multiple of the Haar measure.

## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
* https://en.wikipedia.org/wiki/Haar_measure
-/

@[expose] public section


noncomputable section

open Set Inv Function TopologicalSpace MeasurableSpace

open scoped NNReal ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

section Group

variable {G : Type*} [Group G]

/-! We put the internal functions in the construction of the Haar measure in a namespace,
  so that the chosen names don't clash with other declarations.
  We first define a couple of the functions before proving the properties (that require that `G`
  is a topological group). -/


namespace haar

/-- The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cover `K`.
  It is defined to be 0 if no finite number of translates cover `K`. -/
@[to_additive addIndex /-- additive version of `MeasureTheory.Measure.haar.index` -/]
/-
**MeasureTheory.Measure.haar.index** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Meas
ure.haar`。
形式化陈述：index (K V : Set G) : Nat
参数：K V : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cov
er `K`.
  It is defined to be 0 if no finite number of translates cover `K`.
-/
noncomputable def index (K V : Set G) : ℕ :=
  sInf <| Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V }

@[to_additive addIndex_empty]
/-
**MeasureTheory.Measure.haar.index_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.haar`。
形式化陈述：index_empty {V : Set G} : index ∅ V = 0
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
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem index_empty {V : Set G} : index ∅ V = 0 := by simp [index]

variable [TopologicalSpace G]

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haarProduct` (below). -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.prehaar` -/]
/-
**MeasureTheory.Measure.haar.prehaar** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Me
asure.haar`。
形式化陈述：prehaar (K₀ U : Set G) (K : Compacts G) : Real
参数：K₀ U : Set G；K : Compacts G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U
)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open conta
ining `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar 
K₀ U` as an
  element of `haarProduct` (below).
-/
noncomputable def prehaar (K₀ U : Set G) (K : Compacts G) : ℝ :=
  (index (K : Set G) U : ℝ) / index K₀ U

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure.haar`。
形式化陈述：prehaar_empty (K₀ : PositiveCompacts G) {U : Set G} : prehaar (K₀ : Set G)
 U ⊥ = 0
参数：K₀ : PositiveCompacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haar.prehaar.eq_1`：∀ {G : Type u_1} [inst : Group 
G] [inst_1 : TopologicalSpace G] (K₀ U : Set G) (K : TopologicalSpace.Compacts G
),   MeasureTheory.Measure.ha…
· 使用定理 `TopologicalSpace.Compacts.coe_bot`：coe_bot : (↑(⊥ : Compacts α) : Set α)
 = ∅
· 使用定理 `MeasureTheory.Measure.haar.index_empty`：index_empty {V : Set G} : index 
∅ V = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
-/
theorem prehaar_empty (K₀ : PositiveCompacts G) {U : Set G} : prehaar (K₀ : Set G) U ⊥ = 0 := by
  rw [prehaar, Compacts.coe_bot, index_empty, Nat.cast_zero, zero_div]

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.haar`。
形式化陈述：prehaar_nonneg (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) : 0 
<= prehaar (K₀ : Set G) U K
参数：K₀ : PositiveCompacts G；K : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem prehaar_nonneg (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) :
    0 ≤ prehaar (K₀ : Set G) U K := by apply div_nonneg <;> norm_cast <;> apply zero_le

/-- `haarProduct K₀` is the product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haarProduct K₀`. -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.haarProduct` -/]
/-
**MeasureTheory.Measure.haar.haarProduct** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Measure.haar`。
形式化陈述：haarProduct (K₀ : Set G) : Set (Compacts G -> Real)
参数：K₀ : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`haarProduct K₀` is the product of intervals `[0, (K : K₀)]`, for all compact se
ts `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haarProduct K₀`.
-/
def haarProduct (K₀ : Set G) : Set (Compacts G → ℝ) :=
  pi univ fun K => Icc 0 <| index (K : Set G) K₀

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.haar.mem_prehaar_empty** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.haar`。
形式化陈述：mem_prehaar_empty {K₀ : Set G} {f : Compacts G -> Real} : f in haarProduct
 K₀ ↔ forall K : Compacts G, f K in Icc (0 : Real) (index (K : Set G) K₀)
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_prehaar_empty {K₀ : Set G} {f : Compacts G → ℝ} :
    f ∈ haarProduct K₀ ↔ ∀ K : Compacts G, f K ∈ Icc (0 : ℝ) (index (K : Set G) K₀) := by
  simp only [haarProduct, Set.pi, forall_prop_of_true, mem_univ, mem_ofPred_eq]

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.clPrehaar` -/]
/-
**MeasureTheory.Measure.haar.clPrehaar** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
Measure.haar`。
形式化陈述：clPrehaar (K₀ : Set G) (V : OpenNhdsOf (1 : G)) : Set (Compacts G -> Real)
参数：K₀ : Set G；V : OpenNhdsOf (1 : G)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in 
the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar meas
ure
  on compact sets is defined to be an element in the closure of this intersectio
n.
-/
def clPrehaar (K₀ : Set G) (V : OpenNhdsOf (1 : G)) : Set (Compacts G → ℝ) :=
  closure <| prehaar K₀ '' { U : Set G | U ⊆ V.1 ∧ IsOpen U ∧ (1 : G) ∈ U }

variable [IsTopologicalGroup G]

/-!
### Lemmas about `index`
-/


/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
@[to_additive addIndex_defined
/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/]
/-
**MeasureTheory.Measure.haar.index_defined** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure.haar`。
形式化陈述：index_defined {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty
) : exists n : Nat, n in Finset.card '' { t : Finset G | K subseteq ⋃ g in t, (f
un h => g * h) ⁻¹' V }
参数：hK : IsCompact K；hV : (interior V).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compact_covered_by_mul_left_translates`：compact_covered_by_mul_left_tran
slates {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) : exists t 
: Finset G, K subseteq ⋃ g i…
-/
theorem index_defined {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    ∃ n : ℕ, n ∈ Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V } := by
  rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩; exact ⟨t.card, t, ht, rfl⟩

@[to_additive addIndex_elim]
/-
**MeasureTheory.Measure.haar.index_elim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.haar`。
形式化陈述：index_elim {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
 exists t : Finset G, (K subseteq ⋃ g in t, (fun h => g * h) ⁻¹' V) ∧ Finset.car
d t = index K V
参数：hK : IsCompact K；hV : (interior V).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `MeasureTheory.Measure.haar.index_defined`：index_defined {K V : Set G} (h
K : IsCompact K) (hV : (interior V).Nonempty) : exists n : Nat, n in Finset.card
 '' { t : Finset G | K subsete…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem index_elim {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    ∃ t : Finset G, (K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V) ∧ Finset.card t = index K V := by
  have := Nat.sInf_mem (index_defined hK hV); rwa [mem_image] at this

@[to_additive le_addIndex_mul]
/-
**MeasureTheory.Measure.haar.le_index_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.haar`。
形式化陈述：le_index_mul (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G} (hV : 
(interior V).Nonempty) : index (K : Set G) V <= index (K : Set G) K₀ * index (K₀
 : Set G) V
参数：K₀ : PositiveCompacts G；K : Compacts G；hV : (interior V).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.index_elim`：index_elim {K V : Set G} (hK : Is
Compact K) (hV : (interior V).Nonempty) : exists t : Finset G, (K subseteq ⋃ g i
n t, (fun h => g * h) ⁻¹' V…
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.preimage_subset_iff`：preimage_subset_iff {A : Set α} {B : Set β} {f 
: α -> β} : f ⁻¹' B subseteq A ↔ forall a : α, f a in B -> a in A
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Finset.card_mul_le`：card_mul_le : #(s * t) <= #s * #t
-/
theorem le_index_mul (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G}
    (hV : (interior V).Nonempty) :
    index (K : Set G) V ≤ index (K : Set G) K₀ * index (K₀ : Set G) V := by
  classical
  obtain ⟨s, h1s, h2s⟩ := index_elim K.isCompact K₀.interior_nonempty
  obtain ⟨t, h1t, h2t⟩ := index_elim K₀.isCompact hV
  rw [← h2s, ← h2t, mul_comm]
  refine le_trans ?_ Finset.card_mul_le
  apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_ofPred_eq]; refine Subset.trans h1s ?_
  apply iUnion₂_subset; intro g₁ hg₁; rw [preimage_subset_iff]; intro g₂ hg₂
  have := h1t hg₂
  rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, h2V⟩; rw [mem_preimage, ← mul_assoc] at h2V
  exact mem_biUnion (Finset.mul_mem_mul hg₃ hg₁) h2V

set_option backward.isDefEq.respectTransparency false in
@[to_additive addIndex_pos]
/-
**MeasureTheory.Measure.haar.index_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure.haar`。
形式化陈述：index_pos (K : PositiveCompacts G) {V : Set G} (hV : (interior V).Nonempty
) : 0 < index (K : Set G) V
参数：K : PositiveCompacts G；hV : (interior V).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haar.index.eq_1`：∀ {G : Type u_1} [inst : Group G]
 (K V : Set G),   MeasureTheory.Measure.haar.index K V = sInf (Finset.card '' {t
 | K ⊆ ⋃ g ∈ t, (fun h => g…
· 使用定理 `MeasureTheory.Measure.haar.index_defined`：index_defined {K V : Set G} (h
K : IsCompact K) (hV : (interior V).Nonempty) : exists n : Nat, n in Finset.card
 '' { t : Finset G | K subsete…
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `Nat.sInf_def`：sInf_def {s : Set Nat} (h : s.Nonempty) : sInf s = @Nat.fi
nd (fun n => n in s) _ h
· 使用引理 `Nat.find_pos`：find_pos (h : exists n : Nat, p n) : 0 < Nat.find h ↔ ¬p 0
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
-/
theorem index_pos (K : PositiveCompacts G) {V : Set G} (hV : (interior V).Nonempty) :
    0 < index (K : Set G) V := by
  classical
  rw [index, Nat.sInf_def, Nat.find_pos, mem_image]
  · rintro ⟨t, h1t, h2t⟩; rw [Finset.card_eq_zero] at h2t; subst h2t
    obtain ⟨g, hg⟩ := K.interior_nonempty
    change g ∈ (∅ : Set G)
    convert! h1t (interior_subset hg); symm
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
  · exact index_defined K.isCompact hV

@[to_additive addIndex_mono]
/-
**MeasureTheory.Measure.haar.index_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.haar`。
形式化陈述：index_mono {K K' V : Set G} (hK' : IsCompact K') (h : K subseteq K') (hV :
 (interior V).Nonempty) : index K V <= index K' V
参数：hK' : IsCompact K'；h : K subseteq K'；hV : (interior V).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.index_elim`：index_elim {K V : Set G} (hK : Is
Compact K) (hV : (interior V).Nonempty) : exists t : Finset G, (K subseteq ⋃ g i
n t, (fun h => g * h) ⁻¹' V…
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
theorem index_mono {K K' V : Set G} (hK' : IsCompact K') (h : K ⊆ K') (hV : (interior V).Nonempty) :
    index K V ≤ index K' V := by
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
  apply Nat.sInf_le; rw [mem_image]; exact ⟨s, Subset.trans h h1s, h2s⟩

@[to_additive addIndex_union_le]
/-
**MeasureTheory.Measure.haar.index_union_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.haar`。
形式化陈述：index_union_le (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempt
y) : index (K₁.1 union K₂.1) V <= index K₁.1 V + index K₂.1 V
参数：K₁ K₂ : Compacts G；hV : (interior V).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.index_elim`：index_elim {K V : Set G} (hK : Is
Compact K) (hV : (interior V).Nonempty) : exists t : Finset G, (K subseteq ⋃ g i
n t, (fun h => g * h) ⁻¹' V…
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Finset.set_biUnion_union`：set_biUnion_union (s t : Finset α) (u : α -> S
et β) : ⋃ x in s union t, u x = (⋃ x in s, u x) union ⋃ x in t, u x
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
-/
theorem index_union_le (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty) :
    index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V + index K₂.1 V := by
  classical
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
  rw [← h2s, ← h2t]
  refine le_trans (Nat.sInf_le ⟨_, ?_, rfl⟩) (Finset.card_union_le _ _)
  rw [mem_ofPred_eq, Finset.set_biUnion_union]
  gcongr

@[to_additive addIndex_union_eq]
/-
**MeasureTheory.Measure.haar.index_union_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.haar`。
形式化陈述：index_union_eq (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempt
y) (h : Disjoint (K₁.1 * V⁻¹) (K₂.1 * V⁻¹)) : index (K₁.1 union K₂.1) V = index 
K₁.1 V + index K₂.1 V
参数：K₁ K₂ : Compacts G；hV : (interior V).Nonempty；h : Disjoint (K₁.1 * V⁻¹) (K₂.1
 * V⁻¹)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.haar.index_union_le`：index_union_le (K₁ K₂ : Compa
cts G) {V : Set G} (hV : (interior V).Nonempty) : index (K₁.1 union K₂.1) V <= i
ndex K₁.1 V + index K₂.1 V
· 使用定理 `MeasureTheory.Measure.haar.index_elim`：index_elim {K V : Set G} (hK : Is
Compact K) (hV : (interior V).Nonempty) : exists t : Finset G, (K subseteq ⋃ g i
n t, (fun h => g * h) ⁻¹' V…
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
（共 34 条，此处仅展示前 30 条）
-/
theorem index_union_eq (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
    (h : Disjoint (K₁.1 * V⁻¹) (K₂.1 * V⁻¹)) :
    index (K₁.1 ∪ K₂.1) V = index K₁.1 V + index K₂.1 V := by
  classical
  apply le_antisymm (index_union_le K₁ K₂ hV)
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  have (K : Set G) (hK : K ⊆ ⋃ g ∈ s, (g * ·) ⁻¹' V) :
      index K V ≤ {g ∈ s | ((g * ·) ⁻¹' V ∩ K).Nonempty}.card := by
    apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_ofPred_eq]
    intro g hg; rcases hK hg with ⟨_, ⟨g₀, rfl⟩, _, ⟨h1g₀, rfl⟩, h2g₀⟩
    simp only [mem_preimage] at h2g₀
    simp only [mem_iUnion]; use g₀; constructor; swap
    · simp only [Finset.mem_filter, h1g₀, true_and]; use g
      simp [hg, h2g₀]
    exact h2g₀
  refine
    le_trans
      (add_le_add (this K₁.1 <| Subset.trans subset_union_left h1s)
        (this K₂.1 <| Subset.trans subset_union_right h1s)) ?_
  rw [← Finset.card_union_of_disjoint, Finset.filter_union_right]
  · exact s.card_filter_le _
  apply Finset.disjoint_filter.mpr
  rintro g₁ _ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩
  simp only [mem_preimage] at h1g₃ h1g₂
  refine h.le_bot (?_ : g₁⁻¹ ∈ _)
  constructor <;> simp only [Set.mem_inv, Set.mem_mul]
  · refine ⟨_, h2g₂, (g₁ * g₂)⁻¹, ?_, ?_⟩
    · simp only [inv_inv, h1g₂]
    · simp only [mul_inv_rev, mul_inv_cancel_left]
  · refine ⟨_, h2g₃, (g₁ * g₃)⁻¹, ?_, ?_⟩
    · simp only [inv_inv, h1g₃]
    · simp only [mul_inv_rev, mul_inv_cancel_left]

@[to_additive add_left_addIndex_le]
/-
**MeasureTheory.Measure.haar.mul_left_index_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.haar`。
形式化陈述：mul_left_index_le {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (interi
or V).Nonempty) (g : G) : index ((fun h => g * h) '' K) V <= index K V
参数：hK : IsCompact K；hV : (interior V).Nonempty；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.index_elim`：index_elim {K V : Set G} (hK : Is
Compact K) (hV : (interior V).Nonempty) : exists t : Finset G, (K subseteq ⋃ g i
n t, (fun h => g * h) ⁻¹' V…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem mul_left_index_le {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (interior V).Nonempty)
    (g : G) : index ((fun h => g * h) '' K) V ≤ index K V := by
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  apply Nat.sInf_le; rw [mem_image]
  refine ⟨s.map (Equiv.mulRight g⁻¹).toEmbedding, ?_, Finset.card_map _⟩
  simp only [mem_ofPred_eq]; refine Subset.trans (image_mono h1s) ?_
  rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
  simp only [mem_preimage] at hg₁
  simp only [exists_prop, mem_iUnion, Finset.mem_map, Equiv.coe_mulRight,
    exists_exists_and_eq_and, mem_preimage, Equiv.toEmbedding_apply]
  refine ⟨_, hg₂, ?_⟩; simp only [mul_assoc, hg₁, inv_mul_cancel_left]

@[to_additive is_left_invariant_addIndex]
/-
**MeasureTheory.Measure.haar.is_left_invariant_index** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.haar`。
形式化陈述：is_left_invariant_index {K : Set G} (hK : IsCompact K) (g : G) {V : Set G}
 (hV : (interior V).Nonempty) : index ((fun h => g * h) '' K) V = index K V
参数：hK : IsCompact K；g : G；hV : (interior V).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.Measure.haar.mul_left_index_le`：mul_left_index_le {K : Set
 G} (hK : IsCompact K) {V : Set G} (hV : (interior V).Nonempty) (g : G) : index 
((fun h => g * h) '' K) V <= index…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem is_left_invariant_index {K : Set G} (hK : IsCompact K) (g : G) {V : Set G}
    (hV : (interior V).Nonempty) : index ((fun h => g * h) '' K) V = index K V := by
  refine le_antisymm (mul_left_index_le hK hV g) ?_
  convert! mul_left_index_le (hK.image <| continuous_const_mul g) hV g⁻¹
  rw [image_image]
  simp

/-!
### Lemmas about `prehaar`
-/


@[to_additive add_prehaar_le_addIndex]
/-
**MeasureTheory.Measure.haar.prehaar_le_index** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.haar`。
形式化陈述：prehaar_le_index (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) (h
U : (interior U).Nonempty) : prehaar (K₀ : Set G) U K <= index (K : Set G) K₀
参数：K₀ : PositiveCompacts G；K : Compacts G；hU : (interior U).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.haar.index_pos`：index_pos (K : PositiveCompacts G)
 {V : Set G} (hV : (interior V).Nonempty) : 0 < index (K : Set G) V
· 使用定理 `MeasureTheory.Measure.haar.le_index_mul`：le_index_mul (K₀ : PositiveComp
acts G) (K : Compacts G) {V : Set G} (hV : (interior V).Nonempty) : index (K : S
et G) V <= index (K : Set G) …

--- 原说明 ---
### Lemmas about `prehaar`
-/
theorem prehaar_le_index (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
    (hU : (interior U).Nonempty) : prehaar (K₀ : Set G) U K ≤ index (K : Set G) K₀ := by
  unfold prehaar; rw [div_le_iff₀] <;> norm_cast
  · apply le_index_mul K₀ K hU
  · exact index_pos K₀ hU

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.haar`。
形式化陈述：prehaar_pos (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonem
pty) {K : Set G} (h1K : IsCompact K) (h2K : (interior K).Nonempty) : 0 < prehaar
 (K₀ : Set G) U ⟨K, h1K⟩
参数：K₀ : PositiveCompacts G；hU : (interior U).Nonempty；h1K : IsCompact K；h2K : (i
nterior K).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.haar.index_pos`：index_pos (K : PositiveCompacts G)
 {V : Set G} (hV : (interior V).Nonempty) : 0 < index (K : Set G) V
-/
theorem prehaar_pos (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) {K : Set G}
    (h1K : IsCompact K) (h2K : (interior K).Nonempty) : 0 < prehaar (K₀ : Set G) U ⟨K, h1K⟩ := by
  apply div_pos <;> norm_cast
  · apply index_pos ⟨⟨K, h1K⟩, h2K⟩ hU
  · exact index_pos K₀ hU

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.haar`。
形式化陈述：prehaar_mono {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).None
mpty) {K₁ K₂ : Compacts G} (h : (K₁ : Set G) subseteq K₂.1) : prehaar (K₀ : Set 
G) U K₁ <= prehaar (K₀ : Set G) U K₂
参数：hU : (interior U).Nonempty；h : (K₁ : Set G) subseteq K₂.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.haar.index_pos`：index_pos (K : PositiveCompacts G)
 {V : Set G} (hV : (interior V).Nonempty) : 0 < index (K : Set G) V
· 使用定理 `MeasureTheory.Measure.haar.index_mono`：index_mono {K K' V : Set G} (hK' 
: IsCompact K') (h : K subseteq K') (hV : (interior V).Nonempty) : index K V <= 
index K' V
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
-/
theorem prehaar_mono {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    {K₁ K₂ : Compacts G} (h : (K₁ : Set G) ⊆ K₂.1) :
    prehaar (K₀ : Set G) U K₁ ≤ prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [div_le_div_iff_of_pos_right]
  · exact mod_cast index_mono K₂.2 h hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.haar`。
形式化陈述：prehaar_self {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).None
mpty) : prehaar (K₀ : Set G) U K₀.toCompacts = 1
参数：hU : (interior U).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.haar.index_pos`：index_pos (K : PositiveCompacts G)
 {V : Set G} (hV : (interior V).Nonempty) : 0 < index (K : Set G) V
-/
theorem prehaar_self {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U K₀.toCompacts = 1 :=
  div_self <| ne_of_gt <| mod_cast index_pos K₀ hU

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_sup_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.haar`。
形式化陈述：prehaar_sup_le {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G) 
(hU : (interior U).Nonempty) : prehaar (K₀ : Set G) U (K₁ ⊔ K₂) <= prehaar (K₀ :
 Set G) U K₁ + prehaar (K₀ : Set G) U K₂
参数：K₁ K₂ : Compacts G；hU : (interior U).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.haar.index_pos`：index_pos (K : PositiveCompacts G)
 {V : Set G} (hV : (interior V).Nonempty) : 0 < index (K : Set G) V
· 使用定理 `MeasureTheory.Measure.haar.index_union_le`：index_union_le (K₁ K₂ : Compa
cts G) {V : Set G} (hV : (interior V).Nonempty) : index (K₁.1 union K₂.1) V <= i
ndex K₁.1 V + index K₂.1 V
-/
theorem prehaar_sup_le {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G)
    (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) ≤ prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [← add_div, div_le_div_iff_of_pos_right]
  · exact mod_cast index_union_le K₁ K₂ hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.haar`。
形式化陈述：prehaar_sup_eq {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G} 
(hU : (interior U).Nonempty) (h : Disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)) : prehaar 
(K₀ : Set G) U (K₁ ⊔ K₂) = prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂
参数：hU : (interior U).Nonempty；h : Disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.haar.index_union_eq`：index_union_eq (K₁ K₂ : Compa
cts G) {V : Set G} (hV : (interior V).Nonempty) (h : Disjoint (K₁.1 * V⁻¹) (K₂.1
 * V⁻¹)) : index (K₁.1 union K₂…
-/
theorem prehaar_sup_eq {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G}
    (hU : (interior U).Nonempty) (h : Disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) = prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [← add_div]
  -- Porting note: Here was `congr`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : ℝ => x / index K₀ U) ?_
  exact mod_cast index_union_eq K₁ K₂ hU h

@[to_additive]
/-
**MeasureTheory.Measure.haar.is_left_invariant_prehaar** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure.haar`。
形式化陈述：is_left_invariant_prehaar {K₀ : PositiveCompacts G} {U : Set G} (hU : (int
erior U).Nonempty) (g : G) (K : Compacts G) : prehaar (K₀ : Set G) U (K.map _ <|
 continuous_const_mul g) = prehaar (K₀ : Set G) U K
参数：hU : (interior U).Nonempty；g : G；K : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haar.is_left_invariant_index`：is_left_invariant_in
dex {K : Set G} (hK : IsCompact K) (g : G) {V : Set G} (hV : (interior V).Nonemp
ty) : index ((fun h => g * h) '' K) V = …
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem is_left_invariant_prehaar {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    (g : G) (K : Compacts G) :
    prehaar (K₀ : Set G) U (K.map _ <| continuous_const_mul g) = prehaar (K₀ : Set G) U K := by
  simp only [prehaar, Compacts.coe_map, is_left_invariant_index K.isCompact _ hU]

/-!
### Lemmas about `haarProduct`
-/

@[to_additive]
/-
**MeasureTheory.Measure.haar.prehaar_mem_haarProduct** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.haar`。
形式化陈述：prehaar_mem_haarProduct (K₀ : PositiveCompacts G) {U : Set G} (hU : (inter
ior U).Nonempty) : prehaar (K₀ : Set G) U in haarProduct (K₀ : Set G)
参数：K₀ : PositiveCompacts G；hU : (interior U).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `MeasureTheory.Measure.haar.prehaar_nonneg`：prehaar_nonneg (K₀ : Positive
Compacts G) {U : Set G} (K : Compacts G) : 0 <= prehaar (K₀ : Set G) U K
· 使用定理 `MeasureTheory.Measure.haar.prehaar_le_index`：prehaar_le_index (K₀ : Posi
tiveCompacts G) {U : Set G} (K : Compacts G) (hU : (interior U).Nonempty) : preh
aar (K₀ : Set G) U K <= index (K …

--- 原说明 ---
### Lemmas about `haarProduct`
-/
theorem prehaar_mem_haarProduct (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U ∈ haarProduct (K₀ : Set G) := by
    rintro ⟨K, hK⟩ _; rw [mem_Icc]; exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩

@[to_additive]
/-
**MeasureTheory.Measure.haar.nonempty_iInter_clPrehaar** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure.haar`。
形式化陈述：nonempty_iInter_clPrehaar (K₀ : PositiveCompacts G) : (haarProduct (K₀ : S
et G) inter ⋂ V : OpenNhdsOf (1 : G), clPrehaar K₀ V).Nonempty
参数：K₀ : PositiveCompacts G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_univ_pi`：isCompact_univ_pi {s : forall i, Set (X i)} (h : fora
ll i, IsCompact (s i)) : IsCompact (pi univ s)
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsCompact.inter_iInter_nonempty`：IsCompact.inter_iInter_nonempty {ι : Ty
pe v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst 
: forall u : Finset ι…
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `isOpen_biInter_finset`：isOpen_biInter_finset {s : Finset α} {f : α -> Se
t X} (h : forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.Measure.haar.prehaar_mem_haarProduct`：prehaar_mem_haarProd
uct (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) : prehaar
 (K₀ : Set G) U in haarProduct (K₀ : Set…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem nonempty_iInter_clPrehaar (K₀ : PositiveCompacts G) :
    (haarProduct (K₀ : Set G) ∩ ⋂ V : OpenNhdsOf (1 : G), clPrehaar K₀ V).Nonempty := by
  have : IsCompact (haarProduct (K₀ : Set G)) := by
    apply isCompact_univ_pi; intro K; apply isCompact_Icc
  refine this.inter_iInter_nonempty (clPrehaar K₀) (fun s => isClosed_closure) fun t => ?_
  let V₀ := ⋂ V ∈ t, (V : OpenNhdsOf (1 : G)).carrier
  have h1V₀ : IsOpen V₀ := isOpen_biInter_finset <| by rintro ⟨⟨V, hV₁⟩, hV₂⟩ _; exact hV₁
  have h2V₀ : (1 : G) ∈ V₀ := by simp only [V₀, mem_iInter]; rintro ⟨⟨V, hV₁⟩, hV₂⟩ _; exact hV₂
  refine ⟨prehaar K₀ V₀, ?_⟩
  constructor
  · apply prehaar_mem_haarProduct K₀; use 1; rwa [h1V₀.interior_eq]
  · simp only [mem_iInter]; rintro ⟨V, hV⟩ h2V; apply subset_closure
    apply mem_image_of_mem; rw [mem_ofPred_eq]
    exact ⟨Subset.trans (iInter_subset _ ⟨V, hV⟩) (iInter_subset _ h2V), h1V₀, h2V₀⟩

/-!
### Lemmas about `chaar`
-/

/-- This is the "limit" of `prehaar K₀ U K` as `U` becomes a smaller and smaller open
  neighborhood of `(1 : G)`. More precisely, it is defined to be an arbitrary element
  in the intersection of all the sets `clPrehaar K₀ V` in `haarProduct K₀`.
  This is roughly equal to the Haar measure on compact sets,
  but it can differ slightly. We do know that
  `haarMeasure K₀ (interior K) ≤ chaar K₀ K ≤ haarMeasure K₀ K`. -/
@[to_additive addCHaar /-- additive version of `MeasureTheory.Measure.haar.chaar` -/]
/-
**MeasureTheory.Measure.haar.chaar** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Meas
ure.haar`。
形式化陈述：chaar (K₀ : PositiveCompacts G) (K : Compacts G) : Real
参数：K₀ : PositiveCompacts G；K : Compacts G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.nonempty_iInter_clPrehaar`：nonempty_iInter_cl
Prehaar (K₀ : PositiveCompacts G) : (haarProduct (K₀ : Set G) inter ⋂ V : OpenNh
dsOf (1 : G), clPrehaar K₀ V).Nonempty

--- 原说明 ---
This is the "limit" of `prehaar K₀ U K` as `U` becomes a smaller and smaller ope
n
  neighborhood of `(1 : G)`. More precisely, it is defined to be an arbitrary el
ement
  in the intersection of all the sets `clPrehaar K₀ V` in `haarProduct K₀`.
  This is roughly equal to the Haar measure on compact sets,
  but it can differ slightly. We do know that
  `haarMeasure K₀ (interior K) ≤ chaar K₀ K ≤ haarMeasure K₀ K`.
-/
noncomputable def chaar (K₀ : PositiveCompacts G) (K : Compacts G) : ℝ :=
  Classical.choose (nonempty_iInter_clPrehaar K₀) K

@[to_additive addCHaar_mem_addHaarProduct]
/-
**MeasureTheory.Measure.haar.chaar_mem_haarProduct** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure.haar`。
形式化陈述：chaar_mem_haarProduct (K₀ : PositiveCompacts G) : chaar K₀ in haarProduct 
(K₀ : Set G)
参数：K₀ : PositiveCompacts G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.haar.nonempty_iInter_clPrehaar`：nonempty_iInter_cl
Prehaar (K₀ : PositiveCompacts G) : (haarProduct (K₀ : Set G) inter ⋂ V : OpenNh
dsOf (1 : G), clPrehaar K₀ V).Nonempty
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem chaar_mem_haarProduct (K₀ : PositiveCompacts G) : chaar K₀ ∈ haarProduct (K₀ : Set G) :=
  (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).1

@[to_additive addCHaar_mem_clAddPrehaar]
/-
**MeasureTheory.Measure.haar.chaar_mem_clPrehaar** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.haar`。
形式化陈述：chaar_mem_clPrehaar (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G)) : c
haar K₀ in clPrehaar (K₀ : Set G) V
参数：K₀ : PositiveCompacts G；V : OpenNhdsOf (1 : G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.nonempty_iInter_clPrehaar`：nonempty_iInter_cl
Prehaar (K₀ : PositiveCompacts G) : (haarProduct (K₀ : Set G) inter ⋂ V : OpenNh
dsOf (1 : G), clPrehaar K₀ V).Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem chaar_mem_clPrehaar (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G)) :
    chaar K₀ ∈ clPrehaar (K₀ : Set G) V := by
  have := (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).2; rw [mem_iInter] at this
  exact this V

@[to_additive addCHaar_nonneg]
/-
**MeasureTheory.Measure.haar.chaar_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.haar`。
形式化陈述：chaar_nonneg (K₀ : PositiveCompacts G) (K : Compacts G) : 0 <= chaar K₀ K
参数：K₀ : PositiveCompacts G；K : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.chaar_mem_haarProduct`：chaar_mem_haarProduct 
(K₀ : PositiveCompacts G) : chaar K₀ in haarProduct (K₀ : Set G)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
-/
theorem chaar_nonneg (K₀ : PositiveCompacts G) (K : Compacts G) : 0 ≤ chaar K₀ K := by
  have := chaar_mem_haarProduct K₀ K (mem_univ _); rw [mem_Icc] at this; exact this.1

@[to_additive addCHaar_empty]
/-
**MeasureTheory.Measure.haar.chaar_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.haar`。
形式化陈述：chaar_empty (K₀ : PositiveCompacts G) : chaar K₀ ⊥ = 0
参数：K₀ : PositiveCompacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Measure.haar.prehaar_empty`：prehaar_empty (K₀ : PositiveCo
mpacts G) {U : Set G} : prehaar (K₀ : Set G) U ⊥ = 0
· 使用定理 `MeasureTheory.Measure.haar.chaar_mem_clPrehaar`：chaar_mem_clPrehaar (K₀ 
: PositiveCompacts G) (V : OpenNhdsOf (1 : G)) : chaar K₀ in clPrehaar (K₀ : Set
 G) V
-/
theorem chaar_empty (K₀ : PositiveCompacts G) : chaar K₀ ⊥ = 0 := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f ⊥
  have : Continuous eval := continuous_apply ⊥
  change chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, _, rfl⟩; apply prehaar_empty
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive addCHaar_self]
/-
**MeasureTheory.Measure.haar.chaar_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.haar`。
形式化陈述：chaar_self (K₀ : PositiveCompacts G) : chaar K₀ K₀.toCompacts = 1
参数：K₀ : PositiveCompacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Measure.haar.prehaar_self`：prehaar_self {K₀ : PositiveComp
acts G} {U : Set G} (hU : (interior U).Nonempty) : prehaar (K₀ : Set G) U K₀.toC
ompacts = 1
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `MeasureTheory.Measure.haar.chaar_mem_clPrehaar`：chaar_mem_clPrehaar (K₀ 
: PositiveCompacts G) (V : OpenNhdsOf (1 : G)) : chaar K₀ in clPrehaar (K₀ : Set
 G) V
-/
theorem chaar_self (K₀ : PositiveCompacts G) : chaar K₀ K₀.toCompacts = 1 := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₀.toCompacts
  have : Continuous eval := continuous_apply _
  change chaar K₀ ∈ eval ⁻¹' {(1 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; apply prehaar_self
    rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive addCHaar_mono]
/-
**MeasureTheory.Measure.haar.chaar_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure.haar`。
形式化陈述：chaar_mono {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G
) subseteq K₂) : chaar K₀ K₁ <= chaar K₀ K₂
参数：h : (K₁ : Set G) subseteq K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.haar.prehaar_mono`：prehaar_mono {K₀ : PositiveComp
acts G} {U : Set G} (hU : (interior U).Nonempty) {K₁ K₂ : Compacts G} (h : (K₁ :
 Set G) subseteq K₂.1) : preh…
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `MeasureTheory.Measure.haar.chaar_mem_clPrehaar`：chaar_mem_clPrehaar (K₀ 
: PositiveCompacts G) (V : OpenNhdsOf (1 : G)) : chaar K₀ in clPrehaar (K₀ : Set
 G) V
-/
theorem chaar_mono {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G) ⊆ K₂) :
    chaar K₀ K₁ ≤ chaar K₀ K₂ := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₂ - f K₁
  have : Continuous eval := (continuous_apply K₂).sub (continuous_apply K₁)
  rw [← sub_nonneg]; change chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; simp only [eval, mem_preimage, mem_Ici, sub_nonneg]
    apply prehaar_mono _ h; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_Ici

@[to_additive addCHaar_sup_le]
/-
**MeasureTheory.Measure.haar.chaar_sup_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.haar`。
形式化陈述：chaar_sup_le {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G) : chaar K₀ (K₁
 ⊔ K₂) <= chaar K₀ K₁ + chaar K₀ K₂
参数：K₁ K₂ : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.haar.prehaar_sup_le`：prehaar_sup_le {K₀ : Positive
Compacts G} {U : Set G} (K₁ K₂ : Compacts G) (hU : (interior U).Nonempty) : preh
aar (K₀ : Set G) U (K₁ ⊔ K₂) <=…
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `MeasureTheory.Measure.haar.chaar_mem_clPrehaar`：chaar_mem_clPrehaar (K₀ 
: PositiveCompacts G) (V : OpenNhdsOf (1 : G)) : chaar K₀ in clPrehaar (K₀ : Set
 G) V
-/
theorem chaar_sup_le {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G) :
    chaar K₀ (K₁ ⊔ K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval := by
    exact ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [← sub_nonneg]; change chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; simp only [eval, mem_preimage, mem_Ici, sub_nonneg]
    apply prehaar_sup_le; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_Ici

@[to_additive addCHaar_sup_eq]
/-
**MeasureTheory.Measure.haar.chaar_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure.haar`。
形式化陈述：chaar_sup_eq {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : Disjoint 
K₁.1 K₂.1) (h₂ : IsClosed K₂.1) : chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂
参数：h : Disjoint K₁.1 K₂.1；h₂ : IsClosed K₂.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatedNhds.of_isCompact_isCompact_isClosed`：SeparatedNhds.of_isCompac
t_isCompact_isClosed {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (h'L : 
IsClosed L) (hd : Disjoint K L) : S…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `TopologicalSpace.Compacts.isCompact'`：∀ {α : Type u_4} [inst : Topologic
alSpace α] (self : TopologicalSpace.Compacts α), IsCompact self.carrier
· 使用定理 `compact_open_separated_mul_right`：compact_open_separated_mul_right {K U 
: Set G} (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) : exists V in 𝓝
 (1 : G), K * V subset…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 51 条，此处仅展示前 30 条）
-/
theorem chaar_sup_eq {K₀ : PositiveCompacts G}
    {K₁ K₂ : Compacts G} (h : Disjoint K₁.1 K₂.1) (h₂ : IsClosed K₂.1) :
    chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ := by
  rcases SeparatedNhds.of_isCompact_isCompact_isClosed K₁.2 K₂.2 h₂ h
    with ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩
  rcases compact_open_separated_mul_right K₁.2 h1U₁ h2U₁ with ⟨L₁, h1L₁, h2L₁⟩
  rcases mem_nhds_iff.mp h1L₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩
  replace h2L₁ := Subset.trans (mul_subset_mul_left h1V₁) h2L₁
  rcases compact_open_separated_mul_right K₂.2 h1U₂ h2U₂ with ⟨L₂, h1L₂, h2L₂⟩
  rcases mem_nhds_iff.mp h1L₂ with ⟨V₂, h1V₂, h2V₂, h3V₂⟩
  replace h2L₂ := Subset.trans (mul_subset_mul_left h1V₂) h2L₂
  let eval : (Compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval :=
    ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [eq_comm, ← sub_eq_zero]; change chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  let V := V₁ ∩ V₂
  apply
    mem_of_subset_of_mem _
      (chaar_mem_clPrehaar K₀
        ⟨⟨V⁻¹, (h2V₁.inter h2V₂).preimage continuous_inv⟩, by
          simp only [V, mem_inv, inv_one, h3V₁, h3V₂, mem_inter_iff, true_and]⟩)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [eval, mem_preimage, sub_eq_zero, mem_singleton_iff]; rw [eq_comm]
    apply prehaar_sup_eq
    · rw [h2U.interior_eq]; exact ⟨1, h3U⟩
    · refine disjoint_of_subset ?_ ?_ hU
      · refine Subset.trans (mul_subset_mul Subset.rfl ?_) h2L₁
        exact Subset.trans (inv_subset.mpr h1U) inter_subset_left
      · refine Subset.trans (mul_subset_mul Subset.rfl ?_) h2L₂
        exact Subset.trans (inv_subset.mpr h1U) inter_subset_right
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive is_left_invariant_addCHaar]
/-
**MeasureTheory.Measure.haar.is_left_invariant_chaar** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.haar`。
形式化陈述：is_left_invariant_chaar {K₀ : PositiveCompacts G} (g : G) (K : Compacts G)
 : chaar K₀ (K.map _ <| continuous_const_mul g) = chaar K₀ K
参数：g : G；K : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.haar.is_left_invariant_prehaar`：is_left_invariant_
prehaar {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty) (g : 
G) (K : Compacts G) : prehaar (K₀ : Set G)…
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `MeasureTheory.Measure.haar.chaar_mem_clPrehaar`：chaar_mem_clPrehaar (K₀ 
: PositiveCompacts G) (V : OpenNhdsOf (1 : G)) : chaar K₀ in clPrehaar (K₀ : Set
 G) V
-/
theorem is_left_invariant_chaar {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    chaar K₀ (K.map _ <| continuous_const_mul g) = chaar K₀ K := by
  let eval : (Compacts G → ℝ) → ℝ := fun f => f (K.map _ <| continuous_const_mul g) - f K
  have : Continuous eval := (continuous_apply (K.map _ _)).sub (continuous_apply K)
  rw [← sub_eq_zero]; change chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩
    simp only [eval, mem_singleton_iff, mem_preimage, sub_eq_zero]
    apply is_left_invariant_prehaar; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

set_option backward.isDefEq.respectTransparency false in
/-- The function `chaar` interpreted in `ℝ≥0`, as a content -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.haarContent` -/]
/-
**MeasureTheory.Measure.haar.haarContent** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Measure.haar`。
形式化陈述：haarContent (K₀ : PositiveCompacts G) : Content G where toFun K
参数：K₀ : PositiveCompacts G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.chaar_nonneg`：chaar_nonneg (K₀ : PositiveComp
acts G) (K : Compacts G) : 0 <= chaar K₀ K

--- 原说明 ---
The function `chaar` interpreted in `ℝ≥0`, as a content
-/
noncomputable def haarContent (K₀ : PositiveCompacts G) : Content G where
  toFun K := ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' K₁ K₂ h := by simp only [← NNReal.coe_le_coe, NNReal.toReal, chaar_mono, h]
  sup_disjoint' K₁ K₂ h _h₁ h₂ := by simp only [chaar_sup_eq h]; rfl
  sup_le' K₁ K₂ := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_add]
    simp only [NNReal.toReal, chaar_sup_le]

/-! We only prove the properties for `haarContent` that we use at least twice below. -/


@[to_additive]
/-
**MeasureTheory.Measure.haar.haarContent_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.haar`。
形式化陈述：haarContent_apply (K₀ : PositiveCompacts G) (K : Compacts G) : haarContent
 K₀ K = show NNReal from ⟨chaar K₀ K, chaar_nonneg _ _⟩
参数：K₀ : PositiveCompacts G；K : Compacts G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We only prove the properties for `haarContent` that we use at least twice below.
-/
theorem haarContent_apply (K₀ : PositiveCompacts G) (K : Compacts G) :
    haarContent K₀ K = show NNReal from ⟨chaar K₀ K, chaar_nonneg _ _⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The variant of `chaar_self` for `haarContent` -/
@[to_additive /-- The variant of `addCHaar_self` for `addHaarContent`. -/]
/-
**MeasureTheory.Measure.haar.haarContent_self** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.haar`。
形式化陈述：haarContent_self {K₀ : PositiveCompacts G} : haarContent K₀ K₀.toCompacts 
= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haar.chaar_nonneg`：chaar_nonneg (K₀ : PositiveComp
acts G) (K : Compacts G) : 0 <= chaar K₀ K
· 使用定理 `MeasureTheory.Measure.haar.chaar_self`：chaar_self (K₀ : PositiveCompacts
 G) : chaar K₀ K₀.toCompacts = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩

--- 原说明 ---
The variant of `chaar_self` for `haarContent`
-/
theorem haarContent_self {K₀ : PositiveCompacts G} : haarContent K₀ K₀.toCompacts = 1 := by
  simp_rw [← ENNReal.coe_one, haarContent_apply, ENNReal.coe_inj, chaar_self]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The variant of `is_left_invariant_chaar` for `haarContent` -/
@[to_additive /-- The variant of `is_left_invariant_addCHaar` for `addHaarContent` -/]
/-
**MeasureTheory.Measure.haar.is_left_invariant_haarContent** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.haar`。
形式化陈述：is_left_invariant_haarContent {K₀ : PositiveCompacts G} (g : G) (K : Compa
cts G) : haarContent K₀ (K.map _ <| continuous_const_mul g) = haarContent K₀ K
参数：g : G；K : Compacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.haar.chaar_nonneg`：chaar_nonneg (K₀ : PositiveComp
acts G) (K : Compacts G) : 0 <= chaar K₀ K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.haar.is_left_invariant_chaar`：is_left_invariant_ch
aar {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) : chaar K₀ (K.map _ <| co
ntinuous_const_mul g) = chaar K₀ K

--- 原说明 ---
The variant of `is_left_invariant_chaar` for `haarContent`
-/
theorem is_left_invariant_haarContent {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    haarContent K₀ (K.map _ <| continuous_const_mul g) = haarContent K₀ K := by
  simpa only [ENNReal.coe_inj, ← NNReal.coe_inj, haarContent_apply] using!
    is_left_invariant_chaar g K

@[to_additive]
/-
**MeasureTheory.Measure.haar.haarContent_outerMeasure_self_pos** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure.haar`。
形式化陈述：haarContent_outerMeasure_self_pos (K₀ : PositiveCompacts G) : 0 < (haarCon
tent K₀).outerMeasure K₀
参数：K₀ : PositiveCompacts G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Content.outerMeasure_eq_iInf`：outerMeasure_eq_iInf (A : Se
t G) : μ.outerMeasure A = ⨅ (U : Set G) (hU : IsOpen U) (_ : A subseteq U), μ.in
nerContent ⟨U, hU⟩
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.haar.haarContent_self`：haarContent_self {K₀ : Posi
tiveCompacts G} : haarContent K₀ K₀.toCompacts = 1
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem haarContent_outerMeasure_self_pos (K₀ : PositiveCompacts G) :
    0 < (haarContent K₀).outerMeasure K₀ := by
  refine zero_lt_one.trans_le ?_
  rw [Content.outerMeasure_eq_iInf]
  refine le_iInf₂ fun U hU => le_iInf fun hK₀ => le_trans ?_ <| le_iSup₂ K₀.toCompacts hK₀
  exact haarContent_self.ge

@[to_additive]
/-
**MeasureTheory.Measure.haar.haarContent_outerMeasure_closure_pos** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure.haar`。
形式化陈述：haarContent_outerMeasure_closure_pos (K₀ : PositiveCompacts G) : 0 < (haar
Content K₀).outerMeasure (closure K₀)
参数：K₀ : PositiveCompacts G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.Measure.haar.haarContent_outerMeasure_self_pos`：haarConten
t_outerMeasure_self_pos (K₀ : PositiveCompacts G) : 0 < (haarContent K₀).outerMe
asure K₀
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem haarContent_outerMeasure_closure_pos (K₀ : PositiveCompacts G) :
    0 < (haarContent K₀).outerMeasure (closure K₀) :=
  (haarContent_outerMeasure_self_pos K₀).trans_le (OuterMeasure.mono _ subset_closure)

end haar

open haar

/-!
### The Haar measure
-/

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar measure on the locally compact group `G`, scaled so that `haarMeasure K₀ K₀ = 1`. -/
@[to_additive
/-- The Haar measure on the locally compact additive group `G`, scaled so that
`addHaarMeasure K₀ K₀ = 1`. -/]
/-
**MeasureTheory.Measure.haarMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：haarMeasure (K₀ : PositiveCompacts G) : Measure G
参数：K₀ : PositiveCompacts G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def haarMeasure (K₀ : PositiveCompacts G) : Measure G :=
  ((haarContent K₀).measure K₀)⁻¹ • (haarContent K₀).measure

@[to_additive]
/-
**MeasureTheory.Measure.haarMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：haarMeasure_apply {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSe
t s) : haarMeasure K₀ s = (haarContent K₀).outerMeasure s / (haarContent K₀).mea
sure K₀
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Content.measure_apply`：measure_apply {s : Set G} (hs : Mea
surableSet s) : μ.measure s = μ.outerMeasure s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem haarMeasure_apply {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSet s) :
    haarMeasure K₀ s = (haarContent K₀).outerMeasure s / (haarContent K₀).measure K₀ := by
  change ((haarContent K₀).measure K₀)⁻¹ * (haarContent K₀).measure s = _
  simp only [hs, div_eq_mul_inv, mul_comm, Content.measure_apply]

@[to_additive]
/-
**MeasureTheory.Measure.isMulLeftInvariant_haarMeasure** 是 Mathlib 中的一个实例，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：isMulLeftInvariant_haarMeasure (K₀ : PositiveCompacts G) : IsMulLeftInvari
ant (haarMeasure K₀)
参数：K₀ : PositiveCompacts G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.forall_measure_preimage_mul_iff`：forall_measure_preimage_m
ul_iff (μ : Measure G) : (forall (g : G) (A : Set G), MeasurableSet A -> μ ((fun
 h => g * h) ⁻¹' A) = μ A) ↔ IsMulL…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `MeasureTheory.Measure.haarMeasure_apply`：haarMeasure_apply {K₀ : Positiv
eCompacts G} {s : Set G} (hs : MeasurableSet s) : haarMeasure K₀ s = (haarConten
t K₀).outerMeasure s / (haarC…
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.Content.is_mul_left_invariant_outerMeasure`：is_mul_left_in
variant_outerMeasure [Group G] [SeparatelyContinuousMul G] (h : forall (g : G) {
K : Compacts G}, μ (K.map _ <| continuous_cons…
· 使用定理 `MeasureTheory.Measure.haar.is_left_invariant_haarContent`：is_left_invari
ant_haarContent {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) : haarContent
 K₀ (K.map _ <| continuous_const_mul g) = haar…
-/
instance isMulLeftInvariant_haarMeasure (K₀ : PositiveCompacts G) :
    IsMulLeftInvariant (haarMeasure K₀) := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  rw [haarMeasure_apply hA, haarMeasure_apply (measurable_const_mul g hA)]
  -- Porting note: Here was `congr 1`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : ℝ≥0∞ => x / (haarContent K₀).measure K₀) ?_
  apply Content.is_mul_left_invariant_outerMeasure
  apply is_left_invariant_haarContent

@[to_additive]
/-
**MeasureTheory.Measure.haarMeasure_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：haarMeasure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ K₀ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group`：Topologi
calSpace.PositiveCompacts.locallyCompactSpace_of_group (K : PositiveCompacts G) 
: LocallyCompactSpace G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.measure_closure`：IsCompact.measure_closure [R1Space γ] {K : Se
t γ} (hK : IsCompact K) (μ : Measure γ) : μ (closure K) = μ K
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `MeasureTheory.Content.measure_apply`：measure_apply {s : Set G} (hs : Mea
surableSet s) : μ.measure s = μ.outerMeasure s
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.Measure.haar.haarContent_outerMeasure_closure_pos`：haarCon
tent_outerMeasure_closure_pos (K₀ : PositiveCompacts G) : 0 < (haarContent K₀).o
uterMeasure (closure K₀)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Content.outerMeasure_lt_top_of_isCompact`：outerMeasure_lt_
top_of_isCompact [WeaklyLocallyCompactSpace G] {K : Set G} (hK : IsCompact K) : 
μ.outerMeasure K < ∞
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
-/
theorem haarMeasure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ K₀ = 1 := by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  simp only [haarMeasure, coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← K₀.isCompact.measure_closure,
    Content.measure_apply _ isClosed_closure.measurableSet, ENNReal.inv_mul_cancel]
  · exact (haarContent_outerMeasure_closure_pos K₀).ne'
  · exact (Content.outerMeasure_lt_top_of_isCompact _ K₀.isCompact.closure).ne

/-- The Haar measure is regular. -/
@[to_additive /-- The additive Haar measure is regular. -/]
/-
**MeasureTheory.Measure.regular_haarMeasure** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：regular_haarMeasure {K₀ : PositiveCompacts G} : (haarMeasure K₀).Regular
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group`：Topologi
calSpace.PositiveCompacts.locallyCompactSpace_of_group (K : PositiveCompacts G) 
: LocallyCompactSpace G
· 使用定理 `MeasureTheory.Measure.Regular.smul`：∀ {α : Type u_1} [inst : MeasurableS
pace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.Regular] 
  {x : ENNReal}, x ≠ ⊤ →…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.measure_closure`：IsCompact.measure_closure [R1Space γ] {K : Se
t γ} (hK : IsCompact K) (μ : Measure γ) : μ (closure K) = μ K
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `MeasureTheory.Content.measure_apply`：measure_apply {s : Set G} (hs : Mea
surableSet s) : μ.measure s = μ.outerMeasure s
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.Measure.haar.haarContent_outerMeasure_closure_pos`：haarCon
tent_outerMeasure_closure_pos (K₀ : PositiveCompacts G) : 0 < (haarContent K₀).o
uterMeasure (closure K₀)

--- 原说明 ---
The Haar measure is regular.
-/
instance regular_haarMeasure {K₀ : PositiveCompacts G} : (haarMeasure K₀).Regular := by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  apply Regular.smul
  rw [← K₀.isCompact.measure_closure,
    Content.measure_apply _ isClosed_closure.measurableSet, ENNReal.inv_ne_top]
  exact (haarContent_outerMeasure_closure_pos K₀).ne'

@[to_additive]
/-
**MeasureTheory.Measure.haarMeasure_closure_self** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：haarMeasure_closure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ (closu
re K₀) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.measure_closure`：IsCompact.measure_closure [R1Space γ] {K : Se
t γ} (hK : IsCompact K) (μ : Measure γ) : μ (closure K) = μ K
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `MeasureTheory.Measure.haarMeasure_self`：haarMeasure_self {K₀ : PositiveC
ompacts G} : haarMeasure K₀ K₀ = 1
-/
theorem haarMeasure_closure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ (closure K₀) = 1 := by
  rw [K₀.isCompact.measure_closure, haarMeasure_self]

/-- The Haar measure is sigma-finite in a second countable group. -/
@[to_additive /-- The additive Haar measure is sigma-finite in a second countable group. -/]
/-
**MeasureTheory.Measure.sigmaFinite_haarMeasure** 是 Mathlib 中的一个实例，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：sigmaFinite_haarMeasure [SecondCountableTopology G] {K₀ : PositiveCompacts
 G} : SigmaFinite (haarMeasure K₀)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group`：Topologi
calSpace.PositiveCompacts.locallyCompactSpace_of_group (K : PositiveCompacts G) 
: LocallyCompactSpace G
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…

--- 原说明 ---
The Haar measure is sigma-finite in a second countable group.
-/
instance sigmaFinite_haarMeasure [SecondCountableTopology G] {K₀ : PositiveCompacts G} :
    SigmaFinite (haarMeasure K₀) := by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group; infer_instance

/-- The Haar measure is a Haar measure, i.e., it is invariant and gives finite mass to compact
sets and positive mass to nonempty open sets. -/
@[to_additive
/-- The additive Haar measure is an additive Haar measure, i.e., it is invariant and gives finite
mass to compact sets and positive mass to nonempty open sets. -/]
/-
**MeasureTheory.Measure.isHaarMeasure_haarMeasure** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：isHaarMeasure_haarMeasure (K₀ : PositiveCompacts G) : IsHaarMeasure (haarM
easure K₀)
参数：K₀ : PositiveCompacts G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isHaarMeasure_of_isCompact_nonempty_interior`：isHa
arMeasure_of_isCompact_nonempty_interior [IsTopologicalGroup G] [BorelSpace G] (
μ : Measure G) [IsMulLeftInvariant μ] (K : Set G) (hK : …
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haarMeasure_self`：haarMeasure_self {K₀ : PositiveC
ompacts G} : haarMeasure K₀ K₀ = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance isHaarMeasure_haarMeasure (K₀ : PositiveCompacts G) : IsHaarMeasure (haarMeasure K₀) := by
  apply
    isHaarMeasure_of_isCompact_nonempty_interior (haarMeasure K₀) K₀ K₀.isCompact
      K₀.interior_nonempty
  · simp only [haarMeasure_self]; exact one_ne_zero
  · simp only [haarMeasure_self, ne_eq, ENNReal.one_ne_top, not_false_eq_true]

/-- `haar` is some choice of a Haar measure, on a locally compact group. -/
@[to_additive
/-- `addHaar` is some choice of a Haar measure, on a locally compact additive group. -/]
/-
**MeasureTheory.Measure.haar** 是 Mathlib 中的一个缩写定义，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：haar [LocallyCompactSpace G] : Measure G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev haar [LocallyCompactSpace G] : Measure G :=
  haarMeasure <| Classical.arbitrary _

/-! Steinhaus theorem: if `E` has positive measure, then `E / E` contains a neighborhood of zero.
Note that this is not true for general regular Haar measures: in `ℝ × ℝ` where the first factor
has the discrete topology, then `E = ℝ × {0}` has infinite measure for the regular Haar measure,
but `E / E` does not contain a neighborhood of zero. On the other hand, it is always true for
inner regular Haar measures (and in particular for any Haar measure on a second countable group).
-/

open scoped Pointwise

@[to_additive]
/-
**MeasureTheory.Measure.steinhaus_mul_aux** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma steinhaus_mul_aux (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop]
    [LocallyCompactSpace G] (E : Set G) (hE : MeasurableSet E)
    (hEapprox : ∃ K ⊆ E, IsCompact K ∧ 0 < μ K) : E / E ∈ 𝓝 (1 : G) := by
  /- For any measure `μ` and set `E` containing a compact set `K` of positive measure, there exists
  a neighborhood `V` of the identity such that `v • K \ K` has small measure for all `v ∈ V`, say
  `< μ K`. Then `v • K` and `K` cannot be disjoint, as otherwise `μ (v • K \ K) = μ (v • K) = μ K`.
  This show that `K / K` contains the neighborhood `V` of `1`, and therefore that it is
  itself such a neighborhood. -/
  obtain ⟨K, hKE, hK, K_closed, hKpos⟩ : ∃ K ⊆ E, IsCompact K ∧ IsClosed K ∧ 0 < μ K := by
    obtain ⟨K, hKE, hK_comp, hK_meas⟩ := hEapprox
    exact ⟨closure K, hK_comp.closure_subset_measurableSet hE hKE, hK_comp.closure,
      isClosed_closure, by rwa [hK_comp.measure_closure]⟩
  filter_upwards [eventually_nhds_one_measure_smul_sdiff_lt hK K_closed hKpos.ne' (μ := μ)]
    with g hg
  obtain ⟨_, ⟨x, hxK, rfl⟩, hgxK⟩ : ∃ x ∈ g • K, x ∈ K :=
     not_disjoint_iff.1 fun hd ↦ by simp [hd.symm.sdiff_eq_right, measure_smul] at hg
  simpa using div_mem_div (hKE hgxK) (hKE hxK)

/-- **Steinhaus Theorem** for finite mass sets.

In any locally compact group `G` with a Haar measure `μ` that's inner regular on finite measure
sets, for any measurable set `E` of finite positive measure, the set `E / E` is a neighbourhood of
`1`. -/
@[to_additive
/-- **Steinhaus Theorem** for finite mass sets.

In any locally compact group `G` with a Haar measure `μ` that's inner regular on finite measure
sets, for any measurable set `E` of finite positive measure, the set `E - E` is a neighbourhood of
`0`. -/]
/-
**MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos_ne_top** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：div_mem_nhds_one_of_haar_pos_ne_top (μ : Measure G) [IsHaarMeasure μ] [Loc
allyCompactSpace G] [μ.InnerRegularCompactLTTop] (E : Set G) (hE : MeasurableSet
 E) (hEpos : 0 < μ E) (hEfin : μ E != ∞) : E / E in 𝓝 (1 : G)
参数：μ : Measure G；E : Set G；hE : MeasurableSet E；hEpos : 0 < μ E；hEfin : μ E != ∞
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.Haar.Basic.0.MeasureTheory.Measur
e.steinhaus_mul_aux`：∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpac
e G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]   [BorelSpace G] (μ : M
e…
· 使用定理 `MeasurableSet.exists_lt_isCompact_of_ne_top`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [
μ.InnerRegularCompactLTTop] ⦃A : …
-/
theorem div_mem_nhds_one_of_haar_pos_ne_top (μ : Measure G) [IsHaarMeasure μ]
    [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop] (E : Set G) (hE : MeasurableSet E)
    (hEpos : 0 < μ E) (hEfin : μ E ≠ ∞) : E / E ∈ 𝓝 (1 : G) :=
  steinhaus_mul_aux μ E hE <| hE.exists_lt_isCompact_of_ne_top hEfin hEpos

/-- **Steinhaus Theorem**.

In any locally compact group `G` with an inner regular Haar measure `μ`,
for any measurable set `E` of positive measure, the set `E / E` is a neighbourhood of `1`. -/
@[to_additive
/-- **Steinhaus Theorem**.

In any locally compact group `G` with an inner regular Haar measure `μ`,
for any measurable set `E` of positive measure, the set `E - E` is a neighbourhood of `0`. -/]
/-
**MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：div_mem_nhds_one_of_haar_pos (μ : Measure G) [IsHaarMeasure μ] [LocallyCom
pactSpace G] [InnerRegular μ] (E : Set G) (hE : MeasurableSet E) (hEpos : 0 < μ 
E) : E / E in 𝓝 (1 : G)
参数：μ : Measure G；E : Set G；hE : MeasurableSet E；hEpos : 0 < μ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.Haar.Basic.0.MeasureTheory.Measur
e.steinhaus_mul_aux`：∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpac
e G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]   [BorelSpace G] (μ : M
e…
· 使用定理 `MeasureTheory.Measure.InnerRegular.instInnerRegularCompactLTTop`：∀ {α : 
Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Top
ologicalSpace α]   [μ.InnerRegular], μ.InnerRegularCo…
· 使用定理 `MeasurableSet.exists_lt_isCompact`：∀ {α : Type u_1} [inst : MeasurableSp
ace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.InnerRegul
ar]   ⦃A : Set α⦄, Meas…
-/
theorem div_mem_nhds_one_of_haar_pos (μ : Measure G) [IsHaarMeasure μ] [LocallyCompactSpace G]
    [InnerRegular μ] (E : Set G) (hE : MeasurableSet E) (hEpos : 0 < μ E) :
    E / E ∈ 𝓝 (1 : G) := steinhaus_mul_aux μ E hE <| hE.exists_lt_isCompact hEpos

section SecondCountable_SigmaFinite
/-! In this section, we investigate uniqueness of left-invariant measures without assuming that
the measure is finite on compact sets, but assuming σ-finiteness instead. We also rely on
second-countability, to ensure that the group operations are measurable: in this case, one can
bypass all topological arguments, and conclude using uniqueness of σ-finite left-invariant measures
in measurable groups.

For more general uniqueness statements without second-countability assumptions,
see the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.
-/

variable [SecondCountableTopology G]

/-- **Uniqueness of left-invariant measures**: In a second-countable locally compact group, any
  σ-finite left-invariant measure is a scalar multiple of the Haar measure.
  This is slightly weaker than assuming that `μ` is a Haar measure (in particular we don't require
  `μ ≠ 0`).
  See also `isMulLeftInvariant_eq_smul_of_regular`
  for a statement not assuming second-countability. -/
@[to_additive
/-- **Uniqueness of left-invariant measures**: In a second-countable locally compact additive group,
  any σ-finite left-invariant measure is a scalar multiple of the additive Haar measure.
  This is slightly weaker than assuming that `μ` is an additive Haar measure (in particular we don't
  require `μ ≠ 0`).
  See also `isAddLeftInvariant_eq_smul_of_regular`
  for a statement not assuming second-countability. -/]
/-
**MeasureTheory.Measure.haarMeasure_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：haarMeasure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ] 
(K₀ : PositiveCompacts G) : μ = μ K₀ • haarMeasure K₀
参数：μ : Measure G；K₀ : PositiveCompacts G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.measure_eq_div_smul`：measure_eq_div_smul (h2s : ν' s != 0)
 (h3s : ν' s != ∞) : μ' = (μ' s / ν' s) • ν'
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousInv.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Inv γ]   [ContinuousInv 
γ], MeasurableInv…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.Measure.measure_pos_of_nonempty_interior`：measure_pos_of_n
onempty_interior (h : (interior s).Nonempty) : 0 < μ s
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `IsCompact.measure_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCompact.measure_closure`：IsCompact.measure_closure [R1Space γ] {K : Se
t γ} (hK : IsCompact K) (μ : Measure γ) : μ (closure K) = μ K
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `MeasureTheory.Measure.haarMeasure_closure_self`：haarMeasure_closure_self
 {K₀ : PositiveCompacts G} : haarMeasure K₀ (closure K₀) = 1
-/
theorem haarMeasure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
    (K₀ : PositiveCompacts G) : μ = μ K₀ • haarMeasure K₀ := by
  have A : Set.Nonempty (interior (closure (K₀ : Set G))) :=
    K₀.interior_nonempty.mono (interior_mono subset_closure)
  have := measure_eq_div_smul μ (haarMeasure K₀)
    (measure_pos_of_nonempty_interior _ A).ne' K₀.isCompact.closure.measure_ne_top
  rwa [haarMeasure_closure_self, div_one, K₀.isCompact.measure_closure] at this

/-- Let `μ` be a σ-finite left invariant measure on `G`. Then `μ` is equal to the Haar measure
defined by `K₀` iff `μ K₀ = 1`. -/
@[to_additive /-- Let `μ` be a σ-finite left invariant measure on `G`. Then `μ` is equal to the
additive Haar measure defined by `K₀` iff `μ K₀ = 1`. -/]
/-
**MeasureTheory.Measure.haarMeasure_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：haarMeasure_eq_iff (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite 
μ] [IsMulLeftInvariant μ] : haarMeasure K₀ = μ ↔ μ K₀ = 1
参数：K₀ : PositiveCompacts G；μ : Measure G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haarMeasure_self`：haarMeasure_self {K₀ : PositiveC
ompacts G} : haarMeasure K₀ K₀ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haarMeasure_unique`：haarMeasure_unique (μ : Measur
e G) [SigmaFinite μ] [IsMulLeftInvariant μ] (K₀ : PositiveCompacts G) : μ = μ K₀
 • haarMeasure K₀
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem haarMeasure_eq_iff (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite μ]
    [IsMulLeftInvariant μ] :
    haarMeasure K₀ = μ ↔ μ K₀ = 1 :=
  ⟨fun h => h.symm ▸ haarMeasure_self, fun h => by rw [haarMeasure_unique μ K₀, h, one_smul]⟩
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个示例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haarMeasure_unique μ K₀

/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is finite
  on some compact set with non-empty interior. -/
@[to_additive
/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is
  finite on some compact set with non-empty interior. -/]
/-
**MeasureTheory.Measure.regular_of_isMulLeftInvariant** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：regular_of_isMulLeftInvariant {μ : Measure G} [SigmaFinite μ] [IsMulLeftIn
variant μ] {K : Set G} (hK : IsCompact K) (h2K : (interior K).Nonempty) (hμK : μ
 K != ∞) : Regular μ
参数：hK : IsCompact K；h2K : (interior K).Nonempty；hμK : μ K != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haarMeasure_unique`：haarMeasure_unique (μ : Measur
e G) [SigmaFinite μ] [IsMulLeftInvariant μ] (K₀ : PositiveCompacts G) : μ = μ K₀
 • haarMeasure K₀
· 使用定理 `MeasureTheory.Measure.Regular.smul`：∀ {α : Type u_1} [inst : MeasurableS
pace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.Regular] 
  {x : ENNReal}, x ≠ ⊤ →…
-/
theorem regular_of_isMulLeftInvariant {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ]
    {K : Set G} (hK : IsCompact K) (h2K : (interior K).Nonempty) (hμK : μ K ≠ ∞) : Regular μ := by
  rw [haarMeasure_unique μ ⟨⟨K, hK⟩, h2K⟩]; exact Regular.smul hμK

end SecondCountable_SigmaFinite

end Group

end Measure

end MeasureTheory

