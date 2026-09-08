/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Equicontinuity
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Topology induced by a family of seminorms

## Main definitions

* `SeminormFamily.basisSets`: The set of open seminorm balls for a family of seminorms.
* `SeminormFamily.moduleFilterBasis`: A module filter basis formed by the open balls.
* `Seminorm.IsBounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
  bounded by a finite number of seminorms in `E`.
* `WithSeminorms p`, when `p` is a family of seminorms on `E`, is a proposition expressing that the
  (existing) topology on `E` is induced by the seminorms `p`.
* `PolynormableSpace 𝕜 E` is a class asserting that the (existing) topology on `E` is induced
  by *some* family of `𝕜`-seminorms. If `𝕜` is `RCLike`, this is equivalent to
  `LocallyConvexSpace 𝕜 E`.
  The terminology is inspired by N. Bourbaki, *Variétés différentielles et analytiques*. However,
  unlike Bourbaki, we do not ask seminorms to be ultrametric when `𝕜` is ultrametric.

## Main statements

* `WithSeminorms.toLocallyConvexSpace`: A space equipped with a family of seminorms is locally
  convex.
* `WithSeminorms.firstCountable`: A space is first countable if its topology is induced by a
  countable family of seminorms.

## Continuity of semilinear maps

If `E` and `F` are topological vector space with the topology induced by a family of seminorms, then
we have a direct method to prove that a linear map is continuous:
* `Seminorm.continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.

If the topology of a space `E` is induced by a family of seminorms, then we can characterize von
Neumann boundedness in terms of that seminorm family. Together with
`LinearMap.continuous_of_locally_bounded` this gives general criterion for continuity.

* `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.isVonNBounded_iff_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded`

## Tags

seminorm, locally convex
-/

@[expose] public section


open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {R 𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section FilterBasis

variable [SeminormedRing R] [AddCommGroup E] [Module R E]
variable (R E ι)

/-- An abbreviation for indexed families of seminorms. This is mainly to allow for dot-notation. -/
/-
**SeminormFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SeminormFamily
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for indexed families of seminorms. This is mainly to allow for d
ot-notation.
-/
abbrev SeminormFamily :=
  ι → Seminorm R E

variable {R E ι}

namespace SeminormFamily

/-- The sets of a filter basis for the neighborhood filter of 0. -/
/-
**SeminormFamily.basisSets** 是 Mathlib 中的一个定义，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets (p : SeminormFamily R E ι) : Set (Set E)
参数：p : SeminormFamily R E ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sets of a filter basis for the neighborhood filter of 0.
-/
def basisSets (p : SeminormFamily R E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)

variable (p : SeminormFamily R E ι)
/-
**SeminormFamily.basisSets_iff** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_iff {U : Set E} : U in p.basisSets ↔ exists (i : Finset ι) (r : 
Real), 0 < r ∧ U = ball (i.sup p) 0 r
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem basisSets_iff {U : Set E} :
    U ∈ p.basisSets ↔ ∃ (i : Finset ι) (r : ℝ), 0 < r ∧ U = ball (i.sup p) 0 r := by
  simp only [basisSets, mem_iUnion, exists_prop, mem_singleton_iff]
/-
**SeminormFamily.basisSets_mem** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_mem (i : Finset ι) {r : Real} (hr : 0 < r) : (i.sup p).ball 0 r 
in p.basisSets
参数：i : Finset ι；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
-/
theorem basisSets_mem (i : Finset ι) {r : ℝ} (hr : 0 < r) : (i.sup p).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨i, _, hr, rfl⟩
/-
**SeminormFamily.basisSets_singleton_mem** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFami
ly`。
形式化陈述：basisSets_singleton_mem (i : ι) {r : Real} (hr : 0 < r) : (p i).ball 0 r i
n p.basisSets
参数：i : ι；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
-/
theorem basisSets_singleton_mem (i : ι) {r : ℝ} (hr : 0 < r) : (p i).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩
/-
**SeminormFamily.basisSets_univ_mem** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_univ_mem : univ in p.basisSets
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Seminorm.bot_eq_zero`：bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0
· 使用定理 `Seminorm.ball_zero'`：ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminor
m 𝕜 E) x r = Set.univ
-/
theorem basisSets_univ_mem : univ ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨∅, _, one_pos, by
    rw [Finset.sup_empty, Seminorm.bot_eq_zero, ball_zero' _ one_pos]⟩
/-
**SeminormFamily.basisSets_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_nonempty : p.basisSets.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
· 使用定理 `SeminormFamily.basisSets_univ_mem`：basisSets_univ_mem : univ in p.basisS
ets
-/
theorem basisSets_nonempty : p.basisSets.Nonempty := by
  refine nonempty_def.mpr ⟨univ, basisSets_univ_mem _⟩
/-
**SeminormFamily.basisSets_intersect** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_intersect (U V : Set E) (hU : U in p.basisSets) (hV : V in p.bas
isSets) : exists z in p.basisSets, z subseteq U inter V
参数：U V : Set E；hU : U in p.basisSets；hV : V in p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `SeminormFamily.basisSets_mem`：basisSets_mem (i : Finset ι) {r : Real} (h
r : 0 < r) : (i.sup p).ball 0 r in p.basisSets
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_finset_sup_eq_iInter`：ball_finset_sup_eq_iInter (p : ι -> 
Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 < r) : ball (s.sup p) x 
r = ⋂ i in s, ball (p i)…
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.iInter₂_mono'`：iInter₂_mono' {s : forall i, κ i -> Set α} {t : foral
l i', κ' i' -> Set α} (h : forall i' j', exists i j, s i j subseteq t i' j') : ⋂
 (i) (j…
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Seminorm.ball_mono`：ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : Real} (h : r₁ 
<= r₂) : p.ball x r₁ subseteq p.ball x r₂
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
theorem basisSets_intersect (U V : Set E) (hU : U ∈ p.basisSets) (hV : V ∈ p.basisSets) :
    ∃ z ∈ p.basisSets, z ⊆ U ∩ V := by
  classical
    rcases p.basisSets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basisSets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s ∪ t).sup p).ball 0 (min r₁ r₂)
    refine ⟨p.basisSets_mem (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ?_⟩
    rw [hU, hV, ball_finset_sup_eq_iInter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩),
      ball_finset_sup_eq_iInter _ _ _ hr₁, ball_finset_sup_eq_iInter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_left hi, ball_mono <| min_le_left _ _⟩)
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_right hi, ball_mono <| min_le_right _ _⟩)
/-
**SeminormFamily.basisSets_zero** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_zero (U) (hU : U in p.basisSets) : (0 : E) in U
参数：U；hU : U in p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem basisSets_zero (U) (hU : U ∈ p.basisSets) : (0 : E) ∈ U := by
  rcases p.basisSets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU, mem_ball_zero, map_zero]
  exact hr
/-
**SeminormFamily.basisSets_add** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_add (U) (hU : U in p.basisSets) : exists V in p.basisSets, V + V
 subseteq U
参数：U；hU : U in p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormFamily.basisSets_mem`：basisSets_mem (i : Finset ι) {r : Real} (h
r : 0 < r) : (i.sup p).ball 0 r in p.basisSets
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Seminorm.ball_add_ball_subset`：ball_add_ball_subset (p : Seminorm 𝕜 E) (
r₁ r₂ : Real) (x₁ x₂ : E) : p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ subseteq p.b
all (x₁ + x₂) (r₁ +…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem basisSets_add (U) (hU : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V + V ⊆ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine ⟨p.basisSets_mem s (div_pos hr zero_lt_two), ?_⟩
  refine Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) ?_
  rw [hU, add_zero, add_halves]
/-
**SeminormFamily.basisSets_neg** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_neg (U) (hU' : U in p.basisSets) : exists V in p.basisSets, V su
bseteq (fun x : E => -x) ⁻¹' U
参数：U；hU' : U in p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.neg_preimage`：∀ {α : Type u_2} [inst : Neg α] {s : Set α}, Neg.neg ⁻
¹' s = -s
· 使用定理 `Seminorm.neg_ball`：neg_ball (p : Seminorm 𝕜 E) (r : Real) (x : E) : -bal
l p x r = ball p (-x) r
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem basisSets_neg (U) (hU' : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V ⊆ (fun x : E => -x) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU' with ⟨s, r, _, hU⟩
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩

/-- The `addGroupFilterBasis` induced by the filter basis `Seminorm.basisSets`. -/
@[instance_reducible]
/-
**SeminormFamily.addGroupFilterBasis** 是 Mathlib 中的一个定义，位于命名空间 `SeminormFamily`。
形式化陈述：{R : Type u_1} →   {E : Type u_6} →     {ι : Type u_9} →       [inst : Sem
inormedRing R] →         [inst_1 : AddCommGroup E] → [inst_2 : _root_.Module R E
] → SeminormFamily R E ι → AddGroupFilterBasis E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormFamily.basisSets_nonempty`：basisSets_nonempty : p.basisSets.None
mpty
· 使用定理 `SeminormFamily.basisSets_intersect`：basisSets_intersect (U V : Set E) (h
U : U in p.basisSets) (hV : V in p.basisSets) : exists z in p.basisSets, z subse
teq U inter V
· 使用定理 `SeminormFamily.basisSets_zero`：basisSets_zero (U) (hU : U in p.basisSets
) : (0 : E) in U
· 使用定理 `SeminormFamily.basisSets_add`：basisSets_add (U) (hU : U in p.basisSets) 
: exists V in p.basisSets, V + V subseteq U
· 使用定理 `SeminormFamily.basisSets_neg`：basisSets_neg (U) (hU' : U in p.basisSets)
 : exists V in p.basisSets, V subseteq (fun x : E => -x) ⁻¹' U

--- 原说明 ---
The `addGroupFilterBasis` induced by the filter basis `Seminorm.basisSets`.
-/
protected def addGroupFilterBasis : AddGroupFilterBasis E :=
  addGroupFilterBasisOfComm p.basisSets p.basisSets_nonempty p.basisSets_intersect p.basisSets_zero
    p.basisSets_add p.basisSets_neg
/-
**SeminormFamily.basisSets_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`
。
形式化陈述：basisSets_smul_right (v : E) (U : Set E) (hU : U in p.basisSets) : forallᶠ
 x : R in 𝓝 0, x • v in U
参数：v : E；U : Set E；hU : U in p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_zero_eq`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (r : ℝ), Me
tric.ball 0 r = {x | ‖x‖ < r}
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem basisSets_smul_right (v : E) (U : Set E) (hU : U ∈ p.basisSets) :
    ∀ᶠ x : R in 𝓝 0, x • v ∈ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU, Filter.eventually_iff]
  simp_rw [(s.sup p).mem_ball_zero, map_smul_eq_mul]
  by_cases! h : 0 < (s.sup p) v
  · simp_rw [(lt_div_iff₀ h).symm]
    rw [← _root_.ball_zero_eq]
    exact Metric.ball_mem_nhds 0 (div_pos hr h)
  simp_rw [le_antisymm h (apply_nonneg _ v), mul_zero, hr]
  exact IsOpen.mem_nhds isOpen_univ (mem_univ 0)
/-
**SeminormFamily.basisSets_smul** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_smul (U) (hU : U in p.basisSets) : exists V in 𝓝 (0 : R), exists
 W in p.addGroupFilterBasis.sets, V • W subseteq U
参数：U；hU : U in p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_pos`：sqrt_pos : 0 < √x ↔ 0 < x
· 使用定理 `SeminormFamily.basisSets_mem`：basisSets_mem (i : Finset ι) {r : Real} (h
r : 0 < r) : (i.sup p).ball 0 r in p.basisSets
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Seminorm.ball_smul_ball`：ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : Real
) : Metric.ball (0 : 𝕜) r₁ • p.ball 0 r₂ subseteq p.ball 0 (r₁ * r₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem basisSets_smul (U) (hU : U ∈ p.basisSets) :
    ∃ V ∈ 𝓝 (0 : R), ∃ W ∈ p.addGroupFilterBasis.sets, V • W ⊆ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  refine ⟨Metric.ball 0 √r, Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hr), ?_⟩
  refine ⟨(s.sup p).ball 0 √r, p.basisSets_mem s (Real.sqrt_pos.mpr hr), ?_⟩
  refine Set.Subset.trans (ball_smul_ball (s.sup p) √r √r) ?_
  rw [hU, Real.mul_self_sqrt (le_of_lt hr)]

variable [NormedDivisionRing 𝕜] [AddCommGroup F] [Module 𝕜 F] (p : SeminormFamily 𝕜 F ι)
/-
**SeminormFamily.basisSets_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_smul_left (x : 𝕜) (U : Set F) (hU : U in p.basisSets) : exists V
 in p.addGroupFilterBasis.sets, V subseteq (fun y : F => x • y) ⁻¹' U
参数：x : 𝕜；U : Set F；hU : U in p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.smul_ball_preimage`：smul_ball_preimage (p : Seminorm 𝕜 E) (y : 
E) (r : Real) (a : 𝕜) (ha : a != 0) : (a • ·) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) 
(r / ‖a‖)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `SeminormFamily.basisSets_mem`：basisSets_mem (i : Finset ι) {r : Real} (h
r : 0 < r) : (i.sup p).ball 0 r in p.basisSets
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Set.preimage_const_of_mem`：preimage_const_of_mem {b : β} {s : Set β} (h 
: b in s) : (fun _ : α => b) ⁻¹' s = univ
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem basisSets_smul_left (x : 𝕜) (U : Set F) (hU : U ∈ p.basisSets) :
    ∃ V ∈ p.addGroupFilterBasis.sets, V ⊆ (fun y : F => x • y) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  rw [hU]
  by_cases h : x ≠ 0
  · rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero]
    use (s.sup p).ball 0 (r / ‖x‖)
    exact ⟨p.basisSets_mem s (div_pos hr (norm_pos_iff.mpr h)), Subset.rfl⟩
  refine ⟨(s.sup p).ball 0 r, p.basisSets_mem s hr, ?_⟩
  simp only [not_ne_iff.mp h, Set.subset_def, mem_ball_zero, hr, mem_univ, map_zero, imp_true_iff,
    preimage_const_of_mem, zero_smul]

/-- The `moduleFilterBasis` induced by the filter basis `Seminorm.basisSets`. -/
/-
**SeminormFamily.moduleFilterBasis** 是 Mathlib 中的一个定义，位于命名空间 `SeminormFamily`。
形式化陈述：{𝕜 : Type u_2} →   {F : Type u_7} →     {ι : Type u_9} →       [inst : Nor
medDivisionRing 𝕜] →         [inst_1 : AddCommGroup F] → [inst_2 : _root_.Module
 𝕜 F] → SeminormFamily 𝕜 F ι → ModuleFilterBasis 𝕜 F
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormFamily.basisSets_smul_left`：basisSets_smul_left (x : 𝕜) (U : Set
 F) (hU : U in p.basisSets) : exists V in p.addGroupFilterBasis.sets, V subseteq
 (fun y : F => x • y) ⁻¹…

--- 原说明 ---
The `moduleFilterBasis` induced by the filter basis `Seminorm.basisSets`.
-/
protected def moduleFilterBasis : ModuleFilterBasis 𝕜 F where
  toAddGroupFilterBasis := p.addGroupFilterBasis
  smul' := p.basisSets_smul _
  smul_left' := p.basisSets_smul_left
  smul_right' := p.basisSets_smul_right
/-
**SeminormFamily.filter_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `SeminormFamily`。
形式化陈述：filter_eq_iInf (p : SeminormFamily 𝕜 F ι) : p.moduleFilterBasis.toFilterBa
sis.filter = ⨅ i, (𝓝 0).comap (p i)
参数：p : SeminormFamily 𝕜 F ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `FilterBasis.hasBasis`：∀ {α : Type u_1} (B : FilterBasis α), B.filter.Has
Basis (fun s => s ∈ B) id
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `SeminormFamily.basisSets_mem`：basisSets_mem (i : Finset ι) {r : Real} (h
r : 0 < r) : (i.sup p).ball 0 r in p.basisSets
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Seminorm.ball_zero_eq_preimage_ball`：ball_zero_eq_preimage_ball {r : Rea
l} : p.ball 0 r = p ⁻¹' Metric.ball 0 r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `Seminorm.ball_finset_sup_eq_iInter`：ball_finset_sup_eq_iInter (p : ι -> 
Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 < r) : ball (s.sup p) x 
r = ⋂ i in s, ball (p i)…
· 使用定理 `Finset.iInter_mem_sets`：∀ {α : Type u} {f : Filter α} {β : Type v} {s : 
β → Set α} (is : Finset β), ⋂ i ∈ is, s i ∈ f ↔ ∀ i ∈ is, s i ∈ f
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
-/
theorem filter_eq_iInf (p : SeminormFamily 𝕜 F ι) :
    p.moduleFilterBasis.toFilterBasis.filter = ⨅ i, (𝓝 0).comap (p i) := by
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.le_basis_iff
        (Metric.nhds_basis_ball.comap _)]
    intro ε hε
    refine ⟨(p i).ball 0 ε, ?_, ?_⟩
    · rw [← (Finset.sup_singleton : _ = p i)]
      exact p.basisSets_mem {i} hε
    · rw [id, (p i).ball_zero_eq_preimage_ball]
  · rw [p.moduleFilterBasis.toFilterBasis.hasBasis.ge_iff]
    rintro U (hU : U ∈ p.basisSets)
    rcases p.basisSets_iff.mp hU with ⟨s, r, hr, rfl⟩
    rw [id, Seminorm.ball_finset_sup_eq_iInter _ _ _ hr, s.iInter_mem_sets]
    exact fun i _ =>
      Filter.mem_iInf_of_mem i
        ⟨Metric.ball 0 r, Metric.ball_mem_nhds 0 hr,
          Eq.subset (p i).ball_zero_eq_preimage_ball.symm⟩

/-- If a family of seminorms is continuous, then their basis sets are neighborhoods of zero. -/
/-
**SeminormFamily.basisSets_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 `SeminormFamily`。
形式化陈述：basisSets_mem_nhds {𝕜 E ι : Type*} [NormedField 𝕜] [AddCommGroup E] [Modul
e 𝕜 E] [TopologicalSpace E] (p : SeminormFamily 𝕜 E ι) (hp : forall i, Continuou
s (p i)) (U : Set E) (hU : U in p.basisSets) : U in 𝓝 (0 : E)
参数：p : SeminormFamily 𝕜 E ι；hp : forall i, Continuous (p i)；U : Set E；hU : U in 
p.basisSets。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用引理 `Seminorm.ball_mem_nhds`：ball_mem_nhds [TopologicalSpace E] {p : Seminorm
 𝕝 E} (hp : Continuous p) {r : Real} (hr : 0 < r) : p.ball 0 r in (𝓝 0 : Filter 
E)
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Continuous.max`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : LinearOrder α] [OrderClosedTopology α] {f g : β → α}   [inst_3 : Topol
ogic…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a family of seminorms is continuous, then their basis sets are neighborhoods 
of zero.
-/
lemma basisSets_mem_nhds {𝕜 E ι : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] (p : SeminormFamily 𝕜 E ι)
    (hp : ∀ i, Continuous (p i)) (U : Set E) (hU : U ∈ p.basisSets) : U ∈ 𝓝 (0 : E) := by
  obtain ⟨s, r, hr, rfl⟩ := p.basisSets_iff.mp hU
  clear hU
  refine Seminorm.ball_mem_nhds ?_ hr
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_zero
  | insert a s _ hs =>
    simp only [Finset.sup_insert, coe_sup]
    exact Continuous.max (hp a) hs

end SeminormFamily

end FilterBasis

section Bounded

namespace Seminorm

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
/-
**Seminorm.IsBounded** 是 Mathlib 中的一个定义，位于命名空间 `Seminorm`。
形式化陈述：IsBounded (p : ι -> Seminorm 𝕜 E) (q : ι' -> Seminorm 𝕜₂ F) (f : E ->ₛₗ[σ₁
₂] F) : Prop
参数：p : ι -> Seminorm 𝕜 E；q : ι' -> Seminorm 𝕜₂ F；f : E ->ₛₗ[σ₁₂] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a linear map is bounded between spaces with families of sem
inorms.
-/
def IsBounded (p : ι → Seminorm 𝕜 E) (q : ι' → Seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) : Prop :=
  ∀ i, ∃ s : Finset ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • s.sup p
/-
**Seminorm.IsBounded.of_real** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm.IsBounded`。
形式化陈述：∀ {𝕜 : Type u_2} {𝕜₂ : Type u_3} {E : Type u_6} {F : Type u_7} {ι : Type u
_9} {ι' : Type u_10} [inst : SeminormedRing 𝕜]   [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module 𝕜 E] [inst_3 : SeminormedRing 𝕜₂] [inst_4 : AddCommGroup F]  
 [inst_5 : _root_.Module 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [inst_6 : RingHomIsometric σ₁₂] 
{p : ι → Seminorm 𝕜 E}   {q : ι' → Seminorm 𝕜₂ F} {f : E →ₛₗ[σ₁₂] F},   (∀ (i : 
ι'), ∃ s C, ∀ (x : E), (q i) (f x) ≤ C * (s.sup p) x) → Seminorm.IsBounded p q f
参数：∀ (i : ι'), ∃ s C, ∀ (x : E), (q i) (f x) ≤ C * (s.sup p) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.IsBounded.eq_1`：∀ {𝕜 : Type u_2} {𝕜₂ : Type u_3} {E : Type u_6}
 {F : Type u_7} {ι : Type u_9} {ι' : Type u_10} [inst : SeminormedRing 𝕜]   [ins
t_1 : AddComm…
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem IsBounded.of_real {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F} {f : E →ₛₗ[σ₁₂] F}
    (H : ∀ i, ∃ s : Finset ι, ∃ C : ℝ, ∀ x, q i (f x) ≤ C * (s.sup p) x) :
    IsBounded p q f := by
  rw [IsBounded]
  peel H with i s H
  obtain ⟨C, hC⟩ := H
  refine ⟨C.toNNReal, fun x ↦ show q i (f x) ≤ C.toNNReal • ((s.sup p) x) from ?_⟩
  exact (hC x).trans <| mul_le_mul_of_nonneg_right C.le_coe_toNNReal (apply_nonneg _ _)
/-
**Seminorm.isBounded_const** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：isBounded_const (ι' : Type*) [Nonempty ι'] {p : ι -> Seminorm 𝕜 E} {q : Se
minorm 𝕜₂ F} (f : E ->ₛₗ[σ₁₂] F) : IsBounded p (fun _ : ι' => q) f ↔ exists (s :
 Finset ι) (C : Real>=0), q.comp f <= C • s.sup p
参数：ι' : Type*；f : E ->ₛₗ[σ₁₂] F。
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
theorem isBounded_const (ι' : Type*) [Nonempty ι'] {p : ι → Seminorm 𝕜 E} {q : Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) :
    IsBounded p (fun _ : ι' => q) f ↔ ∃ (s : Finset ι) (C : ℝ≥0), q.comp f ≤ C • s.sup p := by
  simp only [IsBounded, forall_const]
/-
**Seminorm.const_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：const_isBounded (ι : Type*) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' -> Sem
inorm 𝕜₂ F} (f : E ->ₛₗ[σ₁₂] F) : IsBounded (fun _ : ι => p) q f ↔ forall i, exi
sts C : Real>=0, (q i).comp f <= C • p
参数：ι : Type*；f : E ->ₛₗ[σ₁₂] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedSMul.smul_le_smul_left`：∀ {G : Type u_3} {P : Type u_4} {inst :
 LE G} {inst_1 : LE P} {inst_2 : SMul G P} [self : IsOrderedSMul G P] (a b : P),
   a ≤ b → ∀ (c : G),…
· 使用定理 `Seminorm.instIsOrderedSMulOfIsOrderedModuleReal`：∀ {R : Type u_1} {𝕜 : T
ype u_3} {E : Type u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 
: SMul 𝕜 E]   [inst_3 : SMul R ℝ] [in…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem const_isBounded (ι : Type*) [Nonempty ι] {p : Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F}
    (f : E →ₛₗ[σ₁₂] F) : IsBounded (fun _ : ι => p) q f ↔ ∀ i, ∃ C : ℝ≥0, (q i).comp f ≤ C • p := by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, h⟩
    exact ⟨C, h.trans (IsOrderedSMul.smul_le_smul_left _ p (Finset.sup_le fun _ _ ↦ le_rfl) C)⟩
  · use {Classical.arbitrary ι}
    simp only [h, Finset.sup_singleton]
/-
**Seminorm.isBounded_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：isBounded_sup {p : ι -> Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F} {f : E ->ₛ
ₗ[σ₁₂] F} (hf : IsBounded p q f) (s' : Finset ι') : exists (C : Real>=0) (s : Fi
nset ι), (s'.sup q).comp f <= C • s.sup p
参数：hf : IsBounded p q f；s' : Finset ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.comp.congr_simp`：∀ {𝕜 : Type u_3} {𝕜₂ : Type u_4} {E : Type u_7
} {E₂ : Type u_8} [inst : SeminormedRing 𝕜] [inst_1 : SeminormedRing 𝕜₂]   {σ₁₂ 
: 𝕜 →+* 𝕜₂} [i…
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Seminorm.zero_comp`：zero_comp (f : E ->ₛₗ[σ₁₂] E₂) : (0 : Seminorm 𝕜₂ E₂
).comp f = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedSMul.smul_le_smul`：IsOrderedSMul.smul_le_smul [LE G] [Preorder 
P] [SMul G P] [IsOrderedSMul G P] {a b : G} {c d : P} (hab : a <= b) (hcd : c <=
 d) : a • c <= b…
· 使用定理 `Seminorm.instIsOrderedSMulOfIsOrderedModuleReal`：∀ {R : Type u_1} {𝕜 : T
ype u_3} {E : Type u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 
: SMul 𝕜 E]   [inst_3 : SMul R ℝ] [in…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用引理 `Finset.subset_biUnion_of_mem`：subset_biUnion_of_mem (u : α -> Finset β) 
{x : α} (xs : x in s) : u x subseteq s.biUnion u
· 使用定理 `Seminorm.comp_mono`：comp_mono {p q : Seminorm 𝕜₂ E₂} (f : E ->ₛₗ[σ₁₂] E₂
) (hp : p <= q) : p.comp f <= q.comp f
· 使用定理 `Seminorm.finset_sup_le_sum`：finset_sup_le_sum (p : ι -> Seminorm 𝕜 E) (s
 : Finset ι) : s.sup p <= ∑ i in s, p i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Seminorm.pullback_apply`：∀ {𝕜 : Type u_3} {𝕜₂ : Type u_4} {E : Type u_7}
 {E₂ : Type u_8} [inst : SeminormedRing 𝕜] [inst_1 : SeminormedRing 𝕜₂]   {σ₁₂ :
 𝕜 →+* 𝕜₂} [i…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
（共 32 条，此处仅展示前 30 条）
-/
theorem isBounded_sup {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F} {f : E →ₛₗ[σ₁₂] F}
    (hf : IsBounded p q f) (s' : Finset ι') :
    ∃ (C : ℝ≥0) (s : Finset ι), (s'.sup q).comp f ≤ C • s.sup p := by
  classical
  obtain rfl | _ := s'.eq_empty_or_nonempty
  · exact ⟨1, ∅, by simp [Seminorm.bot_eq_zero]⟩
  choose fₛ fC hf using hf
  use s'.card • s'.sup fC, Finset.biUnion s' fₛ
  have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • (Finset.biUnion s' fₛ).sup p := by
    intro i hi
    refine (hf i).trans (IsOrderedSMul.smul_le_smul (Finset.le_sup hi) ?_)
    exact Finset.sup_mono (Finset.subset_biUnion_of_mem fₛ hi)
  refine (comp_mono f (finset_sup_le_sum q s')).trans ?_
  simp_rw [← pullback_apply, map_sum, pullback_apply]
  refine (Finset.sum_le_sum hs).trans ?_
  rw [Finset.sum_const, smul_assoc]

end Seminorm

end Bounded

section Topology

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
/-
**WithSeminorms** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_2} →   {E : Type u_6} →     {ι : Type u_9} →       [inst : Nor
medField 𝕜] →         [inst_1 : AddCommGroup E] →           [inst_2 : _root_.Mod
ule 𝕜 E] → SeminormFamily 𝕜 E ι → [topology : TopologicalSpace E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that the topology of `E` is induced by a family of seminorms `p`
.
-/
structure WithSeminorms (p : SeminormFamily 𝕜 E ι) [topology : TopologicalSpace E] : Prop where
  topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology

variable (𝕜 E) in
/-- A topological vector space `E` is **polynormable** over `𝕜` if its topology is induced by
*some* family of `𝕜`-seminorms. Equivalently, its topology is induced by *all* its continuous
seminorm.

If `𝕜` is `RCLike`, this is equivalent to `LocallyConvexSpace 𝕜 E`. -/
/-
**PolynormableSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_2) →   (E : Type u_6) →     [inst : NormedField 𝕜] → [inst_1 :
 AddCommGroup E] → [_root_.Module 𝕜 E] → [topology : TopologicalSpace E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological vector space `E` is **polynormable** over `𝕜` if its topology is i
nduced by
*some* family of `𝕜`-seminorms. Equivalently, its topology is induced by *all* i
ts continuous
seminorm.

If `𝕜` is `RCLike`, this is equivalent to `LocallyConvexSpace 𝕜 E`.
-/
class PolynormableSpace [topology : TopologicalSpace E] where
  withSeminorms' : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} ↦ p.1)
/-
**WithSeminorms.withSeminorms_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.withSeminorms_eq {p : SeminormFamily 𝕜 E ι} [t : Topological
Space E] (hp : WithSeminorms p) : t = p.moduleFilterBasis.topology
参数：hp : WithSeminorms p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topology_eq_withSeminorms`：∀ {𝕜 : Type u_2} {E : Type u_6}
 {ι : Type u_9} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] {p : Seminorm…
-/
theorem WithSeminorms.withSeminorms_eq {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) : t = p.moduleFilterBasis.topology :=
  hp.1

variable [TopologicalSpace E]
variable {p : SeminormFamily 𝕜 E ι}

variable (𝕜 E) in
/-
**PolynormableSpace.withSeminorms** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PolynormableSpace.withSeminorms [PolynormableSpace 𝕜 E] : WithSeminorms (f
un p : {p : Seminorm 𝕜 E // Continuous p} => p.1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolynormableSpace.withSeminorms'`：∀ {𝕜 : Type u_2} {E : Type u_6} {inst 
: NormedField 𝕜} {inst_1 : AddCommGroup E} {inst_2 : _root_.Module 𝕜 E}   {topol
ogy : TopologicalSpace…
-/
theorem PolynormableSpace.withSeminorms [PolynormableSpace 𝕜 E] :
    WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} ↦ p.1) :=
  PolynormableSpace.withSeminorms'
/-
**WithSeminorms.topologicalAddGroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.topologicalAddGroup (hp : WithSeminorms p) : IsTopologicalAd
dGroup E
参数：hp : WithSeminorms p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.withSeminorms_eq`：WithSeminorms.withSeminorms_eq {p : Semi
normFamily 𝕜 E ι} [t : TopologicalSpace E] (hp : WithSeminorms p) : t = p.module
FilterBasis.topology
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
-/
theorem WithSeminorms.topologicalAddGroup (hp : WithSeminorms p) : IsTopologicalAddGroup E := by
  rw [hp.withSeminorms_eq]
  exact AddGroupFilterBasis.isTopologicalAddGroup _
/-
**WithSeminorms.continuousSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.continuousSMul (hp : WithSeminorms p) : ContinuousSMul 𝕜 E
参数：hp : WithSeminorms p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.withSeminorms_eq`：WithSeminorms.withSeminorms_eq {p : Semi
normFamily 𝕜 E ι} [t : TopologicalSpace E] (hp : WithSeminorms p) : t = p.module
FilterBasis.topology
· 使用定理 `ModuleFilterBasis.continuousSMul`：∀ {R : Type u_1} {M : Type u_2} [inst 
: Ring R] [inst_1 : TopologicalSpace R] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] (B : …
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
theorem WithSeminorms.continuousSMul (hp : WithSeminorms p) : ContinuousSMul 𝕜 E := by
  rw [hp.withSeminorms_eq]
  exact ModuleFilterBasis.continuousSMul _
/-
**WithSeminorms.hasBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.hasBasis (hp : WithSeminorms p) : (𝓝 (0 : E)).HasBasis (fun 
s : Set E => s in p.basisSets) id
参数：hp : WithSeminorms p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `WithSeminorms.topology_eq_withSeminorms`：∀ {𝕜 : Type u_2} {E : Type u_6}
 {ι : Type u_9} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] {p : Seminorm…
· 使用定理 `AddGroupFilterBasis.nhds_zero_hasBasis`：∀ {G : Type u} [inst : AddGroup 
G] (B : AddGroupFilterBasis G), (nhds 0).HasBasis (fun V => V ∈ B) id
-/
theorem WithSeminorms.hasBasis (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basisSets) id := by
  rw [congr_fun (congr_arg (@nhds E) hp.1) 0]
  exact AddGroupFilterBasis.nhds_zero_hasBasis _
/-
**WithSeminorms.hasBasis_zero_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.hasBasis_zero_ball (hp : WithSeminorms p) : (𝓝 (0 : E)).HasB
asis (fun sr : Finset ι × Real => 0 < sr.2) fun sr => (sr.1.sup p).ball 0 sr.2
参数：hp : WithSeminorms p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `WithSeminorms.hasBasis`：WithSeminorms.hasBasis (hp : WithSeminorms p) : 
(𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets) id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem WithSeminorms.hasBasis_zero_ball (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis
    (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball 0 sr.2 := by
  refine ⟨fun V => ?_⟩
  simp only [hp.hasBasis.mem_iff, SeminormFamily.basisSets_iff, Prod.exists, id_eq]
  grind
/-
**WithSeminorms.hasBasis_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.hasBasis_ball (hp : WithSeminorms p) {x : E} : (𝓝 (x : E)).H
asBasis (fun sr : Finset ι × Real => 0 < sr.2) fun sr => (sr.1.sup p).ball x sr.
2
参数：hp : WithSeminorms p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add_left_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.map (fun x_1 => x +
 x_1) (nhds …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Seminorm.vadd_ball`：vadd_ball (p : Seminorm 𝕜 E) : x +ᵥ p.ball y r = p.b
all (x +ᵥ y) r
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `WithSeminorms.hasBasis_zero_ball`：WithSeminorms.hasBasis_zero_ball (hp :
 WithSeminorms p) : (𝓝 (0 : E)).HasBasis (fun sr : Finset ι × Real => 0 < sr.2) 
fun sr => (sr.1.sup p)…
-/
theorem WithSeminorms.hasBasis_ball (hp : WithSeminorms p) {x : E} :
    (𝓝 (x : E)).HasBasis
    (fun sr : Finset ι × ℝ => 0 < sr.2) fun sr => (sr.1.sup p).ball x sr.2 := by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  rw [← map_add_left_nhds_zero]
  convert! hp.hasBasis_zero_ball.map (x + ·) using 1
  ext sr : 1
  -- Porting note: extra type ascriptions needed on `0`
  have : (sr.fst.sup p).ball (x +ᵥ (0 : E)) sr.snd = x +ᵥ (sr.fst.sup p).ball 0 sr.snd :=
    Eq.symm (Seminorm.vadd_ball (sr.fst.sup p))
  rwa [vadd_eq_add, add_zero] at this

/-- The `x`-neighbourhoods of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around `x`. -/
/-
**WithSeminorms.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.mem_nhds_iff (hp : WithSeminorms p) (x : E) (U : Set E) : U 
in 𝓝 x ↔ exists s : Finset ι, exists r > 0, (s.sup p).ball x r subseteq U
参数：hp : WithSeminorms p；x : E；U : Set E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `WithSeminorms.hasBasis_ball`：WithSeminorms.hasBasis_ball (hp : WithSemin
orms p) {x : E} : (𝓝 (x : E)).HasBasis (fun sr : Finset ι × Real => 0 < sr.2) fu
n sr => (sr.1.sup…
· 使用定理 `Prod.exists`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p
 x) ↔ ∃ a b, p (a, b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `x`-neighbourhoods of a space whose topology is induced by a family of semin
orms
are exactly the sets which contain seminorm balls around `x`.
-/
theorem WithSeminorms.mem_nhds_iff (hp : WithSeminorms p) (x : E) (U : Set E) :
    U ∈ 𝓝 x ↔ ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  rw [hp.hasBasis_ball.mem_iff, Prod.exists]

/-- The open sets of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around all of their points. -/
/-
**WithSeminorms.isOpen_iff_mem_balls** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.isOpen_iff_mem_balls (hp : WithSeminorms p) (U : Set E) : Is
Open U ↔ forall x in U, exists s : Finset ι, exists r > 0, (s.sup p).ball x r su
bseteq U
参数：hp : WithSeminorms p；U : Set E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithSeminorms.mem_nhds_iff`：WithSeminorms.mem_nhds_iff (hp : WithSeminor
ms p) (x : E) (U : Set E) : U in 𝓝 x ↔ exists s : Finset ι, exists r > 0, (s.sup
 p).ball x r sub…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The open sets of a space whose topology is induced by a family of seminorms
are exactly the sets which contain seminorm balls around all of their points.
-/
theorem WithSeminorms.isOpen_iff_mem_balls (hp : WithSeminorms p) (U : Set E) :
    IsOpen U ↔ ∀ x ∈ U, ∃ s : Finset ι, ∃ r > 0, (s.sup p).ball x r ⊆ U := by
  simp_rw [← WithSeminorms.mem_nhds_iff hp _ U, isOpen_iff_mem_nhds]

/- Note that through the following lemmas, one also immediately has that separating families
of seminorms induce T₂ and T₃ topologies by `IsTopologicalAddGroup.t2Space`
and `IsTopologicalAddGroup.t3Space` -/
/-- A separating family of seminorms induces a T₁ topology. -/
/-
**WithSeminorms.T1_of_separating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.T1_of_separating (hp : WithSeminorms p) (h : forall x, x != 
0 -> exists i, p i x != 0) : T1Space E
参数：hp : WithSeminorms p；h : forall x, x != 0 -> exists i, p i x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.t1Space`：∀ (G : Type w) [inst : TopologicalSpace G
] [inst_1 : AddGroup G] [ContinuousAdd G], IsClosed {0} → T1Space G
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `WithSeminorms.isOpen_iff_mem_balls`：WithSeminorms.isOpen_iff_mem_balls (
hp : WithSeminorms p) (U : Set E) : IsOpen U ↔ forall x in U, exists s : Finset 
ι, exists r > 0, (s.sup …
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_compl_singleton_iff`：subset_compl_singleton_iff : s subseteq 
{a}ᶜ ↔ a ∉ s
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A separating family of seminorms induces a T₁ topology.
-/
theorem WithSeminorms.T1_of_separating (hp : WithSeminorms p)
    (h : ∀ x, x ≠ 0 → ∃ i, p i x ≠ 0) : T1Space E := by
  have := hp.topologicalAddGroup
  refine IsTopologicalAddGroup.t1Space _ ?_
  rw [← isOpen_compl_iff, hp.isOpen_iff_mem_balls]
  rintro x (hx : x ≠ 0)
  obtain ⟨i, pi_nonzero⟩ := h x hx
  refine ⟨{i}, p i x, by positivity, subset_compl_singleton_iff.mpr ?_⟩
  rw [Finset.sup_singleton, mem_ball, zero_sub, map_neg_eq_map, not_lt]

/-- A family of seminorms inducing a T₁ topology is separating. -/
/-
**WithSeminorms.separating_of_T1** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.separating_of_T1 [T1Space E] (hp : WithSeminorms p) (x : E) 
(hx : x != 0) : exists i, p i x != 0
参数：hp : WithSeminorms p；x : E；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `t1Space_TFAE`：t1Space_TFAE (X : Type u) [TopologicalSpace X] : List.TFAE
 [T1Space X, forall x, IsClosed ({ x } : Set X), forall x, IsOpen ({ x }ᶜ : Set 
X)…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.specializes_iff`：Filter.HasBasis.specializes_iff {ι} {p 
: ι -> Prop} {s : ι -> Set X} (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ forall i, p i -
> x in s i
· 使用定理 `WithSeminorms.hasBasis_zero_ball`：WithSeminorms.hasBasis_zero_ball (hp :
 WithSeminorms p) : (𝓝 (0 : E)).HasBasis (fun sr : Finset ι × Real => 0 < sr.2) 
fun sr => (sr.1.sup p)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Seminorm.ball_finset_sup_eq_iInter`：ball_finset_sup_eq_iInter (p : ι -> 
Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 < r) : ball (s.sup p) x 
r = ⋂ i in s, ball (p i)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
A family of seminorms inducing a T₁ topology is separating.
-/
theorem WithSeminorms.separating_of_T1 [T1Space E] (hp : WithSeminorms p) (x : E) (hx : x ≠ 0) :
    ∃ i, p i x ≠ 0 := by
  have := ((t1Space_TFAE E).out 0 9).mp (inferInstance : T1Space E)
  by_contra! h
  refine hx (this ?_)
  rw [hp.hasBasis_zero_ball.specializes_iff]
  rintro ⟨s, r⟩ (hr : 0 < r)
  simp only [ball_finset_sup_eq_iInter _ _ _ hr, mem_iInter₂, mem_ball_zero, h, hr, forall_true_iff]

/-- A family of seminorms is separating iff it induces a T₁ topology. -/
/-
**WithSeminorms.separating_iff_T1** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.separating_iff_T1 (hp : WithSeminorms p) : (forall x, x != 0
 -> exists i, p i x != 0) ↔ T1Space E
参数：hp : WithSeminorms p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.T1_of_separating`：WithSeminorms.T1_of_separating (hp : Wit
hSeminorms p) (h : forall x, x != 0 -> exists i, p i x != 0) : T1Space E
· 使用定理 `WithSeminorms.separating_of_T1`：WithSeminorms.separating_of_T1 [T1Space 
E] (hp : WithSeminorms p) (x : E) (hx : x != 0) : exists i, p i x != 0

--- 原说明 ---
A family of seminorms is separating iff it induces a T₁ topology.
-/
theorem WithSeminorms.separating_iff_T1 (hp : WithSeminorms p) :
    (∀ x, x ≠ 0 → ∃ i, p i x ≠ 0) ↔ T1Space E := by
  refine ⟨WithSeminorms.T1_of_separating hp, ?_⟩
  intro
  exact WithSeminorms.separating_of_T1 hp

end Topology

section Tendsto

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {p : SeminormFamily 𝕜 E ι}

/-- Convergence along filters for `WithSeminorms`.

Variant with `Finset.sup`. -/
/-
**WithSeminorms.tendsto_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.tendsto_nhds' (hp : WithSeminorms p) (u : F -> E) {f : Filte
r F} (y₀ : E) : Filter.Tendsto u f (𝓝 y₀) ↔ forall (s : Finset ι) (ε), 0 < ε -> 
forallᶠ x in f, s.sup p (u x - y₀) < ε
参数：hp : WithSeminorms p；u : F -> E；y₀ : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `WithSeminorms.hasBasis_ball`：WithSeminorms.hasBasis_ball (hp : WithSemin
orms p) {x : E} : (𝓝 (x : E)).HasBasis (fun sr : Finset ι × Real => 0 < sr.2) fu
n sr => (sr.1.sup…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Convergence along filters for `WithSeminorms`.

Variant with `Finset.sup`.
-/
theorem WithSeminorms.tendsto_nhds' (hp : WithSeminorms p) (u : F → E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔
    ∀ (s : Finset ι) (ε), 0 < ε → ∀ᶠ x in f, s.sup p (u x - y₀) < ε := by
  simp [hp.hasBasis_ball.tendsto_right_iff]

/-- Convergence along filters for `WithSeminorms`. -/
/-
**WithSeminorms.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.tendsto_nhds (hp : WithSeminorms p) (u : F -> E) {f : Filter
 F} (y₀ : E) : Filter.Tendsto u f (𝓝 y₀) ↔ forall i ε, 0 < ε -> forallᶠ x in f, 
p i (u x - y₀) < ε
参数：hp : WithSeminorms p；u : F -> E；y₀ : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.tendsto_nhds'`：WithSeminorms.tendsto_nhds' (hp : WithSemin
orms p) (u : F -> E) {f : Filter F} (y₀ : E) : Filter.Tendsto u f (𝓝 y₀) ↔ foral
l (s : Finset ι) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eventually_all`：∀ {α : Type u} {ι : Type u_2} (I : Finset ι) {l :
 Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ
 (x : α) in…
· 使用定理 `Seminorm.finset_sup_apply_lt`：finset_sup_apply_lt {p : ι -> Seminorm 𝕜 E
} {s : Finset ι} {x : E} {a : Real} (ha : 0 < a) (h : forall i, i in s -> p i x 
< a) : s.sup p x <…

--- 原说明 ---
Convergence along filters for `WithSeminorms`.
-/
theorem WithSeminorms.tendsto_nhds (hp : WithSeminorms p) (u : F → E) {f : Filter F} (y₀ : E) :
    Filter.Tendsto u f (𝓝 y₀) ↔ ∀ i ε, 0 < ε → ∀ᶠ x in f, p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds' u y₀]
  exact
    ⟨fun h i => by simpa only [Finset.sup_singleton] using h {i}, fun h s ε hε =>
      (s.eventually_all.2 fun i _ => h i ε hε).mono fun _ => finset_sup_apply_lt hε⟩

variable [SemilatticeSup F] [Nonempty F]

/-- Limit `→ ∞` for `WithSeminorms`. -/
/-
**WithSeminorms.tendsto_nhds_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.tendsto_nhds_atTop (hp : WithSeminorms p) (u : F -> E) (y₀ :
 E) : Filter.Tendsto u Filter.atTop (𝓝 y₀) ↔ forall i ε, 0 < ε -> exists x₀, for
all x, x₀ <= x -> p i (u x - y₀) < ε
参数：hp : WithSeminorms p；u : F -> E；y₀ : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.tendsto_nhds`：WithSeminorms.tendsto_nhds (hp : WithSeminor
ms p) (u : F -> E) {f : Filter F} (y₀ : E) : Filter.Tendsto u f (𝓝 y₀) ↔ forall 
i ε, 0 < ε -> fo…
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α

--- 原说明 ---
Limit `→ ∞` for `WithSeminorms`.
-/
theorem WithSeminorms.tendsto_nhds_atTop (hp : WithSeminorms p) (u : F → E) (y₀ : E) :
    Filter.Tendsto u Filter.atTop (𝓝 y₀) ↔
    ∀ i ε, 0 < ε → ∃ x₀, ∀ x, x₀ ≤ x → p i (u x - y₀) < ε := by
  rw [hp.tendsto_nhds u y₀]
  exact forall₃_congr fun _ _ _ => Filter.eventually_atTop

end Tendsto

section IsTopologicalAddGroup

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

section TopologicalSpace

variable [t : TopologicalSpace E]

/-
**SeminormFamily.withSeminorms_of_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormFamily.withSeminorms_of_nhds [IsTopologicalAddGroup E] (p : Semino
rmFamily 𝕜 E ι) (h : 𝓝 (0 : E) = p.moduleFilterBasis.toFilterBasis.filter) : Wit
hSeminorms p
参数：p : SeminormFamily 𝕜 E ι；h : 𝓝 (0 : E) = p.moduleFilterBasis.toFilterBasis.fi
lter。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {t t' : 
TopologicalSpace G},   IsTopologicalAddGroup G → IsTopologicalAddGroup G → nhds 
0 = nhds 0 → t …
· 使用定理 `AddGroupFilterBasis.isTopologicalAddGroup`：∀ {G : Type u} [inst : AddGro
up G] (B : AddGroupFilterBasis G), IsTopologicalAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddGroupFilterBasis.nhds_zero_eq`：∀ {G : Type u} [inst : AddGroup G] (B 
: AddGroupFilterBasis G), nhds 0 = B.filter
-/
theorem SeminormFamily.withSeminorms_of_nhds [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι)
    (h : 𝓝 (0 : E) = p.moduleFilterBasis.toFilterBasis.filter) : WithSeminorms p := by
  refine
    ⟨IsTopologicalAddGroup.ext inferInstance p.addGroupFilterBasis.isTopologicalAddGroup ?_⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  exact h
/-
**SeminormFamily.withSeminorms_of_hasBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormFamily.withSeminorms_of_hasBasis [IsTopologicalAddGroup E] (p : Se
minormFamily 𝕜 E ι) (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets
) id) : WithSeminorms p
参数：p : SeminormFamily 𝕜 E ι；h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.ba
sisSets) id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormFamily.withSeminorms_of_nhds`：SeminormFamily.withSeminorms_of_nh
ds [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) (h : 𝓝 (0 : E) = p.modul
eFilterBasis.toFilterBasis…
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `FilterBasis.hasBasis`：∀ {α : Type u_1} (B : FilterBasis α), B.filter.Has
Basis (fun s => s ∈ B) id
-/
theorem SeminormFamily.withSeminorms_of_hasBasis [IsTopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) (h : (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ p.basisSets) id) :
    WithSeminorms p :=
  p.withSeminorms_of_nhds <|
    Filter.HasBasis.eq_of_same_basis h p.addGroupFilterBasis.toFilterBasis.hasBasis
/-
**SeminormFamily.withSeminorms_iff_nhds_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormFamily.withSeminorms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p
 : SeminormFamily 𝕜 E ι) : WithSeminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝 0).comap (p i
)
参数：p : SeminormFamily 𝕜 E ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormFamily.filter_eq_iInf`：filter_eq_iInf (p : SeminormFamily 𝕜 F ι)
 : p.moduleFilterBasis.toFilterBasis.filter = ⨅ i, (𝓝 0).comap (p i)
· 使用定理 `WithSeminorms.topology_eq_withSeminorms`：∀ {𝕜 : Type u_2} {E : Type u_6}
 {ι : Type u_9} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] {p : Seminorm…
· 使用定理 `AddGroupFilterBasis.nhds_zero_eq`：∀ {G : Type u} [inst : AddGroup G] (B 
: AddGroupFilterBasis G), nhds 0 = B.filter
· 使用定理 `SeminormFamily.withSeminorms_of_nhds`：SeminormFamily.withSeminorms_of_nh
ds [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) (h : 𝓝 (0 : E) = p.modul
eFilterBasis.toFilterBasis…
-/
theorem SeminormFamily.withSeminorms_iff_nhds_eq_iInf [IsTopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) : WithSeminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝 0).comap (p i) := by
  rw [← p.filter_eq_iInf]
  refine ⟨fun h => ?_, p.withSeminorms_of_nhds⟩
  rw [h.topology_eq_withSeminorms]
  exact AddGroupFilterBasis.nhds_zero_eq _

/-- The topology induced by a family of seminorms is exactly the infimum of the ones induced by
each seminorm individually. We express this as a characterization of `WithSeminorms p`. -/
/-
**SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf [IsTopologicalAd
dGroup E] (p : SeminormFamily 𝕜 E ι) : WithSeminorms p ↔ t = ⨅ i, (p i).toSemino
rmedAddCommGroup.toUniformSpace.toTopologicalSpace
参数：p : SeminormFamily 𝕜 E ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`：SeminormFamily.withSemino
rms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) : With
Seminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝…
· 使用定理 `IsTopologicalAddGroup.ext_iff`：∀ {G : Type u_1} [inst : AddGroup G] {t t
' : TopologicalSpace G},   IsTopologicalAddGroup G → IsTopologicalAddGroup G → (
t = t' ↔ nhds 0 = n…
· 使用定理 `topologicalAddGroup_iInf`：∀ {G : Type w} {ι : Sort u_1} [inst : AddGroup
 G] {ts' : ι → TopologicalSpace G},   (∀ (i : ι), IsTopologicalAddGroup G) → IsT
opologicalAddG…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `comap_norm_nhds_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Fi
lter.comap norm (nhds 0) = nhds 0

--- 原说明 ---
The topology induced by a family of seminorms is exactly the infimum of the ones
 induced by
each seminorm individually. We express this as a characterization of `WithSemino
rms p`.
-/
theorem SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf [IsTopologicalAddGroup E]
    (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔
      t = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf,
    IsTopologicalAddGroup.ext_iff inferInstance (topologicalAddGroup_iInf fun i => inferInstance),
    nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toSeminormedAddGroup
/-
**WithSeminorms.continuous_seminorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.continuous_seminorm {p : SeminormFamily 𝕜 E ι} (hp : WithSem
inorms p) (i : ι) : Continuous (p i)
参数：hp : WithSeminorms p；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf`：SeminormFamil
y.withSeminorms_iff_topologicalSpace_eq_iInf [IsTopologicalAddGroup E] (p : Semi
normFamily 𝕜 E ι) : WithSeminorms p ↔ t = ⨅ i, …
· 使用定理 `continuous_iInf_dom`：continuous_iInf_dom {t₁ : ι -> TopologicalSpace α} 
{t₂ : TopologicalSpace β} {i : ι} : Continuous[t₁ i, t₂] f -> Continuous[iInf t₁
, t₂] f
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
-/
theorem WithSeminorms.continuous_seminorm {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p)
    (i : ι) : Continuous (p i) := by
  have := hp.topologicalAddGroup
  rw [p.withSeminorms_iff_topologicalSpace_eq_iInf.mp hp]
  exact continuous_iInf_dom (@continuous_norm _ (p i).toSeminormedAddGroup)
/-
**WithSeminorms.toPolynormableSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.toPolynormableSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSem
inorms p) : PolynormableSpace 𝕜 E where withSeminorms'
参数：hp : WithSeminorms p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `WithSeminorms.continuous_seminorm`：WithSeminorms.continuous_seminorm {p 
: SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (i : ι) : Continuous (p i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`：SeminormFamily.withSemino
rms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) : With
Seminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem WithSeminorms.toPolynormableSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    PolynormableSpace 𝕜 E where
  withSeminorms' := by
    have := hp.topologicalAddGroup
    have hp' (i : ι) : Continuous (p i) := hp.continuous_seminorm i
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at ⊢ hp
    refine le_antisymm ?_ ?_
    · simp_rw [le_iInf_iff, ← tendsto_iff_comap]
      intro ⟨p, hp⟩
      exact hp.tendsto' 0 0 (map_zero _)
    · simp_rw [hp, le_iInf_iff]
      intro i
      exact iInf_le (ι := {p : Seminorm 𝕜 E // Continuous p}) _ ⟨p i, hp' i⟩

end TopologicalSpace

/-- The uniform structure induced by a family of seminorms is exactly the infimum of the ones
induced by each seminorm individually. We express this as a characterization of
`WithSeminorms p`. -/
/-
**SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf [u : UniformSpace E]
 [IsUniformAddGroup E] (p : SeminormFamily 𝕜 E ι) : WithSeminorms p ↔ u = ⨅ i, (
p i).toSeminormedAddCommGroup.toUniformSpace
参数：p : SeminormFamily 𝕜 E ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`：SeminormFamily.withSemino
rms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) : With
Seminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝…
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `IsUniformAddGroup.ext_iff`：∀ {G : Type u_3} [inst : AddGroup G] {u v : U
niformSpace G},   IsUniformAddGroup G → IsUniformAddGroup G → (u = v ↔ nhds 0 = 
nhds 0)
· 使用定理 `isUniformAddGroup_iInf`：∀ {G : Type u_1} [inst : AddGroup G] {ι : Sort u
_4} {us' : ι → UniformSpace G},   (∀ (i : ι), IsUniformAddGroup G) → IsUniformAd
dGroup G
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformSpace.toTopologicalSpace_iInf`：toTopologicalSpace_iInf {ι : Sort*
} {u : ι -> UniformSpace α} : (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopolog
icalSpace
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `comap_norm_nhds_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Fi
lter.comap norm (nhds 0) = nhds 0

--- 原说明 ---
The uniform structure induced by a family of seminorms is exactly the infimum of
 the ones
induced by each seminorm individually. We express this as a characterization of
`WithSeminorms p`.
-/
theorem SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf [u : UniformSpace E]
    [IsUniformAddGroup E] (p : SeminormFamily 𝕜 E ι) :
    WithSeminorms p ↔ u = ⨅ i, (p i).toSeminormedAddCommGroup.toUniformSpace := by
  rw [p.withSeminorms_iff_nhds_eq_iInf,
    IsUniformAddGroup.ext_iff inferInstance (isUniformAddGroup_iInf fun i => inferInstance),
    UniformSpace.toTopologicalSpace_iInf, nhds_iInf]
  congrm _ = ⨅ i, ?_
  exact @comap_norm_nhds_zero _ (p i).toAddGroupSeminorm.toSeminormedAddGroup

end IsTopologicalAddGroup

section NormedSpace

/-- The topology of a `NormedSpace 𝕜 E` is induced by the seminorm `normSeminorm 𝕜 E`. -/
/-
**norm_withSeminorms** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [SeminormedAddCommGroup E] [Norme
dSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 𝕜 E
参数：𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`：SeminormFamily.withSemino
rms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) : With
Seminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `iInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
a : α} [Nonempty ι], ⨅ x, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `coe_normSeminorm`：coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm
· 使用定理 `comap_norm_nhds_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Fi
lter.comap norm (nhds 0) = nhds 0

--- 原说明 ---
The topology of a `NormedSpace 𝕜 E` is induced by the seminorm `normSeminorm 𝕜 E
`.
-/
theorem norm_withSeminorms (𝕜 E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    WithSeminorms fun _ : Fin 1 => normSeminorm 𝕜 E := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, iInf_const, coe_normSeminorm,
    comap_norm_nhds_zero]

/-- A (semi-)normed space is polynormable. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (semi-)normed space is polynormable.
-/
instance [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    PolynormableSpace 𝕜 E :=
  norm_withSeminorms 𝕜 E |>.toPolynormableSpace

end NormedSpace

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {p : SeminormFamily 𝕜 E ι}
variable [TopologicalSpace E]

/-
**WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded {s : Set E} (hp : 
WithSeminorms p) : IsVonNBounded 𝕜 s ↔ forall I : Finset ι, exists r > 0, forall
 x in s, I.sup p x < r
参数：hp : WithSeminorms p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.isVonNBounded_iff`：∀ {𝕜 : Type u_1} {E : Type u_3} {ι : 
Type u_5} [inst : SeminormedRing 𝕜] [inst_1 : SMul 𝕜 E] [inst_2 : Zero E]   [ins
t_3 : TopologicalSpace …
· 使用定理 `WithSeminorms.hasBasis`：WithSeminorms.hasBasis (hp : WithSeminorms p) : 
(𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets) id
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `SeminormFamily.basisSets_mem`：basisSets_mem (i : Finset ι) {r : Real} (h
r : 0 < r) : (i.sup p).ball 0 r in p.basisSets
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Seminorm.smul_ball_zero`：smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : 
Real} (hk : k != 0) : k • p.ball 0 r = p.ball 0 (‖k‖ * r)
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用引理 `Absorbs.mono_right`：mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁
) : Absorbs M s t₂
· 使用定理 `Seminorm.ball_zero_absorbs_ball_zero`：ball_zero_absorbs_ball_zero (p : S
eminorm 𝕜 E) {r₁ r₂ : Real} (hr₁ : 0 < r₁) : Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r
₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 s ↔ ∀ I : Finset ι, ∃ r > 0, ∀ x ∈ s, I.sup p x < r := by
  rw [hp.hasBasis.isVonNBounded_iff]
  constructor
  · intro h I
    simp only [id] at h
    specialize h ((I.sup p).ball 0 1) (p.basisSets_mem I zero_lt_one)
    rcases h.exists_pos with ⟨r, hr, h⟩
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm 𝕜 r
    specialize h a (le_of_lt ha)
    rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hr.trans ha), mul_one] at h
    refine ⟨‖a‖, lt_trans hr ha, ?_⟩
    intro x hx
    specialize h hx
    exact (Finset.sup I p).mem_ball_zero.mp h
  intro h s' hs'
  rcases p.basisSets_iff.mp hs' with ⟨I, r, hr, hs'⟩
  rw [id, hs']
  rcases h I with ⟨r', _, h'⟩
  simp_rw [← (I.sup p).mem_ball_zero] at h'
  refine Absorbs.mono_right ?_ h'
  exact (Finset.sup I p).ball_zero_absorbs_ball_zero hr
/-
**WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded (f : G -> E)
 {s : Set G} (hp : WithSeminorms p) : IsVonNBounded 𝕜 (f '' s) ↔ forall I : Fins
et ι, exists r > 0, forall x in s, I.sup p (f x) < r
参数：f : G -> E；hp : WithSeminorms p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`：WithSeminorms.i
sVonNBounded_iff_finset_seminorm_bounded {s : Set E} (hp : WithSeminorms p) : Is
VonNBounded 𝕜 s ↔ forall I : Finset ι, exists…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 (f '' s) ↔
      ∀ I : Finset ι, ∃ r > 0, ∀ x ∈ s, I.sup p (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_finset_seminorm_bounded, Set.forall_mem_image]
/-
**WithSeminorms.isVonNBounded_iff_seminorm_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.isVonNBounded_iff_seminorm_bounded {s : Set E} (hp : WithSem
inorms p) : IsVonNBounded 𝕜 s ↔ forall i : ι, exists r > 0, forall x in s, p i x
 < r
参数：hp : WithSeminorms p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`：WithSeminorms.i
sVonNBounded_iff_finset_seminorm_bounded {s : Set E} (hp : WithSeminorms p) : Is
VonNBounded 𝕜 s ↔ forall I : Finset ι, exists…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Seminorm.finset_sup_apply_lt`：finset_sup_apply_lt {p : ι -> Seminorm 𝕜 E
} {s : Finset ι} {x : E} {a : Real} (ha : 0 < a) (h : forall i, i in s -> p i x 
< a) : s.sup p x <…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem WithSeminorms.isVonNBounded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 s ↔ ∀ i : ι, ∃ r > 0, ∀ x ∈ s, p i x < r := by
  rw [hp.isVonNBounded_iff_finset_seminorm_bounded]
  constructor
  · intro hI i
    convert! hI { i }
    rw [Finset.sup_singleton]
  intro hi I
  by_cases! hI : I.Nonempty
  · choose r hr h using hi
    have h' : 0 < I.sup' hI r := by
      rcases hI with ⟨i, hi⟩
      exact lt_of_lt_of_le (hr i) (Finset.le_sup' r hi)
    refine ⟨I.sup' hI r, h', fun x hx => finset_sup_apply_lt h' fun i hi => ?_⟩
    refine lt_of_lt_of_le (h i x hx) ?_
    simp only [Finset.le_sup'_iff]
    exact ⟨i, hi, (Eq.refl _).le⟩
  simp only [hI, Finset.sup_empty, coe_bot, Pi.zero_apply]
  exact ⟨1, zero_lt_one, fun _ _ => zero_lt_one⟩
/-
**WithSeminorms.image_isVonNBounded_iff_seminorm_bounded** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：WithSeminorms.image_isVonNBounded_iff_seminorm_bounded (f : G -> E) {s : S
et G} (hp : WithSeminorms p) : IsVonNBounded 𝕜 (f '' s) ↔ forall i : ι, exists r
 > 0, forall x in s, p i (f x) < r
参数：f : G -> E；hp : WithSeminorms p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.isVonNBounded_iff_seminorm_bounded`：WithSeminorms.isVonNBo
unded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) : IsVonNBounded 𝕜 
s ↔ forall i : ι, exists r > 0, forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem WithSeminorms.image_isVonNBounded_iff_seminorm_bounded (f : G → E) {s : Set G}
    (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 (f '' s) ↔ ∀ i : ι, ∃ r > 0, ∀ x ∈ s, p i (f x) < r := by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, Set.forall_mem_image]
/-
**WithSeminorms.isVonNBounded_iff_seminorm_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：WithSeminorms.isVonNBounded_iff_seminorm_bddAbove {s : Set E} (hp : WithSe
minorms p) : IsVonNBounded 𝕜 s ↔ forall i : ι, BddAbove (p i '' s)
参数：hp : WithSeminorms p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.isVonNBounded_iff_seminorm_bounded`：WithSeminorms.isVonNBo
unded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) : IsVonNBounded 𝕜 
s ↔ forall i : ι, exists r > 0, forall…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
-/
theorem WithSeminorms.isVonNBounded_iff_seminorm_bddAbove {s : Set E} (hp : WithSeminorms p) :
    IsVonNBounded 𝕜 s ↔ ∀ i : ι, BddAbove (p i '' s) := by
  simp_rw [hp.isVonNBounded_iff_seminorm_bounded, bddAbove_def, forall_mem_image]
  congrm ∀ i, ?_
  constructor
  · rintro ⟨r, _⟩
    use r
    grind
  · rintro ⟨r, _⟩
    use 1 + max r 0
    grind

/-- In a topological vector space, the topology is generated by a single seminorm `p` iff
the unit ball for this seminorm is a bounded neighborhood of `0`. -/
/-
**withSeminorms_iff_mem_nhds_isVonNBounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：withSeminorms_iff_mem_nhds_isVonNBounded [IsTopologicalAddGroup E] [Contin
uousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} : WithSeminorms (fun (_ : Fin 1) => p) ↔ p
.ball 0 1 in 𝓝 0 ∧ IsVonNBounded 𝕜 (p.ball 0 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithSeminorms.mem_nhds_iff`：WithSeminorms.mem_nhds_iff (hp : WithSeminor
ms p) (x : E) (U : Set E) : U in 𝓝 x ↔ exists s : Finset ι, exists r > 0, (s.sup
 p).ball x r sub…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `WithSeminorms.isVonNBounded_iff_seminorm_bounded`：WithSeminorms.isVonNBo
unded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) : IsVonNBounded 𝕜 
s ↔ forall i : ι, exists r > 0, forall…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SeminormFamily.withSeminorms_of_nhds`：SeminormFamily.withSeminorms_of_nh
ds [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) (h : 𝓝 (0 : E) = p.modul
eFilterBasis.toFilterBasis…
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NontriviallyNormedField.cobounded_neBot`：∀ (𝕜 : Type u_1) [inst : Nontri
viallyNormedField 𝕜], (Bornology.cobounded 𝕜).NeBot
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用引理 `Bornology.eventually_ne_cobounded`：eventually_ne_cobounded (a : α) : for
allᶠ x in cobounded α, x != a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Seminorm.smul_ball_zero`：smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : 
Real} (hk : k != 0) : k • p.ball 0 r = p.ball 0 (‖k‖ * r)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Set.smul_set_subset_smul_set_iff₀`：smul_set_subset_smul_set_iff₀ (ha : a
 != 0) {A B : Set β} : a • A subseteq a • B ↔ A subseteq B
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `FilterBasis.mem_filter_of_mem`：mem_filter_of_mem (B : FilterBasis α) {U 
: Set α} : U in B -> U in B.filter
· 使用定理 `SeminormFamily.basisSets_singleton_mem`：basisSets_singleton_mem (i : ι) 
{r : Real} (hr : 0 < r) : (p i).ball 0 r in p.basisSets
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
In a topological vector space, the topology is generated by a single seminorm `p
` iff
the unit ball for this seminorm is a bounded neighborhood of `0`.
-/
theorem withSeminorms_iff_mem_nhds_isVonNBounded [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} :
    WithSeminorms (fun (_ : Fin 1) ↦ p) ↔ p.ball 0 1 ∈ 𝓝 0 ∧ IsVonNBounded 𝕜 (p.ball 0 1) := by
  /- The nontrivial direction is from right to left. With `SeminormFamily.withSeminorms_of_nhds`,
  we need to see that the neighborhoods of zero for the initial topology and for `p` coincide. -/
  refine ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · apply (h.mem_nhds_iff _ _).2
    exact ⟨Finset.univ, 1, zero_lt_one, by simp⟩
  · apply h.isVonNBounded_iff_seminorm_bounded.2 (fun i ↦ ?_)
    exact ⟨1, zero_lt_one, by simp⟩
  rintro ⟨h, h'⟩
  apply SeminormFamily.withSeminorms_of_nhds
  ext s
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · /- Show that a neighborhood `s` of zero for the topology is a neighborhood for `p`, by using the
    boundedness of `p.ball 0 1`: this ensures that, for some nonzero `c`, we have
    `p.ball 0 1 ⊆ c • s`, and therefore `p.ball 0 (‖c‖⁻¹) ⊆ s`. -/
    obtain ⟨c, hc, c_ne⟩ : ∃ (c : 𝕜), p.ball 0 1 ⊆ c • s ∧ c ≠ 0 :=
      ((h' hs).and (eventually_ne_cobounded 0)).exists
    have : p.ball 0 (‖c⁻¹‖) ⊆ s := by
      have : c • p.ball 0 (‖c⁻¹‖) ⊆ c • s := by
        simpa [smul_ball_zero c_ne, ← norm_mul, c_ne] using hc
      rwa [smul_set_subset_smul_set_iff₀ c_ne] at this
    grw [← this]
    apply FilterBasis.mem_filter_of_mem
    change p.ball 0 (‖c⁻¹‖) ∈ SeminormFamily.basisSets (fun (i : Fin 1) ↦ p)
    apply SeminormFamily.basisSets_singleton_mem _ 0
    simpa using c_ne
  · /- Show that a neighborhood `s` for `p` is a neighborhood for the topology, by using the
    fact that `p.ball 0 1` is a neighborhood of `0`. Indeed, `s` contains a ball `p.ball 0 r`,
    which contains `c • p.ball 0 1` for some nonzero `c`. The latter set is a neighborhood of zero
    for the topology thanks to the topological vector space assumption. -/
    rcases (FilterBasis.mem_filter_iff _).1 hs with ⟨t, ht, ts⟩
    grw [← ts]
    rcases (SeminormFamily.basisSets_iff _).1 ht with ⟨w, r, r_pos, hw⟩
    rcases eq_or_ne w ∅ with rfl | w_ne
    · simp only [ball, Finset.sup_empty, sub_zero, coe_bot, Pi.zero_apply, r_pos, ofPred_true] at hw
      simp [hw]
    have : t = p.ball 0 r := by
      have : w = Finset.univ := by
        rcases Finset.nonempty_of_ne_empty w_ne with ⟨i, hi⟩
        ext j
        simp only [Subsingleton.elim j i, hi, Finset.mem_univ]
      simpa only [this, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sup_singleton] using hw
    rw [this]
    obtain ⟨c, c_pos, hc⟩ : ∃ (c : 𝕜), 0 < ‖c‖ ∧ ‖c‖ < r := exists_norm_lt 𝕜 r_pos
    have c_ne : c ≠ 0 := (by simpa using c_pos)
    have : c • p.ball 0 1 ⊆ p.ball 0 r := by
      rw [smul_ball_zero c_ne]
      exact ball_mono (by simpa using hc.le)
    grw [← this]
    simpa using smul_mem_nhds_smul₀ c_ne h

end NontriviallyNormedField

section continuous_of_bounded

namespace WithSeminorms

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedField 𝕝] [Module 𝕝 E]
variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable [NormedField 𝕝₂] [Module 𝕝₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable {τ₁₂ : 𝕝 →+* 𝕝₂} [RingHomIsometric τ₁₂]

/-
**WithSeminorms.continuous_of_continuous_comp** 是 Mathlib 中的一个定理，位于命名空间 `WithSem
inorms`。
形式化陈述：continuous_of_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpa
ce E] [IsTopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q) (f :
 E ->ₛₗ[τ₁₂] F) (hf : forall i, Continuous ((q i).comp f)) : Continuous f
参数：hq : WithSeminorms q；f : E ->ₛₗ[τ₁₂] F；hf : forall i, Continuous ((q i).comp 
f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `continuous_of_continuousAt_zero`：∀ {G : Type w} [inst : TopologicalSpace
 G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {M : Type u_1}   {hom : Type
 u_2} [inst_3 : AddZe…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`：SeminormFamily.withSemino
rms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) : With
Seminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem continuous_of_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
    [IsTopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∀ i, Continuous ((q i).comp f)) : Continuous f := by
  have : IsTopologicalAddGroup F := hq.topologicalAddGroup
  refine continuous_of_continuousAt_zero f ?_
  simp_rw [ContinuousAt, f.map_zero, q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff]
  intro i
  convert! (hf i).continuousAt.tendsto
  exact (map_zero _).symm

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_of_continuous_comp := continuous_of_continuous_comp
/-
**WithSeminorms.continuous_iff_continuous_comp** 是 Mathlib 中的一个定理，位于命名空间 `WithSe
minorms`。
形式化陈述：continuous_iff_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSp
ace E] [IsTopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q) (f 
: E ->ₛₗ[τ₁₂] F) : Continuous f ↔ forall i, Continuous ((q i).comp f)
参数：hq : WithSeminorms q；f : E ->ₛₗ[τ₁₂] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `WithSeminorms.continuous_seminorm`：WithSeminorms.continuous_seminorm {p 
: SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (i : ι) : Continuous (p i)
· 使用定理 `WithSeminorms.continuous_of_continuous_comp`：continuous_of_continuous_co
mp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E] [IsTopologicalAddGroup E] [
TopologicalSpace F] (hq : WithSem…
-/
theorem continuous_iff_continuous_comp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E]
    [IsTopologicalAddGroup E] [TopologicalSpace F] (hq : WithSeminorms q) (f : E →ₛₗ[τ₁₂] F) :
    Continuous f ↔ ∀ i, Continuous ((q i).comp f) :=
  ⟨fun h i => (hq.continuous_seminorm i).comp h, continuous_of_continuous_comp hq f⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_iff_continuous_comp := continuous_iff_continuous_comp
/-
**WithSeminorms.continuous_of_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `WithSeminorms
`。
形式化陈述：continuous_of_isBounded {p : SeminormFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ 
F ι'} {_ : TopologicalSpace E} (hp : WithSeminorms p) {_ : TopologicalSpace F} (
hq : WithSeminorms q) (f : E ->ₛₗ[τ₁₂] F) (hf : Seminorm.IsBounded p q f) : Cont
inuous f
参数：hp : WithSeminorms p；hq : WithSeminorms q；f : E ->ₛₗ[τ₁₂] F；hf : Seminorm.IsB
ounded p q f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `WithSeminorms.continuous_of_continuous_comp`：continuous_of_continuous_co
mp {q : SeminormFamily 𝕝₂ F ι'} [TopologicalSpace E] [IsTopologicalAddGroup E] [
TopologicalSpace F] (hq : WithSem…
· 使用定理 `Seminorm.continuous_of_le`：continuous_of_le [TopologicalSpace E] [IsTopo
logicalAddGroup E] {p q : Seminorm 𝕝 E} (hq : Continuous q) (hpq : p <= q) : Con
tinuous p
· 使用定理 `Seminorm.continuous_finsetSup`：continuous_finsetSup [TopologicalSpace E]
 [IsTopologicalAddGroup E] {p : ι -> Seminorm 𝕝 E} {s : Finset ι} (hp : forall i
 in s, Continuous (…
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `WithSeminorms.continuous_seminorm`：WithSeminorms.continuous_seminorm {p 
: SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (i : ι) : Continuous (p i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Seminorm.finset_sup_smul`：finset_sup_smul (p : ι -> Seminorm 𝕜 E) (s : F
inset ι) (C : Real>=0) : s.sup (C • p) = C • s.sup p
-/
theorem continuous_of_isBounded {p : SeminormFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'}
    {_ : TopologicalSpace E} (hp : WithSeminorms p) {_ : TopologicalSpace F} (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : Seminorm.IsBounded p q f) : Continuous f := by
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  refine continuous_of_continuous_comp hq _ fun i => ?_
  rcases hf i with ⟨s, C, hC⟩
  rw [← finset_sup_smul] at hC
  exact continuous_of_le
    (continuous_finsetSup fun i _ ↦ (hp.continuous_seminorm i).const_smul C) hC

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.continuous_from_bounded := continuous_of_isBounded
/-
**WithSeminorms.continuous_normedSpace_rng** 是 Mathlib 中的一个定理，位于命名空间 `WithSemino
rms`。
形式化陈述：continuous_normedSpace_rng (F) [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ 
F] [TopologicalSpace E] {p : ι -> Seminorm 𝕝 E} (hp : WithSeminorms p) (f : E ->
ₛₗ[τ₁₂] F) (hf : exists (s : Finset ι) (C : Real>=0), (normSeminorm 𝕝₂ F).comp f
 <= C • s.sup p) : Continuous f
参数：F；hp : WithSeminorms p；f : E ->ₛₗ[τ₁₂] F；hf : exists (s : Finset ι) (C : Real
>=0), (normSeminorm 𝕝₂ F).comp f <= C • s.sup p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.continuous_of_isBounded`：continuous_of_isBounded {p : Semi
normFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'} {_ : TopologicalSpace E} (hp : Wi
thSeminorms p) {_ : Topolog…
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Seminorm.isBounded_const`：isBounded_const (ι' : Type*) [Nonempty ι'] {p 
: ι -> Seminorm 𝕜 E} {q : Seminorm 𝕜₂ F} (f : E ->ₛₗ[σ₁₂] F) : IsBounded p (fun 
_ : ι' => q) f…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem continuous_normedSpace_rng (F) [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F]
    [TopologicalSpace E] {p : ι → Seminorm 𝕝 E} (hp : WithSeminorms p)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∃ (s : Finset ι) (C : ℝ≥0), (normSeminorm 𝕝₂ F).comp f ≤ C • s.sup p) :
    Continuous f := by
  rw [← Seminorm.isBounded_const (Fin 1)] at hf
  exact continuous_of_isBounded hp (norm_withSeminorms 𝕝₂ F) f hf
/-
**WithSeminorms._root_.Seminorm.abs_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `WithSemi
norms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Seminorm.abs_le_of_le [Module ℝ E] {p : Seminorm ℝ E}
    {f : E →ₗ[ℝ] ℝ} (hfp : ∀ x, f x ≤ p x) (x : E) :
    |f x| ≤ p x :=
  abs_le.2 ⟨neg_le.1 (by simpa using hfp (-x)), hfp x⟩
/-
**WithSeminorms.continuous_real_rng** 是 Mathlib 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：continuous_real_rng [Module Real E] [TopologicalSpace E] {p : ι -> Seminor
m Real E} (hp : WithSeminorms p) (f : E ->ₗ[Real] Real) (hf : exists (s : Finset
 ι) (C : Real>=0), forall x, f x <= (C • s.sup p) x) : Continuous f
参数：hp : WithSeminorms p；f : E ->ₗ[Real] Real；hf : exists (s : Finset ι) (C : Rea
l>=0), forall x, f x <= (C • s.sup p) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.continuous_normedSpace_rng`：continuous_normedSpace_rng (F)
 [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F] [TopologicalSpace E] {p : ι -> Se
minorm 𝕝 E} (hp : WithSeminorm…
· 使用定理 `Seminorm.abs_le_of_le`：∀ {E : Type u_6} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] {p : Seminorm ℝ E} {f : E →ₗ[ℝ] ℝ},   (∀ (x : E), f x ≤ p x
) → ∀ (x : …
-/
theorem continuous_real_rng [Module ℝ E] [TopologicalSpace E] {p : ι → Seminorm ℝ E}
    (hp : WithSeminorms p) (f : E →ₗ[ℝ] ℝ)
    (hf : ∃ (s : Finset ι) (C : ℝ≥0), ∀ x, f x ≤ (C • s.sup p) x) :
    Continuous f := by
  obtain ⟨s, C, hC⟩ := hf
  exact continuous_normedSpace_rng ℝ hp f ⟨s, C, abs_le_of_le hC⟩

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_withSeminorms_normedSpace := continuous_normedSpace_rng
/-
**WithSeminorms.continuous_normedSpace_dom** 是 Mathlib 中的一个定理，位于命名空间 `WithSemino
rms`。
形式化陈述：continuous_normedSpace_dom (E) [SeminormedAddCommGroup E] [NormedSpace 𝕝 E
] [TopologicalSpace F] {q : ι -> Seminorm 𝕝₂ F} (hq : WithSeminorms q) (f : E ->
ₛₗ[τ₁₂] F) (hf : forall i : ι, exists C : Real>=0, (q i).comp f <= C • normSemin
orm 𝕝 E) : Continuous f
参数：E；hq : WithSeminorms q；f : E ->ₛₗ[τ₁₂] F；hf : forall i : ι, exists C : Real>=
0, (q i).comp f <= C • normSeminorm 𝕝 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.continuous_of_isBounded`：continuous_of_isBounded {p : Semi
normFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'} {_ : TopologicalSpace E} (hp : Wi
thSeminorms p) {_ : Topolog…
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Seminorm.const_isBounded`：const_isBounded (ι : Type*) [Nonempty ι] {p : 
Seminorm 𝕜 E} {q : ι' -> Seminorm 𝕜₂ F} (f : E ->ₛₗ[σ₁₂] F) : IsBounded (fun _ :
 ι => p) q f ↔…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem continuous_normedSpace_dom (E) [SeminormedAddCommGroup E] [NormedSpace 𝕝 E]
    [TopologicalSpace F] {q : ι → Seminorm 𝕝₂ F} (hq : WithSeminorms q)
    (f : E →ₛₗ[τ₁₂] F) (hf : ∀ i : ι, ∃ C : ℝ≥0, (q i).comp f ≤ C • normSeminorm 𝕝 E) :
    Continuous f := by
  rw [← Seminorm.const_isBounded (Fin 1)] at hf
  exact continuous_of_isBounded (norm_withSeminorms 𝕝 E) hq f hf

@[deprecated (since := "2026-03-09")]
alias _root_.Seminorm.cont_normedSpace_to_withSeminorms := continuous_normedSpace_dom

/-- Let `E` and `F` be two topological vector spaces over a `NontriviallyNormedField`, and assume
that the topology of `F` is generated by some family of seminorms `q`. For a family `f` of linear
maps from `E` to `F`, the following are equivalent:
* `f` is equicontinuous at `0`.
* `f` is equicontinuous.
* `f` is uniformly equicontinuous.
* For each `q i`, the family of seminorms `k ↦ (q i) ∘ (f k)` is bounded by some continuous
  seminorm `p` on `E`.
* For each `q i`, the seminorm `⊔ k, (q i) ∘ (f k)` is well-defined and continuous.

In particular, if you can determine all continuous seminorms on `E`, that gives you a complete
characterization of equicontinuity for linear maps from `E` to `F`. For example `E` and `F` are
both normed spaces, you get `NormedSpace.equicontinuous_TFAE`. -/
/-
**WithSeminorms.equicontinuous_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：∀ {𝕜 : Type u_2} {𝕜₂ : Type u_3} {E : Type u_6} {F : Type u_7} {ι' : Type 
u_10} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup E] [inst_2 : _
root_.Module 𝕜 E] [inst_3 : NormedField 𝕜₂] [inst_4 : AddCommGroup F]   [inst_5 
: _root_.Module 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [inst_6 : RingHomIsometric σ₁₂] {κ : Type
 u_11}   {q : SeminormFamily 𝕜₂ F ι'} [inst_7 : UniformSpace E] [IsUniformAddGro
up E] [u : UniformSpace F]   [hu : IsUniformAddGroup F],   WithSeminorms q →    
 ∀ [ContinuousSMul 𝕜 E] (f : κ → E →ₛₗ[σ₁₂] F),       [EquicontinuousAt (DFunLik
e.coe ∘ f) 0, Equicontinuous (DFunLike.coe ∘ f),           UniformEquicontinuous
 (DFunLike.coe ∘ f), ∀ (i : ι'), ∃ p, Continuous ⇑p ∧ ∀ (k : κ), (q i).comp (f k
) ≤ p,           ∀ (i : ι'), BddAbove (Set.range fun k => (q i).comp (f k)) ∧ Co
ntinuous (⨆ k, ⇑((q i).comp (f k)))].TFAE
参数：f : κ → E →ₛₗ[σ₁₂] F；DFunLike.coe ∘ f；DFunLike.coe ∘ f；DFunLike.coe ∘ f；i : ι
'；k : κ；q i；f k；i : ι'；Set.range fun k => (q i).comp (f k)；⨆ k, ⇑((q i).comp (f 
k))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.withSeminorms_iff_uniformSpace_eq_iInf`：SeminormFamily.wi
thSeminorms_iff_uniformSpace_eq_iInf [u : UniformSpace E] [IsUniformAddGroup E] 
(p : SeminormFamily 𝕜 E ι) : WithSeminorms …
· 使用定理 `uniformEquicontinuous_iInf_rng`：uniformEquicontinuous_iInf_rng {u : κ ->
 UniformSpace α'} {F : ι -> β -> α'} : UniformEquicontinuous (uα
· 使用定理 `equicontinuous_iInf_rng`：equicontinuous_iInf_rng {u : κ -> UniformSpace 
α'} {F : ι -> X -> α'} : Equicontinuous (uα
· 使用定理 `equicontinuousAt_iInf_rng`：equicontinuousAt_iInf_rng {u : κ -> UniformSp
ace α'} {F : ι -> X -> α'} {x₀ : X} : EquicontinuousAt (uα
· 使用定理 `List.forall_tfae`：forall_tfae {α : Type*} (l : List (α -> Prop)) (H : fo
rall a : α, (l.map (fun p => p a)).TFAE) : (l.map (fun p => forall a, p a)).TFAE
· 使用定理 `uniformEquicontinuous_of_equicontinuousAt_zero`：∀ {ι : Type u_1} {G : Ty
pe u_2} {M : Type u_3} {hom : Type u_4} [inst : UniformSpace G] [inst_1 : Unifor
mSpace M]   [inst_2 : AddGroup G] [i…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `UniformEquicontinuous.equicontinuous`：UniformEquicontinuous.equicontinuo
us {F : ι -> β -> α} (h : UniformEquicontinuous F) : Equicontinuous F
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.equicontinuousAt_iff_right`：equicontinuousAt_iff_right {ι : Type*
} [TopologicalSpace β] {F : ι -> β -> α} {x₀ : β} : EquicontinuousAt F x₀ ↔ fora
ll ε > 0, forallᶠ x in …
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dist_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], dist 0 = norm
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Seminorm.bddAbove_of_absorbent`：bddAbove_of_absorbent {ι : Sort*} {p : ι
 -> Seminorm 𝕜 E} {s : Set E} (hs : Absorbent 𝕜 s) (h : forall x in s, BddAbove 
(range (p · x))) : B…
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Seminorm.coe_iSup_eq`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFiel
d 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u_12} {p
 : ι → Sem…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Let `E` and `F` be two topological vector spaces over a `NontriviallyNormedField
`, and assume
that the topology of `F` is generated by some family of seminorms `q`. For a fam
ily `f` of linear
maps from `E` to `F`, the following are equivalent:
* `f` is equicontinuous at `0`.
* `f` is equicontinuous.
* `f` is uniformly equicontinuous.
* For each `q i`, the family of seminorms `k ↦ (q i) ∘ (f k)` is bounded by some
 continuous
  seminorm `p` on `E`.
* For each `q i`, the seminorm `⊔ k, (q i) ∘ (f k)` is well-defined and continuo
us.

In particular, if you can determine all continuous seminorms on `E`, that gives 
you a complete
characterization of equicontinuity for linear maps from `E` to `F`. For example 
`E` and `F` are
both normed spaces, you get `NormedSpace.equicontinuous_TFAE`.
-/
protected theorem equicontinuous_TFAE {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F]
    [hu : IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) : TFAE
    [ EquicontinuousAt ((↑) ∘ f) 0,
      Equicontinuous ((↑) ∘ f),
      UniformEquicontinuous ((↑) ∘ f),
      ∀ i, ∃ p : Seminorm 𝕜 E, Continuous p ∧ ∀ k, (q i).comp (f k) ≤ p,
      ∀ i, BddAbove (range fun k ↦ (q i).comp (f k)) ∧ Continuous (⨆ k, (q i).comp (f k)) ] := by
  -- We start by reducing to the case where the target is a seminormed space
  rw [q.withSeminorms_iff_uniformSpace_eq_iInf.mp hq, uniformEquicontinuous_iInf_rng,
      equicontinuous_iInf_rng, equicontinuousAt_iInf_rng]
  refine forall_tfae [_, _, _, _, _] fun i ↦ ?_
  let _ : SeminormedAddCommGroup F := (q i).toSeminormedAddCommGroup
  clear u hu hq
  -- Now we can prove the equivalence in this setting
  simp only [List.map]
  tfae_have 1 → 3 := uniformEquicontinuous_of_equicontinuousAt_zero f
  tfae_have 3 → 2 := UniformEquicontinuous.equicontinuous
  tfae_have 2 → 1 := fun H ↦ H 0
  tfae_have 3 → 5
  | H => by
    have : ∀ᶠ x in 𝓝 0, ∀ k, q i (f k x) ≤ 1 := by
      filter_upwards [Metric.equicontinuousAt_iff_right.mp (H.equicontinuous 0) 1 one_pos]
        with x hx k
      simpa using! (hx k).le
    have bdd : BddAbove (range fun k ↦ (q i).comp (f k)) :=
      Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero this)
        (fun x hx ↦ ⟨1, forall_mem_range.mpr hx⟩)
    rw [← Seminorm.coe_iSup_eq bdd]
    refine ⟨bdd, Seminorm.continuous' (r := 1) ?_⟩
    filter_upwards [this] with x hx
    simpa only [closedBall_iSup bdd _ one_pos, mem_iInter, mem_closedBall_zero] using! hx
  tfae_have 5 → 4 := fun H ↦ ⟨⨆ k, (q i).comp (f k), Seminorm.coe_iSup_eq H.1 ▸ H.2, le_ciSup H.1⟩
  tfae_have 4 → 1 -- This would work over any `NormedField`
  | ⟨p, hp, hfp⟩ =>
    Metric.equicontinuousAt_of_continuity_modulus p (map_zero p ▸ hp.tendsto 0) _ <|
      Eventually.of_forall fun x k ↦ by simpa using! hfp k x
  tfae_finish
/-
**WithSeminorms.uniformEquicontinuous_iff_exists_continuous_seminorm** 是 Mathlib
 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：uniformEquicontinuous_iff_exists_continuous_seminorm {κ : Type*} {q : Semi
normFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F] 
[IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E] (f : κ -> E ->
ₛₗ[σ₁₂] F) : UniformEquicontinuous ((↑) ∘ f) ↔ forall i, exists p : Seminorm 𝕜 E
, Continuous p ∧ forall k, (q i).comp (f k) <= p
参数：hq : WithSeminorms q；f : κ -> E ->ₛₗ[σ₁₂] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `WithSeminorms.equicontinuous_TFAE`：∀ {𝕜 : Type u_2} {𝕜₂ : Type u_3} {E :
 Type u_6} {F : Type u_7} {ι' : Type u_10} [inst : NontriviallyNormedField 𝕜]   
[inst_1 : AddCommGroup …
-/
theorem uniformEquicontinuous_iff_exists_continuous_seminorm {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F]
    [IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔
    ∀ i, ∃ p : Seminorm 𝕜 E, Continuous p ∧ ∀ k, (q i).comp (f k) ≤ p :=
  (hq.equicontinuous_TFAE f).out 2 3
/-
**WithSeminorms.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup** 是 Mathl
ib 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：uniformEquicontinuous_iff_bddAbove_and_continuous_iSup {κ : Type*} {q : Se
minormFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F
] [IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E] (f : κ -> E 
->ₛₗ[σ₁₂] F) : UniformEquicontinuous ((↑) ∘ f) ↔ forall i, BddAbove (range fun k
 => (q i).comp (f k)) ∧ Continuous (⨆ k, (q i).comp (f k))
参数：hq : WithSeminorms q；f : κ -> E ->ₛₗ[σ₁₂] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `WithSeminorms.equicontinuous_TFAE`：∀ {𝕜 : Type u_2} {𝕜₂ : Type u_3} {E :
 Type u_6} {F : Type u_7} {ι' : Type u_10} [inst : NontriviallyNormedField 𝕜]   
[inst_1 : AddCommGroup …
-/
theorem uniformEquicontinuous_iff_bddAbove_and_continuous_iSup {κ : Type*}
    {q : SeminormFamily 𝕜₂ F ι'} [UniformSpace E] [IsUniformAddGroup E] [u : UniformSpace F]
    [IsUniformAddGroup F] (hq : WithSeminorms q) [ContinuousSMul 𝕜 E]
    (f : κ → E →ₛₗ[σ₁₂] F) :
    UniformEquicontinuous ((↑) ∘ f) ↔ ∀ i,
    BddAbove (range fun k ↦ (q i).comp (f k)) ∧
      Continuous (⨆ k, (q i).comp (f k)) :=
  (hq.equicontinuous_TFAE f).out 2 4

end WithSeminorms

section Congr

namespace WithSeminorms

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- Two families of seminorms `p` and `q` on the same space generate the same topology
if each `p i` is bounded by some `C • Finset.sup s q` and vice-versa.

We formulate these boundedness assumptions as `Seminorm.IsBounded q p LinearMap.id` (and
vice-versa) to reuse the API. Furthermore, we don't actually state it as an equality of topologies
but as a way to deduce `WithSeminorms q` from `WithSeminorms p`, since this should be more
useful in practice. -/
/-
**WithSeminorms.congr** 是 Mathlib 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9} {ι' : Type u_10} [inst : No
rmedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] {p : Semin
ormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'} [t : TopologicalSpace E],   WithSem
inorms p → Seminorm.IsBounded p q LinearMap.id → Seminorm.IsBounded q p LinearMa
p.id → WithSeminorms q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.topology_eq_withSeminorms`：∀ {𝕜 : Type u_2} {E : Type u_6}
 {ι : Type u_9} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] {p : Seminorm…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_id_iff_le`：continuous_id_iff_le {t t' : TopologicalSpace α} :
 Continuous[t, t'] id ↔ t <= t'
· 使用定理 `WithSeminorms.continuous_of_isBounded`：continuous_of_isBounded {p : Semi
normFamily 𝕝 E ι} {q : SeminormFamily 𝕝₂ F ι'} {_ : TopologicalSpace E} (hp : Wi
thSeminorms p) {_ : Topolog…

--- 原说明 ---
Two families of seminorms `p` and `q` on the same space generate the same topolo
gy
if each `p i` is bounded by some `C • Finset.sup s q` and vice-versa.

We formulate these boundedness assumptions as `Seminorm.IsBounded q p LinearMap.
id` (and
vice-versa) to reuse the API. Furthermore, we don't actually state it as an equa
lity of topologies
but as a way to deduce `WithSeminorms q` from `WithSeminorms p`, since this shou
ld be more
useful in practice.
-/
protected theorem congr {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}
    [t : TopologicalSpace E] (hp : WithSeminorms p) (hpq : Seminorm.IsBounded p q LinearMap.id)
    (hqp : Seminorm.IsBounded q p LinearMap.id) : WithSeminorms q := by
  constructor
  rw [hp.topology_eq_withSeminorms]
  clear hp t
  refine le_antisymm ?_ ?_ <;>
  rw [← continuous_id_iff_le] <;>
  refine continuous_of_isBounded (.mk (topology := _) rfl) (.mk (topology := _) rfl)
    LinearMap.id (by assumption)
/-
**WithSeminorms.finset_sups** 是 Mathlib 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9} [inst : NormedField 𝕜] [ins
t_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] {p : SeminormFamily 𝕜 E ι} 
[inst_3 : TopologicalSpace E],   WithSeminorms p → WithSeminorms fun s => s.sup 
p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.congr`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9} {ι' 
: Type u_10} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_
.Module 𝕜…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
-/
protected theorem finset_sups {p : SeminormFamily 𝕜 E ι} [TopologicalSpace E]
    (hp : WithSeminorms p) : WithSeminorms (fun s : Finset ι ↦ s.sup p) := by
  refine hp.congr ?_ ?_
  · intro s
    refine ⟨s, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{{i}}, 1, ?_⟩
    rw [Finset.sup_singleton, Finset.sup_singleton, one_smul]
    rfl
/-
**WithSeminorms.partial_sups** 是 Mathlib 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9} [inst : NormedField 𝕜] [ins
t_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Preorder ι] [inst
_4 : LocallyFiniteOrderBot ι] {p : SeminormFamily 𝕜 E ι}   [inst_5 : Topological
Space E], WithSeminorms p → WithSeminorms fun i => (Finset.Iic i).sup p
参数：Finset.Iic i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.congr`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9} {ι' 
: Type u_10} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_
.Module 𝕜…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem partial_sups [Preorder ι] [LocallyFiniteOrderBot ι] {p : SeminormFamily 𝕜 E ι}
    [TopologicalSpace E] (hp : WithSeminorms p) : WithSeminorms (fun i ↦ (Finset.Iic i).sup p) := by
  refine hp.congr ?_ ?_
  · intro i
    refine ⟨Finset.Iic i, 1, ?_⟩
    rw [one_smul]
    rfl
  · intro i
    refine ⟨{i}, 1, ?_⟩
    rw [Finset.sup_singleton, one_smul]
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i ≤ (Finset.Iic i).sup p)
/-
**WithSeminorms.congr_equiv** 是 Mathlib 中的一个定理，位于命名空间 `WithSeminorms`。
形式化陈述：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9} {ι' : Type u_10} [inst : No
rmedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] {p : Semin
ormFamily 𝕜 E ι} [t : TopologicalSpace E],   WithSeminorms p → ∀ (e : ι' ≃ ι), W
ithSeminorms (p ∘ ⇑e)
参数：e : ι' ≃ ι；p ∘ ⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.congr`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9} {ι' 
: Type u_10} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_
.Module 𝕜…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.comp_id`：comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
protected theorem congr_equiv {p : SeminormFamily 𝕜 E ι} [t : TopologicalSpace E]
    (hp : WithSeminorms p) (e : ι' ≃ ι) : WithSeminorms (p ∘ e) := by
  refine hp.congr ?_ ?_ <;>
  intro i <;>
  [use {e i}, 1; use {e.symm i}, 1] <;>
  simp

end WithSeminorms

end Congr

end continuous_of_bounded

section bounded_of_continuous

namespace Seminorm

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : SeminormFamily 𝕜 E ι}

/-- In a semi-`NormedSpace`, a continuous seminorm is zero on elements of norm `0`. -/
/-
**Seminorm.map_eq_zero_of_norm_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：map_eq_zero_of_norm_eq_zero (q : Seminorm 𝕜 F) (hq : Continuous q) {x : F}
 (hx : ‖x‖ = 0) : q x = 0
参数：q : Seminorm 𝕜 F；hq : Continuous q；hx : ‖x‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Specializes.eq`：Specializes.eq [T1Space X] {x y : X} (h : x ⤳ y) : x = y
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
· 使用定理 `mem_closure_zero_iff_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E
] {x : E}, x ∈ closure {0} ↔ ‖x‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…

--- 原说明 ---
In a semi-`NormedSpace`, a continuous seminorm is zero on elements of norm `0`.
-/
lemma map_eq_zero_of_norm_eq_zero (q : Seminorm 𝕜 F)
    (hq : Continuous q) {x : F} (hx : ‖x‖ = 0) : q x = 0 :=
  (map_zero q) ▸
    ((specializes_iff_mem_closure.mpr <| mem_closure_zero_iff_norm.mpr hx).map hq).eq.symm

/-- Let `F` be a semi-`NormedSpace` over a `NontriviallyNormedField`, and let `q` be a
seminorm on `F`. If `q` is continuous, then it is uniformly controlled by the norm, that is there
is some `C > 0` such that `∀ x, q x ≤ C * ‖x‖`.
The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε[`, thus with a
controlled image by `q`. The control of `q` at the original element follows by rescaling. -/
/-
**Seminorm.bound_of_continuous_normedSpace** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：bound_of_continuous_normedSpace (q : Seminorm 𝕜 F) (hq : Continuous q) : e
xists C, 0 < C ∧ (forall x : F, q x <= C * ‖x‖)
参数：q : Seminorm 𝕜 F；hq : Continuous q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `NormedAddGroup.nhds_zero_basis_norm_lt`：∀ {E : Type u_5} [inst : Seminor
medAddGroup E], (nhds 0).HasBasis (fun ε => 0 < ε) fun ε => {y | ‖y‖ < ε}
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Seminorm.map_eq_zero_of_norm_eq_zero`：map_eq_zero_of_norm_eq_zero (q : S
eminorm 𝕜 F) (hq : Continuous q) {x : F} (hx : ‖x‖ = 0) : q x = 0
· 使用引理 `Seminorm.bound_of_shell`：bound_of_shell (p q : Seminorm 𝕜 E) {ε C : Real
} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= p x -> p x <
 ε -> q x <= …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Let `F` be a semi-`NormedSpace` over a `NontriviallyNormedField`, and let `q` be
 a
seminorm on `F`. If `q` is continuous, then it is uniformly controlled by the no
rm, that is there
is some `C > 0` such that `∀ x, q x ≤ C * ‖x‖`.
The continuity ensures boundedness on a ball of some radius `ε`. The nontriviali
ty of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε[`, 
thus with a
controlled image by `q`. The control of `q` at the original element follows by r
escaling.
-/
lemma bound_of_continuous_normedSpace (q : Seminorm 𝕜 F)
    (hq : Continuous q) : ∃ C, 0 < C ∧ (∀ x : F, q x ≤ C * ‖x‖) := by
  have hq' : Tendsto q (𝓝 0) (𝓝 0) := map_zero q ▸ hq.tendsto 0
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp (hq' <| Iio_mem_nhds one_pos)
    with ⟨ε, ε_pos, hε⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < ‖c‖ / ε := by positivity
  refine ⟨‖c‖ / ε, this, fun x ↦ ?_⟩
  by_cases hx : ‖x‖ = 0
  · rw [hx, mul_zero]
    exact le_of_eq (map_eq_zero_of_norm_eq_zero q hq hx)
  · refine (normSeminorm 𝕜 F).bound_of_shell q ε_pos hc (fun x hle hlt ↦ ?_) hx
    refine (le_of_lt <| show q x < _ from hε hlt).trans ?_
    rwa [← div_le_iff₀' this, one_div_div]

/-- Let `E` be a topological vector space (over a `NontriviallyNormedField`) whose topology is
generated by some family of seminorms `p`, and let `q` be a seminorm on `E`. If `q` is continuous,
then it is uniformly controlled by *finitely many* seminorms of `p`, that is there
is some finset `s` of the index set and some `C > 0` such that `q ≤ C • s.sup p`. -/
/-
**Seminorm.bound_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：bound_of_continuous [t : TopologicalSpace E] (hp : WithSeminorms p) (q : S
eminorm 𝕜 E) (hq : Continuous q) : exists s : Finset ι, exists C : Real>=0, C !=
 0 ∧ q <= C • s.sup p
参数：hp : WithSeminorms p；q : Seminorm 𝕜 E；hq : Continuous q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `WithSeminorms.hasBasis`：WithSeminorms.hasBasis (hp : WithSeminorms p) : 
(𝓝 (0 : E)).HasBasis (fun s : Set E => s in p.basisSets) id
· 使用引理 `Seminorm.ball_mem_nhds`：ball_mem_nhds [TopologicalSpace E] {p : Seminorm
 𝕝 E} (hp : Continuous p) {r : Real} (hr : 0 < r) : p.ball 0 r in (𝓝 0 : Filter 
E)
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `Seminorm.continuous`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Nontriviall
yNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3
 : Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Seminorm.ball_eq_metric`：ball_eq_metric : letI
· 使用引理 `Seminorm.bound_of_continuous_normedSpace`：bound_of_continuous_normedSpac
e (q : Seminorm 𝕜 F) (hq : Continuous q) : exists C, 0 < C ∧ (forall x : F, q x 
<= C * ‖x‖)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Let `E` be a topological vector space (over a `NontriviallyNormedField`) whose t
opology is
generated by some family of seminorms `p`, and let `q` be a seminorm on `E`. If 
`q` is continuous,
then it is uniformly controlled by *finitely many* seminorms of `p`, that is the
re
is some finset `s` of the index set and some `C > 0` such that `q ≤ C • s.sup p`
.
-/
lemma bound_of_continuous [t : TopologicalSpace E] (hp : WithSeminorms p)
    (q : Seminorm 𝕜 E) (hq : Continuous q) :
    ∃ s : Finset ι, ∃ C : ℝ≥0, C ≠ 0 ∧ q ≤ C • s.sup p := by
  -- The continuity of `q` gives us a finset `s` and a real `ε > 0`
  -- such that `hε : (s.sup p).ball 0 ε ⊆ q.ball 0 1`.
  rcases hp.hasBasis.mem_iff.mp (ball_mem_nhds hq one_pos) with ⟨V, hV, hε⟩
  rcases p.basisSets_iff.mp hV with ⟨s, ε, ε_pos, rfl⟩
  -- Now forget that `E` already had a topology and view it as the (semi)normed space
  -- `(E, s.sup p)`.
  clear hp hq t
  let _ : SeminormedAddCommGroup E := (s.sup p).toSeminormedAddCommGroup
  let _ : NormedSpace 𝕜 E := { norm_smul_le := fun a b ↦ le_of_eq (map_smul_eq_mul (s.sup p) a b) }
  -- The inclusion `hε` tells us exactly that `q` is *still* continuous for this new topology
  have : Continuous q := by
    apply Seminorm.continuous (r := 1) (mem_of_superset (Metric.ball_mem_nhds _ ε_pos) ?_)
    rw [← ball_eq_metric]
    exact hε
  -- Hence we can conclude by applying `bound_of_continuous_normedSpace`.
  rcases bound_of_continuous_normedSpace q this with ⟨C, C_pos, hC⟩
  exact ⟨s, ⟨C, C_pos.le⟩, fun H ↦ C_pos.ne.symm (congr_arg NNReal.toReal H), hC⟩
  -- Note that the key ingredient for this proof is that, by scaling arguments hidden in
  -- `Seminorm.continuous`, we only have to look at the `q`-ball of radius one, and the `s` we get
  -- from that will automatically work for all other radii.

end Seminorm

end bounded_of_continuous

section LocallyConvexSpace

open LocallyConvexSpace

variable [NormedField 𝕜] [NormedSpace ℝ 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]

/-
**WithSeminorms.toLocallyConvexSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.toLocallyConvexSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSe
minorms p) : LocallyConvexSpace Real E
参数：hp : WithSeminorms p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `LocallyConvexSpace.ofBasisZero`：LocallyConvexSpace.ofBasisZero {ι : Type
*} (b : ι -> Set E) (p : ι -> Prop) (hbasis : (𝓝 0).HasBasis p b) (hconvex : for
all i, p i -> Convex…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithSeminorms.topology_eq_withSeminorms`：∀ {𝕜 : Type u_2} {E : Type u_6}
 {ι : Type u_9} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] {p : Seminorm…
· 使用定理 `AddGroupFilterBasis.nhds_eq`：∀ {G : Type u} [inst : AddGroup G] (B : Add
GroupFilterBasis G) {x₀ : G}, nhds x₀ = B.N x₀
· 使用定理 `AddGroupFilterBasis.N_zero`：∀ {G : Type u} [inst : AddGroup G] (B : AddG
roupFilterBasis G), B.N 0 = B.filter
· 使用定理 `FilterBasis.hasBasis`：∀ {α : Type u_1} (B : FilterBasis α), B.filter.Has
Basis (fun s => s ∈ B) id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Seminorm.convex_ball`：convex_ball : Convex Real (ball p x r)
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem WithSeminorms.toLocallyConvexSpace {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) :
    LocallyConvexSpace ℝ E := by
  have := hp.topologicalAddGroup
  apply ofBasisZero ℝ E id fun s => s ∈ p.basisSets
  · rw [hp.1, AddGroupFilterBasis.nhds_eq _, AddGroupFilterBasis.N_zero]
    exact FilterBasis.hasBasis _
  · intro s hs
    change s ∈ Set.iUnion _ at hs
    simp_rw [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    rcases hs with ⟨I, r, _, rfl⟩
    exact convex_ball _ _ _

/-- A `PolynormableSpace` over `ℝ` is locally convex.

TODO: generalize to `RCLike`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PolynormableSpace` over `ℝ` is locally convex.

TODO: generalize to `RCLike`.
-/
instance (priority := low) [PolynormableSpace ℝ E] : LocallyConvexSpace ℝ E :=
  PolynormableSpace.withSeminorms ℝ E |>.toLocallyConvexSpace

end LocallyConvexSpace

section NormedSpace

variable (𝕜) [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SeminormedAddCommGroup E]

/-- Not an instance since `𝕜` can't be inferred. See `NormedSpace.toLocallyConvexSpace` for a
slightly weaker instance version. -/
/-
**NormedSpace.toLocallyConvexSpace'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedSpace.toLocallyConvexSpace' [NormedSpace 𝕜 E] [Module Real E] [IsSca
larTower Real 𝕜 E] : LocallyConvexSpace Real E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.toLocallyConvexSpace`：WithSeminorms.toLocallyConvexSpace {
p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : LocallyConvexSpace Real E
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E

--- 原说明 ---
Not an instance since `𝕜` can't be inferred. See `NormedSpace.toLocallyConvexSpa
ce` for a
slightly weaker instance version.
-/
theorem NormedSpace.toLocallyConvexSpace' [NormedSpace 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] :
    LocallyConvexSpace ℝ E :=
  (norm_withSeminorms 𝕜 E).toLocallyConvexSpace

/-- See `NormedSpace.toLocallyConvexSpace'` for a slightly stronger version which is not an
instance. -/
/-
**NormedSpace.toLocallyConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NormedSpace.toLocallyConvexSpace [NormedSpace Real E] : LocallyConvexSpace
 Real E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.toLocallyConvexSpace'`：NormedSpace.toLocallyConvexSpace' [No
rmedSpace 𝕜 E] [Module Real E] [IsScalarTower Real 𝕜 E] : LocallyConvexSpace Rea
l E

--- 原说明 ---
See `NormedSpace.toLocallyConvexSpace'` for a slightly stronger version which is
 not an
instance.
-/
instance NormedSpace.toLocallyConvexSpace [NormedSpace ℝ E] : LocallyConvexSpace ℝ E :=
  NormedSpace.toLocallyConvexSpace' ℝ

end NormedSpace

section TopologicalConstructions

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedField 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- The family of seminorms obtained by composing each seminorm by a linear map. -/
/-
**SeminormFamily.comp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E ->ₛₗ[σ₁₂] F) : Semi
normFamily 𝕜 E ι
参数：q : SeminormFamily 𝕜₂ F ι；f : E ->ₛₗ[σ₁₂] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of seminorms obtained by composing each seminorm by a linear map.
-/
def SeminormFamily.comp (q : SeminormFamily 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) : SeminormFamily 𝕜 E ι :=
  fun i => (q i).comp f
/-
**SeminormFamily.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormFamily.comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E ->ₛₗ[
σ₁₂] F) : q.comp f i = (q i).comp f
参数：q : SeminormFamily 𝕜₂ F ι；i : ι；f : E ->ₛₗ[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SeminormFamily.comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E →ₛₗ[σ₁₂] F) :
    q.comp f i = (q i).comp f :=
  rfl
/-
**SeminormFamily.comp_smul_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormFamily.comp_smul_nnreal (q : SeminormFamily 𝕜₂ F ι) (c : NNReal) (
f : E ->ₛₗ[σ₁₂] F) : c • q.comp f = (c • q).comp f
参数：q : SeminormFamily 𝕜₂ F ι；c : NNReal；f : E ->ₛₗ[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SeminormFamily.comp_smul_nnreal (q : SeminormFamily 𝕜₂ F ι) (c : NNReal)
    (f : E →ₛₗ[σ₁₂] F) :
    c • q.comp f = (c • q).comp f := by
  ext
  simp [SeminormFamily.comp_apply, Seminorm.comp_apply]
/-
**SeminormFamily.finset_sup_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeminormFamily.finset_sup_comp (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι) 
(f : E ->ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f)
参数：q : SeminormFamily 𝕜₂ F ι；s : Finset ι；f : E ->ₛₗ[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.comp_apply`：comp_apply (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂
) (x : E) : (p.comp f) x = p (f x)
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Seminorm.finset_sup_apply`：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s :
 Finset ι) (x : E) : s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonne
g (p i) x))
-/
theorem SeminormFamily.finset_sup_comp (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι)
    (f : E →ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f) := by
  ext x
  rw [Seminorm.comp_apply, Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl

variable [TopologicalSpace F]
/-
**LinearMap.withSeminorms_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.withSeminorms_induced {q : SeminormFamily 𝕜₂ F ι} (hq : WithSemi
norms q) (f : E ->ₛₗ[σ₁₂] F) : WithSeminorms (topology
参数：hq : WithSeminorms q；f : E ->ₛₗ[σ₁₂] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `topologicalAddGroup_induced`：∀ {G : Type w} {H : Type x} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Type u_1}   [i
nst_3 : AddGroup …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`：SeminormFamily.withSemino
rms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) : With
Seminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝…
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
-/
theorem LinearMap.withSeminorms_induced {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) (f : E →ₛₗ[σ₁₂] F) :
    WithSeminorms (topology := induced f inferInstance) (q.comp f) := by
  have := hq.topologicalAddGroup
  let _ : TopologicalSpace E := induced f inferInstance
  have : IsTopologicalAddGroup E := topologicalAddGroup_induced f
  rw [(q.comp f).withSeminorms_iff_nhds_eq_iInf, nhds_induced, map_zero,
    q.withSeminorms_iff_nhds_eq_iInf.mp hq, Filter.comap_iInf]
  refine iInf_congr fun i => ?_
  exact Filter.comap_comap
/-
**PolynormableSpace.induced** 是 Mathlib 中的一个定理，位于命名空间 `PolynormableSpace`。
形式化陈述：∀ {𝕜 : Type u_2} {𝕜₂ : Type u_3} {E : Type u_6} {F : Type u_7} [inst : Nor
medField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : N
ormedField 𝕜₂] [inst_4 : AddCommGroup F] [inst_5 : _root_.Module 𝕜₂ F]   {σ₁₂ : 
𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [inst_7 : TopologicalSpace F] [PolynormableSpac
e 𝕜₂ F] (f : E →ₛₗ[σ₁₂] F),   PolynormableSpace 𝕜 E
参数：f : E →ₛₗ[σ₁₂] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.toPolynormableSpace`：WithSeminorms.toPolynormableSpace {p 
: SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : PolynormableSpace 𝕜 E where wit
hSeminorms'
· 使用定理 `LinearMap.withSeminorms_induced`：LinearMap.withSeminorms_induced {q : Se
minormFamily 𝕜₂ F ι} (hq : WithSeminorms q) (f : E ->ₛₗ[σ₁₂] F) : WithSeminorms 
(topology
· 使用定理 `PolynormableSpace.withSeminorms`：PolynormableSpace.withSeminorms [Polyno
rmableSpace 𝕜 E] : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => 
p.1)
-/
protected theorem PolynormableSpace.induced [PolynormableSpace 𝕜₂ F] (f : E →ₛₗ[σ₁₂] F) :
    PolynormableSpace 𝕜 E (topology := induced f inferInstance) := by
  let _ : TopologicalSpace E := induced f inferInstance
  exact f.withSeminorms_induced (PolynormableSpace.withSeminorms 𝕜₂ F) |>.toPolynormableSpace
/-
**Topology.IsInducing.withSeminorms** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.withSeminorms {q : SeminormFamily 𝕜₂ F ι} (hq : WithSe
minorms q) [TopologicalSpace E] {f : E ->ₛₗ[σ₁₂] F} (hf : IsInducing f) : WithSe
minorms (q.comp f)
参数：hq : WithSeminorms q；hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `LinearMap.withSeminorms_induced`：LinearMap.withSeminorms_induced {q : Se
minormFamily 𝕜₂ F ι} (hq : WithSeminorms q) (f : E ->ₛₗ[σ₁₂] F) : WithSeminorms 
(topology
-/
lemma Topology.IsInducing.withSeminorms {q : SeminormFamily 𝕜₂ F ι}
    (hq : WithSeminorms q) [TopologicalSpace E] {f : E →ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    WithSeminorms (q.comp f) := by
  rw [hf.eq_induced]
  exact f.withSeminorms_induced hq
/-
**Topology.IsInducing.polynormableSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.polynormableSpace [PolynormableSpace 𝕜₂ F] [Topologica
lSpace E] {f : E ->ₛₗ[σ₁₂] F} (hf : IsInducing f) : PolynormableSpace 𝕜 E
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.toPolynormableSpace`：WithSeminorms.toPolynormableSpace {p 
: SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : PolynormableSpace 𝕜 E where wit
hSeminorms'
· 使用引理 `Topology.IsInducing.withSeminorms`：Topology.IsInducing.withSeminorms {q 
: SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q) [TopologicalSpace E] {f : E ->ₛₗ
[σ₁₂] F} (hf : IsInduci…
· 使用定理 `PolynormableSpace.withSeminorms`：PolynormableSpace.withSeminorms [Polyno
rmableSpace 𝕜 E] : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => 
p.1)
-/
theorem Topology.IsInducing.polynormableSpace [PolynormableSpace 𝕜₂ F]
    [TopologicalSpace E] {f : E →ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    PolynormableSpace 𝕜 E :=
  hf.withSeminorms (PolynormableSpace.withSeminorms 𝕜₂ F) |>.toPolynormableSpace
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PolynormableSpace 𝕜₂ F] {S : Submodule 𝕜₂ F} :
    PolynormableSpace 𝕜₂ S :=
  IsInducing.polynormableSpace (f := S.subtype) .subtypeVal

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Module 𝕜 E] [TopologicalSpace E]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-
**Seminorm.bound_comp_of_isInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Seminorm.bound_comp_of_isInducing {p : Seminorm 𝕜 E} (hp : Continuous p) {
q : SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q) {f : E ->ₛₗ[σ₁₂] F} (hf : IsIn
ducing f) : exists (s : Finset ι) (C : Real>=0), C != 0 ∧ p <= (C • s.sup q).com
p f
参数：hp : Continuous p；hq : WithSeminorms q；hf : IsInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Seminorm.bound_of_continuous`：bound_of_continuous [t : TopologicalSpace 
E] (hp : WithSeminorms p) (q : Seminorm 𝕜 E) (hq : Continuous q) : exists s : Fi
nset ι, exists C :…
· 使用引理 `Topology.IsInducing.withSeminorms`：Topology.IsInducing.withSeminorms {q 
: SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q) [TopologicalSpace E] {f : E ->ₛₗ
[σ₁₂] F} (hf : IsInduci…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Seminorm.smul_comp`：smul_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) 
(c : R) : (c • p).comp f = c • p.comp f
· 使用定理 `SeminormFamily.finset_sup_comp`：SeminormFamily.finset_sup_comp (q : Semi
normFamily 𝕜₂ F ι) (s : Finset ι) (f : E ->ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup
 (q.comp f)
-/
theorem Seminorm.bound_comp_of_isInducing {p : Seminorm 𝕜 E} (hp : Continuous p)
    {q : SeminormFamily 𝕜₂ F ι} (hq : WithSeminorms q) {f : E →ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    ∃ (s : Finset ι) (C : ℝ≥0), C ≠ 0 ∧ p ≤ (C • s.sup q).comp f := by
  obtain ⟨s, C, hC, hqC⟩ := Seminorm.bound_of_continuous (hf.withSeminorms hq) p hp
  rw [← SeminormFamily.finset_sup_comp, ← Seminorm.smul_comp] at hqC
  exact ⟨s, C, hC, hqC⟩
/-
**Seminorm.exists_le_comp_of_isInducing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Seminorm.exists_le_comp_of_isInducing {p : Seminorm 𝕜 E} (hp : Continuous 
p) [PolynormableSpace 𝕜₂ F] {f : E ->ₛₗ[σ₁₂] F} (hf : IsInducing f) : exists p₂ 
: Seminorm 𝕜₂ F, Continuous p₂ ∧ p <= p₂.comp f
参数：hp : Continuous p；hf : IsInducing f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.bound_comp_of_isInducing`：Seminorm.bound_comp_of_isInducing {p 
: Seminorm 𝕜 E} (hp : Continuous p) {q : SeminormFamily 𝕜₂ F ι} (hq : WithSemino
rms q) {f : E ->ₛₗ[σ₁₂]…
· 使用定理 `PolynormableSpace.withSeminorms`：PolynormableSpace.withSeminorms [Polyno
rmableSpace 𝕜 E] : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => 
p.1)
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Seminorm.continuous_finsetSup`：continuous_finsetSup [TopologicalSpace E]
 [IsTopologicalAddGroup E] {p : ι -> Seminorm 𝕝 E} {s : Finset ι} (hp : forall i
 in s, Continuous (…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Seminorm.exists_le_comp_of_isInducing {p : Seminorm 𝕜 E} (hp : Continuous p)
    [PolynormableSpace 𝕜₂ F] {f : E →ₛₗ[σ₁₂] F} (hf : IsInducing f) :
    ∃ p₂ : Seminorm 𝕜₂ F, Continuous p₂ ∧ p ≤ p₂.comp f := by
  obtain ⟨s, C, -, hqC⟩ := Seminorm.bound_comp_of_isInducing hp
    (PolynormableSpace.withSeminorms 𝕜₂ F) hf
  have := (PolynormableSpace.withSeminorms 𝕜₂ F).topologicalAddGroup
  exact ⟨_, Continuous.const_smul (continuous_finsetSup fun i _ => i.2) C, hqC⟩

end NontriviallyNormedField

/-- (Disjoint) union of seminorm families. -/
/-
**SeminormFamily.sigma** 是 Mathlib 中的一个定义，位于命名空间 `SeminormFamily`。
形式化陈述：{𝕜 : Type u_2} →   {E : Type u_6} →     {ι : Type u_9} →       [inst : Nor
medField 𝕜] →         [inst_1 : AddCommGroup E] →           [inst_2 : _root_.Mod
ule 𝕜 E] →             {κ : ι → Type u_11} → ((i : ι) → SeminormFamily 𝕜 E (κ i)
) → SeminormFamily 𝕜 E ((i : ι) × κ i)
参数：(i : ι) → SeminormFamily 𝕜 E (κ i)；(i : ι) × κ i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Disjoint) union of seminorm families.
-/
protected def SeminormFamily.sigma {κ : ι → Type*} (p : (i : ι) → SeminormFamily 𝕜 E (κ i)) :
    SeminormFamily 𝕜 E ((i : ι) × κ i) :=
  fun ⟨i, k⟩ => p i k
/-
**withSeminorms_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：withSeminorms_iInf {κ : ι -> Type*} {p : (i : ι) -> SeminormFamily 𝕜 E (κ 
i)} {t : ι -> TopologicalSpace E} (hp : forall i, WithSeminorms (topology
参数：i : ι；κ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `topologicalAddGroup_iInf`：∀ {G : Type w} {ι : Sort u_1} [inst : AddGroup
 G] {ts' : ι → TopologicalSpace G},   (∀ (i : ι), IsTopologicalAddGroup G) → IsT
opologicalAddG…
· 使用定理 `SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf`：SeminormFamil
y.withSeminorms_iff_topologicalSpace_eq_iInf [IsTopologicalAddGroup E] (p : Semi
normFamily 𝕜 E ι) : WithSeminorms p ↔ t = ⨅ i, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_sigma`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
p : β → Type u_8} {f : Sigma p → α},   ⨅ x, f x = ⨅ i, ⨅ j, f ⟨i, j⟩
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem withSeminorms_iInf {κ : ι → Type*}
    {p : (i : ι) → SeminormFamily 𝕜 E (κ i)} {t : ι → TopologicalSpace E}
    (hp : ∀ i, WithSeminorms (topology := t i) (p i)) :
    WithSeminorms (topology := ⨅ i, t i) (SeminormFamily.sigma p) := by
  have : ∀ i, @IsTopologicalAddGroup E (t i) _ :=
    fun i ↦ @WithSeminorms.topologicalAddGroup _ _ _ _ _ _ (t i) _ (hp i)
  have : @IsTopologicalAddGroup E (⨅ i, t i) _ := topologicalAddGroup_iInf inferInstance
  simp_rw [@SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _ _ _ _ _ _ _ (_)] at hp ⊢
  rw [iInf_sigma]
  exact iInf_congr hp
/-
**PolynormableSpace.iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PolynormableSpace.iInf {t : ι -> TopologicalSpace E} (ht : forall i, Polyn
ormableSpace 𝕜 E (topology
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.toPolynormableSpace`：WithSeminorms.toPolynormableSpace {p 
: SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : PolynormableSpace 𝕜 E where wit
hSeminorms'
· 使用定理 `withSeminorms_iInf`：withSeminorms_iInf {κ : ι -> Type*} {p : (i : ι) -> 
SeminormFamily 𝕜 E (κ i)} {t : ι -> TopologicalSpace E} (hp : forall i, WithSemi
norms (t…
· 使用定理 `PolynormableSpace.withSeminorms'`：∀ {𝕜 : Type u_2} {E : Type u_6} {inst 
: NormedField 𝕜} {inst_1 : AddCommGroup E} {inst_2 : _root_.Module 𝕜 E}   {topol
ogy : TopologicalSpace…
-/
theorem PolynormableSpace.iInf {t : ι → TopologicalSpace E}
    (ht : ∀ i, PolynormableSpace 𝕜 E (topology := t i)) :
    PolynormableSpace 𝕜 E (topology := ⨅ i, t i) := by
  let _ : TopologicalSpace E := ⨅ i, t i
  exact withSeminorms_iInf (fun i ↦ (ht i).withSeminorms') |>.toPolynormableSpace
/-
**PolynormableSpace.sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PolynormableSpace.sInf {ts : Set (TopologicalSpace E)} (hts : forall t in 
ts, PolynormableSpace 𝕜 E (topology
参数：TopologicalSpace E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `PolynormableSpace.iInf`：PolynormableSpace.iInf {t : ι -> TopologicalSpac
e E} (ht : forall i, PolynormableSpace 𝕜 E (topology
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem PolynormableSpace.sInf {ts : Set (TopologicalSpace E)}
    (hts : ∀ t ∈ ts, PolynormableSpace 𝕜 E (topology := t)) :
    PolynormableSpace 𝕜 E (topology := sInf ts) := by
  rw [sInf_eq_iInf']
  exact .iInf fun t ↦ hts t.1 t.2
/-
**PolynormableSpace.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PolynormableSpace.inf {t₁ t₂ : TopologicalSpace E} (ht₁ : PolynormableSpac
e 𝕜 E (topology
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_pair`：∀ {α : Type u_1} [inst : CompleteLattice α] {a b : α}, sInf {
a, b} = a ⊓ b
· 使用定理 `PolynormableSpace.sInf`：PolynormableSpace.sInf {ts : Set (TopologicalSpa
ce E)} (hts : forall t in ts, PolynormableSpace 𝕜 E (topology
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem PolynormableSpace.inf {t₁ t₂ : TopologicalSpace E}
    (ht₁ : PolynormableSpace 𝕜 E (topology := t₁))
    (ht₂ : PolynormableSpace 𝕜 E (topology := t₂)) :
    PolynormableSpace 𝕜 E (topology := t₁ ⊓ t₂) := by
  rw [← sInf_pair]
  exact .sInf (by simp [ht₁, ht₂])
/-
**withSeminorms_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：withSeminorms_pi {κ : ι -> Type*} {E : ι -> Type*} [forall i, AddCommGroup
 (E i)] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)] {p : (i : 
ι) -> SeminormFamily 𝕜 (E i) (κ i)} (hp : forall i, WithSeminorms (p i)) : WithS
eminorms (SeminormFamily.sigma (fun i => (p i).comp (LinearMap.proj i)))
参数：E i；E i；E i；i : ι；E i；κ i；hp : forall i, WithSeminorms (p i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `withSeminorms_iInf`：withSeminorms_iInf {κ : ι -> Type*} {p : (i : ι) -> 
SeminormFamily 𝕜 E (κ i)} {t : ι -> TopologicalSpace E} (hp : forall i, WithSemi
norms (t…
· 使用定理 `LinearMap.withSeminorms_induced`：LinearMap.withSeminorms_induced {q : Se
minormFamily 𝕜₂ F ι} (hq : WithSeminorms q) (f : E ->ₛₗ[σ₁₂] F) : WithSeminorms 
(topology
-/
theorem withSeminorms_pi {κ : ι → Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    {p : (i : ι) → SeminormFamily 𝕜 (E i) (κ i)}
    (hp : ∀ i, WithSeminorms (p i)) :
    WithSeminorms (SeminormFamily.sigma (fun i ↦ (p i).comp (LinearMap.proj i))) :=
  withSeminorms_iInf fun i ↦ (LinearMap.proj i).withSeminorms_induced (hp i)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, PolynormableSpace 𝕜 (E i)] :
    PolynormableSpace 𝕜 (Π i, E i) :=
  .iInf fun i ↦ .induced (LinearMap.proj (R := 𝕜) (φ := E) i)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {E₁ E₂ : Type*} [AddCommGroup E₁] [AddCommGroup E₂] [Module 𝕜 E₁] [Module 𝕜 E₂]
    [TopologicalSpace E₁] [TopologicalSpace E₂] [PolynormableSpace 𝕜 E₁] [PolynormableSpace 𝕜 E₂] :
    PolynormableSpace 𝕜 (E₁ × E₂) :=
  .inf (.induced <| LinearMap.fst 𝕜 E₁ E₂) (.induced <| LinearMap.snd 𝕜 E₁ E₂)

end TopologicalConstructions

section TopologicalProperties

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Countable ι]
variable {p : SeminormFamily 𝕜 E ι}
variable [TopologicalSpace E]

/-- If the topology of a space is induced by a countable family of seminorms, then the topology
is first countable. -/
/-
**WithSeminorms.firstCountableTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithSeminorms.firstCountableTopology (hp : WithSeminorms p) : FirstCountab
leTopology E
参数：hp : WithSeminorms p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.topologicalAddGroup`：WithSeminorms.topologicalAddGroup (hp
 : WithSeminorms p) : IsTopologicalAddGroup E
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormFamily.withSeminorms_iff_nhds_eq_iInf`：SeminormFamily.withSemino
rms_iff_nhds_eq_iInf [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) : With
Seminorms p ↔ (𝓝 (0 : E)) = ⨅ i, (𝓝…
· 使用定理 `Filter.iInf.isCountablyGenerated`：∀ {ι : Sort u_6} {α : Type u_7} [Count
able ι] (f : ι → Filter α) [∀ (i : ι), (f i).IsCountablyGenerated],   (⨅ i, f i)
.IsCountablyGenerated
· 使用定理 `Filter.comap.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : 
Filter β) [l.IsCountablyGenerated] (f : α → β),   (Filter.comap f l).IsCountably
Generated
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsUniformAddGroup.uniformity_countably_generated`：∀ {α : Type u_1} [inst
 : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] [(nhds 0).IsCount
ablyGenerated],   (uniformity α).IsCou…
· 使用定理 `UniformSpace.firstCountableTopology`：∀ (α : Type u) [uniformSpace : Unif
ormSpace α] [(uniformity α).IsCountablyGenerated], FirstCountableTopology α

--- 原说明 ---
If the topology of a space is induced by a countable family of seminorms, then t
he topology
is first countable.
-/
theorem WithSeminorms.firstCountableTopology (hp : WithSeminorms p) :
    FirstCountableTopology E := by
  have := hp.topologicalAddGroup
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : (𝓝 (0 : E)).IsCountablyGenerated := by
    rw [p.withSeminorms_iff_nhds_eq_iInf.mp hp]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.firstCountableTopology E

end TopologicalProperties

