/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Monotone

/-!
# Points in sight

This file defines the relation of visibility with respect to a set, and lower bounds how many
elements of a set a point sees in terms of the dimension of that set.

## TODO

The art gallery problem can be stated using the visibility predicate: A set `A` (the art gallery) is
guarded by a finite set `G` (the guards) iff `∀ a ∈ A, ∃ g ∈ G, IsVisible ℝ sᶜ a g`.
-/

@[expose] public section

open AffineMap Filter Finset Set
open scoped Cardinal Pointwise Topology

variable {𝕜 V P : Type*}

section AddTorsor
variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
  {s t : Set P} {x y z : P}

omit [IsOrderedRing 𝕜] in
variable (𝕜) in
/-- Two points are visible to each other through a set if no point of that set lies strictly
between them.

By convention, a point `x` sees itself through any set `s`, even when `x ∈ s`. -/
/-
**IsVisible** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsVisible (s : Set P) (x y : P) : Prop
参数：s : Set P；x y : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two points are visible to each other through a set if no point of that set lies 
strictly
between them.

By convention, a point `x` sees itself through any set `s`, even when `x ∈ s`.
-/
def IsVisible (s : Set P) (x y : P) : Prop := ∀ ⦃z⦄, z ∈ s → ¬ Sbtw 𝕜 x z y

@[simp, refl]
/-
**IsVisible.rfl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsVisible.rfl : IsVisible 𝕜 s x x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsVisible.rfl : IsVisible 𝕜 s x x := by simp [IsVisible]
/-
**isVisible_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isVisible_comm : IsVisible 𝕜 s x y ↔ IsVisible 𝕜 s y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isVisible_comm : IsVisible 𝕜 s x y ↔ IsVisible 𝕜 s y x := by
  simp [IsVisible, sbtw_comm]

@[symm] alias ⟨IsVisible.symm, _⟩ := isVisible_comm

omit [IsOrderedRing 𝕜] in
/-
**IsVisible.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsVisible.mono (hst : s subseteq t) (ht : IsVisible 𝕜 t x y) : IsVisible 𝕜
 s x y
参数：hst : s subseteq t；ht : IsVisible 𝕜 t x y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsVisible.mono (hst : s ⊆ t) (ht : IsVisible 𝕜 t x y) : IsVisible 𝕜 s x y :=
  fun _z hz ↦ ht <| hst hz

set_option backward.isDefEq.respectTransparency false in
/-
**isVisible_iff_lineMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isVisible_iff_lineMap (hxy : x != y) : IsVisible 𝕜 s x y ↔ forall δ in Set
.Ioo (0 : 𝕜) 1, lineMap x y δ ∉ s
参数：hxy : x != y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
lemma isVisible_iff_lineMap (hxy : x ≠ y) :
    IsVisible 𝕜 s x y ↔ ∀ δ ∈ Set.Ioo (0 : 𝕜) 1, lineMap x y δ ∉ s := by
  simp [IsVisible, sbtw_iff_mem_image_Ioo_and_ne, hxy]
  aesop

end AddTorsor

section Module
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {s : Set V} {x y z : V}

set_option backward.isDefEq.respectTransparency false in
/-- If a point `x` sees a convex combination of points of a set `s` through `convexHull ℝ s ∌ x`,
then it sees all terms of that combination.

Note that the converse does not hold. -/
/-
**IsVisible.of_convexHull_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsVisible.of_convexHull_of_pos {ι : Type*} {t : Finset ι} {a : ι -> V} {w 
: ι -> 𝕜} (hw₀ : forall i in t, 0 <= w i) (hw₁ : ∑ i in t, w i = 1) (ha : forall
 i in t, a i in s) (hx : x ∉ convexHull 𝕜 s) (hw : IsVisible 𝕜 (convexHull 𝕜 s) 
x (∑ i in t, w i • a i)) {i : ι} (hi : i in t) (hwi : 0 < w i) : IsVisible 𝕜 (co
nvexHull 𝕜 s) x (a i)
参数：hw₀ : forall i in t, 0 <= w i；hw₁ : ∑ i in t, w i = 1；ha : forall i in t, a i
 in s；hx : x ∉ convexHull 𝕜 s；hw : IsVisible 𝕜 (convexHull 𝕜 s) x (∑ i in t, w i
 • a i)；hi : i in t；hwi : 0 < w i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.sum_erase_eq_sub`：∀ {ι : Type u_1} {G : Type u_3} {s : Finset ι} 
[inst : AddCommGroup G] [inst_1 : DecidableEq ι] {f : ι → G} {a : ι},   a ∈ s → 
∑ x ∈ s.erase…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
（共 168 条，此处仅展示前 30 条）

--- 原说明 ---
If a point `x` sees a convex combination of points of a set `s` through `convexH
ull ℝ s ∌ x`,
then it sees all terms of that combination.

Note that the converse does not hold.
-/
lemma IsVisible.of_convexHull_of_pos {ι : Type*} {t : Finset ι} {a : ι → V} {w : ι → 𝕜}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1) (ha : ∀ i ∈ t, a i ∈ s)
    (hx : x ∉ convexHull 𝕜 s) (hw : IsVisible 𝕜 (convexHull 𝕜 s) x (∑ i ∈ t, w i • a i)) {i : ι}
    (hi : i ∈ t) (hwi : 0 < w i) : IsVisible 𝕜 (convexHull 𝕜 s) x (a i) := by
  classical
  obtain hwi | hwi : w i = 1 ∨ w i < 1 := eq_or_lt_of_le <| (single_le_sum hw₀ hi).trans_eq hw₁
  · convert! hw
    rw [← one_smul 𝕜 (a i), ← hwi, eq_comm]
    rw [← hwi, ← sub_eq_zero, ← sum_erase_eq_sub hi,
      sum_eq_zero_iff_of_nonneg fun j hj ↦ hw₀ _ <| erase_subset _ _ hj] at hw₁
    refine sum_eq_single _ (fun j hj hji ↦ ?_) (by simp [hi])
    rw [hw₁ _ <| mem_erase.2 ⟨hji, hj⟩, zero_smul]
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, h⟩
  replace hε₀ : 0 < ε := hε₀.lt_of_ne <| by rintro rfl; simp at h
  replace hε₁ : ε < 1 := hε₁.lt_of_ne <| by rintro rfl; simp at h
  have : 0 < 1 - ε := by linarith
  have hwi : 0 < 1 - w i := by linarith
  refine hw (z := lineMap x (∑ j ∈ t, w j • a j) ((w i)⁻¹ / ((1 - ε) / ε + (w i)⁻¹)))
    ?_ <| sbtw_lineMap_iff.2 ⟨(ne_of_mem_of_not_mem ((convex_convexHull ..).sum_mem hw₀ hw₁
    fun i hi ↦ subset_convexHull _ _ <| ha _ hi) hx).symm, by positivity,
    (div_lt_one <| by positivity).2 ?_⟩
  · have : Wbtw 𝕜
      (lineMap x (a i) ε)
      (lineMap x (∑ j ∈ t, w j • a j) ((w i)⁻¹ / ((1 - ε) / ε + (w i)⁻¹)))
      (∑ j ∈ t.erase i, (w j / (1 - w i)) • a j) := by
      refine ⟨((1 - w i) / w i) / ((1 - ε) / ε + (1 - w i) / w i + 1), ⟨by positivity, ?_⟩, ?_⟩
      · refine (div_le_one <| by positivity).2 ?_
        calc
          (1 - w i) / w i = 0 + (1 - w i) / w i + 0 := by simp
          _ ≤ (1 - ε) / ε + (1 - w i) / w i + 1 := by gcongr <;> positivity
      have :
        w i • a i + (1 - w i) • ∑ j ∈ t.erase i, (w j / (1 - w i)) • a j = ∑ j ∈ t, w j • a j := by
        rw [smul_sum]
        simp_rw [smul_smul, mul_div_cancel₀ _ hwi.ne']
        exact add_sum_erase _ (fun i ↦ w i • a i) hi
      simp_rw [lineMap_apply_module, ← this]
      match_scalars <;> field
    refine (convex_convexHull _ _).mem_of_wbtw this hε <| (convex_convexHull _ _).sum_mem ?_ ?_ ?_
    · intro j hj
      positivity [hw₀ j <| erase_subset _ _ hj]
    · rw [← sum_div, sum_erase_eq_sub hi, hw₁, div_self hwi.ne']
    · exact fun j hj ↦ subset_convexHull _ _ <| ha _ <| erase_subset _ _ hj
  · exact lt_add_of_pos_left _ <| by positivity

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V]

set_option backward.isDefEq.respectTransparency false in
/-- One cannot see any point in the interior of a set. -/
/-
**IsVisible.eq_of_mem_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsVisible.eq_of_mem_interior (hsxy : IsVisible 𝕜 s x y) (hy : y in interio
r s) : x = y
参数：hsxy : IsVisible 𝕜 s x y；hy : y in interior s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `AffineMap.lineMap_continuous`：lineMap_continuous {p q : P} : Continuous 
(lineMap p q : R ->ᵃ[R] P)
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsVisible.symm`：∀ {𝕜 : Type u_1} {V : Type u_2} {P : Type u_3} [inst : F
ield 𝕜] [inst_1 : LinearOrder 𝕜] [IsOrderedRing 𝕜]   [inst_3 : AddCommGroup V] [
inst…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
One cannot see any point in the interior of a set.
-/
lemma IsVisible.eq_of_mem_interior (hsxy : IsVisible 𝕜 s x y) (hy : y ∈ interior s) :
    x = y := by
  by_contra! hxy
  suffices h : ∀ᶠ (_δ : 𝕜) in 𝓝[>] 0, False by obtain ⟨_, ⟨⟩⟩ := h.exists
  have hmem : ∀ᶠ (δ : 𝕜) in 𝓝[>] 0, lineMap y x δ ∈ s :=
    lineMap_continuous.continuousWithinAt.eventually_mem
      (by simpa using mem_interior_iff_mem_nhds.1 hy)
  filter_upwards [hmem, Ioo_mem_nhdsGT zero_lt_one] with δ hmem hsbt using hsxy.symm hmem (by aesop)

/-- One cannot see any point of an open set. -/
/-
**IsOpen.eq_of_isVisible_of_left_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsOpen.eq_of_isVisible_of_left_mem (hs : IsOpen s) (hsxy : IsVisible 𝕜 s x
 y) (hy : y in s) : x = y
参数：hs : IsOpen s；hsxy : IsVisible 𝕜 s x y；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsVisible.eq_of_mem_interior`：IsVisible.eq_of_mem_interior (hsxy : IsVis
ible 𝕜 s x y) (hy : y in interior s) : x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s

--- 原说明 ---
One cannot see any point of an open set.
-/
lemma IsOpen.eq_of_isVisible_of_left_mem (hs : IsOpen s) (hsxy : IsVisible 𝕜 s x y) (hy : y ∈ s) :
    x = y :=
  hsxy.eq_of_mem_interior (by simpa [hs.interior_eq])

end Module

section Real
variable [AddCommGroup V] [Module ℝ V] {s : Set V} {x y z : V}

/-- All points of the convex hull of a set `s` visible from a point `x ∉ convexHull ℝ s` lie in the
convex hull of such points that actually lie in `s`.

Note that the converse does not hold. -/
/-
**IsVisible.mem_convexHull_isVisible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsVisible.mem_convexHull_isVisible (hx : x ∉ convexHull Real s) (hy : y in
 convexHull Real s) (hxy : IsVisible Real (convexHull Real s) x y) : y in convex
Hull Real {z in s | IsVisible Real (convexHull Real s) x z}
参数：hx : x ∉ convexHull Real s；hy : y in convexHull Real s；hxy : IsVisible Real (
convexHull Real s) x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_convexHull_iff_exists_fintype`：mem_convexHull_iff_exists_fintype {s 
: Set E} {x : E} : x in convexHull R s ↔ exists (ι : Type) (_ : Fintype ι) (w : 
ι -> R) (z : ι -> E), (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_subset`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] {s : Finset ι} {f : ι → M},   (∀ (i : ι), f i ≠ 0 → i 
∈ s) → ∑…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `left_ne_zero_of_smul`：left_ne_zero_of_smul : a • b != 0 -> a != 0
· 使用定理 `Convex.sum_mem`：Convex.sum_mem (hs : Convex R s) (h₀ : forall i in t, 0 
<= w i) (h₁ : ∑ i in t, w i = 1) (hz : forall i in t, z i in s) : (∑ i in t, w i
 • z…
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用引理 `IsVisible.of_convexHull_of_pos`：IsVisible.of_convexHull_of_pos {ι : Type
*} {t : Finset ι} {a : ι -> V} {w : ι -> 𝕜} (hw₀ : forall i in t, 0 <= w i) (hw₁
 : ∑ i in t, w i = 1…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
All points of the convex hull of a set `s` visible from a point `x ∉ convexHull 
ℝ s` lie in the
convex hull of such points that actually lie in `s`.

Note that the converse does not hold.
-/
lemma IsVisible.mem_convexHull_isVisible (hx : x ∉ convexHull ℝ s) (hy : y ∈ convexHull ℝ s)
    (hxy : IsVisible ℝ (convexHull ℝ s) x y) :
    y ∈ convexHull ℝ {z ∈ s | IsVisible ℝ (convexHull ℝ s) x z} := by
  obtain ⟨ι, _, w, a, hw₀, hw₁, ha, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hy
  rw [← Fintype.sum_subset (s := {i | w i ≠ 0})
    fun i hi ↦ mem_filter.2 ⟨mem_univ _, left_ne_zero_of_smul hi⟩]
  exact (convex_convexHull ..).sum_mem (fun i _ ↦ hw₀ _) (by rwa [sum_filter_ne_zero])
    fun i hi ↦ subset_convexHull _ _ ⟨ha _, IsVisible.of_convexHull_of_pos (fun _ _ ↦ hw₀ _) hw₁
      (by simpa) hx hxy (mem_univ _) <| (hw₀ _).lt_of_ne' (mem_filter.1 hi).2⟩

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

set_option backward.isDefEq.respectTransparency false in
/-- If `s` is a closed set, then any point `x` sees some point of `s` in any direction where there
is something to see. -/
/-
**IsClosed.exists_wbtw_isVisible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.exists_wbtw_isVisible (hs : IsClosed s) (hy : y in s) (x : V) : e
xists z in s, Wbtw Real x z y ∧ IsVisible Real s x z
参数：hs : IsClosed s；hy : y in s；x : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `BddBelow.inter_of_left`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, BddBelow s → BddBelow (s ∩ t)
· 使用定理 `bddBelow_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, BddBelow (Se
t.Ici a)
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `IsClosed.csInf_mem`：IsClosed.csInf_mem {s : Set α} (hc : IsClosed s) (hs
 : s.Nonempty) (B : BddBelow s) : sInf s in s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `AffineMap.lineMap_continuous`：lineMap_continuous {p q : P} : Continuous 
(lineMap p q : R ->ᵃ[R] P)
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `wbtw_lineMap_iff`：wbtw_lineMap_iff : Wbtw R x (lineMap x y r) y ↔ x = y 
∨ r in Set.Icc (0 : R) 1
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is a closed set, then any point `x` sees some point of `s` in any directi
on where there
is something to see.
-/
lemma IsClosed.exists_wbtw_isVisible (hs : IsClosed s) (hy : y ∈ s) (x : V) :
    ∃ z ∈ s, Wbtw ℝ x z y ∧ IsVisible ℝ s x z := by
  let t : Set ℝ := Ici 0 ∩ lineMap x y ⁻¹' s
  have ht₁ : 1 ∈ t := by simpa [t]
  have ht : BddBelow t := bddBelow_Ici.inter_of_left
  let δ : ℝ := sInf t
  have hδ₁ : δ ≤ 1 := csInf_le ht ht₁
  obtain ⟨hδ₀, hδ⟩ : 0 ≤ δ ∧ lineMap x y δ ∈ s :=
    (isClosed_Ici.inter <| hs.preimage lineMap_continuous).csInf_mem ⟨1, ht₁⟩ ht
  refine ⟨lineMap x y δ, hδ, wbtw_lineMap_iff.2 <| .inr ⟨hδ₀, hδ₁⟩, ?_⟩
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, -, h⟩
  replace hδ₀ : 0 < δ := hδ₀.lt_of_ne' <| by rintro hδ₀; simp [hδ₀] at h
  replace hε₁ : ε < 1 := hε₁.lt_of_ne <| by rintro rfl; simp at h
  rw [lineMap_lineMap_right] at hε
  exact (csInf_le ht ⟨mul_nonneg hε₀ hδ₀.le, hε⟩).not_gt <| mul_lt_of_lt_one_left hδ₀ hε₁

-- TODO: Once we have cone hulls, the RHS can be strengthened to
-- `coneHull ℝ x {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}`
/-- A set whose convex hull is closed lies in the cone based at a point `x` generated by its points
visible from `x` through its convex hull. -/
/-
**IsClosed.convexHull_subset_affineSpan_isVisible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClosed.convexHull_subset_affineSpan_isVisible (hs : IsClosed (convexHull
 Real s)) (hx : x ∉ convexHull Real s) : convexHull Real s subseteq affineSpan R
eal ({x} union {y in s | IsVisible Real (convexHull Real s) x y})
参数：hs : IsClosed (convexHull Real s)；hx : x ∉ convexHull Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClosed.exists_wbtw_isVisible`：IsClosed.exists_wbtw_isVisible (hs : IsC
losed s) (hy : y in s) (x : V) : exists z in s, Wbtw Real x z y ∧ IsVisible Real
 s x z
· 使用引理 `AffineSubspace.right_mem_of_wbtw`：AffineSubspace.right_mem_of_wbtw {s : 
AffineSubspace R P} (hxyz : Wbtw R x y z) (hx : x in s) (hy : y in s) (hxy : x !
= y) : z in s
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `convexHull_subset_affineSpan`：convexHull_subset_affineSpan (s : Set E) :
 convexHull 𝕜 s subseteq (affineSpan 𝕜 s : Set E)
· 使用引理 `IsVisible.mem_convexHull_isVisible`：IsVisible.mem_convexHull_isVisible (
hx : x ∉ convexHull Real s) (hy : y in convexHull Real s) (hxy : IsVisible Real 
(convexHull Real s) x y)…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b

--- 原说明 ---
A set whose convex hull is closed lies in the cone based at a point `x` generate
d by its points
visible from `x` through its convex hull.
-/
lemma IsClosed.convexHull_subset_affineSpan_isVisible (hs : IsClosed (convexHull ℝ s))
    (hx : x ∉ convexHull ℝ s) :
    convexHull ℝ s ⊆ affineSpan ℝ ({x} ∪ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) := by
  rintro y hy
  obtain ⟨z, hz, hxzy, hxz⟩ := hs.exists_wbtw_isVisible hy x
  -- TODO: `calc` doesn't work with `∈` :(
  exact AffineSubspace.right_mem_of_wbtw hxzy (subset_affineSpan _ _ <| subset_union_left rfl)
    (affineSpan_mono _ subset_union_right <| convexHull_subset_affineSpan _ <|
      hxz.mem_convexHull_isVisible hx hz) (ne_of_mem_of_not_mem hz hx).symm

open Submodule in
/-- If `s` is a closed set of dimension `d` and `x` is a point outside of its convex hull,
then `x` sees at least `d` points of the convex hull of `s` that actually lie in `s`. -/
/-
**rank_le_card_isVisible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rank_le_card_isVisible (hs : IsClosed (convexHull Real s)) (hx : x ∉ conve
xHull Real s) : Module.rank Real (span Real (-x +ᵥ s)) <= #{y in s | IsVisible R
eal (convexHull Real s) x y}
参数：hs : IsClosed (convexHull Real s)；hx : x ∉ convexHull Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.vadd_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {s 
t : Set β} {a : α}, s ⊆ t → a +ᵥ s ⊆ a +ᵥ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用引理 `IsClosed.convexHull_subset_affineSpan_isVisible`：IsClosed.convexHull_sub
set_affineSpan_isVisible (hs : IsClosed (convexHull Real s)) (hx : x ∉ convexHul
l Real s) : convexHull Real s subsete…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.pointwise_vadd_span`：pointwise_vadd_span (v : V) (s : Set
 P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s)
· 使用定理 `Set.vadd_set_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] (
a : α) (b : β) (s : Set β),   a +ᵥ insert b s = insert (a +ᵥ b) (a +ᵥ s)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `affineSpan_insert_zero`：affineSpan_insert_zero (s : Set V) : (affineSpan
 k (insert 0 s) : Set V) = Submodule.span k s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineSubspace.coe_pointwise_vadd`：∀ {k : Type u_2} {V : Type u_3} {P : 
Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]
   [inst_3 : AddTorsor …
· 使用定理 `Submodule.span_span`：span_span : span R (span R s : Set M) = span R s
· 使用定理 `rank_span_le`：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Cardinal.mk_vadd_set`：∀ {G : Type u_1} {α : Type u_3} [inst : AddGroup G
] [inst_1 : AddAction G α] (a : G) (s : Set α),   Cardinal.mk ↑(a +ᵥ s) = Cardin
al.mk ↑s

--- 原说明 ---
If `s` is a closed set of dimension `d` and `x` is a point outside of its convex
 hull,
then `x` sees at least `d` points of the convex hull of `s` that actually lie in
 `s`.
-/
lemma rank_le_card_isVisible (hs : IsClosed (convexHull ℝ s)) (hx : x ∉ convexHull ℝ s) :
    Module.rank ℝ (span ℝ (-x +ᵥ s)) ≤ #{y ∈ s | IsVisible ℝ (convexHull ℝ s) x y} := by
  calc
    Module.rank ℝ (span ℝ (-x +ᵥ s)) ≤
      Module.rank ℝ (span ℝ
        (-x +ᵥ affineSpan ℝ ({x} ∪ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) : Set V)) := by
      push_cast
      refine Submodule.rank_mono ?_
      gcongr
      exact (subset_convexHull ..).trans <| hs.convexHull_subset_affineSpan_isVisible hx
    _ = Module.rank ℝ (span ℝ (-x +ᵥ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y})) := by
      suffices h :
        -x +ᵥ (affineSpan ℝ ({x} ∪ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) : Set V) =
          span ℝ (-x +ᵥ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) by
        rw [AffineSubspace.coe_pointwise_vadd, h, span_span]
      simp [← AffineSubspace.coe_pointwise_vadd, AffineSubspace.pointwise_vadd_span,
        vadd_set_insert, affineSpan_insert_zero]
    _ ≤ #(-x +ᵥ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) := rank_span_le _
    _ = #{y ∈ s | IsVisible ℝ (convexHull ℝ s) x y} := by simp

end Real

