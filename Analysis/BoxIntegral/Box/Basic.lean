/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.Order.MonotoneConvergence
/-!
# Rectangular boxes in `ℝⁿ`

In this file we define rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the type of
functions `ι → ℝ` (usually `ι = Fin n` for some `n`). When we need to interpret a box `[l, u]` as a
set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals `(l i, u i]`. We
exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

We use the same structure `BoxIntegral.Box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `Membership (ι → ℝ) (Box ι)` and `CoeTC (Box ι) (Set <| ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ Set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. The empty box can
be represented as `⊥ : WithBot (BoxIntegral.Box ι)`.

We define the following operations on boxes:

* coercion to `Set (ι → ℝ)` and `Membership (ι → ℝ) (BoxIntegral.Box ι)` as described above;
* `PartialOrder` and `SemilatticeSup` instances such that `I ≤ J` is equivalent to
  `(I : Set (ι → ℝ)) ⊆ J`;
* `Lattice` instances on `WithBot (BoxIntegral.Box ι)`;
* `BoxIntegral.Box.Icc`: the closed box `Set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `Box ι` to `Set (ι → ℝ)`;
* `BoxIntegral.Box.face I i : Box (Fin n)`: a hyperface of `I : BoxIntegral.Box (Fin (n + 1))`;
* `BoxIntegral.Box.distortion`: the maximal ratio of two lengths of edges of a box; defined as the
  supremum of `nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.

We also provide a convenience constructor `BoxIntegral.Box.mk' (l u : ι → ℝ) : WithBot (Box ι)`
that returns the box `⟨l, u, _⟩` if it is nonempty and `⊥` otherwise.

## Tags

rectangular box
-/

@[expose] public section

open Set Function Metric Filter

noncomputable section

open scoped NNReal Topology

namespace BoxIntegral

variable {ι : Type*}

/-!
### Rectangular box: definition and partial order
-/


/-- A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Represents the product
of half-open intervals `(lower i, upper i]`. -/
/-
**BoxIntegral.Box** 是 Mathlib 中的一个归纳类型，位于命名空间 `BoxIntegral`。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Repres
ents the product
of half-open intervals `(lower i, upper i]`.
-/
structure Box (ι : Type*) where
  /-- coordinates of the lower and upper corners of the box -/
  (lower upper : ι → ℝ)
  /-- Each lower coordinate is less than its upper coordinate: i.e., the box is non-empty -/
  lower_lt_upper : ∀ i, lower i < upper i

attribute [simp] Box.lower_lt_upper

namespace Box

variable (I J : Box ι) {x y : ι → ℝ}

/-
**BoxIntegral.Box.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Box ι) :=
  ⟨⟨0, 1, fun _ ↦ zero_lt_one⟩⟩
/-
**BoxIntegral.Box.lower_le_upper** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：lower_le_upper : I.lower <= I.upper
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
-/
theorem lower_le_upper : I.lower ≤ I.upper :=
  fun i ↦ (I.lower_lt_upper i).le
/-
**BoxIntegral.Box.lower_ne_upper** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：lower_ne_upper (i) : I.lower i != I.upper i
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
-/
theorem lower_ne_upper (i) : I.lower i ≠ I.upper i :=
  (I.lower_lt_upper i).ne
/-
**BoxIntegral.Box.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (ι → ℝ) (Box ι) :=
  ⟨fun I x ↦ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)⟩

/-- The set of points in this box: this is the product of half-open intervals `(lower i, upper i]`,
where `lower` and `upper` are this box' corners. -/
@[coe]
/-
**BoxIntegral.Box.toSet** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：toSet (I : Box ι) : Set (ι -> Real)
参数：I : Box ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of points in this box: this is the product of half-open intervals `(lowe
r i, upper i]`,
where `lower` and `upper` are this box' corners.
-/
def toSet (I : Box ι) : Set (ι → ℝ) := { x | x ∈ I }
/-
**BoxIntegral.Box.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC (Box ι) (Set <| ι → ℝ) :=
  ⟨toSet⟩

@[simp]
/-
**BoxIntegral.Box.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：mem_mk {l u x : ι -> Real} {H} : x in mk l u H ↔ forall i, x i in Ioc (l i
) (u i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {l u x : ι → ℝ} {H} : x ∈ mk l u H ↔ ∀ i, x i ∈ Ioc (l i) (u i) := Iff.rfl

@[simp, norm_cast]
/-
**BoxIntegral.Box.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：mem_coe : x in (I : Set (ι -> Real)) ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe : x ∈ (I : Set (ι → ℝ)) ↔ x ∈ I := Iff.rfl
/-
**BoxIntegral.Box.mem_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：mem_def : x in I ↔ forall i, x i in Ioc (I.lower i) (I.upper i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_def : x ∈ I ↔ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i) := Iff.rfl
/-
**BoxIntegral.Box.mem_univ_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：mem_univ_Ioc {I : Box ι} : (x in pi univ fun i => Ioc (I.lower i) (I.upper
 i)) ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
-/
theorem mem_univ_Ioc {I : Box ι} : (x ∈ pi univ fun i ↦ Ioc (I.lower i) (I.upper i)) ↔ x ∈ I :=
  mem_univ_pi
/-
**BoxIntegral.Box.coe_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_eq_pi : (I : Set (ι -> Real)) = pi univ fun i => Ioc (I.lower i) (I.up
per i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `BoxIntegral.Box.mem_univ_Ioc`：mem_univ_Ioc {I : Box ι} : (x in pi univ f
un i => Ioc (I.lower i) (I.upper i)) ↔ x in I
-/
theorem coe_eq_pi : (I : Set (ι → ℝ)) = pi univ fun i ↦ Ioc (I.lower i) (I.upper i) :=
  Set.ext fun _ ↦ mem_univ_Ioc.symm

@[simp]
/-
**BoxIntegral.Box.upper_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：upper_mem : I.upper in I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
-/
theorem upper_mem : I.upper ∈ I :=
  fun i ↦ right_mem_Ioc.2 <| I.lower_lt_upper i
/-
**BoxIntegral.Box.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：exists_mem : exists x, x in I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.upper_mem`：upper_mem : I.upper in I
-/
theorem exists_mem : ∃ x, x ∈ I :=
  ⟨_, I.upper_mem⟩
/-
**BoxIntegral.Box.nonempty_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：nonempty_coe : Set.Nonempty (I : Set (ι -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.exists_mem`：exists_mem : exists x, x in I
-/
theorem nonempty_coe : Set.Nonempty (I : Set (ι → ℝ)) :=
  I.exists_mem

@[simp]
/-
**BoxIntegral.Box.coe_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_ne_empty : (I : Set (ι -> Real)) != ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `BoxIntegral.Box.nonempty_coe`：nonempty_coe : Set.Nonempty (I : Set (ι ->
 Real))
-/
theorem coe_ne_empty : (I : Set (ι → ℝ)) ≠ ∅ :=
  I.nonempty_coe.ne_empty

@[simp]
/-
**BoxIntegral.Box.empty_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：empty_ne_coe : ∅ != (I : Set (ι -> Real))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `BoxIntegral.Box.coe_ne_empty`：coe_ne_empty : (I : Set (ι -> Real)) != ∅
-/
theorem empty_ne_coe : ∅ ≠ (I : Set (ι → ℝ)) :=
  I.coe_ne_empty.symm
/-
**BoxIntegral.Box.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (Box ι) :=
  ⟨fun I J ↦ ∀ ⦃x⦄, x ∈ I → x ∈ J⟩
/-
**BoxIntegral.Box.le_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：le_def : I <= J ↔ forall x in I, x in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : I ≤ J ↔ ∀ x ∈ I, x ∈ J := Iff.rfl
/-
**BoxIntegral.Box.le_TFAE** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：le_TFAE : List.TFAE [I <= J, (I : Set (ι -> Real)) subseteq J, Icc I.lower
 I.upper subseteq Icc J.lower J.upper, J.lower <= I.lower ∧ I.upper <= J.upper]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `closure_pi_set`：closure_pi_set {ι : Type*} {α : ι -> Type*} [forall i, T
opologicalSpace (α i)] (I : Set ι) (s : forall i, Set (α i)) : closure (pi I s) 
= pi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `closure_Ioc`：closure_Ioc {a b : α} (hab : a != b) : closure (Ioc a b) = 
Icc a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.Icc_subset_Icc_iff`：Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ s
ubseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem le_TFAE : List.TFAE [I ≤ J, (I : Set (ι → ℝ)) ⊆ J,
    Icc I.lower I.upper ⊆ Icc J.lower J.upper, J.lower ≤ I.lower ∧ I.upper ≤ J.upper] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 → 3
  | h => by simpa [coe_eq_pi, closure_pi_set, lower_ne_upper] using closure_mono h
  tfae_have 3 ↔ 4 := Icc_subset_Icc_iff I.lower_le_upper
  tfae_have 4 → 2
  | h, x, hx, i => Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)
  tfae_finish

variable {I J}

@[simp, norm_cast]
/-
**BoxIntegral.Box.coe_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_subset_coe : (I : Set (ι -> Real)) subseteq J ↔ I <= J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_subset_coe : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J := Iff.rfl
/-
**BoxIntegral.Box.le_iff_bounds** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：le_iff_bounds : I <= J ↔ J.lower <= I.lower ∧ I.upper <= J.upper
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `BoxIntegral.Box.le_TFAE`：le_TFAE : List.TFAE [I <= J, (I : Set (ι -> Rea
l)) subseteq J, Icc I.lower I.upper subseteq Icc J.lower J.upper, J.lower <= I.l
ower ∧ I.uppe…
-/
theorem le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper :=
  (le_TFAE I J).out 0 3
/-
**BoxIntegral.Box.injective_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：injective_coe : Injective ((↑) : Box ι -> Set (ι -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem injective_coe : Injective ((↑) : Box ι → Set (ι → ℝ)) := by
  rintro ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h
  simp only [Subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h
  congr
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]

@[simp, norm_cast]
/-
**BoxIntegral.Box.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_inj : (I : Set (ι -> Real)) = J ↔ I = J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `BoxIntegral.Box.injective_coe`：injective_coe : Injective ((↑) : Box ι ->
 Set (ι -> Real))
-/
theorem coe_inj : (I : Set (ι → ℝ)) = J ↔ I = J :=
  injective_coe.eq_iff

@[ext]
/-
**BoxIntegral.Box.ext** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：ext (H : forall x, x in I ↔ x in J) : I = J
参数：H : forall x, x in I ↔ x in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.injective_coe`：injective_coe : Injective ((↑) : Box ι ->
 Set (ι -> Real))
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem ext (H : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  injective_coe <| Set.ext H
/-
**BoxIntegral.Box.ne_of_disjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`
。
形式化陈述：ne_of_disjoint_coe (h : Disjoint (I : Set (ι -> Real)) J) : I != J
参数：h : Disjoint (I : Set (ι -> Real)) J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Box.coe_inj`：coe_inj : (I : Set (ι -> Real)) = J ↔ I = J
· 使用定理 `Disjoint.ne`：Disjoint.ne (ha : a != ⊥) (hab : Disjoint a b) : a != b
· 使用定理 `BoxIntegral.Box.coe_ne_empty`：coe_ne_empty : (I : Set (ι -> Real)) != ∅
-/
theorem ne_of_disjoint_coe (h : Disjoint (I : Set (ι → ℝ)) J) : I ≠ J :=
  mt coe_inj.2 <| h.ne I.coe_ne_empty
/-
**BoxIntegral.Box.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Box ι) :=
  { PartialOrder.lift ((↑) : Box ι → Set (ι → ℝ)) injective_coe with le := (· ≤ ·) }

/-- Closed box corresponding to `I : BoxIntegral.Box ι`. -/
/-
**BoxIntegral.Box.Icc** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：{ι : Type u_1} → BoxIntegral.Box ι ↪o Set (ι → ℝ)
参数：ι → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Closed box corresponding to `I : BoxIntegral.Box ι`.
-/
protected def Icc : Box ι ↪o Set (ι → ℝ) :=
  OrderEmbedding.ofMapLEIff (fun I : Box ι ↦ Icc I.lower I.upper) fun I J ↦ (le_TFAE I J).out 2 0
/-
**BoxIntegral.Box.Icc_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：Icc_def : Box.Icc I = Icc I.lower I.upper
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_def : Box.Icc I = Icc I.lower I.upper := rfl

@[simp]
/-
**BoxIntegral.Box.upper_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：upper_mem_Icc (I : Box ι) : I.upper in Box.Icc I
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
-/
theorem upper_mem_Icc (I : Box ι) : I.upper ∈ Box.Icc I :=
  right_mem_Icc.2 I.lower_le_upper

@[simp]
/-
**BoxIntegral.Box.lower_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：lower_mem_Icc (I : Box ι) : I.lower in Box.Icc I
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
-/
theorem lower_mem_Icc (I : Box ι) : I.lower ∈ Box.Icc I :=
  left_mem_Icc.2 I.lower_le_upper
/-
**BoxIntegral.Box.isCompact_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：∀ {ι : Type u_1} (I : BoxIntegral.Box ι), IsCompact (BoxIntegral.Box.Icc I
)
参数：I : BoxIntegral.Box ι；BoxIntegral.Box.Icc I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
protected theorem isCompact_Icc (I : Box ι) : IsCompact (Box.Icc I) :=
  isCompact_Icc
/-
**BoxIntegral.Box.Icc_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：Icc_eq_pi : Box.Icc I = pi univ fun i => Icc (I.lower i) (I.upper i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
-/
theorem Icc_eq_pi : Box.Icc I = pi univ fun i ↦ Icc (I.lower i) (I.upper i) :=
  (pi_univ_Icc _ _).symm
/-
**BoxIntegral.Box.le_iff_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：le_iff_Icc : I <= J ↔ Box.Icc I subseteq Box.Icc J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `BoxIntegral.Box.le_TFAE`：le_TFAE : List.TFAE [I <= J, (I : Set (ι -> Rea
l)) subseteq J, Icc I.lower I.upper subseteq Icc J.lower J.upper, J.lower <= I.l
ower ∧ I.uppe…
-/
theorem le_iff_Icc : I ≤ J ↔ Box.Icc I ⊆ Box.Icc J :=
  (le_TFAE I J).out 0 2
/-
**BoxIntegral.Box.antitone_lower** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：antitone_lower : Antitone fun I : Box ι => I.lower
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Box.le_iff_bounds`：le_iff_bounds : I <= J ↔ J.lower <= I.low
er ∧ I.upper <= J.upper
-/
theorem antitone_lower : Antitone fun I : Box ι ↦ I.lower :=
  fun _ _ H ↦ (le_iff_bounds.1 H).1
/-
**BoxIntegral.Box.monotone_upper** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：monotone_upper : Monotone fun I : Box ι => I.upper
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Box.le_iff_bounds`：le_iff_bounds : I <= J ↔ J.lower <= I.low
er ∧ I.upper <= J.upper
-/
theorem monotone_upper : Monotone fun I : Box ι ↦ I.upper :=
  fun _ _ H ↦ (le_iff_bounds.1 H).2
/-
**BoxIntegral.Box.coe_subset_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_subset_Icc : ↑I subseteq Box.Icc I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem coe_subset_Icc : ↑I ⊆ Box.Icc I :=
  fun _ hx ↦ ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
/-
**BoxIntegral.Box.isBounded_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：isBounded_Icc [Finite ι] (I : Box ι) : Bornology.IsBounded (Box.Icc I)
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Metric.isBounded_Icc`：isBounded_Icc (a b : α) : IsBounded (Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem isBounded_Icc [Finite ι] (I : Box ι) : Bornology.IsBounded (Box.Icc I) := by
  cases nonempty_fintype ι
  exact Metric.isBounded_Icc _ _
/-
**BoxIntegral.Box.isBounded** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：isBounded [Finite ι] (I : Box ι) : Bornology.IsBounded I.toSet
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `BoxIntegral.Box.isBounded_Icc`：isBounded_Icc [Finite ι] (I : Box ι) : Bo
rnology.IsBounded (Box.Icc I)
· 使用定理 `BoxIntegral.Box.coe_subset_Icc`：coe_subset_Icc : ↑I subseteq Box.Icc I
-/
theorem isBounded [Finite ι] (I : Box ι) : Bornology.IsBounded I.toSet :=
  Bornology.IsBounded.subset I.isBounded_Icc coe_subset_Icc

/-!
### Supremum of two boxes
-/


/-- `I ⊔ J` is the least box that includes both `I` and `J`. Since `↑I ∪ ↑J` is usually not a box,
`↑(I ⊔ J)` is larger than `↑I ∪ ↑J`. -/
/-
**BoxIntegral.Box.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I ⊔ J` is the least box that includes both `I` and `J`. Since `↑I ∪ ↑J` is usua
lly not a box,
`↑(I ⊔ J)` is larger than `↑I ∪ ↑J`.
-/
instance : SemilatticeSup (Box ι) :=
  { sup := fun I J ↦ ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
    fun i ↦ (min_le_left _ _).trans_lt <| (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩
    le_sup_left := fun _ _ ↦ le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩
    le_sup_right := fun _ _ ↦ le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩
    sup_le := fun _ _ _ h₁ h₂ ↦ le_iff_bounds.2
      ⟨le_inf (antitone_lower h₁) (antitone_lower h₂),
        sup_le (monotone_upper h₁) (monotone_upper h₂)⟩ }

/-!
### `WithBot (Box ι)`

In this section we define coercion from `WithBot (Box ι)` to `Set (ι → ℝ)` by sending `⊥` to `∅`.
-/

/-- The set underlying this box: `⊥` is mapped to `∅`. -/
@[coe]
/-
**BoxIntegral.Box.withBotToSet** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：withBotToSet (o : WithBot (Box ι)) : Set (ι -> Real)
参数：o : WithBot (Box ι)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set underlying this box: `⊥` is mapped to `∅`.
-/
def withBotToSet (o : WithBot (Box ι)) : Set (ι → ℝ) := o.elim ∅ (↑)
/-
**BoxIntegral.Box.withBotCoe** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
形式化陈述：withBotCoe : CoeTC (WithBot (Box ι)) (Set (ι -> Real))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance withBotCoe : CoeTC (WithBot (Box ι)) (Set (ι → ℝ)) :=
  ⟨withBotToSet⟩

@[simp, norm_cast]
/-
**BoxIntegral.Box.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_bot : ((⊥ : WithBot (Box ι)) : Set (ι -> Real)) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : WithBot (Box ι)) : Set (ι → ℝ)) = ∅ := rfl

@[simp, norm_cast]
/-
**BoxIntegral.Box.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_coe : ((I : WithBot (Box ι)) : Set (ι -> Real)) = I
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe : ((I : WithBot (Box ι)) : Set (ι → ℝ)) = I := rfl
/-
**BoxIntegral.Box.isSome_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：∀ {ι : Type u_1} {I : WithBot (BoxIntegral.Box ι)}, Option.isSome I = true
 ↔ (↑I).Nonempty
参数：BoxIntegral.Box ι；↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `BoxIntegral.Box.nonempty_coe`：nonempty_coe : Set.Nonempty (I : Set (ι ->
 Real))
-/
theorem isSome_iff : ∀ {I : WithBot (Box ι)}, I.isSome ↔ (I : Set (ι → ℝ)).Nonempty
  | ⊥ => by
    unfold Option.isSome
    simp
  | (I : Box ι) => by
    unfold Option.isSome
    simp [I.nonempty_coe]
/-
**BoxIntegral.Box.biUnion_coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`
。
形式化陈述：biUnion_coe_eq_coe (I : WithBot (Box ι)) : ⋃ (J : Box ι) (_ : ↑J = I), (J 
: Set (ι -> Real)) = I
参数：I : WithBot (Box ι)。
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
-/
theorem biUnion_coe_eq_coe (I : WithBot (Box ι)) :
    ⋃ (J : Box ι) (_ : ↑J = I), (J : Set (ι → ℝ)) = I := by
  induction I <;> simp

@[simp, norm_cast]
/-
**BoxIntegral.Box.withBotCoe_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.B
ox`。
形式化陈述：withBotCoe_subset_iff {I J : WithBot (Box ι)} : (I : Set (ι -> Real)) subs
eteq J ↔ I <= J
参数：Box ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem withBotCoe_subset_iff {I J : WithBot (Box ι)} : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J := by
  induction I; · simp
  induction J; · simp [subset_empty_iff]
  simp [le_def]

@[simp, norm_cast]
/-
**BoxIntegral.Box.withBotCoe_inj** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：withBotCoe_inj {I J : WithBot (Box ι)} : (I : Set (ι -> Real)) = J ↔ I = J
参数：Box ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem withBotCoe_inj {I J : WithBot (Box ι)} : (I : Set (ι → ℝ)) = J ↔ I = J := by
  simp only [Subset.antisymm_iff, ← le_antisymm_iff, withBotCoe_subset_iff]

open scoped Classical in
/-- Make a `WithBot (Box ι)` from a pair of corners `l u : ι → ℝ`. If `l i < u i` for all `i`,
then the result is `⟨l, u, _⟩ : Box ι`, otherwise it is `⊥`. In any case, the result interpreted
as a set in `ι → ℝ` is the set `{x : ι → ℝ | ∀ i, x i ∈ Ioc (l i) (u i)}`. -/
/-
**BoxIntegral.Box.mk'** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：mk' (l u : ι -> Real) : WithBot (Box ι)
参数：l u : ι -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a `WithBot (Box ι)` from a pair of corners `l u : ι → ℝ`. If `l i < u i` fo
r all `i`,
then the result is `⟨l, u, _⟩ : Box ι`, otherwise it is `⊥`. In any case, the re
sult interpreted
as a set in `ι → ℝ` is the set `{x : ι → ℝ | ∀ i, x i ∈ Ioc (l i) (u i)}`.
-/
def mk' (l u : ι → ℝ) : WithBot (Box ι) :=
  if h : ∀ i, l i < u i then ↑(⟨l, u, h⟩ : Box ι) else ⊥

@[simp]
/-
**BoxIntegral.Box.mk'_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：∀ {ι : Type u_1} {l u : ι → ℝ}, BoxIntegral.Box.mk' l u = ⊥ ↔ ∃ i, u i ≤ l
 i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.mk'.eq_1`：∀ {ι : Type u_1} (l u : ι → ℝ),   BoxIntegral.
Box.mk' l u = if h : ∀ (i : ι), l i < u i then ↑{ lower := l, upper := u, lower_
lt_upper := h …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mk'_eq_bot {l u : ι → ℝ} : mk' l u = ⊥ ↔ ∃ i, u i ≤ l i := by
  rw [mk']
  split_ifs with h <;> simpa using h

@[simp]
/-
**BoxIntegral.Box.mk'_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} {l u : ι → ℝ}, BoxIntegral.Box.mk
' l u = ↑I ↔ l = I.lower ∧ u = I.upper
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.mk'.eq_1`：∀ {ι : Type u_1} (l u : ι → ℝ),   BoxIntegral.
Box.mk' l u = if h : ∀ (i : ι), l i < u i then ↑{ lower := l, upper := u, lower_
lt_upper := h …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Box.mk.injEq`：∀ {ι : Type u_2} (lower upper : ι → ℝ) (lower_
lt_upper : ∀ (i : ι), lower i < upper i) (lower_1 upper_1 : ι → ℝ)   (lower_lt_u
pper_1 : ∀ (i …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
-/
theorem mk'_eq_coe {l u : ι → ℝ} : mk' l u = I ↔ l = I.lower ∧ u = I.upper := by
  obtain ⟨lI, uI, hI⟩ := I; rw [mk']; split_ifs with h
  · simp
  · suffices l = lI → u ≠ uI by simpa
    rintro rfl rfl
    exact h hI

@[simp]
/-
**BoxIntegral.Box.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_mk' (l u : ι -> Real) : (mk' l u : Set (ι -> Real)) = pi univ fun i =>
 Ioc (l i) (u i)
参数：l u : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.mk'.eq_1`：∀ {ι : Type u_1} (l u : ι → ℝ),   BoxIntegral.
Box.mk' l u = if h : ∀ (i : ι), l i < u i then ↑{ lower := l, upper := u, lower_
lt_upper := h …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `BoxIntegral.Box.coe_bot`：coe_bot : ((⊥ : WithBot (Box ι)) : Set (ι -> Re
al)) = ∅
· 使用定理 `Set.univ_pi_eq_empty`：univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
-/
theorem coe_mk' (l u : ι → ℝ) : (mk' l u : Set (ι → ℝ)) = pi univ fun i ↦ Ioc (l i) (u i) := by
  rw [mk']; split_ifs with h
  · exact coe_eq_pi _
  · rcases not_forall.mp h with ⟨i, hi⟩
    rw [coe_bot, univ_pi_eq_empty]
    exact Ioc_eq_empty hi
/-
**BoxIntegral.Box.WithBot.inf** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box.WithBot
`。
形式化陈述：{ι : Type u_1} → Min (WithBot (BoxIntegral.Box ι))
参数：WithBot (BoxIntegral.Box ι)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WithBot.inf : Min (WithBot (Box ι)) :=
  ⟨fun I ↦
    WithBot.recBotCoe (fun _ ↦ ⊥)
      (fun I J ↦ WithBot.recBotCoe ⊥ (fun J ↦ mk' (I.lower ⊔ J.lower) (I.upper ⊓ J.upper)) J) I⟩

@[simp]
/-
**BoxIntegral.Box.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : Set (ι -> Real)) = (I : Set 
_) inter J
参数：I J : WithBot (Box ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoxIntegral.Box.coe_mk'`：coe_mk' (l u : ι -> Real) : (mk' l u : Set (ι -
> Real)) = pi univ fun i => Ioc (l i) (u i)
· 使用定理 `BoxIntegral.Box.coe_eq_pi`：coe_eq_pi : (I : Set (ι -> Real)) = pi univ f
un i => Ioc (I.lower i) (I.upper i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Ioc_inter_Ioc`：∀ {α : Type u_1} [inst : LinearOrder α] {a₁ a₂ b₁ b₂ 
: α},   Set.Ioc b₁ a₁ ∩ Set.Ioc b₂ a₂ = Set.Ioc (max b₁ b₂) (min a₁ a₂)
-/
theorem coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : Set (ι → ℝ)) = (I : Set _) ∩ J := by
  induction I
  · change ∅ = _
    simp
  induction J
  · change ∅ = _
    simp
  change ((mk' _ _ : WithBot (Box ι)) : Set (ι → ℝ)) = _
  simp only [coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, Pi.sup_apply, Pi.inf_apply, coe_mk',
    coe_coe]
/-
**BoxIntegral.Box.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Box`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (WithBot (Box ι)) :=
  { inf := min
    inf_le_left := fun I J ↦ by
      rw [← withBotCoe_subset_iff, coe_inf]
      exact inter_subset_left
    inf_le_right := fun I J ↦ by
      rw [← withBotCoe_subset_iff, coe_inf]
      exact inter_subset_right
    le_inf := fun I J₁ J₂ h₁ h₂ ↦ by
      simp only [← withBotCoe_subset_iff, coe_inf] at *
      exact subset_inter h₁ h₂ }

@[simp, norm_cast]
/-
**BoxIntegral.Box.disjoint_withBotCoe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box
`。
形式化陈述：disjoint_withBotCoe {I J : WithBot (Box ι)} : Disjoint (I : Set (ι -> Real
)) J ↔ Disjoint I J
参数：Box ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Box.coe_inf`：coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : S
et (ι -> Real)) = (I : Set _) inter J
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_withBotCoe {I J : WithBot (Box ι)} :
    Disjoint (I : Set (ι → ℝ)) J ↔ Disjoint I J := by
  simp only [disjoint_iff_inf_le, ← withBotCoe_subset_iff, coe_inf]
  rfl
/-
**BoxIntegral.Box.disjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：disjoint_coe : Disjoint (I : WithBot (Box ι)) J ↔ Disjoint (I : Set (ι -> 
Real)) J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `BoxIntegral.Box.disjoint_withBotCoe`：disjoint_withBotCoe {I J : WithBot 
(Box ι)} : Disjoint (I : Set (ι -> Real)) J ↔ Disjoint I J
-/
theorem disjoint_coe : Disjoint (I : WithBot (Box ι)) J ↔ Disjoint (I : Set (ι → ℝ)) J :=
  disjoint_withBotCoe.symm
/-
**BoxIntegral.Box.not_disjoint_coe_iff_nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 
`BoxIntegral.Box`。
形式化陈述：not_disjoint_coe_iff_nonempty_inter : ¬Disjoint (I : WithBot (Box ι)) J ↔ 
(I inter J : Set (ι -> Real)).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.disjoint_coe`：disjoint_coe : Disjoint (I : WithBot (Box 
ι)) J ↔ Disjoint (I : Set (ι -> Real)) J
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_disjoint_coe_iff_nonempty_inter :
    ¬Disjoint (I : WithBot (Box ι)) J ↔ (I ∩ J : Set (ι → ℝ)).Nonempty := by
  rw [disjoint_coe, Set.not_disjoint_iff_nonempty_inter]

/-!
### Hyperface of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`
-/


/-- Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at
`I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`. -/
@[simps +simpRhs]
/-
**BoxIntegral.Box.face** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：face {n} (I : Box (Fin (n + 1))) (i : Fin (n + 1)) : Box (Fin n)
参数：I : Box (Fin (n + 1))；i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corn
ers at
`I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
-/
def face {n} (I : Box (Fin (n + 1))) (i : Fin (n + 1)) : Box (Fin n) :=
  ⟨I.lower ∘ Fin.succAbove i, I.upper ∘ Fin.succAbove i, fun _ ↦ I.lower_lt_upper _⟩

@[simp]
/-
**BoxIntegral.Box.face_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：face_mk {n} (l u : Fin (n + 1) -> Real) (h : forall i, l i < u i) (i : Fin
 (n + 1)) : face ⟨l, u, h⟩ i = ⟨l ∘ Fin.succAbove i, u ∘ Fin.succAbove i, fun _ 
=> h _⟩
参数：l u : Fin (n + 1) -> Real；h : forall i, l i < u i；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem face_mk {n} (l u : Fin (n + 1) → ℝ) (h : ∀ i, l i < u i) (i : Fin (n + 1)) :
    face ⟨l, u, h⟩ i = ⟨l ∘ Fin.succAbove i, u ∘ Fin.succAbove i, fun _ ↦ h _⟩ := rfl

@[gcongr, mono]
/-
**BoxIntegral.Box.face_mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：face_mono {n} {I J : Box (Fin (n + 1))} (h : I <= J) (i : Fin (n + 1)) : f
ace I i <= face J i
参数：Fin (n + 1)；h : I <= J；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Box.le_iff_bounds`：le_iff_bounds : I <= J ↔ J.lower <= I.low
er ∧ I.upper <= J.upper
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem face_mono {n} {I J : Box (Fin (n + 1))} (h : I ≤ J) (i : Fin (n + 1)) :
    face I i ≤ face J i :=
  fun _ hx _ ↦ Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)
/-
**BoxIntegral.Box.monotone_face** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：monotone_face {n} (i : Fin (n + 1)) : Monotone fun I => face I i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Box.face_mono`：face_mono {n} {I J : Box (Fin (n + 1))} (h : 
I <= J) (i : Fin (n + 1)) : face I i <= face J i
-/
theorem monotone_face {n} (i : Fin (n + 1)) : Monotone fun I ↦ face I i :=
  fun _ _ h ↦ face_mono h i
/-
**BoxIntegral.Box.mapsTo_insertNth_face_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Box`。
形式化陈述：mapsTo_insertNth_face_Icc {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x
 : Real} (hx : x in Icc (I.lower i) (I.upper i)) : MapsTo (i.insertNth x) (Box.I
cc (I.face i)) (Box.Icc I)
参数：I : Box (Fin (n + 1))；n + 1；hx : x in Icc (I.lower i) (I.upper i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Fin.insertNth_mem_Icc`：insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p 
: forall j, α (i.succAbove j)} {q₁ q₂ : forall j, α j} : i.insertNth x p in Icc 
q₁ q₂ ↔ x i…
-/
theorem mapsTo_insertNth_face_Icc {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Icc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (Box.Icc (I.face i)) (Box.Icc I) :=
  fun _ hy ↦ Fin.insertNth_mem_Icc.2 ⟨hx, hy⟩
/-
**BoxIntegral.Box.mapsTo_insertNth_face** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.B
ox`。
形式化陈述：mapsTo_insertNth_face {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : R
eal} (hx : x in Ioc (I.lower i) (I.upper i)) : MapsTo (i.insertNth x) (I.face i 
: Set (_ -> _)) (I : Set (_ -> _))
参数：I : Box (Fin (n + 1))；n + 1；hx : x in Ioc (I.lower i) (I.upper i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
-/
theorem mapsTo_insertNth_face {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Ioc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (I.face i : Set (_ → _)) (I : Set (_ → _)) := by
  intro y hy
  simp_rw [mem_coe, mem_def, i.forall_iff_succAbove, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact ⟨hx, hy⟩
/-
**BoxIntegral.Box.continuousOn_face_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.B
ox`。
形式化陈述：continuousOn_face_Icc {X} [TopologicalSpace X] {n} {f : (Fin (n + 1) -> Re
al) -> X} {I : Box (Fin (n + 1))} (h : ContinuousOn f (Box.Icc I)) {i : Fin (n +
 1)} {x : Real} (hx : x in Icc (I.lower i) (I.upper i)) : ContinuousOn (f ∘ i.in
sertNth x) (Box.Icc (I.face i))
参数：Fin (n + 1) -> Real；Fin (n + 1)；h : ContinuousOn f (Box.Icc I)；n + 1；hx : x i
n Icc (I.lower i) (I.upper i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `ContinuousOn.finInsertNth`：ContinuousOn.finInsertNth (i : Fin (n + 1)) {
f : α -> X i} {g : α -> forall j : Fin n, X (i.succAbove j)} {s : Set α} (hf : C
ontinuousOn f s…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `BoxIntegral.Box.mapsTo_insertNth_face_Icc`：mapsTo_insertNth_face_Icc {n}
 (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : Real} (hx : x in Icc (I.lower i)
 (I.upper i)) : MapsTo (i.inser…
-/
theorem continuousOn_face_Icc {X} [TopologicalSpace X] {n} {f : (Fin (n + 1) → ℝ) → X}
    {I : Box (Fin (n + 1))} (h : ContinuousOn f (Box.Icc I)) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Icc (I.lower i) (I.upper i)) :
    ContinuousOn (f ∘ i.insertNth x) (Box.Icc (I.face i)) :=
  h.comp (continuousOn_const.finInsertNth i continuousOn_id) (I.mapsTo_insertNth_face_Icc hx)

/-!
### Covering of the interior of a box by a monotone sequence of smaller boxes
-/


/-- The interior of a box. -/
/-
**BoxIntegral.Box.Ioo** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：{ι : Type u_1} → BoxIntegral.Box ι →o Set (ι → ℝ)
参数：ι → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interior of a box.
-/
protected def Ioo : Box ι →o Set (ι → ℝ) where
  toFun I := pi univ fun i ↦ Ioo (I.lower i) (I.upper i)
  monotone' _ _ h :=
    pi_mono fun i _ ↦ Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i) ((le_iff_bounds.1 h).2 i)
/-
**BoxIntegral.Box.Ioo_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：Ioo_subset_coe (I : Box ι) : Box.Ioo I subseteq I
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `trivial`：True
-/
theorem Ioo_subset_coe (I : Box ι) : Box.Ioo I ⊆ I :=
  fun _ hx i ↦ Ioo_subset_Ioc_self (hx i trivial)
/-
**BoxIntegral.Box.Ioo_subset_Icc** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：∀ {ι : Type u_1} (I : BoxIntegral.Box ι), BoxIntegral.Box.Ioo I ⊆ BoxInteg
ral.Box.Icc I
参数：I : BoxIntegral.Box ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoxIntegral.Box.Ioo_subset_coe`：Ioo_subset_coe (I : Box ι) : Box.Ioo I s
ubseteq I
· 使用定理 `BoxIntegral.Box.coe_subset_Icc`：coe_subset_Icc : ↑I subseteq Box.Icc I
-/
protected theorem Ioo_subset_Icc (I : Box ι) : Box.Ioo I ⊆ Box.Icc I :=
  I.Ioo_subset_coe.trans coe_subset_Icc
/-
**BoxIntegral.Box.iUnion_Ioo_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.B
ox`。
形式化陈述：iUnion_Ioo_of_tendsto [Finite ι] {I : Box ι} {J : Nat -> Box ι} (hJ : Mono
tone J) (hl : Tendsto (lower ∘ J) atTop (𝓝 I.lower)) (hu : Tendsto (upper ∘ J) a
tTop (𝓝 I.upper)) : ⋃ n, Box.Ioo (J n) = Box.Ioo I
参数：hJ : Monotone J；hl : Tendsto (lower ∘ J) atTop (𝓝 I.lower)；hu : Tendsto (uppe
r ∘ J) atTop (𝓝 I.upper)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用定理 `Function.monotone_eval`：Function.monotone_eval {ι : Type u} {α : ι -> Ty
pe v} [forall i, Preorder (α i)] (i : ι) : Monotone (Function.eval i : (forall i
, α i) -> α …
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `BoxIntegral.Box.antitone_lower`：antitone_lower : Antitone fun I : Box ι 
=> I.lower
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `BoxIntegral.Box.monotone_upper`：monotone_upper : Monotone fun I : Box ι 
=> I.upper
· 使用定理 `Set.iUnion_univ_pi_of_monotone`：iUnion_univ_pi_of_monotone {ι ι' : Type*
} [LinearOrder ι'] [Nonempty ι'] [Finite ι] {α : ι -> Type*} {s : forall i, ι' -
> Set (α i)} (hs : f…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Antitone.Ioo`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f g : α → β},   Antitone f → Monotone g → Monotone fun x => Set
.I…
· 使用定理 `Set.pi_congr`：pi_congr (h : s₁ = s₂) (h' : forall i in s₁, t₁ i = t₂ i) 
: s₁.pi t₁ = s₂.pi t₂
· 使用定理 `iUnion_Ioo_of_mono_of_isGLB_of_isLUB`：iUnion_Ioo_of_mono_of_isGLB_of_isL
UB (hf : Antitone f) (hg : Monotone g) (ha : IsGLB (range f) a) (hb : IsLUB (ran
ge g) b) : ⋃ x, Ioo (f x) …
· 使用定理 `isGLB_of_tendsto_atTop`：isGLB_of_tendsto_atTop [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {
f : β -> α} …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `isLUB_of_tendsto_atTop`：isLUB_of_tendsto_atTop [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] [Nonempty β] {
f : β -> α} …
-/
theorem iUnion_Ioo_of_tendsto [Finite ι] {I : Box ι} {J : ℕ → Box ι} (hJ : Monotone J)
    (hl : Tendsto (lower ∘ J) atTop (𝓝 I.lower)) (hu : Tendsto (upper ∘ J) atTop (𝓝 I.upper)) :
    ⋃ n, Box.Ioo (J n) = Box.Ioo I :=
  have hl' : ∀ i, Antitone fun n ↦ (J n).lower i :=
    fun i ↦ (monotone_eval i).comp_antitone (antitone_lower.comp_monotone hJ)
  have hu' : ∀ i, Monotone fun n ↦ (J n).upper i :=
    fun i ↦ (monotone_eval i).comp (monotone_upper.comp hJ)
  calc
    ⋃ n, Box.Ioo (J n) = pi univ fun i ↦ ⋃ n, Ioo ((J n).lower i) ((J n).upper i) :=
      iUnion_univ_pi_of_monotone fun i ↦ (hl' i).Ioo (hu' i)
    _ = Box.Ioo I :=
      pi_congr rfl fun i _ ↦
        iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hl' i) (hu' i)
          (isGLB_of_tendsto_atTop (hl' i) (tendsto_pi_nhds.1 hl _))
          (isLUB_of_tendsto_atTop (hu' i) (tendsto_pi_nhds.1 hu _))
/-
**BoxIntegral.Box.exists_seq_mono_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Box`。
形式化陈述：exists_seq_mono_tendsto (I : Box ι) : exists J : Nat ->o Box ι, (forall n,
 Box.Icc (J n) subseteq Box.Ioo I) ∧ Tendsto (lower ∘ J) atTop (𝓝 I.lower) ∧ Ten
dsto (upper ∘ J) atTop (𝓝 I.upper)
参数：I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Box.le_iff_bounds`：le_iff_bounds : I <= J ↔ J.lower <= I.low
er ∧ I.upper <= J.upper
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `exists_seq_strictAnti_strictMono_tendsto`：exists_seq_strictAnti_strictMo
no_tendsto [DenselyOrdered α] [FirstCountableTopology α] {x y : α} (h : x < y) :
 exists u v : Nat -> α, Strict…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
-/
theorem exists_seq_mono_tendsto (I : Box ι) :
    ∃ J : ℕ →o Box ι,
      (∀ n, Box.Icc (J n) ⊆ Box.Ioo I) ∧
        Tendsto (lower ∘ J) atTop (𝓝 I.lower) ∧ Tendsto (upper ∘ J) atTop (𝓝 I.upper) := by
  choose a b ha_anti hb_mono ha_mem hb_mem hab ha_tendsto hb_tendsto using
    fun i ↦ exists_seq_strictAnti_strictMono_tendsto (I.lower_lt_upper i)
  exact
    ⟨⟨fun k ↦ ⟨flip a k, flip b k, fun i ↦ hab _ _ _⟩, fun k l hkl ↦
        le_iff_bounds.2 ⟨fun i ↦ (ha_anti i).antitone hkl, fun i ↦ (hb_mono i).monotone hkl⟩⟩,
      fun n x hx i _ ↦ ⟨(ha_mem _ _).1.trans_le (hx.1 _), (hx.2 _).trans_lt (hb_mem _ _).2⟩,
      tendsto_pi_nhds.2 ha_tendsto, tendsto_pi_nhds.2 hb_tendsto⟩

section Distortion

variable [Fintype ι]

/-- The distortion of a box `I` is the maximum of the ratios of the lengths of its edges.
It is defined as the maximum of the ratios
`nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`. -/
/-
**BoxIntegral.Box.distortion** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：distortion (I : Box ι) : Real>=0
参数：I : Box ι。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distortion of a box `I` is the maximum of the ratios of the lengths of its e
dges.
It is defined as the maximum of the ratios
`nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.
-/
def distortion (I : Box ι) : ℝ≥0 :=
  Finset.univ.sup fun i : ι ↦ nndist I.lower I.upper / nndist (I.lower i) (I.upper i)
/-
**BoxIntegral.Box.distortion_eq_of_sub_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.Box`。
形式化陈述：distortion_eq_of_sub_eq_div {I J : Box ι} {r : Real} (h : forall i, I.uppe
r i - I.lower i = (J.upper i - J.lower i) / r) : distortion I = distortion J
参数：h : forall i, I.upper i - I.lower i = (J.upper i - J.lower i) / r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.nndist_eq'`：Real.nndist_eq' (x y : Real) : nndist x y = Real.nnabs 
(y - x)
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `div_nonpos_of_nonneg_of_nonpos`：div_nonpos_of_nonneg_of_nonpos (ha : 0 <
= a) (hb : b <= 0) : a / b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.finset_sup_div`：finset_sup_div {α} {f : α -> Real>=0} {s : Finset
 α} (r : Real>=0) : s.sup f / r = s.sup fun a => f a / r
（共 34 条，此处仅展示前 30 条）
-/
theorem distortion_eq_of_sub_eq_div {I J : Box ι} {r : ℝ}
    (h : ∀ i, I.upper i - I.lower i = (J.upper i - J.lower i) / r) :
    distortion I = distortion J := by
  simp only [distortion, nndist_pi_def, Real.nndist_eq', h, map_div₀]
  congr 1 with i
  have : 0 < r := by
    by_contra hr
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 <| J.lower_le_upper i) (not_lt.1 hr)
    rw [← h] at this
    exact this.not_gt (sub_pos.2 <| I.lower_lt_upper i)
  have hn0 := (map_ne_zero Real.nnabs).2 this.ne'
  simp_rw [NNReal.finset_sup_div, div_div_div_cancel_right₀ hn0]
/-
**BoxIntegral.Box.nndist_le_distortion_mul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Box`。
形式化陈述：nndist_le_distortion_mul (I : Box ι) (i : ι) : nndist I.lower I.upper <= I
.distortion * nndist (I.lower i) (I.upper i)
参数：I : Box ι；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nndist_eq_zero`：nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.distortion.eq_1`：∀ {ι : Type u_1} [inst : Fintype ι] (I 
: BoxIntegral.Box ι),   I.distortion = Finset.univ.sup fun i => nndist I.lower I
.upper / nndist (I.lo…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem nndist_le_distortion_mul (I : Box ι) (i : ι) :
    nndist I.lower I.upper ≤ I.distortion * nndist (I.lower i) (I.upper i) :=
  calc
    nndist I.lower I.upper =
        nndist I.lower I.upper / nndist (I.lower i) (I.upper i) * nndist (I.lower i) (I.upper i) :=
      (div_mul_cancel₀ _ <| mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
    _ ≤ I.distortion * nndist (I.lower i) (I.upper i) := by
      grw [distortion, ← Finset.le_sup (Finset.mem_univ i)]
/-
**BoxIntegral.Box.dist_le_distortion_mul** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Box`。
形式化陈述：dist_le_distortion_mul (I : Box ι) (i : ι) : dist I.lower I.upper <= I.dis
tortion * (I.upper i - I.lower i)
参数：I : Box ι；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `BoxIntegral.Box.nndist_le_distortion_mul`：nndist_le_distortion_mul (I : 
Box ι) (i : ι) : nndist I.lower I.upper <= I.distortion * nndist (I.lower i) (I.
upper i)
-/
theorem dist_le_distortion_mul (I : Box ι) (i : ι) :
    dist I.lower I.upper ≤ I.distortion * (I.upper i - I.lower i) := by
  have A : I.lower i - I.upper i < 0 := sub_neg.2 (I.lower_lt_upper i)
  simpa only [← NNReal.coe_le_coe, ← dist_nndist, NNReal.coe_mul, Real.dist_eq, abs_of_neg A,
    neg_sub] using I.nndist_le_distortion_mul i
/-
**BoxIntegral.Box.diam_Icc_le_of_distortion_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.Box`。
形式化陈述：diam_Icc_le_of_distortion_le (I : Box ι) (i : ι) {c : Real>=0} (h : I.dist
ortion <= c) : diam (Box.Icc I) <= c * (I.upper i - I.lower i)
参数：I : Box ι；i : ι；h : I.distortion <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `BoxIntegral.Box.lower_le_upper`：lower_le_upper : I.lower <= I.upper
· 使用定理 `Metric.diam_le_of_forall_dist_le`：diam_le_of_forall_dist_le {C : Real} (
h₀ : 0 <= C) (h : forall x in s, forall y in s, dist x y <= C) : diam s <= C
· 使用引理 `Real.dist_le_of_mem_pi_Icc`：dist_le_of_mem_pi_Icc (hx : x in Icc x' y') 
(hy : y in Icc x' y') : dist x y <= dist x' y'
· 使用定理 `BoxIntegral.Box.dist_le_distortion_mul`：dist_le_distortion_mul (I : Box 
ι) (i : ι) : dist I.lower I.upper <= I.distortion * (I.upper i - I.lower i)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
-/
theorem diam_Icc_le_of_distortion_le (I : Box ι) (i : ι) {c : ℝ≥0} (h : I.distortion ≤ c) :
    diam (Box.Icc I) ≤ c * (I.upper i - I.lower i) :=
  have : (0 : ℝ) ≤ c * (I.upper i - I.lower i) :=
    mul_nonneg c.coe_nonneg (sub_nonneg.2 <| I.lower_le_upper _)
  diam_le_of_forall_dist_le this fun x hx y hy ↦
    calc
      dist x y ≤ dist I.lower I.upper := Real.dist_le_of_mem_pi_Icc hx hy
      _ ≤ I.distortion * (I.upper i - I.lower i) := I.dist_le_distortion_mul i
      _ ≤ c * (I.upper i - I.lower i) := by gcongr; exact sub_nonneg.2 (I.lower_le_upper i)

end Distortion

end Box

end BoxIntegral

