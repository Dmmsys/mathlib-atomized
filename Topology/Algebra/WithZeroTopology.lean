/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Regular

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element.  Then
`Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{ γ | γ < γ₀ }` for some invertible element `γ₀` and
every invertible element is open.  In particular the topology is the following: "a subset `U ⊆ Γ₀`
is open if `0 ∉ U` or if there is an invertible `γ₀ ∈ Γ₀` such that `{ γ | γ < γ₀ } ⊆ U`", see
`WithZeroTopology.isOpen_iff`.

We prove this topology is ordered and T₅ (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is defined as a scoped instance since it may not be the desired topology on
a linearly ordered commutative group with zero. You can locally activate this topology using
`open WithZeroTopology`.
-/

public section

open Topology Filter TopologicalSpace Filter Set Function

namespace WithZeroTopology

variable {α Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {γ γ₁ γ₂ : Γ₀} {l : Filter α}
  {f : α → Γ₀}

/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset `U` is open if `0 ∉ U` or if there is an invertible element γ₀ such that
`{γ | γ < γ₀} ⊆ U`. -/
/-
**WithZeroTopology.** 是 Mathlib 中的一个实例，位于命名空间 `WithZeroTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on a linearly ordered commutative group with a zero element adjoine
d.
A subset `U` is open if `0 ∉ U` or if there is an invertible element γ₀ such tha
t
`{γ | γ < γ₀} ⊆ U`.
-/
scoped instance (priority := 100) topologicalSpace : TopologicalSpace Γ₀ :=
  nhdsAdjoint 0 <| ⨅ γ ≠ 0, 𝓟 (Iio γ)
/-
**WithZeroTopology.nhds_eq_update** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：nhds_eq_update : (𝓝 : Γ₀ -> Filter Γ₀) = update pure 0 (⨅ γ != 0, 𝓟 (Iio γ
))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_nhdsAdjoint`：nhds_nhdsAdjoint [DecidableEq α] (a : α) (f : Filter α
) : @nhds α (nhdsAdjoint a f) = update pure a (pure a ⊔ f)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem nhds_eq_update : (𝓝 : Γ₀ → Filter Γ₀) = update pure 0 (⨅ γ ≠ 0, 𝓟 (Iio γ)) := by
  rw [nhds_nhdsAdjoint, sup_of_le_right]
  exact le_iInf₂ fun γ hγ ↦ le_principal_iff.2 <| zero_lt_iff.2 hγ

/-!
### Neighbourhoods of zero
-/

/-
**WithZeroTopology.nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：nhds_zero : 𝓝 (0 : Γ₀) = ⨅ γ != 0, 𝓟 (Iio γ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZeroTopology.nhds_eq_update`：nhds_eq_update : (𝓝 : Γ₀ -> Filter Γ₀) 
= update pure 0 (⨅ γ != 0, 𝓟 (Iio γ))
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v

--- 原说明 ---
### Neighbourhoods of zero
-/
theorem nhds_zero : 𝓝 (0 : Γ₀) = ⨅ γ ≠ 0, 𝓟 (Iio γ) := by
  rw [nhds_eq_update, update_self]

/-- In a linearly ordered group with zero element adjoined, `U` is a neighbourhood of `0` if and
only if there exists a nonzero element `γ₀` such that `Iio γ₀ ⊆ U`. -/
/-
**WithZeroTopology.hasBasis_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopolog
y`。
形式化陈述：hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ != 0) Iio
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZeroTopology.nhds_zero`：nhds_zero : 𝓝 (0 : Γ₀) = ⨅ γ != 0, 𝓟 (Iio γ)
· 使用定理 `Filter.hasBasis_biInf_principal`：hasBasis_biInf_principal {s : β -> Set 
α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· >= ·)) S) (ne : S.Nonempty) : (⨅ i in 
S, 𝓟 (s i)).HasBasis …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `Monotone.directed_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [IsCodirectedOrder α] [inst_2 : Preorder β] {f : α → β},   Monotone f → Direct
ed (fun x1…
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀

--- 原说明 ---
In a linearly ordered group with zero element adjoined, `U` is a neighbourhood o
f `0` if and
only if there exists a nonzero element `γ₀` such that `Iio γ₀ ⊆ U`.
-/
theorem hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ ≠ 0) Iio := by
  rw [nhds_zero]
  refine hasBasis_biInf_principal ?_ ⟨1, one_ne_zero⟩
  exact directedOn_iff_directed.2 (Monotone.directed_ge fun a b hab => Iio_subset_Iio hab)
/-
**WithZeroTopology.Iio_mem_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology
`。
形式化陈述：Iio_mem_nhds_zero (hγ : γ != 0) : Iio γ in 𝓝 (0 : Γ₀)
参数：hγ : γ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `WithZeroTopology.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).H
asBasis (fun γ : Γ₀ => γ != 0) Iio
-/
theorem Iio_mem_nhds_zero (hγ : γ ≠ 0) : Iio γ ∈ 𝓝 (0 : Γ₀) :=
  hasBasis_nhds_zero.mem_of_mem hγ

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`Iio (γ : Γ₀)` is a neighbourhood of `0`. -/
/-
**WithZeroTopology.nhds_zero_of_units** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopolog
y`。
形式化陈述：nhds_zero_of_units (γ : Γ₀ˣ) : Iio ↑γ in 𝓝 (0 : Γ₀)
参数：γ : Γ₀ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZeroTopology.Iio_mem_nhds_zero`：Iio_mem_nhds_zero (hγ : γ != 0) : Ii
o γ in 𝓝 (0 : Γ₀)
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀

--- 原说明 ---
If `γ` is an invertible element of a linearly ordered group with zero element ad
joined, then
`Iio (γ : Γ₀)` is a neighbourhood of `0`.
-/
theorem nhds_zero_of_units (γ : Γ₀ˣ) : Iio ↑γ ∈ 𝓝 (0 : Γ₀) :=
  Iio_mem_nhds_zero γ.ne_zero
/-
**WithZeroTopology.tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔ forall (γ₀) (_ : γ₀ != 0), foral
lᶠ x in l, f x < γ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZeroTopology.nhds_zero`：nhds_zero : 𝓝 (0 : Γ₀) = ⨅ γ != 0, 𝓟 (Iio γ)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔ ∀ (γ₀) (_ : γ₀ ≠ 0), ∀ᶠ x in l, f x < γ₀ := by
  simp [nhds_zero]

/-!
### Neighbourhoods of non-zero elements
-/

/-- The neighbourhood filter of a nonzero element consists of all sets containing that
element. -/
@[simp]
/-
**WithZeroTopology.nhds_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0) : 𝓝 γ = pure γ
参数：h₀ : γ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_nhdsAdjoint_of_ne`：nhds_nhdsAdjoint_of_ne {a b : α} (f : Filter α) 
(h : b != a) : @nhds α (nhdsAdjoint a f) b = pure b

--- 原说明 ---
The neighbourhood filter of a nonzero element consists of all sets containing th
at
element.
-/
theorem nhds_of_ne_zero {γ : Γ₀} (h₀ : γ ≠ 0) : 𝓝 γ = pure γ :=
  nhds_nhdsAdjoint_of_ne _ h₀

/-- The neighbourhood filter of an invertible element consists of all sets containing that
element. -/
/-
**WithZeroTopology.nhds_coe_units** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：nhds_coe_units (γ : Γ₀ˣ) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀)
参数：γ : Γ₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZeroTopology.nhds_of_ne_zero`：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0)
 : 𝓝 γ = pure γ
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀

--- 原说明 ---
The neighbourhood filter of an invertible element consists of all sets containin
g that
element.
-/
theorem nhds_coe_units (γ : Γ₀ˣ) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) :=
  nhds_of_ne_zero γ.ne_zero

/-- If `γ` is an invertible element of a linearly ordered group with zero element adjoined, then
`{γ}` is a neighbourhood of `γ`. -/
/-
**WithZeroTopology.singleton_mem_nhds_of_units** 是 Mathlib 中的一个定理，位于命名空间 `WithZe
roTopology`。
形式化陈述：singleton_mem_nhds_of_units (γ : Γ₀ˣ) : ({↑γ} : Set Γ₀) in 𝓝 (γ : Γ₀)
参数：γ : Γ₀ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZeroTopology.nhds_of_ne_zero`：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0)
 : 𝓝 γ = pure γ
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `γ` is an invertible element of a linearly ordered group with zero element ad
joined, then
`{γ}` is a neighbourhood of `γ`.
-/
theorem singleton_mem_nhds_of_units (γ : Γ₀ˣ) : ({↑γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp

/-- If `γ` is a nonzero element of a linearly ordered group with zero element adjoined, then `{γ}`
is a neighbourhood of `γ`. -/
/-
**WithZeroTopology.singleton_mem_nhds_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `With
ZeroTopology`。
形式化陈述：singleton_mem_nhds_of_ne_zero (h : γ != 0) : ({γ} : Set Γ₀) in 𝓝 (γ : Γ₀)
参数：h : γ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZeroTopology.nhds_of_ne_zero`：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0)
 : 𝓝 γ = pure γ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `γ` is a nonzero element of a linearly ordered group with zero element adjoin
ed, then `{γ}`
is a neighbourhood of `γ`.
-/
theorem singleton_mem_nhds_of_ne_zero (h : γ ≠ 0) : ({γ} : Set Γ₀) ∈ 𝓝 (γ : Γ₀) := by simp [h]
/-
**WithZeroTopology.hasBasis_nhds_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroT
opology`。
形式化陈述：hasBasis_nhds_of_ne_zero {x : Γ₀} (h : x != 0) : HasBasis (𝓝 x) (fun _ : U
nit => True) fun _ => {x}
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZeroTopology.nhds_of_ne_zero`：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0)
 : 𝓝 γ = pure γ
· 使用定理 `Filter.hasBasis_pure`：hasBasis_pure (x : α) : (pure x : Filter α).HasBas
is (fun _ : Unit => True) fun _ => {x}
-/
theorem hasBasis_nhds_of_ne_zero {x : Γ₀} (h : x ≠ 0) :
    HasBasis (𝓝 x) (fun _ : Unit => True) fun _ => {x} := by
  rw [nhds_of_ne_zero h]
  exact hasBasis_pure _
/-
**WithZeroTopology.hasBasis_nhds_units** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopolo
gy`。
形式化陈述：hasBasis_nhds_units (γ : Γ₀ˣ) : HasBasis (𝓝 (γ : Γ₀)) (fun _ : Unit => Tru
e) fun _ => {↑γ}
参数：γ : Γ₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZeroTopology.hasBasis_nhds_of_ne_zero`：hasBasis_nhds_of_ne_zero {x :
 Γ₀} (h : x != 0) : HasBasis (𝓝 x) (fun _ : Unit => True) fun _ => {x}
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem hasBasis_nhds_units (γ : Γ₀ˣ) :
    HasBasis (𝓝 (γ : Γ₀)) (fun _ : Unit => True) fun _ => {↑γ} :=
  hasBasis_nhds_of_ne_zero γ.ne_zero
/-
**WithZeroTopology.tendsto_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopolog
y`。
形式化陈述：tendsto_of_ne_zero {γ : Γ₀} (h : γ != 0) : Tendsto f l (𝓝 γ) ↔ forallᶠ x i
n l, f x = γ
参数：h : γ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZeroTopology.nhds_of_ne_zero`：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0)
 : 𝓝 γ = pure γ
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_of_ne_zero {γ : Γ₀} (h : γ ≠ 0) : Tendsto f l (𝓝 γ) ↔ ∀ᶠ x in l, f x = γ := by
  rw [nhds_of_ne_zero h, tendsto_pure]
/-
**WithZeroTopology.tendsto_units** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：tendsto_units {γ₀ : Γ₀ˣ} : Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ forallᶠ x in l, f x
 = γ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZeroTopology.tendsto_of_ne_zero`：tendsto_of_ne_zero {γ : Γ₀} (h : γ 
!= 0) : Tendsto f l (𝓝 γ) ↔ forallᶠ x in l, f x = γ
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem tendsto_units {γ₀ : Γ₀ˣ} : Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ ∀ᶠ x in l, f x = γ₀ :=
  tendsto_of_ne_zero γ₀.ne_zero
/-
**WithZeroTopology.Iio_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：Iio_mem_nhds (h : γ₁ < γ₂) : Iio γ₂ in 𝓝 γ₁
参数：h : γ₁ < γ₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithZeroTopology.nhds_of_ne_zero`：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0)
 : 𝓝 γ = pure γ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem Iio_mem_nhds (h : γ₁ < γ₂) : Iio γ₂ ∈ 𝓝 γ₁ := by
  rcases eq_or_ne γ₁ 0 with (rfl | h₀) <;> simp [*, h.ne', Iio_mem_nhds_zero]

/-!
### Open/closed sets
-/

/-
**WithZeroTopology.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：isOpen_iff {s : Set Γ₀} : IsOpen s ↔ (0 : Γ₀) ∉ s ∨ exists γ, γ != 0 ∧ Iio
 γ subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_forall_ne`：and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔
 forall b, p b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `WithZeroTopology.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).H
asBasis (fun γ : Γ₀ => γ != 0) Iio
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `WithZeroTopology.nhds_of_ne_zero`：nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0)
 : 𝓝 γ = pure γ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Open/closed sets
-/
theorem isOpen_iff {s : Set Γ₀} : IsOpen s ↔ (0 : Γ₀) ∉ s ∨ ∃ γ, γ ≠ 0 ∧ Iio γ ⊆ s := by
  rw [isOpen_iff_mem_nhds, ← and_forall_ne (0 : Γ₀)]
  simp +contextual [nhds_of_ne_zero, imp_iff_not_or,
    hasBasis_nhds_zero.mem_iff]
/-
**WithZeroTopology.isClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：isClosed_iff {s : Set Γ₀} : IsClosed s ↔ (0 : Γ₀) in s ∨ exists γ, γ != 0 
∧ s subseteq Ici γ
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_iff {s : Set Γ₀} : IsClosed s ↔ (0 : Γ₀) ∈ s ∨ ∃ γ, γ ≠ 0 ∧ s ⊆ Ici γ := by
  simp only [← isOpen_compl_iff, isOpen_iff, mem_compl_iff, not_not, ← compl_Ici,
    compl_subset_compl]
/-
**WithZeroTopology.isOpen_Iio** 是 Mathlib 中的一个定理，位于命名空间 `WithZeroTopology`。
形式化陈述：isOpen_Iio {a : Γ₀} : IsOpen (Iio a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithZeroTopology.isOpen_iff`：isOpen_iff {s : Set Γ₀} : IsOpen s ↔ (0 : Γ
₀) ∉ s ∨ exists γ, γ != 0 ∧ Iio γ subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem isOpen_Iio {a : Γ₀} : IsOpen (Iio a) :=
  isOpen_iff.mpr <| imp_iff_not_or.mp fun ha => ⟨a, ne_of_gt ha, Subset.rfl⟩

/-!
### Instances
-/

/-- The topology on a linearly ordered group with zero element adjoined is compatible with the order
structure: the set `{p : Γ₀ × Γ₀ | p.1 ≤ p.2}` is closed. -/
/-
**WithZeroTopology.** 是 Mathlib 中的一个实例，位于命名空间 `WithZeroTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on a linearly ordered group with zero element adjoined is compatibl
e with the order
structure: the set `{p : Γ₀ × Γ₀ | p.1 ≤ p.2}` is closed.
-/
scoped instance (priority := 100) orderClosedTopology : OrderClosedTopology Γ₀ where
  isClosed_le' := by
    simp only [← isOpen_compl_iff, compl_ofPred, not_le, isOpen_iff_mem_nhds]
    rintro ⟨a, b⟩ (hab : b < a)
    rw [nhds_prod_eq, nhds_of_ne_zero hab.ne_zero, pure_prod]
    exact Iio_mem_nhds hab

/-- The topology on a linearly ordered group with zero element adjoined is T₅. -/
/-
**WithZeroTopology.** 是 Mathlib 中的一个实例，位于命名空间 `WithZeroTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on a linearly ordered group with zero element adjoined is T₅.
-/
scoped instance (priority := 100) t5Space : T5Space Γ₀ where
  completely_normal := fun s t h₁ h₂ => by
    by_cases hs : 0 ∈ s
    · have ht : 0 ∉ t := fun ht => disjoint_left.1 h₁ (subset_closure hs) ht
      rwa [(isOpen_iff.2 (.inl ht)).nhdsSet_eq, disjoint_nhdsSet_principal]
    · rwa [(isOpen_iff.2 (.inl hs)).nhdsSet_eq, disjoint_principal_nhdsSet]

/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/
/-
**WithZeroTopology.** 是 Mathlib 中的一个实例，位于命名空间 `WithZeroTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on a linearly ordered group with zero element adjoined makes it a t
opological
monoid.
-/
scoped instance (priority := 100) : ContinuousMul Γ₀ where
  continuous_mul := by
    simp only [continuous_iff_continuousAt, ContinuousAt]
    rintro ⟨x, y⟩
    wlog hle : x ≤ y generalizing x y
    · have := (this y x (le_of_not_ge hle)).comp (continuous_swap.tendsto (x, y))
      simpa only [mul_comm, Function.comp_def, Prod.swap] using this
    rcases eq_or_ne x 0 with (rfl | hx) <;> [rcases eq_or_ne y 0 with (rfl | hy); skip]
    · rw [zero_mul]
      refine ((hasBasis_nhds_zero.prod_nhds hasBasis_nhds_zero).tendsto_iff hasBasis_nhds_zero).2
        fun γ hγ => ⟨(γ, 1), ⟨hγ, one_ne_zero⟩, ?_⟩
      rintro ⟨x, y⟩ ⟨hx : x < γ, hy : y < 1⟩
      exact (mul_lt_mul'' hx hy zero_le zero_le).trans_eq (mul_one γ)
    · rw [zero_mul, nhds_prod_eq, nhds_of_ne_zero hy, prod_pure, tendsto_map'_iff]
      refine (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun γ hγ => ?_
      refine ⟨γ / y, div_ne_zero hγ hy, fun x hx => ?_⟩
      calc x * y < γ / y * y := mul_lt_mul_of_pos_right hx (zero_lt_iff.2 hy)
      _ = γ := div_mul_cancel₀ _ hy
    · have hy : y ≠ 0 := ((zero_lt_iff.mpr hx).trans_le hle).ne'
      rw [nhds_prod_eq, nhds_of_ne_zero hx, nhds_of_ne_zero hy, prod_pure_pure]
      exact pure_le_nhds (x * y)
/-
**WithZeroTopology.** 是 Mathlib 中的一个实例，位于命名空间 `WithZeroTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (priority := 100) : ContinuousInv₀ Γ₀ :=
  ⟨fun γ h => by
    rw [ContinuousAt, nhds_of_ne_zero h]
    exact pure_le_nhds γ⁻¹⟩

end WithZeroTopology

