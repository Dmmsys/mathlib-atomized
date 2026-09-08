/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Orthogonal complements of submodules

In this file, the `orthogonal` complement of a submodule `K` is defined, and basic API established.
We make duplicates for `Submodule` and `ClosedSubmodule`.
Some of the more subtle results about the orthogonal complement are delayed to
`Mathlib/Analysis/InnerProductSpace/Projection/`.

See also `BilinForm.orthogonal` for orthogonality with respect to a general bilinear form.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

The proposition that two submodules are orthogonal, `Submodule.IsOrtho`, is denoted by `U ⟂ V`.
Note this is not the same unicode symbol as `⊥` (`Bot`).
-/

@[expose] public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Submodule

variable (K : Submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace, denoted `Kᗮ`. -/
/-
**Submodule.orthogonal** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：orthogonal : Submodule 𝕜 E where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subspace of vectors orthogonal to a given subspace, denoted `Kᗮ`.
-/
def orthogonal : Submodule 𝕜 E where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

/-- When a vector is in `Kᗮ`. -/
/-
**Submodule.mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in K, ⟪u, v⟫ = 0
参数：v : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
When a vector is in `Kᗮ`.
-/
theorem mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 :=
  Iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
/-
**Submodule.mem_orthogonal'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u in K, ⟪v, u⟫ = 0
参数：v : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When a vector is in `Kᗮ`, with the inner product the
other way round.
-/
theorem mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 := by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]

variable {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
/-
**Submodule.inner_right_of_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inner_right_of_mem_orthogonal {u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u,
 v⟫ = 0
参数：hu : u in K；hv : v in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_orthogonal`：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in
 K, ⟪u, v⟫ = 0

--- 原说明 ---
A vector in `K` is orthogonal to one in `Kᗮ`.
-/
theorem inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
/-
**Submodule.inner_left_of_mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inner_left_of_mem_orthogonal {u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪v, 
u⟫ = 0
参数：hu : u in K；hv : v in Kᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
· 使用定理 `Submodule.inner_right_of_mem_orthogonal`：inner_right_of_mem_orthogonal {
u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0

--- 原说明 ---
A vector in `Kᗮ` is orthogonal to one in `K`.
-/
theorem inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 := by
  rw [inner_eq_zero_symm]; exact inner_right_of_mem_orthogonal hu hv

/-- A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`. -/
/-
**Submodule.mem_orthogonal_singleton_iff_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule`。
形式化陈述：mem_orthogonal_singleton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v
⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.inner_right_of_mem_orthogonal`：inner_right_of_mem_orthogonal {
u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`.
-/
theorem mem_orthogonal_singleton_iff_inner_right {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 := by
  refine ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), ?_⟩
  intro hv w hw
  rw [mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
/-
**Submodule.mem_orthogonal_singleton_iff_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `S
ubmodule`。
形式化陈述：mem_orthogonal_singleton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`.
-/
theorem mem_orthogonal_singleton_iff_inner_left {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 := by
  rw [mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm]
/-
**Submodule.sub_mem_orthogonal_of_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：sub_mem_orthogonal_of_inner_left {x y : E} (h : forall v : K, ⟪x, v⟫ = ⟪y,
 v⟫) : x - y in Kᗮ
参数：h : forall v : K, ⟪x, v⟫ = ⟪y, v⟫。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_orthogonal'`：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u 
in K, ⟪v, u⟫ = 0
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
theorem sub_mem_orthogonal_of_inner_left {x y : E} (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Kᗮ := by
  rw [mem_orthogonal']
  intro u hu
  rw [inner_sub_left, sub_eq_zero]
  exact h ⟨u, hu⟩
/-
**Submodule.sub_mem_orthogonal_of_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：sub_mem_orthogonal_of_inner_right {x y : E} (h : forall v : K, ⟪(v : E), x
⟫ = ⟪(v : E), y⟫) : x - y in Kᗮ
参数：h : forall v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
theorem sub_mem_orthogonal_of_inner_right {x y : E} (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x - y ∈ Kᗮ := by
  intro u hu
  rw [inner_sub_right, sub_eq_zero]
  exact h ⟨u, hu⟩

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
/-
**Submodule.inf_orthogonal_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0

--- 原说明 ---
`K` and `Kᗮ` have trivial intersection.
-/
theorem inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x
  rw [mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)

/-- `K` and `Kᗮ` have trivial intersection. -/
/-
**Submodule.orthogonal_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_disjoint : Disjoint K Kᗮ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.inf_orthogonal_eq_bot`：inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`K` and `Kᗮ` have trivial intersection.
-/
theorem orthogonal_disjoint : Disjoint K Kᗮ := by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
/-
**Submodule.orthogonal_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_eq_inter : Kᗮ = ⨅ v : K, (innerSL 𝕜 (v : E)).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.mem_orthogonal`：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in
 K, ⟪u, v⟫ = 0

--- 原说明 ---
`Kᗮ` can be characterized as the intersection of the kernels of the operations o
f
inner product with each of the elements of `K`.
-/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, (innerSL 𝕜 (v : E)).ker := by
  ext
  simpa using mem_orthogonal _ _

/-- The orthogonal complement of any submodule `K` is closed. -/
/-
**Submodule.isClosed_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isClosed_orthogonal : IsClosed (Kᗮ : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonal_eq_inter`：orthogonal_eq_inter : Kᗮ = ⨅ v : K, (inne
rSL 𝕜 (v : E)).ker
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `ContinuousLinearMap.isClosed_ker`：isClosed_ker [T1Space M₂] (f : M₁ ->SL
[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
The orthogonal complement of any submodule `K` is closed.
-/
theorem isClosed_orthogonal : IsClosed (Kᗮ : Set E) := by
  rw [orthogonal_eq_inter K]
  convert! isClosed_iInter <| fun v : K => ContinuousLinearMap.isClosed_ker (innerSL 𝕜 (v : E))
  simp

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
/-
**Submodule.instOrthogonalCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：instOrthogonalCompleteSpace [CompleteSpace E] : CompleteSpace Kᗮ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isClosed_orthogonal`：isClosed_orthogonal : IsClosed (Kᗮ : Set 
E)

--- 原说明 ---
In a complete space, the orthogonal complement of any submodule `K` is complete.
-/
instance instOrthogonalCompleteSpace [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.isClosed_orthogonal.completeSpace_coe
/-
**Submodule.map_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：map_orthogonal (f : E ->ₗᵢ[𝕜] F) : Kᗮ.map f.toLinearMap = (K.map f.toLinea
rMap)ᗮ ⊓ f.range
参数：f : E ->ₗᵢ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma map_orthogonal (f : E →ₗᵢ[𝕜] F) :
    Kᗮ.map f.toLinearMap = (K.map f.toLinearMap)ᗮ ⊓ f.range := by
  simp only [Submodule.ext_iff, mem_map, mem_orthogonal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_inf, mem_map, LinearMap.mem_range,
    LinearIsometry.coe_toLinearMap]
  grind [LinearIsometry.inner_map_map]
/-
**Submodule.map_orthogonal_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：map_orthogonal_equiv (f : E ≃ₗᵢ[𝕜] F) : Kᗮ.map (f.toLinearEquiv : E ->ₗ[𝕜]
 F) = (K.map (f.toLinearEquiv : E ->ₗ[𝕜] F))ᗮ
参数：f : E ≃ₗᵢ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Submodule.map_orthogonal`：map_orthogonal (f : E ->ₗᵢ[𝕜] F) : Kᗮ.map f.to
LinearMap = (K.map f.toLinearMap)ᗮ ⊓ f.range
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
-/
lemma map_orthogonal_equiv (f : E ≃ₗᵢ[𝕜] F) :
    Kᗮ.map (f.toLinearEquiv : E →ₗ[𝕜] F) = (K.map (f.toLinearEquiv : E →ₗ[𝕜] F))ᗮ := by
  refine (map_orthogonal K f.toLinearIsometry).trans ?_
  have : f.toLinearIsometry.range = ⊤ := f.range
  rw [this, inf_top_eq]
  rfl

variable (𝕜 E)

/-- `orthogonal` gives a `GaloisConnection` between
`Submodule 𝕜 E` and its `OrderDual`. -/
/-
**Submodule.orthogonal_gc** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_gc : @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ or
thogonal orthogonal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.inner_left_of_mem_orthogonal`：inner_left_of_mem_orthogonal {u 
v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪v, u⟫ = 0

--- 原说明 ---
`orthogonal` gives a `GaloisConnection` between
`Submodule 𝕜 E` and its `OrderDual`.
-/
theorem orthogonal_gc :
    @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal := fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    inner_left_of_mem_orthogonal hv (h hu)⟩

variable {𝕜 E}

/-- `orthogonal` reverses the `≤` ordering of two
subspaces. -/
/-
**Submodule.orthogonal_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂) : K₂ᗮ <= K₁ᗮ
参数：h : K₁ <= K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Submodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Submodule 𝕜 
E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
`orthogonal` reverses the `≤` ordering of two
subspaces.
-/
theorem orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (orthogonal_gc 𝕜 E).monotone_l h

/-- `orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
/-
**Submodule.orthogonal_orthogonal_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂) : K₁
ᗮᗮ <= K₂ᗮᗮ
参数：h : K₁ <= K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ

--- 原说明 ---
`orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces.
-/
theorem orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  orthogonal_le (orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
/-
**Submodule.le_orthogonal_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_orthogonal_orthogonal : K <= Kᗮᗮ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Submodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Submodule 𝕜 
E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
`K` is contained in `Kᗮᗮ`.
-/
theorem le_orthogonal_orthogonal : K ≤ Kᗮᗮ :=
  (orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
/-
**Submodule.inf_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ
参数：K₁ K₂ : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Submodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Submodule 𝕜 
E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup.
-/
theorem inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
/-
**Submodule.iInf_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iInf_orthogonal {ι : Type*} (K : ι -> Submodule 𝕜 E) : ⨅ i, (K i)ᗮ = (iSup
 K)ᗮ
参数：K : ι -> Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Submodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Submodule 𝕜 
E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup.
-/
theorem iInf_orthogonal {ι : Type*} (K : ι → Submodule 𝕜 E) : ⨅ i, (K i)ᗮ = (iSup K)ᗮ :=
  (orthogonal_gc 𝕜 E).l_iSup.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
/-
**Submodule.sInf_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sInf_orthogonal (s : Set <| Submodule 𝕜 E) : ⨅ K in s, Kᗮ = (sSup s)ᗮ
参数：s : Set <| Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `Submodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Submodule 𝕜 
E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
The inf of a set of orthogonal subspaces equals the subspace orthogonal to the s
up.
-/
theorem sInf_orthogonal (s : Set <| Submodule 𝕜 E) : ⨅ K ∈ s, Kᗮ = (sSup s)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]
/-
**Submodule.top_orthogonal_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Submodule.mem_orthogonal`：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in
 K, ⟪u, v⟫ = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ := by
  ext x
  rw [mem_bot, mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x mem_top), by
      rintro rfl
      simp⟩

@[simp]
/-
**Submodule.bot_orthogonal_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.top_orthogonal_eq_bot`：top_orthogonal_eq_bot : (⊤ : Submodule 
𝕜 E)ᗮ = ⊥
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.le_orthogonal_orthogonal`：le_orthogonal_orthogonal : K <= Kᗮᗮ
-/
theorem bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ := by
  rw [← top_orthogonal_eq_bot, eq_top_iff]
  exact le_orthogonal_orthogonal ⊤

@[simp]
/-
**Submodule.orthogonal_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Submodule.orthogonal_disjoint`：orthogonal_disjoint : Disjoint K Kᗮ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Submodule.bot_orthogonal_eq_top`：bot_orthogonal_eq_top : (⊥ : Submodule 
𝕜 E)ᗮ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ := by
  refine
    ⟨?_, by
      rintro rfl
      exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

/-- The closure of a submodule has the same orthogonal complement and the submodule itself. -/
@[simp]
/-
**Submodule.orthogonal_closure** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_closure (K : Submodule 𝕜 E) : K.topologicalClosureᗮ = Kᗮ
参数：K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `Submodule.le_topologicalClosure`：Submodule.le_topologicalClosure (s : Su
bmodule R M) : s <= s.topologicalClosure
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
The closure of a submodule has the same orthogonal complement and the submodule 
itself.
-/
lemma orthogonal_closure (K : Submodule 𝕜 E) : K.topologicalClosureᗮ = Kᗮ :=
  le_antisymm (orthogonal_le <| le_topologicalClosure _)
    fun x hx y hy ↦ closure_minimal hx (isClosed_eq (by fun_prop) (by fun_prop)) hy
/-
**Submodule.orthogonal_closure'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：orthogonal_closure' (K : Submodule 𝕜 E) (x : E) : (forall y in K, ⟪y, x⟫ =
 0) ↔ forall y in K.topologicalClosure, ⟪y, x⟫ = 0
参数：K : Submodule 𝕜 E；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.orthogonal_closure`：orthogonal_closure (K : Submodule 𝕜 E) : K
.topologicalClosureᗮ = Kᗮ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma orthogonal_closure' (K : Submodule 𝕜 E) (x : E) :
    (∀ y ∈ K, ⟪y, x⟫ = 0) ↔ ∀ y ∈ K.topologicalClosure, ⟪y, x⟫ = 0 := by
  simp_rw [← mem_orthogonal, orthogonal_closure]
/-
**Submodule.orthogonalFamily_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   (K : Submodule 𝕜 E), OrthogonalFamily
 𝕜 (fun b => ↥(bif b then K else Kᗮ)) fun b => (bif b then K else Kᗮ).subtypeₗᵢ
参数：K : Submodule 𝕜 E；fun b => ↥(bif b then K else Kᗮ)；bif b then K else Kᗮ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.inner_right_of_mem_orthogonal`：inner_right_of_mem_orthogonal {
u v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪u, v⟫ = 0
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Submodule.inner_left_of_mem_orthogonal`：inner_left_of_mem_orthogonal {u 
v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪v, u⟫ = 0
-/
theorem orthogonalFamily_self :
    OrthogonalFamily 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ
  | true, true => absurd rfl
  | true, false => fun _ x y => inner_right_of_mem_orthogonal x.prop y.prop
  | false, true => fun _ x y => inner_left_of_mem_orthogonal y.prop x.prop
  | false, false => absurd rfl

end Submodule

@[simp]
/-
**orthogonalBilin_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orthogonalBilin_innerₗ {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) : K.orthogonalBilin (innerₗ E) = Kᗮ :=
  rfl

/-!
### Orthogonality of submodules

In this section we define `Submodule.IsOrtho U V`, denoted as `U ⟂ V`.

The API roughly matches that of `Disjoint`.
-/


namespace Submodule

/-- The proposition that two submodules are orthogonal, denoted as `U ⟂ V`. -/
/-
**Submodule.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：IsOrtho (U V : Submodule 𝕜 E) : Prop
参数：U V : Submodule 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that two submodules are orthogonal, denoted as `U ⟂ V`.
-/
def IsOrtho (U V : Submodule 𝕜 E) : Prop :=
  U ≤ Vᗮ

@[inherit_doc]
infixl:50 " ⟂ " => Submodule.IsOrtho
/-
**Submodule.isOrtho_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_iff_le {U V : Submodule 𝕜 E} : U ⟂ V ↔ U <= Vᗮ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOrtho_iff_le {U V : Submodule 𝕜 E} : U ⟂ V ↔ U ≤ Vᗮ :=
  Iff.rfl

@[symm]
/-
**Submodule.IsOrtho.symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E}, U ⟂ V → V ⟂ U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.le_orthogonal_orthogonal`：le_orthogonal_orthogonal : K <= Kᗮᗮ
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
-/
theorem IsOrtho.symm {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ⟂ U :=
  (le_orthogonal_orthogonal _).trans (orthogonal_le h)
/-
**Submodule.isOrtho_comm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂ U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
-/
theorem isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂ U :=
  ⟨IsOrtho.symm, IsOrtho.symm⟩
/-
**Submodule.symmetric_isOrtho** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：symmetric_isOrtho : Std.Symm IsOrtho (𝕜
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
-/
instance symmetric_isOrtho : Std.Symm <| IsOrtho (𝕜 := 𝕜) (E := E) where
  symm _ _ := IsOrtho.symm
/-
**Submodule.IsOrtho.inner_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E}, U ⟂ V → ∀ {u v
 : E}, u ∈ U → v ∈ V → inner 𝕜 u v = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
-/
theorem IsOrtho.inner_eq {U V : Submodule 𝕜 E} (h : U ⟂ V) {u v : E} (hu : u ∈ U) (hv : v ∈ V) :
    ⟪u, v⟫ = 0 :=
  h.symm hv _ hu
/-
**Submodule.isOrtho_iff_inner_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_iff_inner_eq {U V : Submodule 𝕜 E} : U ⟂ V ↔ forall u in U, forall
 v in V, ⟪u, v⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
-/
theorem isOrtho_iff_inner_eq {U V : Submodule 𝕜 E} : U ⟂ V ↔ ∀ u ∈ U, ∀ v ∈ V, ⟪u, v⟫ = 0 :=
  forall₄_congr fun _u _hu _v _hv => inner_eq_zero_symm

/-- TODO: generalize `Submodule.map₂` to semilinear maps, so that we can state
`U ⟂ V ↔ Submodule.map₂ (innerₛₗ 𝕜) U V ≤ ⊥`. -/
@[simp]
/-
**Submodule.isOrtho_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
TODO: generalize `Submodule.map₂` to semilinear maps, so that we can state
`U ⟂ V ↔ Submodule.map₂ (innerₛₗ 𝕜) U V ≤ ⊥`.
-/
theorem isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V :=
  bot_le

@[simp]
/-
**Submodule.isOrtho_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_bot_right {U : Submodule 𝕜 E} : U ⟂ ⊥
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
· 使用定理 `Submodule.isOrtho_bot_left`：isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V
-/
theorem isOrtho_bot_right {U : Submodule 𝕜 E} : U ⟂ ⊥ :=
  isOrtho_bot_left.symm
/-
**Submodule.IsOrtho.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U₁ U₂ V : Submodule 𝕜 E}, U₂ ≤ U₁ → 
U₁ ⟂ V → U₂ ⟂ V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem IsOrtho.mono_left {U₁ U₂ V : Submodule 𝕜 E} (hU : U₂ ≤ U₁) (h : U₁ ⟂ V) : U₂ ⟂ V :=
  hU.trans h
/-
**Submodule.IsOrtho.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V₁ V₂ : Submodule 𝕜 E}, V₂ ≤ V₁ → 
U ⟂ V₁ → U ⟂ V₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
· 使用定理 `Submodule.IsOrtho.mono_left`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCL
ike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U₁ U₂
 V : Submodule 𝕜 …
-/
theorem IsOrtho.mono_right {U V₁ V₂ : Submodule 𝕜 E} (hV : V₂ ≤ V₁) (h : U ⟂ V₁) : U ⟂ V₂ :=
  (h.symm.mono_left hV).symm
/-
**Submodule.IsOrtho.mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U₁ V₁ U₂ V₂ : Submodule 𝕜 E}, U₂ ≤ U
₁ → V₂ ≤ V₁ → U₁ ⟂ V₁ → U₂ ⟂ V₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.mono_left`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCL
ike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U₁ U₂
 V : Submodule 𝕜 …
· 使用定理 `Submodule.IsOrtho.mono_right`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RC
Like 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V₁
 V₂ : Submodule 𝕜 …
-/
theorem IsOrtho.mono {U₁ V₁ U₂ V₂ : Submodule 𝕜 E} (hU : U₂ ≤ U₁) (hV : V₂ ≤ V₁) (h : U₁ ⟂ V₁) :
    U₂ ⟂ V₂ :=
  (h.mono_right hV).mono_left hU

@[simp]
/-
**Submodule.isOrtho_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_self {U : Submodule 𝕜 E} : U ⟂ U ↔ U = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `Submodule.isOrtho_bot_left`：isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isOrtho_self {U : Submodule 𝕜 E} : U ⟂ U ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun x hx => inner_self_eq_zero.mp (h hx x hx), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]
/-
**Submodule.isOrtho_orthogonal_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_orthogonal_right (U : Submodule 𝕜 E) : U ⟂ Uᗮ
参数：U : Submodule 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.le_orthogonal_orthogonal`：le_orthogonal_orthogonal : K <= Kᗮᗮ
-/
theorem isOrtho_orthogonal_right (U : Submodule 𝕜 E) : U ⟂ Uᗮ :=
  le_orthogonal_orthogonal _

@[simp]
/-
**Submodule.isOrtho_orthogonal_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_orthogonal_left (U : Submodule 𝕜 E) : Uᗮ ⟂ U
参数：U : Submodule 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
· 使用定理 `Submodule.isOrtho_orthogonal_right`：isOrtho_orthogonal_right (U : Submod
ule 𝕜 E) : U ⟂ Uᗮ
-/
theorem isOrtho_orthogonal_left (U : Submodule 𝕜 E) : Uᗮ ⟂ U :=
  (isOrtho_orthogonal_right U).symm
/-
**Submodule.IsOrtho.le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E}, U ⟂ V → U ≤ Vᗮ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsOrtho.le {U V : Submodule 𝕜 E} (h : U ⟂ V) : U ≤ Vᗮ :=
  h
/-
**Submodule.IsOrtho.ge** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E}, U ⟂ V → V ≤ Uᗮ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
-/
theorem IsOrtho.ge {U V : Submodule 𝕜 E} (h : U ⟂ V) : V ≤ Uᗮ :=
  h.symm

@[simp]
/-
**Submodule.isOrtho_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_top_right {U : Submodule 𝕜 E} : U ⟂ ⊤ ↔ U = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Submodule.isOrtho_bot_left`：isOrtho_bot_left {V : Submodule 𝕜 E} : ⊥ ⟂ V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isOrtho_top_right {U : Submodule 𝕜 E} : U ⟂ ⊤ ↔ U = ⊥ :=
  ⟨fun h => eq_bot_iff.mpr fun _x hx => inner_self_eq_zero.mp (h hx _ mem_top), fun h =>
    h.symm ▸ isOrtho_bot_left⟩

@[simp]
/-
**Submodule.isOrtho_top_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_top_left {V : Submodule 𝕜 E} : ⊤ ⟂ V ↔ V = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.isOrtho_comm`：isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂
 U
· 使用定理 `Submodule.isOrtho_top_right`：isOrtho_top_right {U : Submodule 𝕜 E} : U ⟂
 ⊤ ↔ U = ⊥
-/
theorem isOrtho_top_left {V : Submodule 𝕜 E} : ⊤ ⟂ V ↔ V = ⊥ :=
  isOrtho_comm.trans isOrtho_top_right

/-- Orthogonal submodules are disjoint. -/
/-
**Submodule.IsOrtho.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Submodule 𝕜 E}, U ⟂ V → Disjoi
nt U V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Submodule.IsOrtho.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜
] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : Subm
odule 𝕜 E}, …
· 使用定理 `Submodule.orthogonal_disjoint`：orthogonal_disjoint : Disjoint K Kᗮ

--- 原说明 ---
Orthogonal submodules are disjoint.
-/
theorem IsOrtho.disjoint {U V : Submodule 𝕜 E} (h : U ⟂ V) : Disjoint U V :=
  (Submodule.orthogonal_disjoint _).mono_right h.symm

@[simp]
/-
**Submodule.isOrtho_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_sup_left {U₁ U₂ V : Submodule 𝕜 E} : U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
-/
theorem isOrtho_sup_left {U₁ U₂ V : Submodule 𝕜 E} : U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V :=
  sup_le_iff

@[simp]
/-
**Submodule.isOrtho_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_sup_right {U V₁ V₂ : Submodule 𝕜 E} : U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.isOrtho_comm`：isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂
 U
· 使用定理 `Submodule.isOrtho_sup_left`：isOrtho_sup_left {U₁ U₂ V : Submodule 𝕜 E} :
 U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
-/
theorem isOrtho_sup_right {U V₁ V₂ : Submodule 𝕜 E} : U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V₂ :=
  isOrtho_comm.trans <| isOrtho_sup_left.trans <| isOrtho_comm.and isOrtho_comm

@[simp]
/-
**Submodule.isOrtho_sSup_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_sSup_left {U : Set (Submodule 𝕜 E)} {V : Submodule 𝕜 E} : sSup U ⟂
 V ↔ forall Uᵢ in U, Uᵢ ⟂ V
参数：Submodule 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le_iff`：sSup_le_iff : sSup s <= a ↔ forall b in s, b <= a
-/
theorem isOrtho_sSup_left {U : Set (Submodule 𝕜 E)} {V : Submodule 𝕜 E} :
    sSup U ⟂ V ↔ ∀ Uᵢ ∈ U, Uᵢ ⟂ V :=
  sSup_le_iff

@[simp]
/-
**Submodule.isOrtho_sSup_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_sSup_right {U : Submodule 𝕜 E} {V : Set (Submodule 𝕜 E)} : U ⟂ sSu
p V ↔ forall Vᵢ in V, U ⟂ Vᵢ
参数：Submodule 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.isOrtho_comm`：isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂
 U
· 使用定理 `Submodule.isOrtho_sSup_left`：isOrtho_sSup_left {U : Set (Submodule 𝕜 E)}
 {V : Submodule 𝕜 E} : sSup U ⟂ V ↔ forall Uᵢ in U, Uᵢ ⟂ V
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
theorem isOrtho_sSup_right {U : Submodule 𝕜 E} {V : Set (Submodule 𝕜 E)} :
    U ⟂ sSup V ↔ ∀ Vᵢ ∈ V, U ⟂ Vᵢ :=
  isOrtho_comm.trans <| isOrtho_sSup_left.trans <| by simp_rw [isOrtho_comm]

@[simp]
/-
**Submodule.isOrtho_iSup_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_iSup_left {ι : Sort*} {U : ι -> Submodule 𝕜 E} {V : Submodule 𝕜 E}
 : iSup U ⟂ V ↔ forall i, U i ⟂ V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
-/
theorem isOrtho_iSup_left {ι : Sort*} {U : ι → Submodule 𝕜 E} {V : Submodule 𝕜 E} :
    iSup U ⟂ V ↔ ∀ i, U i ⟂ V :=
  iSup_le_iff

@[simp]
/-
**Submodule.isOrtho_iSup_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_iSup_right {ι : Sort*} {U : Submodule 𝕜 E} {V : ι -> Submodule 𝕜 E
} : U ⟂ iSup V ↔ forall i, U ⟂ V i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.isOrtho_comm`：isOrtho_comm {U V : Submodule 𝕜 E} : U ⟂ V ↔ V ⟂
 U
· 使用定理 `Submodule.isOrtho_iSup_left`：isOrtho_iSup_left {ι : Sort*} {U : ι -> Sub
module 𝕜 E} {V : Submodule 𝕜 E} : iSup U ⟂ V ↔ forall i, U i ⟂ V
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
theorem isOrtho_iSup_right {ι : Sort*} {U : Submodule 𝕜 E} {V : ι → Submodule 𝕜 E} :
    U ⟂ iSup V ↔ ∀ i, U ⟂ V i :=
  isOrtho_comm.trans <| isOrtho_iSup_left.trans <| by simp_rw [isOrtho_comm]

@[simp]
/-
**Submodule.isOrtho_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOrtho_span {s t : Set E} : span 𝕜 s ⟂ span 𝕜 t ↔ forall ⦃u⦄, u in s -> f
orall ⦃v⦄, v in t -> ⟪u, v⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_eq_iSup_of_singleton_spans`：span_eq_iSup_of_singleton_spa
ns (s : Set M) : span R s = ⨆ x in s, R ∙ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOrtho_span {s t : Set E} :
    span 𝕜 s ⟂ span 𝕜 t ↔ ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ t → ⟪u, v⟫ = 0 := by
  simp_rw [span_eq_iSup_of_singleton_spans s, span_eq_iSup_of_singleton_spans t, isOrtho_iSup_left,
    isOrtho_iSup_right, isOrtho_iff_le, span_le, Set.subset_def, SetLike.mem_coe,
    mem_orthogonal_singleton_iff_inner_left, Set.mem_singleton_iff, forall_eq]
/-
**Submodule.IsOrtho.map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (f : E →ₗᵢ[𝕜] F)   {U V : Submodule 𝕜
 E}, U ⟂ V → Submodule.map (↑f) U ⟂ Submodule.map (↑f) V
参数：f : E →ₗᵢ[𝕜] F；↑f；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsOrtho.map (f : E →ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} (h : U ⟂ V) :
    U.map (f : E →ₗ[𝕜] F) ⟂ V.map (f : E →ₗ[𝕜] F) := by
  aesop (add simp [isOrtho_iff_inner_eq])
/-
**Submodule.IsOrtho.comap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (f : E →ₗᵢ[𝕜] F)   {U V : Submodule 𝕜
 F}, U ⟂ V → Submodule.comap (↑f) U ⟂ Submodule.comap (↑f) V
参数：f : E →ₗᵢ[𝕜] F；↑f；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.isOrtho_iff_inner_eq`：isOrtho_iff_inner_eq {U V : Submodule 𝕜 
E} : U ⟂ V ↔ forall u in U, forall v in V, ⟪u, v⟫ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
-/
theorem IsOrtho.comap (f : E →ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} (h : U ⟂ V) :
    U.comap (f : E →ₗ[𝕜] F) ⟂ V.comap (f : E →ₗ[𝕜] F) := by
  rw [isOrtho_iff_inner_eq] at *
  simp_rw [mem_comap, ← f.inner_map_map]
  intro u hu v hv
  exact h _ hu _ hv

@[simp]
/-
**Submodule.IsOrtho.map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F)   {U V : Submodule 𝕜
 E}, Submodule.map (↑↑↑f) U ⟂ Submodule.map (↑↑↑f) V ↔ U ⟂ V
参数：f : E ≃ₗᵢ[𝕜] F；↑↑↑f；↑↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `Submodule.comap_map_eq_of_injective`：comap_map_eq_of_injective (p : Subm
odule R M) : (p.map f).comap f = p
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsOrtho.comap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 
𝕜 E] [inst_3 …
· 使用定理 `Submodule.IsOrtho.map`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 
E] [inst_3 …
-/
theorem IsOrtho.map_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 E} :
    U.map (f : E →ₗ[𝕜] F) ⟂ V.map (f : E →ₗ[𝕜] F) ↔ U ⟂ V := by
  refine ⟨fun h ↦ ?_, IsOrtho.map f.toLinearIsometry⟩
  have hf : ∀ p : Submodule 𝕜 E,
      (p.map (f : E →ₗ[𝕜] F)).comap (f.toLinearIsometry : E →ₗ[𝕜] F) = p :=
    comap_map_eq_of_injective f.injective
  simpa only [hf] using h.comap f.toLinearIsometry

@[simp]
/-
**Submodule.IsOrtho.comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsOrtho`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F)   {U V : Submodule 𝕜
 F}, Submodule.comap (↑↑↑f) U ⟂ Submodule.comap (↑↑↑f) V ↔ U ⟂ V
参数：f : E ≃ₗᵢ[𝕜] F；↑↑↑f；↑↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
· 使用定理 `Submodule.IsOrtho.map_iff`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
-/
theorem IsOrtho.comap_iff (f : E ≃ₗᵢ[𝕜] F) {U V : Submodule 𝕜 F} :
    U.comap (f : E →ₗ[𝕜] F) ⟂ V.comap (f : E →ₗ[𝕜] F) ↔ U ⟂ V := by
  convert IsOrtho.map_iff f.symm <;>
    exact Submodule.comap_equiv_eq_map_symm (f : E ≃ₗ[𝕜] F) _

end Submodule

open scoped Function in -- required for scoped `on` notation
/-
**orthogonalFamily_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthogonalFamily_iff_pairwise {ι} {V : ι -> Submodule 𝕜 E} : (OrthogonalFa
mily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) ↔ Pairwise ((· ⟂ ·) on V)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
-/
theorem orthogonalFamily_iff_pairwise {ι} {V : ι → Submodule 𝕜 E} :
    (OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) ↔ Pairwise ((· ⟂ ·) on V) :=
  forall₃_congr fun _i _j _hij =>
    Subtype.forall.trans <|
      forall₂_congr fun _x _hx => Subtype.forall.trans <|
        forall₂_congr fun _y _hy => inner_eq_zero_symm

alias ⟨OrthogonalFamily.pairwise, OrthogonalFamily.of_pairwise⟩ := orthogonalFamily_iff_pairwise

/-- Two submodules in an orthogonal family with different indices are orthogonal. -/
/-
**OrthogonalFamily.isOrtho** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthogonalFamily.isOrtho {ι} {V : ι -> Submodule 𝕜 E} (hV : OrthogonalFami
ly 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i j : ι} (hij : i != j) : V i ⟂ V
 j
参数：hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ；hij : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthogonalFamily.pairwise`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLik
e 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Typ
e u_4} {V : ι →…

--- 原说明 ---
Two submodules in an orthogonal family with different indices are orthogonal.
-/
theorem OrthogonalFamily.isOrtho {ι} {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i j : ι} (hij : i ≠ j) :
    V i ⟂ V j :=
  hV.pairwise hij

namespace ClosedSubmodule

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : ClosedSubmodule 𝕜 E)

/-- The closed subspace of vectors orthogonal to a given subspace, denoted `Kᗮ`. -/
/-
**ClosedSubmodule.orthogonal** 是 Mathlib 中的一个定义，位于命名空间 `ClosedSubmodule`。
形式化陈述：orthogonal : ClosedSubmodule 𝕜 E where toSubmodule
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed subspace of vectors orthogonal to a given subspace, denoted `Kᗮ`.
-/
def orthogonal : ClosedSubmodule 𝕜 E where
  toSubmodule := K.toSubmodule.orthogonal
  isClosed' := K.toSubmodule.isClosed_orthogonal

@[inherit_doc]
notation:1200 K "ᗮ" => orthogonal K

@[simp]
/-
**ClosedSubmodule.toSubmodule_orthogonal_eq** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSub
module`。
形式化陈述：toSubmodule_orthogonal_eq : K.orthogonal.toSubmodule = K.toSubmodule.ortho
gonal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubmodule_orthogonal_eq : K.orthogonal.toSubmodule = K.toSubmodule.orthogonal := rfl

@[deprecated (since := "2026-01-18")] alias orthogonal_toSubmodule_eq := toSubmodule_orthogonal_eq

@[simp]
/-
**ClosedSubmodule.mem_orthogonal_toSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `Clos
edSubmodule`。
形式化陈述：mem_orthogonal_toSubmodule_iff (v : E) : v in (K.toSubmodule)ᗮ ↔ v in Kᗮ
参数：v : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_orthogonal_toSubmodule_iff (v : E) : v ∈ (K.toSubmodule)ᗮ ↔ v ∈ Kᗮ := Iff.rfl

@[deprecated (since := "2026-01-18")] alias mem_orthogonal_iff := mem_orthogonal_toSubmodule_iff

/-- When a vector is in `Kᗮ`. -/
@[simp]
/-
**ClosedSubmodule.mem_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mem_orthogonal (v : E) : v in Kᗮ ↔ forall u in K, ⟪u, v⟫ = 0
参数：v : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
When a vector is in `Kᗮ`.
-/
theorem mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 := Iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
/-
**ClosedSubmodule.mem_orthogonal'** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u in K, ⟪v, u⟫ = 0
参数：v : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_orthogonal'`：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u 
in K, ⟪v, u⟫ = 0

--- 原说明 ---
When a vector is in `Kᗮ`, with the inner product the
other way round.
-/
theorem mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 :=
  Submodule.mem_orthogonal' K.toSubmodule v

variable {K}
/-
**ClosedSubmodule.sub_mem_orthogonal_of_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `Cl
osedSubmodule`。
形式化陈述：sub_mem_orthogonal_of_inner_left {x y : E} (h : forall v : K, ⟪x, v⟫ = ⟪y,
 v⟫) : x - y in Kᗮ
参数：h : forall v : K, ⟪x, v⟫ = ⟪y, v⟫。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sub_mem_orthogonal_of_inner_left`：sub_mem_orthogonal_of_inner_
left {x y : E} (h : forall v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y in Kᗮ
-/
theorem sub_mem_orthogonal_of_inner_left {x y : E} (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Kᗮ :=
  Submodule.sub_mem_orthogonal_of_inner_left h
/-
**ClosedSubmodule.sub_mem_orthogonal_of_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `C
losedSubmodule`。
形式化陈述：sub_mem_orthogonal_of_inner_right {x y : E} (h : forall v : K, ⟪(v : E), x
⟫ = ⟪(v : E), y⟫) : x - y in Kᗮ
参数：h : forall v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sub_mem_orthogonal_of_inner_right`：sub_mem_orthogonal_of_inner
_right {x y : E} (h : forall v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x - y in Kᗮ
-/
theorem sub_mem_orthogonal_of_inner_right {x y : E} (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x - y ∈ Kᗮ := Submodule.sub_mem_orthogonal_of_inner_right h

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
/-
**ClosedSubmodule.inf_orthogonal_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodu
le`。
形式化陈述：inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0

--- 原说明 ---
`K` and `Kᗮ` have trivial intersection.
-/
theorem inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x
  simpa using fun hx ho => inner_self_eq_zero.1 (ho x hx)

/-- `K` and `Kᗮ` have trivial intersection. -/
/-
**ClosedSubmodule.orthogonal_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：orthogonal_disjoint : Disjoint K Kᗮ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.inf_orthogonal_eq_bot`：inf_orthogonal_eq_bot : K ⊓ Kᗮ = 
⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`K` and `Kᗮ` have trivial intersection.
-/
theorem orthogonal_disjoint : Disjoint K Kᗮ := by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
/-
**ClosedSubmodule.orthogonal_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：orthogonal_eq_inter : Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)).toLi
nearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Kᗮ` can be characterized as the intersection of the kernels of the operations o
f
inner product with each of the elements of `K`.
-/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)).toLinearMap := by
  ext
  simp

variable (𝕜 E)

/-- `orthogonal` gives a `GaloisConnection` between
`ClosedSubmodule 𝕜 E` and its `OrderDual`. -/
/-
**ClosedSubmodule.orthogonal_gc** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：orthogonal_gc : @GaloisConnection (ClosedSubmodule 𝕜 E) (ClosedSubmodule 𝕜
 E)ᵒᵈ _ _ orthogonal orthogonal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.inner_left_of_mem_orthogonal`：inner_left_of_mem_orthogonal {u 
v : E} (hu : u in K) (hv : v in Kᗮ) : ⟪v, u⟫ = 0

--- 原说明 ---
`orthogonal` gives a `GaloisConnection` between
`ClosedSubmodule 𝕜 E` and its `OrderDual`.
-/
theorem orthogonal_gc :
    @GaloisConnection (ClosedSubmodule 𝕜 E) (ClosedSubmodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal :=
  fun _K₁ _K₂ =>
  ⟨fun h _v hv _u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu), fun h _v hv _u hu =>
    Submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

variable {𝕜 E}

/-- `orthogonal` reverses the `≤` ordering of two
subspaces. -/
/-
**ClosedSubmodule.orthogonal_le** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：orthogonal_le {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂) : K₂ᗮ <= K₁ᗮ
参数：h : K₁ <= K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `ClosedSubmodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Closed
Submodule 𝕜 E) (ClosedSubmodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
`orthogonal` reverses the `≤` ordering of two
subspaces.
-/
theorem orthogonal_le {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (orthogonal_gc 𝕜 E).monotone_l h

/-- `orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
/-
**ClosedSubmodule.orthogonal_orthogonal_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Clos
edSubmodule`。
形式化陈述：orthogonal_orthogonal_monotone {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ <= K₂
) : K₁ᗮᗮ <= K₂ᗮᗮ
参数：h : K₁ <= K₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.orthogonal_le`：orthogonal_le {K₁ K₂ : ClosedSubmodule 𝕜 
E} (h : K₁ <= K₂) : K₂ᗮ <= K₁ᗮ

--- 原说明 ---
`orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces.
-/
theorem orthogonal_orthogonal_monotone {K₁ K₂ : ClosedSubmodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  orthogonal_le (orthogonal_le h)

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
/-
**ClosedSubmodule.inf_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：inf_orthogonal (K₁ K₂ : ClosedSubmodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ
参数：K₁ K₂ : ClosedSubmodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `ClosedSubmodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Closed
Submodule 𝕜 E) (ClosedSubmodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup.
-/
theorem inf_orthogonal (K₁ K₂ : ClosedSubmodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
/-
**ClosedSubmodule.iInf_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：iInf_orthogonal {ι : Type*} (K : ι -> ClosedSubmodule 𝕜 E) : ⨅ i, (K i)ᗮ =
 (iSup K)ᗮ
参数：K : ι -> ClosedSubmodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `ClosedSubmodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Closed
Submodule 𝕜 E) (ClosedSubmodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup.
-/
theorem iInf_orthogonal {ι : Type*} (K : ι → ClosedSubmodule 𝕜 E) : ⨅ i, (K i)ᗮ = (iSup K)ᗮ :=
  (orthogonal_gc 𝕜 E).l_iSup.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
/-
**ClosedSubmodule.sInf_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：sInf_orthogonal (s : Set <| ClosedSubmodule 𝕜 E) : ⨅ K in s, Kᗮ = (sSup s)
ᗮ
参数：s : Set <| ClosedSubmodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `ClosedSubmodule.orthogonal_gc`：orthogonal_gc : @GaloisConnection (Closed
Submodule 𝕜 E) (ClosedSubmodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal

--- 原说明 ---
The inf of a set of orthogonal subspaces equals the subspace orthogonal to the s
up.
-/
theorem sInf_orthogonal (s : Set <| ClosedSubmodule 𝕜 E) : ⨅ K ∈ s, Kᗮ = (sSup s)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sSup.symm

@[simp]
/-
**ClosedSubmodule.top_orthogonal_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodu
le`。
形式化陈述：top_orthogonal_eq_bot : (⊤ : ClosedSubmodule 𝕜 E)ᗮ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.top_orthogonal_eq_bot`：top_orthogonal_eq_bot : (⊤ : Submodule 
𝕜 E)ᗮ = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem top_orthogonal_eq_bot : (⊤ : ClosedSubmodule 𝕜 E)ᗮ = ⊥ := by ext x; simp

@[simp]
/-
**ClosedSubmodule.bot_orthogonal_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodu
le`。
形式化陈述：bot_orthogonal_eq_top : (⊥ : ClosedSubmodule 𝕜 E)ᗮ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.bot_orthogonal_eq_top`：bot_orthogonal_eq_top : (⊥ : Submodule 
𝕜 E)ᗮ = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bot_orthogonal_eq_top : (⊥ : ClosedSubmodule 𝕜 E)ᗮ = ⊤ := by ext x; simp

@[simp]
/-
**ClosedSubmodule.orthogonal_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodu
le`。
形式化陈述：orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `ClosedSubmodule.orthogonal_disjoint`：orthogonal_disjoint : Disjoint K Kᗮ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `ClosedSubmodule.bot_orthogonal_eq_top`：bot_orthogonal_eq_top : (⊥ : Clos
edSubmodule 𝕜 E)ᗮ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ := by
  refine
    ⟨?_, by rintro rfl; exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

/-- The orthogonal complement of the closure of a submodule (as a `Submodule`) is equal to
the orthogonal complement. -/
@[simp]
/-
**ClosedSubmodule.orthogonal_closure** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`
。
形式化陈述：orthogonal_closure (K : Submodule 𝕜 E) : (K.closure : Submodule 𝕜 E)ᗮ = Kᗮ
参数：K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.orthogonal_closure`：orthogonal_closure (K : Submodule 𝕜 E) : K
.topologicalClosureᗮ = Kᗮ

--- 原说明 ---
The orthogonal complement of the closure of a submodule (as a `Submodule`) is eq
ual to
the orthogonal complement.
-/
lemma orthogonal_closure (K : Submodule 𝕜 E) : (K.closure : Submodule 𝕜 E)ᗮ = Kᗮ := by
  rw [← Submodule.orthogonal_closure K]
  congr

/-- The orthogonal complement of the closure of a submodule (as a `ClosedSubmodule`) is equal to
the orthogonal complement. -/
/-
**ClosedSubmodule.orthogonal_closure'** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：orthogonal_closure' (K : Submodule 𝕜 E) : K.closureᗮ = ⟨Kᗮ, K.isClosed_ort
hogonal⟩
参数：K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Submodule.isClosed_orthogonal`：isClosed_orthogonal : IsClosed (Kᗮ : Set 
E)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ClosedSubmodule.orthogonal_closure`：orthogonal_closure (K : Submodule 𝕜 
E) : (K.closure : Submodule 𝕜 E)ᗮ = Kᗮ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The orthogonal complement of the closure of a submodule (as a `ClosedSubmodule`)
 is equal to
the orthogonal complement.
-/
lemma orthogonal_closure' (K : Submodule 𝕜 E) : K.closureᗮ = ⟨Kᗮ, K.isClosed_orthogonal⟩ := by
  ext x; simp

/-- The orthogonal complement of the closure of a submodule (as a `ClosedSubmodule`) is equal to
the closure of the orthogonal complement. -/
/-
**ClosedSubmodule.orthogonal_closure''** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodul
e`。
形式化陈述：orthogonal_closure'' (K : Submodule 𝕜 E) : K.closureᗮ = Kᗮ.closure
参数：K : Submodule 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Submodule.isClosed_orthogonal`：isClosed_orthogonal : IsClosed (Kᗮ : Set 
E)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.closure_eq'`：closure_eq' {s : Submodule R M} (hs : IsClosed s.
carrier) : s.closure = ⟨s, hs⟩
· 使用引理 `ClosedSubmodule.orthogonal_closure'`：orthogonal_closure' (K : Submodule 
𝕜 E) : K.closureᗮ = ⟨Kᗮ, K.isClosed_orthogonal⟩

--- 原说明 ---
The orthogonal complement of the closure of a submodule (as a `ClosedSubmodule`)
 is equal to
the closure of the orthogonal complement.
-/
lemma orthogonal_closure'' (K : Submodule 𝕜 E) : K.closureᗮ = Kᗮ.closure := by
  rw [Submodule.closure_eq' K.isClosed_orthogonal]
  exact orthogonal_closure' K

end ClosedSubmodule

