/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Congruence
public import Mathlib.Topology.MetricSpace.Dilation
public import Mathlib.Tactic.FinCases

/-!
# Similarities

This file defines `Similar`, i.e., the equivalence between indexed sets of points in a metric space
where all corresponding pairwise distances have the same ratio. The motivating example is
triangles in the plane.

## Implementation notes

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation
Let `P₁` and `P₂` be metric spaces, let `ι` be an index set, and let `v₁ : ι → P₁` and
`v₂ : ι → P₂` be indexed families of points.

* `(v₁ ∼ v₂ : Prop)` represents that `(v₁ : ι → P₁)` and `(v₂ : ι → P₂)` are similar.
-/

@[expose] public section

open scoped NNReal

variable {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [PseudoEMetricSpace P₃]

/-- Similarity between indexed sets of vertices v₁ and v₂.
Use `open scoped Similar` to access the `v₁ ∼ v₂` notation. -/
/-
**Similar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Similar (v₁ : ι -> P₁) (v₂ : ι -> P₂) : Prop
参数：v₁ : ι -> P₁；v₂ : ι -> P₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Similarity between indexed sets of vertices v₁ and v₂.
Use `open scoped Similar` to access the `v₁ ∼ v₂` notation.
-/
def Similar (v₁ : ι → P₁) (v₂ : ι → P₂) : Prop :=
  ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Similar] infixl:25 " ∼ " => Similar

/-- Similarity holds if and only if all extended distances are proportional. -/
/-
**similar_iff_exists_edist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_edist_eq : Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 
∧ forall (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Similarity holds if and only if all extended distances are proportional.
-/
lemma similar_iff_exists_edist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) :=
  Iff.rfl

/-- Similarity holds if and only if all extended distances between points with different
indices are proportional. -/
/-
**similar_iff_exists_pairwise_edist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_pairwise_edist_eq : Similar v₁ v₂ ↔ (exists r : Real>=0
, r != 0 ∧ Pairwise fun i₁ i₂ => (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ 
i₂)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `similar_iff_exists_edist_eq`：similar_iff_exists_edist_eq : Similar v₁ v₂
 ↔ (exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r 
* edist (v₂ i₁) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Similarity holds if and only if all extended distances between points with diffe
rent
indices are proportional.
-/
lemma similar_iff_exists_pairwise_edist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_edist_eq]
  refine ⟨?_, ?_⟩ <;> rintro ⟨r, hr, h⟩ <;> refine ⟨r, hr, fun i₁ i₂ ↦ ?_⟩
  · exact fun _ ↦ h i₁ i₂
  · by_cases hi : i₁ = i₂
    · simp [hi]
    · exact h hi
/-
**Congruent.similar** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Congruent.similar {v₁ : ι -> P₁} {v₂ : ι -> P₂} (h : Congruent v₁ v₂) : Si
milar v₁ v₂
参数：h : Congruent v₁ v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma Congruent.similar {v₁ : ι → P₁} {v₂ : ι → P₂} (h : Congruent v₁ v₂) : Similar v₁ v₂ :=
  ⟨1, one_ne_zero, fun i₁ i₂ ↦ by simpa using h i₁ i₂⟩

namespace Similar

/-- A similarity scales extended distance. Forward direction of `similar_iff_exists_edist_eq`. -/
alias ⟨exists_edist_eq, _⟩ := similar_iff_exists_edist_eq

/-- Similarity follows from scaled extended distance. Backward direction of
`similar_iff_exists_edist_eq`. -/
alias ⟨_, of_exists_edist_eq⟩ := similar_iff_exists_edist_eq

/-- A similarity pairwise scales extended distance. Forward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨exists_pairwise_edist_eq, _⟩ := similar_iff_exists_pairwise_edist_eq

/-- Similarity follows from pairwise scaled extended distance. Backward direction of
`similar_iff_exists_pairwise_edist_eq`. -/
alias ⟨_, of_exists_pairwise_edist_eq⟩ := similar_iff_exists_pairwise_edist_eq

/-
**Similar.refl** 是 Mathlib 中的一个定理，位于命名空间 `Similar`。
形式化陈述：∀ {ι : Type u_1} {P₁ : Type u_3} [inst : PseudoEMetricSpace P₁] (v₁ : ι → 
P₁), Similar v₁ v₁
参数：v₁ : ι → P₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[refl] protected lemma refl (v₁ : ι → P₁) : v₁ ∼ v₁ :=
  ⟨1, one_ne_zero, fun _ _ => by {norm_cast; rw [one_mul]}⟩
/-
**Similar.symm** 是 Mathlib 中的一个定理，位于命名空间 `Similar`。
形式化陈述：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ : ι → P₁} {v₂ : ι → P
₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetricSpace P₂], Similar v₁
 v₂ → Similar v₂ v₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `ENNReal.eq_div_iff`：eq_div_iff (ha : a != 0) (ha' : a != ∞) : b = c / a 
↔ a * b = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
@[symm] protected lemma symm (h : v₁ ∼ v₂) : v₂ ∼ v₁ := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r⁻¹, inv_ne_zero hr, fun _ _ => ?_⟩
  rw [ENNReal.coe_inv hr, ← ENNReal.div_eq_inv_mul, ENNReal.eq_div_iff _ ENNReal.coe_ne_top, h]
  norm_cast
/-
**Similar._root_.similar_comm** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.similar_comm : v₁ ∼ v₂ ↔ v₂ ∼ v₁ := ⟨Similar.symm, Similar.symm⟩
/-
**Similar.trans** 是 Mathlib 中的一个定理，位于命名空间 `Similar`。
形式化陈述：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {P₃ : Type u_5} {v₁ : ι →
 P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}   [inst : PseudoEMetricSpace P₁] [inst_1 : Pseu
doEMetricSpace P₂] [inst_2 : PseudoEMetricSpace P₃],   Similar v₁ v₂ → Similar v
₂ v₃ → Similar v₁ v₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
@[trans] protected lemma trans (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃) : v₁ ∼ v₃ := by
  rcases h₁ with ⟨r₁, hr₁, h₁⟩; rcases h₂ with ⟨r₂, hr₂, h₂⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun _ _ => ?_⟩
  rw [ENNReal.coe_mul, mul_assoc, h₁, h₂]

/-- Change the index set ι to an index ι' that maps to ι. -/
/-
**Similar.index_map** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：index_map (h : v₁ ∼ v₂) (f : ι' -> ι) : (v₁ ∘ f) ∼ (v₂ ∘ f)
参数：h : v₁ ∼ v₂；f : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the index set ι to an index ι' that maps to ι.
-/
lemma index_map (h : v₁ ∼ v₂) (f : ι' → ι) : (v₁ ∘ f) ∼ (v₂ ∘ f) := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun _ _ => ?_⟩
  apply h

/-- Change between equivalent index sets ι and ι'. -/
@[simp]
/-
**Similar.index_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：index_equiv (f : ι' ≃ ι) (v₁ : ι -> P₁) (v₂ : ι -> P₂) : v₁ ∘ f ∼ v₂ ∘ f ↔
 v₁ ∼ v₂
参数：f : ι' ≃ ι；v₁ : ι -> P₁；v₂ : ι -> P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `Similar.index_map`：index_map (h : v₁ ∼ v₂) (f : ι' -> ι) : (v₁ ∘ f) ∼ (v
₂ ∘ f)

--- 原说明 ---
Change between equivalent index sets ι and ι'.
-/
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι → P₁) (v₂ : ι → P₂) :
    v₁ ∘ f ∼ v₂ ∘ f ↔ v₁ ∼ v₂ := by
  refine ⟨fun h => ?_, fun h => Similar.index_map h f⟩
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂)

/-- Families with at most a single point are always similar. -/
@[nontriviality, simp]
/-
**Similar.of_subsingleton_index** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：of_subsingleton_index [Subsingleton ι] : v₁ ∼ v₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Congruent.similar`：Congruent.similar {v₁ : ι -> P₁} {v₂ : ι -> P₂} (h : 
Congruent v₁ v₂) : Similar v₁ v₂
· 使用引理 `Congruent.of_subsingleton_index`：of_subsingleton_index [Subsingleton ι] 
: v₁ ≅ v₂

--- 原说明 ---
Families with at most a single point are always similar.
-/
lemma of_subsingleton_index [Subsingleton ι] : v₁ ∼ v₂ :=
  Congruent.of_subsingleton_index.similar

/-! Similarity is preserved under dilations. -/

section Dilation
variable {F}

/-
**Similar.comp_left** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_left [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) (h : v₁ ∼ v₂) 
: f ∘ v₁ ∼ v₂
参数：f : F；h : v₁ ∼ v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Similar.trans`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {P₃ : Ty
pe u_5} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}   [inst : PseudoEMetricSpace P
₁] …
· 使用定理 `Dilation.ratio_ne_zero`：ratio_ne_zero [DilationClass F α β] (f : F) : ra
tio f != 0
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
-/
lemma comp_left [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) (h : v₁ ∼ v₂) :
    f ∘ v₁ ∼ v₂ :=
  .trans ⟨Dilation.ratio f, Dilation.ratio_ne_zero f, fun _ _ => Dilation.edist_eq f _ _⟩ h
/-
**Similar.comp_right** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_right [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) (h : v₁ ∼ v₂)
 : v₁ ∼ f ∘ v₂
参数：f : F；h : v₁ ∼ v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Similar.symm`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ : ι →
 P₁} {v₂ : ι → P₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetricSpace
 P…
· 使用引理 `Similar.comp_left`：comp_left [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (
f : F) (h : v₁ ∼ v₂) : f ∘ v₁ ∼ v₂
-/
lemma comp_right [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂ :=
  .symm (h.symm.comp_left f)

@[simp]
/-
**Similar.comp_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_left_iff [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) : f ∘ v₁ ∼
 v₂ ↔ v₁ ∼ v₂
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Similar.trans`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {P₃ : Ty
pe u_5} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}   [inst : PseudoEMetricSpace P
₁] …
· 使用引理 `Similar.comp_right`：comp_right [FunLike F P₂ P₃] [DilationClass F P₂ P₃]
 (f : F) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂
· 使用定理 `Similar.refl`：∀ {ι : Type u_1} {P₁ : Type u_3} [inst : PseudoEMetricSpac
e P₁] (v₁ : ι → P₁), Similar v₁ v₁
· 使用引理 `Similar.comp_left`：comp_left [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (
f : F) (h : v₁ ∼ v₂) : f ∘ v₁ ∼ v₂
-/
lemma comp_left_iff [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (f : F) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂ :=
  ⟨.trans <| .comp_right f (.refl _), .comp_left f⟩

@[simp]
/-
**Similar.comp_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_right_iff [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) : v₁ ∼ f 
∘ v₂ ↔ v₁ ∼ v₂
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `similar_comm`：∀ {ι : Type u_1} {P₁ : Type u_3} {P₂ : Type u_4} {v₁ : ι →
 P₁} {v₂ : ι → P₂} [inst : PseudoEMetricSpace P₁]   [inst_1 : PseudoEMetricSpace
 P…
· 使用引理 `Similar.comp_left_iff`：comp_left_iff [FunLike F P₁ P₃] [DilationClass F 
P₁ P₃] (f : F) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma comp_right_iff [FunLike F P₂ P₃] [DilationClass F P₂ P₃] (f : F) : v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂ := by
  rw [similar_comm, comp_left_iff, similar_comm]

end Dilation

/-! Similarity is preserved under isometries.

While these are trivial consequences of the dilation results, they avoid ending up with a
`toDilation` in the expression, and so are easier to apply to plain functions.
If `Dilation` were a predicate like `Isometry` then these would not be needed.
-/

section Isometry

/-
**Similar.comp_isometry_left** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_isometry_left {f : P₁ -> P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : f ∘ v₁
 ∼ v₂
参数：hf : Isometry f；h : v₁ ∼ v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Similar.comp_left`：comp_left [FunLike F P₁ P₃] [DilationClass F P₁ P₃] (
f : F) (h : v₁ ∼ v₂) : f ∘ v₁ ∼ v₂
-/
lemma comp_isometry_left {f : P₁ → P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : f ∘ v₁ ∼ v₂ :=
  comp_left hf.toDilation h
/-
**Similar.comp_isometry_right** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_isometry_right {f : P₂ -> P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : v₁ ∼ 
f ∘ v₂
参数：hf : Isometry f；h : v₁ ∼ v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Similar.comp_right`：comp_right [FunLike F P₂ P₃] [DilationClass F P₂ P₃]
 (f : F) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂
-/
lemma comp_isometry_right {f : P₂ → P₃} (hf : Isometry f) (h : v₁ ∼ v₂) : v₁ ∼ f ∘ v₂ :=
  comp_right hf.toDilation h

@[simp]
/-
**Similar.comp_isometry_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_isometry_left_iff {f : P₁ -> P₃} (hf : Isometry f) : f ∘ v₁ ∼ v₂ ↔ v₁
 ∼ v₂
参数：hf : Isometry f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Similar.comp_left_iff`：comp_left_iff [FunLike F P₁ P₃] [DilationClass F 
P₁ P₃] (f : F) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂
-/
lemma comp_isometry_left_iff {f : P₁ → P₃} (hf : Isometry f) : f ∘ v₁ ∼ v₂ ↔ v₁ ∼ v₂ :=
  comp_left_iff hf.toDilation

@[simp]
/-
**Similar.comp_isometry_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Similar`。
形式化陈述：comp_isometry_right_iff {f : P₂ -> P₃} (hf : Isometry f) : v₁ ∼ f ∘ v₂ ↔ v
₁ ∼ v₂
参数：hf : Isometry f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Similar.comp_right_iff`：comp_right_iff [FunLike F P₂ P₃] [DilationClass 
F P₂ P₃] (f : F) : v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂
-/
lemma comp_isometry_right_iff {f : P₂ → P₃} (hf : Isometry f) : v₁ ∼ f ∘ v₂ ↔ v₁ ∼ v₂ :=
  comp_right_iff hf.toDilation

end Isometry

section Triangle

variable {a b c : P₁} {a' b' c' : P₂}

/-- Swapping the first two vertices preserves similarity. -/
/-
**Similar.comm_left** 是 Mathlib 中的一个定理，位于命名空间 `Similar`。
形式化陈述：comm_left (h : ![a, b, c] ∼ ![a', b', c']) : ![b, a, c] ∼ ![b', a', c']
参数：h : ![a, b, c] ∼ ![a', b', c']。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
Swapping the first two vertices preserves similarity.
-/
theorem comm_left (h : ![a, b, c] ∼ ![a', b', c']) :
    ![b, a, c] ∼ ![b', a', c'] := by
  have hl : ![b, a, c] = ![a, b, c] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![b', a', c'] = ![a', b', c'] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

/-- Swapping the last two vertices preserves similarity. -/
/-
**Similar.comm_right** 是 Mathlib 中的一个定理，位于命名空间 `Similar`。
形式化陈述：comm_right (h : ![a, b, c] ∼ ![a', b', c']) : ![a, c, b] ∼ ![a', c', b']
参数：h : ![a, b, c] ∼ ![a', b', c']。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
Swapping the last two vertices preserves similarity.
-/
theorem comm_right (h : ![a, b, c] ∼ ![a', b', c']) :
    ![a, c, b] ∼ ![a', c', b'] := by
  have hl : ![a, c, b] = ![a, b, c] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have hr : ![a', c', b'] = ![a', b', c'] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]
  grind [index_equiv]

/-- Reversing the order of vertices preserves similarity. -/
/-
**Similar.reverse_of_three** 是 Mathlib 中的一个定理，位于命名空间 `Similar`。
形式化陈述：reverse_of_three (h : ![a, b, c] ∼ ![a', b', c']) : ![c, b, a] ∼ ![c', b',
 a']
参数：h : ![a, b, c] ∼ ![a', b', c']。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Similar.comm_left`：comm_left (h : ![a, b, c] ∼ ![a', b', c']) : ![b, a, 
c] ∼ ![b', a', c']
· 使用定理 `Similar.comm_right`：comm_right (h : ![a, b, c] ∼ ![a', b', c']) : ![a, c
, b] ∼ ![a', c', b']

--- 原说明 ---
Reversing the order of vertices preserves similarity.
-/
theorem reverse_of_three (h : ![a, b, c] ∼ ![a', b', c']) :
    ![c, b, a] ∼ ![c', b', a'] :=
  h.comm_left.comm_right.comm_left

end Triangle

end Similar

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]

/-- Similarity holds if and only if all non-negative distances are proportional. -/
/-
**similar_iff_exists_nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_nndist_eq : Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0
 ∧ forall (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) = r * nndist (v₂ i₁) (v₂ i₂)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Similarity holds if and only if all non-negative distances are proportional.
-/
lemma similar_iff_exists_nndist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) :=
  exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
  fun _ _ => by { rw [edist_nndist, edist_nndist]; norm_cast }

/-- Similarity holds if and only if all non-negative distances between points with different
indices are proportional. -/
/-
**similar_iff_exists_pairwise_nndist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_pairwise_nndist_eq : Similar v₁ v₂ ↔ (exists r : Real>=
0, r != 0 ∧ Pairwise fun i₁ i₂ => (nndist (v₁ i₁) (v₁ i₂) = r * nndist (v₂ i₁) (
v₂ i₂)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Similarity holds if and only if all non-negative distances between points with d
ifferent
indices are proportional.
-/
lemma similar_iff_exists_pairwise_nndist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_edist_eq, edist_nndist]
  exact_mod_cast Iff.rfl

/-- Similarity holds if and only if all distances are proportional. -/
/-
**similar_iff_exists_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_dist_eq : Similar v₁ v₂ ↔ (exists r : Real>=0, r != 0 ∧
 forall (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `similar_iff_exists_nndist_eq`：similar_iff_exists_nndist_eq : Similar v₁ 
v₂ ↔ (exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) =
 r * nndist (v₂ i₁…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y

--- 原说明 ---
Similarity holds if and only if all distances are proportional.
-/
lemma similar_iff_exists_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) :=
  similar_iff_exists_nndist_eq.trans
  (exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
    fun _ _ => by { rw [dist_nndist, dist_nndist]; norm_cast })

/-- Similarity holds if and only if all distances between points with different indices are
proportional. -/
/-
**similar_iff_exists_pairwise_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_pairwise_dist_eq : Similar v₁ v₂ ↔ (exists r : Real>=0,
 r != 0 ∧ Pairwise fun i₁ i₂ => (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂)
))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Similarity holds if and only if all distances between points with different indi
ces are
proportional.
-/
lemma similar_iff_exists_pairwise_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ≥0, r ≠ 0 ∧ Pairwise fun i₁ i₂ ↦ (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_nndist_eq, dist_nndist]
  exact_mod_cast Iff.rfl

/-- Similarity holds if and only if all distances are proportional with a positive real ratio. -/
/-
**similar_iff_exists_pos_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_pos_dist_eq : Similar v₁ v₂ ↔ (exists r : Real, 0 < r ∧
 forall (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `similar_iff_exists_dist_eq`：similar_iff_exists_dist_eq : Similar v₁ v₂ ↔
 (exists r : Real>=0, r != 0 ∧ forall (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = r * d
ist (v₂ i₁) (v₂ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯

--- 原说明 ---
Similarity holds if and only if all distances are proportional with a positive r
eal ratio.
-/
lemma similar_iff_exists_pos_dist_eq : Similar v₁ v₂ ↔
    (∃ r : ℝ, 0 < r ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂))) := by
  rw [similar_iff_exists_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

/-- Similarity holds iff pairwise distances are proportional with a positive ratio. -/
/-
**similar_iff_exists_pos_pairwise_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：similar_iff_exists_pos_pairwise_dist_eq : Similar v₁ v₂ ↔ (exists r : Real
, 0 < r ∧ Pairwise fun i₁ i₂ => (dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂)
))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯

--- 原说明 ---
Similarity holds iff pairwise distances are proportional with a positive ratio.
-/
lemma similar_iff_exists_pos_pairwise_dist_eq :
    Similar v₁ v₂ ↔ (∃ r : ℝ, 0 < r ∧ Pairwise fun i₁ i₂ ↦ (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) := by
  simp_rw [similar_iff_exists_pairwise_dist_eq]
  simp_rw [← pos_iff_ne_zero, NNReal.exists, ← NNReal.coe_pos, NNReal.coe_mk]
  grind

namespace Similar

/-- A similarity scales non-negative distance. Forward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨exists_nndist_eq, _⟩ := similar_iff_exists_nndist_eq

/-- Similarity follows from scaled non-negative distance. Backward direction of
`similar_iff_exists_nndist_eq`. -/
alias ⟨_, of_exists_nndist_eq⟩ := similar_iff_exists_nndist_eq

/-- A similarity scales distance. Forward direction of `similar_iff_exists_dist_eq`. -/
alias ⟨exists_dist_eq, _⟩ := similar_iff_exists_dist_eq

/-- Similarity follows from scaled distance. Backward direction of
`similar_iff_exists_dist_eq`. -/
alias ⟨_, of_exists_dist_eq⟩ := similar_iff_exists_dist_eq

/-- A similarity pairwise scales non-negative distance. Forward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨exists_pairwise_nndist_eq, _⟩ := similar_iff_exists_pairwise_nndist_eq

/-- Similarity follows from pairwise scaled non-negative distance. Backward direction of
`similar_iff_exists_pairwise_nndist_eq`. -/
alias ⟨_, of_exists_pairwise_nndist_eq⟩ := similar_iff_exists_pairwise_nndist_eq

/-- A similarity pairwise scales distance. Forward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨exists_pairwise_dist_eq, _⟩ := similar_iff_exists_pairwise_dist_eq

/-- Similarity follows from pairwise scaled distance. Backward direction of
`similar_iff_exists_pairwise_dist_eq`. -/
alias ⟨_, of_exists_pairwise_dist_eq⟩ := similar_iff_exists_pairwise_dist_eq

/-- Scales distance with positive ratio. Forward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨exists_pos_dist_eq, _⟩ := similar_iff_exists_pos_dist_eq

/-- Similarity from scaled positive distance. Backward direction of
`similar_iff_exists_pos_dist_eq`. -/
alias ⟨_, of_exists_pos_dist_eq⟩ := similar_iff_exists_pos_dist_eq

/-- Scales pairwise distance with positive ratio. Forward of
`similar_iff_exists_pos_pairwise_dist_eq`. -/
alias ⟨exists_pos_pairwise_dist_eq, _⟩ := similar_iff_exists_pos_pairwise_dist_eq

/-- Similarity from scaled pairwise positive distance. Backward of
`similar_iff_exists_pos_pairwise_dist_eq`. -/
alias ⟨_, of_exists_pos_pairwise_dist_eq⟩ := similar_iff_exists_pos_pairwise_dist_eq

end Similar

section Triangle

variable {a b c : P₁} {a' b' c' : P₂}

/-- If two triangles have two pairs of proportional adjacent sides, then the triangles are similar.
-/
/-
**similar_of_dist_mul_eq_dist_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：similar_of_dist_mul_eq_dist_mul_eq (h_ne : dist a b != 0) (h_ne' : dist a'
 b' != 0) (heq1 : dist a b * dist b' c' = dist b c * dist a' b') (heq2 : dist a 
b * dist c' a' = dist c a * dist a' b') : Similar ![a, b, c] ![a', b', c']
参数：h_ne : dist a b != 0；h_ne' : dist a' b' != 0；heq1 : dist a b * dist b' c' = d
ist b c * dist a' b'；heq2 : dist a b * dist c' a' = dist c a * dist a' b'。
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
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Similar.of_exists_pos_pairwise_dist_eq`：∀ {ι : Type u_1} {P₁ : Type u_3}
 {P₂ : Type u_4} {v₁ : ι → P₁} {v₂ : ι → P₂} [inst : PseudoMetricSpace P₁]   [in
st_1 : PseudoMetricSpace P₂]…
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
If two triangles have two pairs of proportional adjacent sides, then the triangl
es are similar.
-/
theorem similar_of_dist_mul_eq_dist_mul_eq (h_ne : dist a b ≠ 0) (h_ne' : dist a' b' ≠ 0)
    (heq1 : dist a b * dist b' c' = dist b c * dist a' b')
    (heq2 : dist a b * dist c' a' = dist c a * dist a' b') :
    Similar ![a, b, c] ![a', b', c'] := by
  set r : ℝ := (dist a b / dist a' b') with hr
  have hr_pos : 0 < r := by positivity
  apply Similar.of_exists_pos_pairwise_dist_eq
  use r
  refine ⟨hr_pos, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

alias similar_of_side_side := similar_of_dist_mul_eq_dist_mul_eq

end Triangle

end PseudoMetricSpace

