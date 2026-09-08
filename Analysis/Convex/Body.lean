/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Convex bodies

This file contains the definition of the type `ConvexBody V`
consisting of
convex, compact, nonempty subsets of a real topological vector space `V`.

`ConvexBody V` is a module over the nonnegative reals (`NNReal`) and a pseudo-metric space.
If `V` is a normed space, `ConvexBody V` is a metric space.

## TODO

- define positive convex bodies, requiring the interior to be nonempty
- introduce support sets
- Characterise the interaction of the distance with algebraic operations, e.g.
  `dist (a • K) (a • L) = ‖a‖ * dist K L`, `dist (a +ᵥ K) (a +ᵥ L) = dist K L`

## Tags

convex, convex body
-/

public section


open scoped Pointwise Topology NNReal

variable {V : Type*}

/-- Let `V` be a real topological vector space. A subset of `V` is a convex body if and only if
it is convex, compact, and nonempty.
-/
/-
**ConvexBody** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(V : Type u_2) → [TopologicalSpace V] → [AddCommMonoid V] → [SMul ℝ V] → T
ype u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `V` be a real topological vector space. A subset of `V` is a convex body if 
and only if
it is convex, compact, and nonempty.
-/
structure ConvexBody (V : Type*) [TopologicalSpace V] [AddCommMonoid V] [SMul ℝ V] where
  /-- The **carrier set** underlying a convex body: the set of points contained in it -/
  carrier : Set V
  /-- A convex body has convex carrier set -/
  convex' : Convex ℝ carrier
  /-- A convex body has compact carrier set -/
  isCompact' : IsCompact carrier
  /-- A convex body has non-empty carrier set -/
  nonempty' : carrier.Nonempty

namespace ConvexBody

section TVS

variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (ConvexBody V) V where
  coe := ConvexBody.carrier
  coe_injective K L h := by
    cases K
    cases L
    congr
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (ConvexBody V) := .ofSetLike (ConvexBody V) V
/-
**ConvexBody.convex** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 : AddCommGroup V] [in
st_2 : _root_.Module ℝ V] (K : ConvexBody V),   Convex ℝ ↑K
参数：K : ConvexBody V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexBody.convex'`：∀ {V : Type u_2} [inst : TopologicalSpace V] [inst_1
 : AddCommMonoid V] [inst_2 : SMul ℝ V] (self : ConvexBody V),   Convex ℝ self.c
arrier
-/
protected theorem convex (K : ConvexBody V) : Convex ℝ (K : Set V) :=
  K.convex'
/-
**ConvexBody.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 : AddCommGroup V] [in
st_2 : _root_.Module ℝ V] (K : ConvexBody V),   IsCompact ↑K
参数：K : ConvexBody V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexBody.isCompact'`：∀ {V : Type u_2} [inst : TopologicalSpace V] [ins
t_1 : AddCommMonoid V] [inst_2 : SMul ℝ V] (self : ConvexBody V),   IsCompact se
lf.carrier
-/
protected theorem isCompact (K : ConvexBody V) : IsCompact (K : Set V) :=
  K.isCompact'
/-
**ConvexBody.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 : AddCommGroup V] [in
st_2 : _root_.Module ℝ V] [T2Space V]   (K : ConvexBody V), IsClosed ↑K
参数：K : ConvexBody V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `ConvexBody.isCompact`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst
_1 : AddCommGroup V] [inst_2 : _root_.Module ℝ V] (K : ConvexBody V),   IsCompac
t ↑K
-/
protected theorem isClosed [T2Space V] (K : ConvexBody V) : IsClosed (K : Set V) :=
  K.isCompact.isClosed
/-
**ConvexBody.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 : AddCommGroup V] [in
st_2 : _root_.Module ℝ V] (K : ConvexBody V),   (↑K).Nonempty
参数：K : ConvexBody V；↑K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexBody.nonempty'`：∀ {V : Type u_2} [inst : TopologicalSpace V] [inst
_1 : AddCommMonoid V] [inst_2 : SMul ℝ V] (self : ConvexBody V),   self.carrier.
Nonempty
-/
protected theorem nonempty (K : ConvexBody V) : (K : Set V).Nonempty :=
  K.nonempty'

@[ext]
/-
**ConvexBody.ext** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 : AddCommGroup V] [in
st_2 : _root_.Module ℝ V]   {K L : ConvexBody V}, ↑K = ↑L → K = L
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {K L : ConvexBody V} (h : (K : Set V) = L) : K = L :=
  SetLike.ext' h

@[simp]
/-
**ConvexBody.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：coe_mk (s : Set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : Set V) = s
参数：s : Set V；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : Set V) = s :=
  rfl

/-- A convex body that is symmetric contains `0`. -/
/-
**ConvexBody.zero_mem_of_symmetric** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：zero_mem_of_symmetric (K : ConvexBody V) (h_symm : forall x in K, -x in K)
 : 0 in K
参数：K : ConvexBody V；h_symm : forall x in K, -x in K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexBody.nonempty`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_
1 : AddCommGroup V] [inst_2 : _root_.Module ℝ V] (K : ConvexBody V),   (↑K).None
mpty
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `convex_iff_forall_pos`：convex_iff_forall_pos : Convex 𝕜 s ↔ forall ⦃x⦄, 
x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
 a • x + b …
· 使用定理 `ConvexBody.convex`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 
: AddCommGroup V] [inst_2 : _root_.Module ℝ V] (K : ConvexBody V),   Convex ℝ ↑K
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
A convex body that is symmetric contains `0`.
-/
theorem zero_mem_of_symmetric (K : ConvexBody V) (h_symm : ∀ x ∈ K, -x ∈ K) : 0 ∈ K := by
  obtain ⟨x, hx⟩ := K.nonempty
  rw [show 0 = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) by simp]
  apply convex_iff_forall_pos.mp K.convex hx (h_symm x hx)
  all_goals linarith

section ContinuousAdd

/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (ConvexBody V) where
  zero := ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩

@[simp, norm_cast]
/-
**ConvexBody.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：coe_zero : (↑(0 : ConvexBody V) : Set V) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : (↑(0 : ConvexBody V) : Set V) = 0 :=
  rfl
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ConvexBody V) :=
  ⟨0⟩

variable [ContinuousAdd V]
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (ConvexBody V) where
  add K L :=
    ⟨K + L, K.convex.add L.convex, K.isCompact.add L.isCompact,
      K.nonempty.add L.nonempty⟩
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (ConvexBody V) where
  smul := nsmulRec

@[simp, norm_cast]
/-
**ConvexBody.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 : AddCommGroup V] [in
st_2 : _root_.Module ℝ V]   [inst_3 : ContinuousAdd V] (n : ℕ) (K : ConvexBody V
), ↑(n • K) = n • ↑K
参数：n : ℕ；K : ConvexBody V；n • K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul : ∀ (n : ℕ) (K : ConvexBody V), ↑(n • K) = n • (K : Set V)
  | 0, _ => rfl
  | (n + 1), K => congr_arg₂ (Set.image2 (· + ·)) (coe_nsmul n K) rfl
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : AddMonoid (ConvexBody V) :=
  SetLike.coe_injective.addMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ coe_nsmul _ _

@[simp, norm_cast]
/-
**ConvexBody.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：coe_add (K L : ConvexBody V) : (↑(K + L) : Set V) = (K : Set V) + L
参数：K L : ConvexBody V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (K L : ConvexBody V) : (↑(K + L) : Set V) = (K : Set V) + L :=
  rfl
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : AddCommMonoid (ConvexBody V) :=
  SetLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ coe_nsmul _ _

end ContinuousAdd

variable [ContinuousSMul ℝ V]

/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℝ (ConvexBody V) where
  smul c K := ⟨c • (K : Set V), K.convex.smul _, K.isCompact.smul _, K.nonempty.smul_set⟩

@[simp, norm_cast]
/-
**ConvexBody.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：coe_smul (c : Real) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set
 V)
参数：c : Real；K : ConvexBody V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (c : ℝ) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl

@[simp, norm_cast]
/-
**ConvexBody.coe_smul'** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：coe_smul' (c : Real>=0) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K :
 Set V)
参数：c : Real>=0；K : ConvexBody V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul' (c : ℝ≥0) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl
/-
**ConvexBody.smul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：smul_le_of_le (K : ConvexBody V) (h_zero : 0 in K) {a b : Real>=0} (h : a 
<= b) : a • K <= b • K
参数：K : ConvexBody V；h_zero : 0 in K；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `ConvexBody.coe_smul'`：coe_smul' (c : Real>=0) (K : ConvexBody V) : (↑(c 
• K) : Set V) = c • (K : Set V)
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `ConvexBody.nonempty`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_
1 : AddCommGroup V] [inst_2 : _root_.Module ℝ V] (K : ConvexBody V),   (↑K).None
mpty
· 使用定理 `Set.zero_subset`：∀ {α : Type u_2} [inst : Zero α] {s : Set α}, 0 ⊆ s ↔ 0
 ∈ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.mem_inv_smul_set_iff₀`：mem_inv_smul_set_iff₀ (ha : a != 0) (A : Set 
β) (x : β) : x in a⁻¹ • A ↔ a • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Convex.mem_smul_of_zero_mem`：Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s
) {x : E} (zero_mem : (0 : E) in s) (hx : x in s) {t : 𝕜} (ht : 1 <= t) : x in t
 • s
· 使用定理 `ConvexBody.convex`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_1 
: AddCommGroup V] [inst_2 : _root_.Module ℝ V] (K : ConvexBody V),   Convex ℝ ↑K
· 使用引理 `le_inv_mul_iff₀`：le_inv_mul_iff₀ (hc : 0 < c) : a <= c⁻¹ * b ↔ c * a <= 
b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_le_of_le (K : ConvexBody V) (h_zero : 0 ∈ K) {a b : ℝ≥0} (h : a ≤ b) :
    a • K ≤ b • K := by
  rw [← SetLike.coe_subset_coe, coe_smul', coe_smul']
  obtain rfl | ha := eq_zero_or_pos a
  · rw [Set.zero_smul_set K.nonempty, Set.zero_subset]
    exact Set.mem_smul_set.mpr ⟨0, h_zero, smul_zero _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rw [← Set.mem_inv_smul_set_iff₀ ha.ne', smul_smul]
    refine Convex.mem_smul_of_zero_mem K.convex h_zero hy (?_ : 1 ≤ a⁻¹ * b)
    rwa [le_inv_mul_iff₀ ha, mul_one]

variable [ContinuousAdd V]
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DistribMulAction ℝ (ConvexBody V) :=
  SetLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

/-- The convex bodies in a fixed space $V$ form a module over the nonnegative reals. -/
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convex bodies in a fixed space $V$ form a module over the nonnegative reals.
-/
noncomputable instance : Module ℝ≥0 (ConvexBody V) where
  add_smul c d K := SetLike.ext' <| Convex.add_smul K.convex c.coe_nonneg d.coe_nonneg
  zero_smul K := SetLike.ext' <| Set.zero_smul_set K.nonempty

end TVS

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] (K L : ConvexBody V)

/-
**ConvexBody.isBounded** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：∀ {V : Type u_1} [inst : SeminormedAddCommGroup V] [inst_1 : NormedSpace ℝ
 V] (K : ConvexBody V), Bornology.IsBounded ↑K
参数：K : ConvexBody V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `ConvexBody.isCompact`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst
_1 : AddCommGroup V] [inst_2 : _root_.Module ℝ V] (K : ConvexBody V),   IsCompac
t ↑K
-/
protected theorem isBounded : Bornology.IsBounded (K : Set V) :=
  K.isCompact.isBounded
/-
**ConvexBody.hausdorffEDist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：hausdorffEDist_ne_top {K L : ConvexBody V} : Metric.hausdorffEDist (K : Se
t V) L != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded`：hausdorffEDist_ne_t
op_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty) (bs : IsBounded s)
 (bt : IsBounded t) : hausdorffEDist s t …
· 使用定理 `ConvexBody.nonempty`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_
1 : AddCommGroup V] [inst_2 : _root_.Module ℝ V] (K : ConvexBody V),   (↑K).None
mpty
· 使用定理 `ConvexBody.isBounded`：∀ {V : Type u_1} [inst : SeminormedAddCommGroup V]
 [inst_1 : NormedSpace ℝ V] (K : ConvexBody V), Bornology.IsBounded ↑K
-/
theorem hausdorffEDist_ne_top {K L : ConvexBody V} : Metric.hausdorffEDist (K : Set V) L ≠ ⊤ := by
  apply_rules [Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded, ConvexBody.nonempty,
    ConvexBody.isBounded]

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top := hausdorffEDist_ne_top

/-- Convex bodies in a fixed seminormed space $V$ form a pseudo-metric space under the Hausdorff
metric. -/
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convex bodies in a fixed seminormed space $V$ form a pseudo-metric space under t
he Hausdorff
metric.
-/
noncomputable instance : PseudoMetricSpace (ConvexBody V) where
  dist K L := Metric.hausdorffDist (K : Set V) L
  dist_self _ := Metric.hausdorffDist_self_zero
  dist_comm _ _ := Metric.hausdorffDist_comm
  dist_triangle _ _ _ := Metric.hausdorffDist_triangle hausdorffEDist_ne_top

@[simp, norm_cast]
/-
**ConvexBody.hausdorffDist_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：hausdorffDist_coe : Metric.hausdorffDist (K : Set V) L = dist K L
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hausdorffDist_coe : Metric.hausdorffDist (K : Set V) L = dist K L :=
  rfl

@[simp, norm_cast]
/-
**ConvexBody.hausdorffEDist_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：hausdorffEDist_coe : Metric.hausdorffEDist (K : Set V) L = edist K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ConvexBody.hausdorffEDist_ne_top`：hausdorffEDist_ne_top {K L : ConvexBod
y V} : Metric.hausdorffEDist (K : Set V) L != ⊤
-/
theorem hausdorffEDist_coe : Metric.hausdorffEDist (K : Set V) L = edist K L := by
  rw [edist_dist]
  exact (ENNReal.ofReal_toReal hausdorffEDist_ne_top).symm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_coe := hausdorffEDist_coe

open Filter

/-- Let `K` be a convex body that contains `0` and let `u n` be a sequence of nonnegative real
numbers that tends to `0`. Then the intersection of the dilated bodies `(1 + u n) • K` is equal
to `K`. -/
/-
**ConvexBody.iInter_smul_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `ConvexBody`。
形式化陈述：iInter_smul_eq_self [T2Space V] {u : Nat -> Real>=0} (K : ConvexBody V) (h
_zero : 0 in K) (hu : Tendsto u atTop (𝓝 0)) : ⋂ n : Nat, (1 + (u n : Real)) • (
K : Set V) = K
参数：K : ConvexBody V；h_zero : 0 in K；hu : Tendsto u atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Bornology.IsBounded.exists_pos_norm_le`：∀ {E : Type u_2} [inst : Seminor
medAddGroup E] {s : Set E}, Bornology.IsBounded s → ∃ R > 0, ∀ x ∈ s, ‖x‖ ≤ R
· 使用定理 `ConvexBody.isBounded`：∀ {V : Type u_1} [inst : SeminormedAddCommGroup V]
 [inst_1 : NormedSpace ℝ V] (K : ConvexBody V), Bornology.IsBounded ↑K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `ConvexBody.isClosed`：∀ {V : Type u_1} [inst : TopologicalSpace V] [inst_
1 : AddCommGroup V] [inst_2 : _root_.Module ℝ V] [T2Space V]   (K : ConvexBody V
), IsClos…
· 使用定理 `SeminormedAddCommGroup.mem_closure_iff`：∀ {E : Type u_4} [inst : Seminor
medAddCommGroup E] {a : E} {s : Set E},   a ∈ closure s ↔ ∀ (ε : ℝ), 0 < ε → ∃ b
 ∈ s, ‖a - b‖ < ε
· 使用定理 `NormedAddCommGroup.tendsto_atTop`：NormedAddCommGroup.tendsto_atTop [None
mpty α] [Preorder α] [IsDirectedOrder α] {β : Type*} [SeminormedAddCommGroup β] 
{f : α -> β} {b : β} :…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `NNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : R
eal>=0} : Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` be a convex body that contains `0` and let `u n` be a sequence of nonneg
ative real
numbers that tends to `0`. Then the intersection of the dilated bodies `(1 + u n
) • K` is equal
to `K`.
-/
theorem iInter_smul_eq_self [T2Space V] {u : ℕ → ℝ≥0} (K : ConvexBody V) (h_zero : 0 ∈ K)
    (hu : Tendsto u atTop (𝓝 0)) :
    ⋂ n : ℕ, (1 + (u n : ℝ)) • (K : Set V) = K := by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨C, hC_pos, hC_bdd⟩ := K.isBounded.exists_pos_norm_le
    rw [← K.isClosed.closure_eq, SeminormedAddCommGroup.mem_closure_iff]
    rw [← NNReal.tendsto_coe, NormedAddCommGroup.tendsto_atTop] at hu
    intro ε hε
    obtain ⟨n, hn⟩ := hu (ε / C) (div_pos hε hC_pos)
    obtain ⟨y, hyK, rfl⟩ := Set.mem_smul_set.mp (Set.mem_iInter.mp h n)
    refine ⟨y, hyK, ?_⟩
    rw [show (1 + u n : ℝ) • y - y = (u n : ℝ) • y by rw [add_smul, one_smul, add_sub_cancel_left],
      norm_smul, Real.norm_eq_abs]
    specialize hn n le_rfl
    rw [lt_div_iff₀' hC_pos, mul_comm, NNReal.coe_zero, sub_zero, Real.norm_eq_abs] at hn
    refine lt_of_le_of_lt ?_ hn
    gcongr; exact hC_bdd _ hyK
  · refine Set.mem_iInter.mpr (fun n => Convex.mem_smul_of_zero_mem K.convex h_zero h ?_)
    exact le_add_of_nonneg_right (by positivity)

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Convex bodies in a fixed normed space `V` form a metric space under the Hausdorff metric. -/
/-
**ConvexBody.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexBody`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convex bodies in a fixed normed space `V` form a metric space under the Hausdorf
f metric.
-/
noncomputable instance : MetricSpace (ConvexBody V) where
  eq_of_dist_eq_zero {K L} hd := ConvexBody.ext <|
    (K.isClosed.hausdorffDist_zero_iff_eq L.isClosed hausdorffEDist_ne_top).1 hd

end NormedAddCommGroup

end ConvexBody

