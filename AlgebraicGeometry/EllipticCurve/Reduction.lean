/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Reduction of Weierstrass curves over local fields

This file defines reduction of Weierstrass curves over local fields, or more generally,
fraction fields of discrete valuation rings.

## Main definitions

* `IsIntegral`: a predicate expressing that a given Weierstrass equation
  has integral coefficients.
* `IsMinimal`: a predicate expressing that a given Weierstrass equation
  has minimal valuation of discriminant among all isomorphic integral Weierstrass equations.
* `reduction`: the reduction of a Weierstrass curve given by a minimal Weierstrass equation,
  which is a Weierstrass curve over the residue field.
* `IsGoodReduction`: a predicate expressing that a given minimal Weierstrass equation
  has valuation of its discriminant equal to zero.

## Main statements

* `exists_isIntegral`: any Weierstrass curve is isomorphic to one given by
  an integral Weierstrass equation.
* `exists_isMinimal`: any Weierstrass curve is isomorphic to one given by
  a minimal Weierstrass equation.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, minimal weierstrass equation, reduction
-/

@[expose] public section

namespace WeierstrassCurve

section Integral

variable (R : Type*) [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

/-- A Weierstrass equation over the fraction field `K` is integral if
it has coefficients in the ring `R`. -/
@[mk_iff]
/-
**WeierstrassCurve.IsIntegral** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurve`。
形式化陈述：(R : Type u_1) → [inst : CommRing R] → {K : Type u_2} → [inst_1 : Field K]
 → [Algebra R K] → WeierstrassCurve K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Weierstrass equation over the fraction field `K` is integral if
it has coefficients in the ring `R`.
-/
class IsIntegral (W : WeierstrassCurve K) : Prop where
  integral : ∃ W_int : WeierstrassCurve R, W = W_int⁄K

/-- An integral model of an integral Weierstrass curve. -/
/-
**WeierstrassCurve.integralModel** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：integralModel (W : WeierstrassCurve K) [hW : IsIntegral R W] : Weierstrass
Curve R
参数：W : WeierstrassCurve K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.IsIntegral.integral`：∀ {R : Type u_1} {inst : CommRing 
R} {K : Type u_2} {inst_1 : Field K} {inst_2 : Algebra R K} {W : WeierstrassCurv
e K}   [self : Weierstrass…

--- 原说明 ---
An integral model of an integral Weierstrass curve.
-/
noncomputable def integralModel (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    WeierstrassCurve R :=
  hW.integral.choose

variable (W : WeierstrassCurve K) [hW : IsIntegral R W]
/-
**WeierstrassCurve.baseChange_integralModel_eq** 是 Mathlib 中的一个引理，位于命名空间 `Weiers
trassCurve`。
形式化陈述：baseChange_integralModel_eq (W : WeierstrassCurve K) [hW : IsIntegral R W]
 : (integralModel R W)⁄K = W
参数：W : WeierstrassCurve K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WeierstrassCurve.IsIntegral.integral`：∀ {R : Type u_1} {inst : CommRing 
R} {K : Type u_2} {inst_1 : Field K} {inst_2 : Algebra R K} {W : WeierstrassCurv
e K}   [self : Weierstrass…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma baseChange_integralModel_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    (integralModel R W)⁄K = W :=
  hW.integral.choose_spec.symm
/-
**WeierstrassCurve.isIntegral_of_exists_lift** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve`。
形式化陈述：isIntegral_of_exists_lift {W : WeierstrassCurve K} (h₁ : exists r₁, (algeb
raMap R K) r₁ = W.a₁) (h₂ : exists r₂, (algebraMap R K) r₂ = W.a₂) (h₃ : exists 
r₃, (algebraMap R K) r₃ = W.a₃) (h₄ : exists r₄, (algebraMap R K) r₄ = W.a₄) (h₆
 : exists r₆, (algebraMap R K) r₆ = W.a₆) : IsIntegral R W
参数：h₁ : exists r₁, (algebraMap R K) r₁ = W.a₁；h₂ : exists r₂, (algebraMap R K) r
₂ = W.a₂；h₃ : exists r₃, (algebraMap R K) r₃ = W.a₃；h₄ : exists r₄, (algebraMap 
R K) r₄ = W.a₄；h₆ : exists r₆, (algebraMap R K) r₆ = W.a₆。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.ext`：∀ {R : Type u} {x y : WeierstrassCurve R}, x.a₁ = 
y.a₁ → x.a₂ = y.a₂ → x.a₃ = y.a₃ → x.a₄ = y.a₄ → x.a₆ = y.a₆ → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.map_a₁`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   (W.map f).a₁ = 
f W.a₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `WeierstrassCurve.map_a₂`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   (W.map f).a₂ = 
f W.a₂
· 使用定理 `WeierstrassCurve.map_a₃`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   (W.map f).a₃ = 
f W.a₃
· 使用定理 `WeierstrassCurve.map_a₄`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   (W.map f).a₄ = 
f W.a₄
· 使用定理 `WeierstrassCurve.map_a₆`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) {A : Type v} [inst_1 : CommRing A] (f : R →+* A),   (W.map f).a₆ = 
f W.a₆
-/
lemma isIntegral_of_exists_lift {W : WeierstrassCurve K}
    (h₁ : ∃ r₁, (algebraMap R K) r₁ = W.a₁)
    (h₂ : ∃ r₂, (algebraMap R K) r₂ = W.a₂)
    (h₃ : ∃ r₃, (algebraMap R K) r₃ = W.a₃)
    (h₄ : ∃ r₄, (algebraMap R K) r₄ = W.a₄)
    (h₆ : ∃ r₆, (algebraMap R K) r₆ = W.a₆) :
    IsIntegral R W := by
  use ⟨h₁.choose, h₂.choose, h₃.choose, h₄.choose, h₆.choose⟩
  ext
  all_goals simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  · apply h₁.choose_spec.symm
  · apply h₂.choose_spec.symm
  · apply h₃.choose_spec.symm
  · apply h₄.choose_spec.symm
  · apply h₆.choose_spec.symm
/-
**WeierstrassCurve.** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Δ_integral_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    ∃ r : R, algebraMap R K r = W.Δ := by
  obtain ⟨W_int, hW_int⟩ : ∃ W_int : WeierstrassCurve R, W = W_int⁄K :=
    IsIntegral.integral
  use W_int.Δ
  rw [hW_int, baseChange, map_Δ]
/-
**WeierstrassCurve.integralModel_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_a₁_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₁ = W.a₁ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_a₂_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₂ = W.a₂ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_a₃_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₃ = W.a₃ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_a₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₄ = W.a₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_a** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_a₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₆ = W.a₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_b₂_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₂ = W.b₂ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_b₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₄ = W.b₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_b₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₆ = W.b₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_b** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_b₈_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₈ = W.b₈ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_c** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_c₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).c₄ = W.c₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_c** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_c₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).c₆ = W.c₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]
/-
**WeierstrassCurve.integralModel_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma integralModel_Δ_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).Δ = W.Δ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

variable [IsDomain R] [ValuationRing R] [IsFractionRing R K]

open ValuationRing

set_option backward.isDefEq.respectTransparency false in
/-
**WeierstrassCurve.exists_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve
`。
形式化陈述：exists_isIntegral (W : WeierstrassCurve K) : exists C : VariableChange K, 
IsIntegral R (C • W)
参数：W : WeierstrassCurve K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.maximum_of_length_pos_mem`：maximum_of_length_pos_mem (h : 0 < l.len
gth) : maximum_of_length_pos h in l
· 使用定理 `List.le_maximum_of_length_pos_of_mem`：le_maximum_of_length_pos_of_mem (h
 : a in l) (w : 0 < l.length) : a <= l.maximum_of_length_pos w
· 使用引理 `WeierstrassCurve.isIntegral_of_exists_lift`：isIntegral_of_exists_lift {W
 : WeierstrassCurve K} (h₁ : exists r₁, (algebraMap R K) r₁ = W.a₁) (h₂ : exists
 r₂, (algebraMap R K) r₂ = W.a₂)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
（共 105 条，此处仅展示前 30 条）
-/
theorem exists_isIntegral (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsIntegral R (C • W) := by
  let l₀ := [W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  let l := l₀.map (fun a ↦ valuation R K a)
  let lmax : ValueGroup R K :=
    l.maximum_of_length_pos (by simp [l₀, l])
  have hlmax_mem : lmax ∈ l :=
    List.maximum_of_length_pos_mem (by simp [l₀, l])
  have hlmax : ∀ v ∈ l, v ≤ lmax := fun v hv ↦
    List.le_maximum_of_length_pos_of_mem hv (by simp [l₀, l])
  by_cases hlmax_le_1 : lmax ≤ 1
  · use ⟨1, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals simpa [← mem_integer_iff, variableChange_def, Valuation.mem_integer_iff]
      using (hlmax _ (by simp [l₀, l])).trans hlmax_le_1
  · have hlmax_ge_1 : lmax ≥ 1 := le_of_not_ge hlmax_le_1
    have h : ∃ a : K, valuation R K a = lmax := by
      let i : ℕ := l.idxOf lmax
      have hi : i < l.length := List.idxOf_lt_length_of_mem hlmax_mem
      use l₀[i]
      have hi₁ : (valuation R K) l₀[i] = l[i] := by simp [l]
      simpa only [hi₁] using (List.getElem_idxOf hi)
    choose a ha using h
    have ha₀ : a ≠ 0 := by
      by_contra ha₀; simp only [ha₀, map_zero] at ha
      exact (ha ▸ hlmax_le_1) zero_le_one
    use ⟨Units.mk0 a ha₀, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals
      apply (mem_integer_iff _ _ _).mp
      simp only [variableChange_def, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, add_zero,
        inv_pow, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply (Valuation.mem_integer_iff _ _).mpr
      simp only [map_mul, map_inv₀, map_pow, ha]
      refine inv_mul_le_one_of_le₀ ?_ zero_le
      refine (hlmax _ (by simp [l₀, l])).trans ?_
    any_goals
      apply le_self_pow hlmax_ge_1.le
      linarith
    rfl

end Integral

section Minimal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

open scoped Classical in
/-- The valuation of the discriminant of a Weierstrass curve `W`,
which is at most 1 if `W` is integral. Zero otherwise. -/
/-
**WeierstrassCurve.valuation_** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation of the discriminant of a Weierstrass curve `W`,
which is at most 1 if `W` is integral. Zero otherwise.
-/
noncomputable def valuation_Δ_aux (W : WeierstrassCurve K) :
    { v : ℤᵐ⁰ // v ≤ 1 } :=
  if h : IsIntegral R W then
    ⟨valuation K (maximalIdeal R) W.Δ, by
      choose r hr using Δ_integral_of_isIntegral R W
      rw [← hr]
      exact valuation_le_one (maximalIdeal R) r⟩
  else ⟨⊥, bot_le⟩
/-
**WeierstrassCurve.valuation_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valuation_Δ_aux_eq_of_isIntegral (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    valuation_Δ_aux R W = valuation K (maximalIdeal R) W.Δ := by
  simp [valuation_Δ_aux, hW]

/-- A Weierstrass equation over the fraction field `K` is minimal if the (multiplicative) valuation
of its discriminant is maximal among all isomorphic integral Weierstrass equations.
We still use 'minimal' for the naming, so as to standardize the naming with Silverman's book. -/
@[mk_iff]
/-
**WeierstrassCurve.IsMinimal** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurve`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     [inst_1 : IsDomain R] →      
 [IsDiscreteValuationRing R] →         {K : Type u_2} → [inst_3 : Field K] → [in
st_4 : Algebra R K] → [IsFractionRing R K] → WeierstrassCurve K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Weierstrass equation over the fraction field `K` is minimal if the (multiplica
tive) valuation
of its discriminant is maximal among all isomorphic integral Weierstrass equatio
ns.
We still use 'minimal' for the naming, so as to standardize the naming with Silv
erman's book.
-/
class IsMinimal (W : WeierstrassCurve K) : Prop where
  val_Δ_maximal :
    MaximalFor
      (fun (C : VariableChange K) ↦ IsIntegral R (C • W))
      (fun (C : VariableChange K) ↦ valuation_Δ_aux R (C • W))
      (1 : VariableChange K)

omit [IsFractionRing R K] in
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {W : WeierstrassCurve K} [IsMinimal R W] :
    IsIntegral R W := by simpa using IsMinimal.val_Δ_maximal.1
/-
**WeierstrassCurve.exists_isMinimal** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`
。
形式化陈述：exists_isMinimal (W : WeierstrassCurve K) : exists C : VariableChange K, I
sMinimal R (C • W)
参数：W : WeierstrassCurve K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximalFor_of_wellFoundedGT`：∀ {ι : Type u_1} {α : Type u_2} [ins
t : Preorder α] [WellFoundedGT α] (P : ι → Prop) (f : ι → α),   (∃ i, P i) → ∃ i
, MaximalFor P f i
· 使用定理 `WeierstrassCurve.exists_isIntegral`：exists_isIntegral (W : WeierstrassCu
rve K) : exists C : VariableChange K, IsIntegral R (C • W)
· 使用定理 `of_isDiscreteValuationRing`：∀ (A : Type u) [inst : CommRing A] [inst_1 :
 IsDomain A] [IsDiscreteValuationRing A], ValuationRing A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WeierstrassCurve.valuation_Δ_aux.congr_simp`：∀ (R : Type u_1) [inst : Co
mmRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u
_2}   [inst_3 : Field K] [inst_4 …
-/
theorem exists_isMinimal (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsMinimal R (C • W) := by
  obtain ⟨C, hC⟩ := exists_maximalFor_of_wellFoundedGT
    (fun (C : VariableChange K) ↦ IsIntegral R (C • W))
    (fun (C : VariableChange K) ↦ valuation_Δ_aux R (C • W))
    (exists_isIntegral R W)
  refine ⟨C, ⟨⟨by simp only [one_smul, hC.1], ?_⟩⟩⟩
  intro j hj; rw [← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [one_smul]
  rw [← smul_assoc]
  exact h

/-- A minimal Weierstrass equation for a given Weierstrass curve over `K`. -/
/-
**WeierstrassCurve.minimal** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：minimal (W : WeierstrassCurve K) : WeierstrassCurve K
参数：W : WeierstrassCurve K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.exists_isMinimal`：exists_isMinimal (W : WeierstrassCurv
e K) : exists C : VariableChange K, IsMinimal R (C • W)

--- 原说明 ---
A minimal Weierstrass equation for a given Weierstrass curve over `K`.
-/
noncomputable def minimal (W : WeierstrassCurve K) : WeierstrassCurve K :=
  (W.exists_isMinimal R).choose • W
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {W : WeierstrassCurve K} :
    IsMinimal R (W.minimal R) := (W.exists_isMinimal R).choose_spec

end Minimal

section Reduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

/-- The reduction of a Weierstrass curve over `K` given by a minimal Weierstrass equation,
which is a Weierstrass curve over the residue field of `R`. -/
/-
**WeierstrassCurve.reduction** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：reduction (W : WeierstrassCurve K) [IsMinimal R W] : WeierstrassCurve (Res
idueField R)
参数：W : WeierstrassCurve K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.instIsIntegralOfIsMinimal`：∀ (R : Type u_1) [inst : Com
mRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u_
2}   [inst_3 : Field K] [inst_4 …
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R

--- 原说明 ---
The reduction of a Weierstrass curve over `K` given by a minimal Weierstrass equ
ation,
which is a Weierstrass curve over the residue field of `R`.
-/
noncomputable def reduction (W : WeierstrassCurve K) [IsMinimal R W] :
    WeierstrassCurve (ResidueField R) :=
  (integralModel R W).map (residue R)

/-- A minimal Weierstrass equation has good reduction if and only if
the valuation of its discriminant is 1. -/
@[mk_iff]
/-
**WeierstrassCurve.HasGoodReduction** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurv
e`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     [inst_1 : IsDomain R] →      
 [IsDiscreteValuationRing R] →         {K : Type u_2} → [inst_3 : Field K] → [in
st_4 : Algebra R K] → [IsFractionRing R K] → WeierstrassCurve K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A minimal Weierstrass equation has good reduction if and only if
the valuation of its discriminant is 1.
-/
class HasGoodReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  goodReduction : valuation K (maximalIdeal R) W.Δ = 1

@[deprecated (since := "2026-03-04")] alias IsGoodReduction := HasGoodReduction
/-
**WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction** 是 Mathlib 中的一个引理，
位于命名空间 `WeierstrassCurve`。
形式化陈述：hasGoodReduction_iff_isElliptic_reduction {W : WeierstrassCurve K} [hW : I
sMinimal R W] : HasGoodReduction R W ↔ (W.reduction R).IsElliptic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `WeierstrassCurve.instIsIntegralOfIsMinimal`：∀ (R : Type u_1) [inst : Com
mRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u_
2}   [inst_3 : Field K] [inst_4 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `WeierstrassCurve.map_Δ`：map_Δ : (W.map f).Δ = f W.Δ
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`：valuation_l
t_one_iff_mem (r : R) : v.valuation K r < 1 ↔ r in v.asIdeal
· 使用定理 `WeierstrassCurve.hasGoodReduction_iff`：∀ (R : Type u_1) [inst : CommRing
 R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u_2}   
[inst_3 : Field K] [inst_4 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.integralModel_Δ_eq`：integralModel_Δ_eq (W : Weierstrass
Curve K) [hW : IsIntegral R W] : algebraMap R K (integralModel R W).Δ = W.Δ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`：valuation_le_one (r
 : R) : v.valuation K r <= 1
· 使用定理 `WeierstrassCurve.isElliptic_iff`：∀ {R : Type u} [inst : CommRing R] (W :
 WeierstrassCurve R), W.IsElliptic ↔ IsUnit W.Δ
-/
lemma hasGoodReduction_iff_isElliptic_reduction {W : WeierstrassCurve K} [hW : IsMinimal R W] :
    HasGoodReduction R W ↔ (W.reduction R).IsElliptic := by
  refine Iff.trans ?_ (W.reduction R).isElliptic_iff.symm
  simp only [reduction, map_Δ, isUnit_iff_ne_zero, ne_eq, residue_eq_zero_iff]
  have h :
      ¬(valuation K (maximalIdeal R) (algebraMap R K (integralModel R W).Δ) < 1)
      ↔ (integralModel R W).Δ ∉ IsLocalRing.maximalIdeal R :=
    not_iff_not.mpr <| valuation_lt_one_iff_mem _ _
  refine ((integralModel_Δ_eq R W ▸ hasGoodReduction_iff _ _).trans ?_).trans h
  simpa [hW] using (valuation_le_one (R := R) (K := K) _ _).ge_iff_eq.symm

@[deprecated (since := "2026-03-04")] alias isGoodReduction_iff_isElliptic_reduction :=
  hasGoodReduction_iff_isElliptic_reduction

/-- A minimal Weierstrass equation has multiplicative reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` equals 1. -/
@[mk_iff]
/-
**WeierstrassCurve.HasMultiplicativeReduction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Weier
strassCurve`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     [inst_1 : IsDomain R] →      
 [IsDiscreteValuationRing R] →         {K : Type u_2} → [inst_3 : Field K] → [in
st_4 : Algebra R K] → [IsFractionRing R K] → WeierstrassCurve K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A minimal Weierstrass equation has multiplicative reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` equal
s 1.
-/
class HasMultiplicativeReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  badReduction : valuation K (maximalIdeal R) W.Δ < 1
  multiplicativeReduction : valuation K (maximalIdeal R) W.c₄ = 1

/-- A minimal Weierstrass equation has additive reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` is less than 1. -/
@[mk_iff]
/-
**WeierstrassCurve.HasAdditiveReduction** 是 Mathlib 中的一个归纳类型，位于命名空间 `Weierstrass
Curve`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     [inst_1 : IsDomain R] →      
 [IsDiscreteValuationRing R] →         {K : Type u_2} → [inst_3 : Field K] → [in
st_4 : Algebra R K] → [IsFractionRing R K] → WeierstrassCurve K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A minimal Weierstrass equation has additive reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` is le
ss than 1.
-/
class HasAdditiveReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  badReduction : valuation K (maximalIdeal R) W.Δ < 1
  additiveReduction : valuation K (maximalIdeal R) W.c₄ < 1

-- TODO: add characterization in terms of the discriminant when the characteristic is not 2
open Polynomial in
/-- A minimal Weierstrass equation has split multiplicative reduction if and only if
the polynomial `c₄ T ^ 2 + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` splits in the residue field.

To see how this expression arises, note that the node `(x₀, y₀)` has second order Taylor expansion
`(Y - y₀)^2 + a_1(X - x₀)(Y - y₀) - (3x₀ + a_2)(X - x₀)^2` where `x₀ = (18 b₆ - b₂ b₄) / c₄`. -/
@[mk_iff]
/-
**WeierstrassCurve.HasSplitMultiplicativeReduction** 是 Mathlib 中的一个类，位于命名空间 `Wei
erstrassCurve`。
形式化陈述：HasSplitMultiplicativeReduction (W : WeierstrassCurve K) : Prop extends W.
HasMultiplicativeReduction R where splitMultiplicativeReduction : letI I
参数：W : WeierstrassCurve K。
继承自：W.HasMultiplicativeReduction R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A minimal Weierstrass equation has split multiplicative reduction if and only if
the polynomial `c₄ T ^ 2 + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` splits in the re
sidue field.

To see how this expression arises, note that the node `(x₀, y₀)` has second orde
r Taylor expansion
`(Y - y₀)^2 + a_1(X - x₀)(Y - y₀) - (3x₀ + a_2)(X - x₀)^2` where `x₀ = (18 b₆ - 
b₂ b₄) / c₄`.
-/
class HasSplitMultiplicativeReduction (W : WeierstrassCurve K) : Prop
    extends W.HasMultiplicativeReduction R where
  splitMultiplicativeReduction : letI I := W.integralModel R
    Splits <| .map (algebraMap R (ResidueField R)) <|
      C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X - C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)

variable {W : WeierstrassCurve K}
/-
**WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditive
Reduction** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
形式化陈述：hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction [Is
Minimal R W] : W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R ∨ W.HasAddi
tiveReduction R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.hasGoodReduction_iff`：∀ (R : Type u_1) [inst : CommRing
 R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u_2}   
[inst_3 : Field K] [inst_4 …
· 使用定理 `WeierstrassCurve.hasMultiplicativeReduction_iff`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Ty
pe u_2}   [inst_3 : Field K] [inst_4 …
· 使用定理 `WeierstrassCurve.hasAdditiveReduction_iff`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u_2
}   [inst_3 : Field K] [inst_4 …
· 使用定理 `WeierstrassCurve.instIsIntegralOfIsMinimal`：∀ (R : Type u_1) [inst : Com
mRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] {K : Type u_
2}   [inst_3 : Field K] [inst_4 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeierstrassCurve.integralModel_Δ_eq`：integralModel_Δ_eq (W : Weierstrass
Curve K) [hW : IsIntegral R W] : algebraMap R K (integralModel R W).Δ = W.Δ
· 使用引理 `WeierstrassCurve.integralModel_c₄_eq`：integralModel_c₄_eq (W : Weierstra
ssCurve K) [hW : IsIntegral R W] : algebraMap R K (integralModel R W).c₄ = W.c₄
-/
theorem hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction [IsMinimal R W] :
    W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R ∨ W.HasAdditiveReduction R := by
  rw [hasGoodReduction_iff, hasMultiplicativeReduction_iff, hasAdditiveReduction_iff,
    ← integralModel_Δ_eq R W, ← integralModel_c₄_eq R W]
  grind [valuation_le_one]
/-
**WeierstrassCurve.HasGoodReduction.not_hasMultiplicativeReduction** 是 Mathlib 中
的一个定理，位于命名空间 `WeierstrassCurve.HasGoodReduction`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra R K]
 [inst_5 : IsFractionRing R K] {W : WeierstrassCurve K},   WeierstrassCurve.HasG
oodReduction R W → ¬WeierstrassCurve.HasMultiplicativeReduction R W
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `WeierstrassCurve.HasMultiplicativeReduction.badReduction`：∀ {R : Type u_
1} {inst : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R
} {K : Type u_2}   {inst_3 : Field K} {inst_4 …
· 使用定理 `WeierstrassCurve.HasGoodReduction.goodReduction`：∀ {R : Type u_1} {inst 
: CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R} {K : Ty
pe u_2}   {inst_3 : Field K} {inst_4 …
-/
theorem HasGoodReduction.not_hasMultiplicativeReduction (hW : W.HasGoodReduction R) :
    ¬ W.HasMultiplicativeReduction R :=
  fun h ↦ h.badReduction.ne hW.goodReduction
/-
**WeierstrassCurve.HasGoodReduction.not_hasAdditiveReduction** 是 Mathlib 中的一个定理，
位于命名空间 `WeierstrassCurve.HasGoodReduction`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra R K]
 [inst_5 : IsFractionRing R K] {W : WeierstrassCurve K},   WeierstrassCurve.HasG
oodReduction R W → ¬WeierstrassCurve.HasAdditiveReduction R W
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `WeierstrassCurve.HasAdditiveReduction.badReduction`：∀ {R : Type u_1} {in
st : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R} {K :
 Type u_2}   {inst_3 : Field K} {inst_4 …
· 使用定理 `WeierstrassCurve.HasGoodReduction.goodReduction`：∀ {R : Type u_1} {inst 
: CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R} {K : Ty
pe u_2}   {inst_3 : Field K} {inst_4 …
-/
theorem HasGoodReduction.not_hasAdditiveReduction (hW : W.HasGoodReduction R) :
    ¬ W.HasAdditiveReduction R :=
  fun h ↦ h.badReduction.ne hW.goodReduction
/-
**WeierstrassCurve.HasMultiplicativeReduction.not_hasGoodReduction** 是 Mathlib 中
的一个定理，位于命名空间 `WeierstrassCurve.HasMultiplicativeReduction`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra R K]
 [inst_5 : IsFractionRing R K] {W : WeierstrassCurve K},   WeierstrassCurve.HasM
ultiplicativeReduction R W → ¬WeierstrassCurve.HasGoodReduction R W
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `WeierstrassCurve.HasMultiplicativeReduction.badReduction`：∀ {R : Type u_
1} {inst : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R
} {K : Type u_2}   {inst_3 : Field K} {inst_4 …
· 使用定理 `WeierstrassCurve.HasGoodReduction.goodReduction`：∀ {R : Type u_1} {inst 
: CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R} {K : Ty
pe u_2}   {inst_3 : Field K} {inst_4 …
-/
theorem HasMultiplicativeReduction.not_hasGoodReduction (hW : W.HasMultiplicativeReduction R) :
    ¬ W.HasGoodReduction R :=
  fun h ↦ hW.badReduction.ne h.goodReduction
/-
**WeierstrassCurve.HasAdditiveReduction.not_hasGoodReduction** 是 Mathlib 中的一个定理，
位于命名空间 `WeierstrassCurve.HasAdditiveReduction`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra R K]
 [inst_5 : IsFractionRing R K] {W : WeierstrassCurve K},   WeierstrassCurve.HasA
dditiveReduction R W → ¬WeierstrassCurve.HasGoodReduction R W
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `WeierstrassCurve.HasAdditiveReduction.badReduction`：∀ {R : Type u_1} {in
st : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R} {K :
 Type u_2}   {inst_3 : Field K} {inst_4 …
· 使用定理 `WeierstrassCurve.HasGoodReduction.goodReduction`：∀ {R : Type u_1} {inst 
: CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R} {K : Ty
pe u_2}   {inst_3 : Field K} {inst_4 …
-/
theorem HasAdditiveReduction.not_hasGoodReduction (hW : W.HasAdditiveReduction R) :
    ¬ W.HasGoodReduction R :=
  fun h ↦ hW.badReduction.ne h.goodReduction
/-
**WeierstrassCurve.HasMultiplicativeReduction.not_hasAdditiveReduction** 是 Mathl
ib 中的一个定理，位于命名空间 `WeierstrassCurve.HasMultiplicativeReduction`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra R K]
 [inst_5 : IsFractionRing R K] {W : WeierstrassCurve K},   WeierstrassCurve.HasM
ultiplicativeReduction R W → ¬WeierstrassCurve.HasAdditiveReduction R W
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `WeierstrassCurve.HasAdditiveReduction.additiveReduction`：∀ {R : Type u_1
} {inst : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R}
 {K : Type u_2}   {inst_3 : Field K} {inst_4 …
· 使用定理 `WeierstrassCurve.HasMultiplicativeReduction.multiplicativeReduction`：∀ {
R : Type u_1} {inst : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValu
ationRing R} {K : Type u_2}   {inst_3 : Field K} {inst_4 …
-/
theorem HasMultiplicativeReduction.not_hasAdditiveReduction (hW : W.HasMultiplicativeReduction R) :
    ¬ W.HasAdditiveReduction R :=
  fun h ↦ h.additiveReduction.ne hW.multiplicativeReduction
/-
**WeierstrassCurve.HasAdditiveReduction.not_hasMultiplicativeReduction** 是 Mathl
ib 中的一个定理，位于命名空间 `WeierstrassCurve.HasAdditiveReduction`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] {K : Type u_2}   [inst_3 : Field K] [inst_4 : Algebra R K]
 [inst_5 : IsFractionRing R K] {W : WeierstrassCurve K},   WeierstrassCurve.HasA
dditiveReduction R W → ¬WeierstrassCurve.HasMultiplicativeReduction R W
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `WeierstrassCurve.HasAdditiveReduction.additiveReduction`：∀ {R : Type u_1
} {inst : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValuationRing R}
 {K : Type u_2}   {inst_3 : Field K} {inst_4 …
· 使用定理 `WeierstrassCurve.HasMultiplicativeReduction.multiplicativeReduction`：∀ {
R : Type u_1} {inst : CommRing R} {inst_1 : IsDomain R} {inst_2 : IsDiscreteValu
ationRing R} {K : Type u_2}   {inst_3 : Field K} {inst_4 …
-/
theorem HasAdditiveReduction.not_hasMultiplicativeReduction (hW : W.HasAdditiveReduction R) :
    ¬ W.HasMultiplicativeReduction R :=
  fun h ↦ hW.additiveReduction.ne h.multiplicativeReduction

end Reduction

end WeierstrassCurve

