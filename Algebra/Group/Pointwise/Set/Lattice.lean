/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Indexed unions and intersections of pointwise operations of sets

This file contains lemmas on taking the union and intersection over pointwise algebraic operations
on sets.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

assert_not_exists MulAction MonoidWithZero

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### Set negation/inversion -/

open scoped Pointwise

section Inv

variable {ι : Sort*} [Inv α]

@[to_additive (attr := simp)]
/-
**Set.iInter_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_inv (s : ι -> Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iInter`：preimage_iInter {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i
-/
theorem iInter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_iInter

@[to_additive (attr := simp)]
/-
**Set.sInter_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_inv (S : Set (Set α)) : (⋂₀ S)⁻¹ = ⋂ s in S, s⁻¹
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_sInter`：preimage_sInter {f : α -> β} {s : Set (Set β)} : f 
⁻¹' ⋂₀ s = ⋂ t in s, f ⁻¹' t
-/
theorem sInter_inv (S : Set (Set α)) : (⋂₀ S)⁻¹ = ⋂ s ∈ S, s⁻¹ :=
  preimage_sInter

@[to_additive (attr := simp)]
/-
**Set.iUnion_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_inv (s : ι -> Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
-/
theorem iUnion_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_iUnion

@[to_additive (attr := simp)]
/-
**Set.sUnion_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_inv (S : Set (Set α)) : (⋃₀ S)⁻¹ = ⋃ s in S, s⁻¹
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_sUnion`：preimage_sUnion {f : α -> β} {s : Set (Set β)} : f 
⁻¹' ⋃₀ s = ⋃ t in s, f ⁻¹' t
-/
theorem sUnion_inv (S : Set (Set α)) : (⋃₀ S)⁻¹ = ⋃ s ∈ S, s⁻¹ :=
  preimage_sUnion

end Inv

/-! ### Set addition/multiplication -/
section Mul

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

@[to_additive]
/-
**Set.iUnion_mul_left_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_mul_left_image : ⋃ a in s, (a * ·) '' t = s * t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
theorem iUnion_mul_left_image : ⋃ a ∈ s, (a * ·) '' t = s * t :=
  iUnion_image_left _

@[to_additive]
/-
**Set.iUnion_mul_right_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_mul_right_image : ⋃ a in t, (· * a) '' s = s * t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
-/
theorem iUnion_mul_right_image : ⋃ a ∈ t, (· * a) '' s = s * t :=
  iUnion_image_right _

@[to_additive]
/-
**Set.iUnion_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_mul (s : ι -> Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t
参数：s : ι -> Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_left`：image2_iUnion_left (s : ι -> Set α) (t : Set β) 
: image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t
-/
theorem iUnion_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_iUnion_left ..

@[to_additive]
/-
**Set.mul_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mul_iUnion (s : Set α) (t : ι -> Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i
参数：s : Set α；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
theorem mul_iUnion (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_iUnion_right ..

@[to_additive]
/-
**Set.sUnion_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_mul (S : Set (Set α)) (t : Set α) : ⋃₀ S * t = ⋃ s in S, s * t
参数：S : Set (Set α)；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_left`：image2_sUnion_left (S : Set (Set α)) (t : Set β)
 : image2 f (⋃₀ S) t = ⋃ s in S, image2 f s t
-/
theorem sUnion_mul (S : Set (Set α)) (t : Set α) : ⋃₀ S * t = ⋃ s ∈ S, s * t :=
  image2_sUnion_left ..

@[to_additive]
/-
**Set.mul_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mul_sUnion (s : Set α) (T : Set (Set α)) : s * ⋃₀ T = ⋃ t in T, s * t
参数：s : Set α；T : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_right`：image2_sUnion_right (s : Set α) (T : Set (Set β
)) : image2 f s (⋃₀ T) = ⋃ t in T, image2 f s t
-/
theorem mul_sUnion (s : Set α) (T : Set (Set α)) : s * ⋃₀ T = ⋃ t ∈ T, s * t :=
  image2_sUnion_right ..

@[to_additive]
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_mul (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_iUnion₂_left ..

@[to_additive]
/-
**Set.mul_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mul_iUnion (s : Set α) (t : ι -> Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i
参数：s : Set α；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
theorem mul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_iUnion₂_right ..

@[to_additive]
/-
**Set.iInter_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_mul_subset (s : ι -> Set α) (t : Set α) : (⋂ i, s i) * t subseteq ⋂
 i, s i * t
参数：s : ι -> Set α；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_left`：image2_iInter_subset_left (s : ι -> Set α
) (t : Set β) : image2 f (⋂ i, s i) t subseteq ⋂ i, image2 f (s i) t
-/
theorem iInter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  Set.image2_iInter_subset_left ..

@[to_additive]
/-
**Set.mul_iInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mul_iInter_subset (s : Set α) (t : ι -> Set α) : (s * ⋂ i, t i) subseteq ⋂
 i, s * t i
参数：s : Set α；t : ι -> Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_right`：image2_iInter_subset_right (s : Set α) (
t : ι -> Set β) : image2 f s (⋂ i, t i) subseteq ⋂ i, image2 f s (t i)
-/
theorem mul_iInter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_iInter_subset_right ..

@[to_additive]
/-
**Set.mul_sInter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mul_sInter_subset (s : Set α) (T : Set (Set α)) : s * ⋂₀ T subseteq ⋂ t in
 T, s * t
参数：s : Set α；T : Set (Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_right_subset`：image2_sInter_right_subset (t : Set α) (
S : Set (Set β)) (f : α -> β -> γ) : image2 f t (⋂₀ S) subseteq ⋂ s in S, image2
 f t s
-/
lemma mul_sInter_subset (s : Set α) (T : Set (Set α)) :
    s * ⋂₀ T ⊆ ⋂ t ∈ T, s * t := image2_sInter_right_subset s T (fun a b => a * b)

@[to_additive]
/-
**Set.sInter_mul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sInter_mul_subset (S : Set (Set α)) (t : Set α) : ⋂₀ S * t subseteq ⋂ s in
 S, s * t
参数：S : Set (Set α)；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_left_subset`：image2_sInter_left_subset (S : Set (Set α
)) (t : Set β) (f : α -> β -> γ) : image2 f (⋂₀ S) t subseteq ⋂ s in S, image2 f
 s t
-/
lemma sInter_mul_subset (S : Set (Set α)) (t : Set α) :
    ⋂₀ S * t ⊆ ⋂ s ∈ S, s * t := image2_sInter_left_subset S t (fun a b => a * b)

@[to_additive]
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_iInter₂_subset_left ..

@[to_additive]
/-
**Set.mul_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_iInter₂_subset_right ..

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

@[to_additive]
/-
**Set.iUnion_div_left_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_div_left_image : ⋃ a in s, (a / ·) '' t = s / t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
theorem iUnion_div_left_image : ⋃ a ∈ s, (a / ·) '' t = s / t :=
  iUnion_image_left _

@[to_additive]
/-
**Set.iUnion_div_right_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_div_right_image : ⋃ a in t, (· / a) '' s = s / t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
-/
theorem iUnion_div_right_image : ⋃ a ∈ t, (· / a) '' s = s / t :=
  iUnion_image_right _

@[to_additive]
/-
**Set.iUnion_div** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_div (s : ι -> Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t
参数：s : ι -> Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_left`：image2_iUnion_left (s : ι -> Set α) (t : Set β) 
: image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t
-/
theorem iUnion_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_iUnion_left ..

@[to_additive]
/-
**Set.div_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：div_iUnion (s : Set α) (t : ι -> Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i
参数：s : Set α；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
theorem div_iUnion (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_iUnion_right ..

@[to_additive]
/-
**Set.sUnion_div** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_div (S : Set (Set α)) (t : Set α) : ⋃₀ S / t = ⋃ s in S, s / t
参数：S : Set (Set α)；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_left`：image2_sUnion_left (S : Set (Set α)) (t : Set β)
 : image2 f (⋃₀ S) t = ⋃ s in S, image2 f s t
-/
theorem sUnion_div (S : Set (Set α)) (t : Set α) : ⋃₀ S / t = ⋃ s ∈ S, s / t :=
  image2_sUnion_left ..

@[to_additive]
/-
**Set.div_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：div_sUnion (s : Set α) (T : Set (Set α)) : s / ⋃₀ T = ⋃ t in T, s / t
参数：s : Set α；T : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_right`：image2_sUnion_right (s : Set α) (T : Set (Set β
)) : image2 f s (⋃₀ T) = ⋃ t in T, image2 f s t
-/
theorem div_sUnion (s : Set α) (T : Set (Set α)) : s / ⋃₀ T = ⋃ t ∈ T, s / t :=
  image2_sUnion_right ..

@[to_additive]
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnion₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_iUnion₂_left ..

@[to_additive]
/-
**Set.div_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：div_iUnion (s : Set α) (t : ι -> Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i
参数：s : Set α；t : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
theorem div_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_iUnion₂_right ..

@[to_additive]
/-
**Set.iInter_div_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_div_subset (s : ι -> Set α) (t : Set α) : (⋂ i, s i) / t subseteq ⋂
 i, s i / t
参数：s : ι -> Set α；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_left`：image2_iInter_subset_left (s : ι -> Set α
) (t : Set β) : image2 f (⋂ i, s i) t subseteq ⋂ i, image2 f (s i) t
-/
theorem iInter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_iInter_subset_left ..

@[to_additive]
/-
**Set.div_iInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：div_iInter_subset (s : Set α) (t : ι -> Set α) : (s / ⋂ i, t i) subseteq ⋂
 i, s / t i
参数：s : Set α；t : ι -> Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_right`：image2_iInter_subset_right (s : Set α) (
t : ι -> Set β) : image2 f s (⋂ i, t i) subseteq ⋂ i, image2 f s (t i)
-/
theorem div_iInter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_iInter_subset_right ..

@[to_additive]
/-
**Set.sInter_div_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sInter_div_subset (S : Set (Set α)) (t : Set α) : ⋂₀ S / t subseteq ⋂ s in
 S, s / t
参数：S : Set (Set α)；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_subset_left`：image2_sInter_subset_left (S : Set (Set α
)) (t : Set β) : image2 f (⋂₀ S) t subseteq ⋂ s in S, image2 f s t
-/
theorem sInter_div_subset (S : Set (Set α)) (t : Set α) : ⋂₀ S / t ⊆ ⋂ s ∈ S, s / t :=
  image2_sInter_subset_left ..

@[to_additive]
/-
**Set.div_sInter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：div_sInter_subset (s : Set α) (T : Set (Set α)) : s / ⋂₀ T subseteq ⋂ t in
 T, s / t
参数：s : Set α；T : Set (Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_subset_right`：image2_sInter_subset_right (s : Set α) (
T : Set (Set β)) : image2 f s (⋂₀ T) subseteq ⋂ t in T, image2 f s t
-/
theorem div_sInter_subset (s : Set α) (T : Set (Set α)) : s / ⋂₀ T ⊆ ⋂ t ∈ T, s / t :=
  image2_sInter_subset_right ..

@[to_additive]
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_iInter₂_subset_left ..

@[to_additive]
/-
**Set.div_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_iInter₂_subset_right ..

end Div

/-! ### Translation/scaling of sets -/

section SMul

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

/-
**Set.iUnion_smul_left_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : Set α} {t : Set β},
 ⋃ a ∈ s, a • t = s • t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
@[to_additive] lemma iUnion_smul_left_image : ⋃ a ∈ s, a • t = s • t := iUnion_image_left _

@[to_additive]
/-
**Set.iUnion_smul_right_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_smul_right_image : ⋃ a in t, (· • a) '' s = s • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
-/
lemma iUnion_smul_right_image : ⋃ a ∈ t, (· • a) '' s = s • t := iUnion_image_right _

@[to_additive]
/-
**Set.iUnion_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_smul (s : ι -> Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t
参数：s : ι -> Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_left`：image2_iUnion_left (s : ι -> Set α) (t : Set β) 
: image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t
-/
lemma iUnion_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_iUnion_left ..

@[to_additive]
/-
**Set.smul_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_iUnion (s : Set α) (t : ι -> Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i
参数：s : Set α；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
lemma smul_iUnion (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_iUnion_right ..

@[to_additive]
/-
**Set.sUnion_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sUnion_smul (S : Set (Set α)) (t : Set β) : ⋃₀ S • t = ⋃ s in S, s • t
参数：S : Set (Set α)；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_left`：image2_sUnion_left (S : Set (Set α)) (t : Set β)
 : image2 f (⋃₀ S) t = ⋃ s in S, image2 f s t
-/
lemma sUnion_smul (S : Set (Set α)) (t : Set β) : ⋃₀ S • t = ⋃ s ∈ S, s • t :=
  image2_sUnion_left ..

@[to_additive]
/-
**Set.smul_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_sUnion (s : Set α) (T : Set (Set β)) : s • ⋃₀ T = ⋃ t in T, s • t
参数：s : Set α；T : Set (Set β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_right`：image2_sUnion_right (s : Set α) (T : Set (Set β
)) : image2 f s (⋃₀ T) = ⋃ t in T, image2 f s t
-/
lemma smul_sUnion (s : Set α) (T : Set (Set β)) : s • ⋃₀ T = ⋃ t ∈ T, s • t :=
  image2_sUnion_right ..

@[to_additive]
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iUnion₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ i, ⋃ j, s i j) • t = ⋃ i, ⋃ j, s i j • t := image2_iUnion₂_left ..

@[to_additive]
/-
**Set.smul_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_iUnion (s : Set α) (t : ι -> Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i
参数：s : Set α；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
lemma smul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s • t i j := image2_iUnion₂_right ..

@[to_additive]
/-
**Set.iInter_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_smul_subset (s : ι -> Set α) (t : Set β) : (⋂ i, s i) • t subseteq 
⋂ i, s i • t
参数：s : ι -> Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_left`：image2_iInter_subset_left (s : ι -> Set α
) (t : Set β) : image2 f (⋂ i, s i) t subseteq ⋂ i, image2 f (s i) t
-/
lemma iInter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_iInter_subset_left ..

@[to_additive]
/-
**Set.smul_iInter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_iInter_subset (s : Set α) (t : ι -> Set β) : (s • ⋂ i, t i) subseteq 
⋂ i, s • t i
参数：s : Set α；t : ι -> Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_right`：image2_iInter_subset_right (s : Set α) (
t : ι -> Set β) : image2 f s (⋂ i, t i) subseteq ⋂ i, image2 f s (t i)
-/
lemma smul_iInter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_iInter_subset_right ..

@[to_additive]
/-
**Set.sInter_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sInter_smul_subset (S : Set (Set α)) (t : Set β) : ⋂₀ S • t subseteq ⋂ s i
n S, s • t
参数：S : Set (Set α)；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_left_subset`：image2_sInter_left_subset (S : Set (Set α
)) (t : Set β) (f : α -> β -> γ) : image2 f (⋂₀ S) t subseteq ⋂ s in S, image2 f
 s t
-/
lemma sInter_smul_subset (S : Set (Set α)) (t : Set β) : ⋂₀ S • t ⊆ ⋂ s ∈ S, s • t :=
  image2_sInter_left_subset S t (fun a x => a • x)

@[to_additive]
/-
**Set.smul_sInter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_sInter_subset (s : Set α) (T : Set (Set β)) : s • ⋂₀ T subseteq ⋂ t i
n T, s • t
参数：s : Set α；T : Set (Set β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_right_subset`：image2_sInter_right_subset (t : Set α) (
S : Set (Set β)) (f : α -> β -> γ) : image2 f t (⋂₀ S) subseteq ⋂ s in S, image2
 f t s
-/
lemma smul_sInter_subset (s : Set α) (T : Set (Set β)) : s • ⋂₀ T ⊆ ⋂ t ∈ T, s • t :=
  image2_sInter_right_subset s T (fun a x => a • x)

@[to_additive]
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iInter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋂ i, ⋂ j, s i j) • t ⊆ ⋂ i, ⋂ j, s i j • t := image2_iInter₂_subset_left ..

@[to_additive]
/-
**Set.smul_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ i, ⋂ j, t i j) ⊆ ⋂ i, ⋂ j, s • t i j := image2_iInter₂_subset_right ..

@[to_additive (attr := simp)]
/-
**Set.iUnion_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s, a • t = s • t
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
lemma iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a ∈ s, a • t = s • t := iUnion_image_left _

end SMul

section SMulSet
variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[to_additive]
/-
**Set.smul_set_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_iUnion (a : α) (s : ι -> Set β) : a • ⋃ i, s i = ⋃ i, a • s i
参数：a : α；s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
-/
lemma smul_set_iUnion (a : α) (s : ι → Set β) : a • ⋃ i, s i = ⋃ i, a • s i :=
  image_iUnion

@[to_additive]
/-
**Set.smul_set_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_iUnion (a : α) (s : ι -> Set β) : a • ⋃ i, s i = ⋃ i, a • s i
参数：a : α；s : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
-/
lemma smul_set_iUnion₂ (a : α) (s : ∀ i, κ i → Set β) :
    a • ⋃ i, ⋃ j, s i j = ⋃ i, ⋃ j, a • s i j := image_iUnion₂ ..

@[to_additive]
/-
**Set.smul_set_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_sUnion (a : α) (S : Set (Set β)) : a • ⋃₀ S = ⋃ s in S, a • s
参数：a : α；S : Set (Set β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用引理 `Set.smul_set_iUnion₂`：smul_set_iUnion₂ (a : α) (s : forall i, κ i -> Set
 β) : a • ⋃ i, ⋃ j, s i j = ⋃ i, ⋃ j, a • s i j
-/
lemma smul_set_sUnion (a : α) (S : Set (Set β)) : a • ⋃₀ S = ⋃ s ∈ S, a • s := by
  rw [sUnion_eq_biUnion, smul_set_iUnion₂]

@[to_additive]
/-
**Set.smul_set_iInter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_iInter_subset (a : α) (t : ι -> Set β) : a • ⋂ i, t i subseteq ⋂ 
i, a • t i
参数：a : α；t : ι -> Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_iInter_subset`：image_iInter_subset (s : ι -> Set α) (f : α -> 
β) : (f '' ⋂ i, s i) subseteq ⋂ i, f '' s i
-/
lemma smul_set_iInter_subset (a : α) (t : ι → Set β) : a • ⋂ i, t i ⊆ ⋂ i, a • t i :=
  image_iInter_subset ..

@[to_additive]
/-
**Set.smul_set_sInter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_sInter_subset (a : α) (S : Set (Set β)) : a • ⋂₀ S subseteq ⋂ s i
n S, a • s
参数：a : α；S : Set (Set β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_sInter_subset`：image_sInter_subset (S : Set (Set α)) (f : α ->
 β) : f '' ⋂₀ S subseteq ⋂ s in S, f '' s
-/
lemma smul_set_sInter_subset (a : α) (S : Set (Set β)) :
    a • ⋂₀ S ⊆ ⋂ s ∈ S, a • s := image_sInter_subset ..

@[to_additive]
/-
**Set.smul_set_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_iInter {ι : Sort*} (a : α) (t : ι -> Set β) : (a • ⋂ i, t i) = ⋂ 
i, a • t i
参数：a : α；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_iInter`：image_iInter {f : α -> β} (hf : Bijective f) (s : ι ->
 Set α) : (f '' ⋂ i, s i) = ⋂ i, f '' s i
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
lemma smul_set_iInter₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    a • ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, a • t i j := image_iInter₂_subset ..

end SMulSet
variable {s : Set α} {t : Set β} {a : α} {b : β}

section VSub
variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

/-
**Set.iUnion_vsub_left_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_vsub_left_image : ⋃ a in s, (a -ᵥ ·) '' t = s -ᵥ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_left`：iUnion_image_left : ⋃ a in s, f a '' t = image2 f
 s t
-/
lemma iUnion_vsub_left_image : ⋃ a ∈ s, (a -ᵥ ·) '' t = s -ᵥ t := iUnion_image_left _
/-
**Set.iUnion_vsub_right_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_vsub_right_image : ⋃ a in t, (· -ᵥ a) '' s = s -ᵥ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
-/
lemma iUnion_vsub_right_image : ⋃ a ∈ t, (· -ᵥ a) '' s = s -ᵥ t := iUnion_image_right _
/-
**Set.iUnion_vsub** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_vsub (s : ι -> Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t
参数：s : ι -> Set β；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_left`：image2_iUnion_left (s : ι -> Set α) (t : Set β) 
: image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t
-/
lemma iUnion_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_iUnion_left ..
/-
**Set.vsub_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：vsub_iUnion (s : Set β) (t : ι -> Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
lemma vsub_iUnion (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_iUnion_right ..
/-
**Set.sUnion_vsub** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sUnion_vsub (S : Set (Set β)) (t : Set β) : ⋃₀ S -ᵥ t = ⋃ s in S, s -ᵥ t
参数：S : Set (Set β)；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_left`：image2_sUnion_left (S : Set (Set α)) (t : Set β)
 : image2 f (⋃₀ S) t = ⋃ s in S, image2 f s t
-/
lemma sUnion_vsub (S : Set (Set β)) (t : Set β) : ⋃₀ S -ᵥ t = ⋃ s ∈ S, s -ᵥ t :=
  image2_sUnion_left ..
/-
**Set.vsub_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：vsub_sUnion (s : Set β) (T : Set (Set β)) : s -ᵥ ⋃₀ T = ⋃ t in T, s -ᵥ t
参数：s : Set β；T : Set (Set β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sUnion_right`：image2_sUnion_right (s : Set α) (T : Set (Set β
)) : image2 f s (⋃₀ T) = ⋃ t in T, image2 f s t
-/
lemma vsub_sUnion (s : Set β) (T : Set (Set β)) : s -ᵥ ⋃₀ T = ⋃ t ∈ T, s -ᵥ t :=
  image2_sUnion_right ..
/-
**Set.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnion (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iUnion₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋃ i, ⋃ j, s i j) -ᵥ t = ⋃ i, ⋃ j, s i j -ᵥ t := image2_iUnion₂_left ..
/-
**Set.vsub_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：vsub_iUnion (s : Set β) (t : ι -> Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i
参数：s : Set β；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iUnion_right`：image2_iUnion_right (s : Set α) (t : ι -> Set β
) : image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i)
-/
lemma vsub_iUnion₂ (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s -ᵥ t i j := image2_iUnion₂_right ..
/-
**Set.iInter_vsub_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iInter_vsub_subset (s : ι -> Set β) (t : Set β) : (⋂ i, s i) -ᵥ t subseteq
 ⋂ i, s i -ᵥ t
参数：s : ι -> Set β；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_left`：image2_iInter_subset_left (s : ι -> Set α
) (t : Set β) : image2 f (⋂ i, s i) t subseteq ⋂ i, image2 f (s i) t
-/
lemma iInter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_iInter_subset_left ..
/-
**Set.vsub_iInter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：vsub_iInter_subset (s : Set β) (t : ι -> Set β) : (s -ᵥ ⋂ i, t i) subseteq
 ⋂ i, s -ᵥ t i
参数：s : Set β；t : ι -> Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_iInter_subset_right`：image2_iInter_subset_right (s : Set α) (
t : ι -> Set β) : image2 f s (⋂ i, t i) subseteq ⋂ i, image2 f s (t i)
-/
lemma vsub_iInter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_iInter_subset_right ..
/-
**Set.sInter_vsub_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sInter_vsub_subset (S : Set (Set β)) (t : Set β) : ⋂₀ S -ᵥ t subseteq ⋂ s 
in S, s -ᵥ t
参数：S : Set (Set β)；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_subset_left`：image2_sInter_subset_left (S : Set (Set α
)) (t : Set β) : image2 f (⋂₀ S) t subseteq ⋂ s in S, image2 f s t
-/
lemma sInter_vsub_subset (S : Set (Set β)) (t : Set β) : ⋂₀ S -ᵥ t ⊆ ⋂ s ∈ S, s -ᵥ t :=
  image2_sInter_subset_left ..
/-
**Set.vsub_sInter_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：vsub_sInter_subset (s : Set β) (T : Set (Set β)) : s -ᵥ ⋂₀ T subseteq ⋂ t 
in T, s -ᵥ t
参数：s : Set β；T : Set (Set β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_sInter_subset_right`：image2_sInter_subset_right (s : Set α) (
T : Set (Set β)) : image2 f s (⋂₀ T) subseteq ⋂ t in T, image2 f s t
-/
lemma vsub_sInter_subset (s : Set β) (T : Set (Set β)) : s -ᵥ ⋂₀ T ⊆ ⋂ t ∈ T, s -ᵥ t :=
  image2_sInter_subset_right ..
/-
**Set.iInter** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iInter (s : ι -> Set α) : Set α
参数：s : ι -> Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iInter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ i, ⋂ j, s i j) -ᵥ t ⊆ ⋂ i, ⋂ j, s i j -ᵥ t := image2_iInter₂_subset_left ..
/-
**Set.vsub_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma vsub_iInter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    s -ᵥ ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, s -ᵥ t i j := image2_iInter₂_subset_right ..

end VSub

end Set

