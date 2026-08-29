/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Instances for the range submonoid of a monoid with zero hom
-/

public section

assert_not_exists Ring

namespace MonoidWithZeroHom

variable {G H : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: G] [MulZeroOneClass H] (f
  body: ⟨0, 0, by simp⟩
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_zero _ := Subtype.ext (mul_zero _)

@[simp]

中文:
实例 [乘零幺类
  签名: G] [乘零幺类 H] (f
  定义体: ⟨0, 0, by simp⟩
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_zero _ := Subtype.ext (mul_zero _)

@[simp]
-/
instance [MulZeroOneClass G] [MulZeroOneClass H] (f : G ->*₀ H) :
    MulZeroOneClass (MonoidHom.mrange f) where
  zero := ⟨0, 0, by simp⟩
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_zero _ := Subtype.ext (mul_zero _)

@[simp]
/--
lemma `val_mrange_zero` / 引理 `val_mrange_zero`

English:
lemma val_mrange_zero
  given: [MulZeroOneClass G] [MulZeroOneClass H] (f : G ->*₀ H)
  proof: rfl

中文:
引理 val_mrange_zero
  条件: [乘零幺类 G] [乘零幺类 H] (f : G ->*₀ H)
  证明: rfl
-/
lemma val_mrange_zero [MulZeroOneClass G] [MulZeroOneClass H] (f : G ->*₀ H) :
    ((0 : MonoidHom.mrange f) : H) = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: G] [MonoidWithZero H] (f

中文:
实例 [乘零幺类
  签名: G] [带零幺半群 H] (f
-/
instance [MulZeroOneClass G] [MonoidWithZero H] (f : G ->*₀ H) :
    MonoidWithZero (MonoidHom.mrange f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: G] [CommMonoidWithZero H] (f

中文:
实例 [乘零幺类
  签名: G] [带零交换幺半群 H] (f
-/
instance [MulZeroOneClass G] [CommMonoidWithZero H] (f : G ->*₀ H) :
    CommMonoidWithZero (MonoidHom.mrange f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GroupWithZero
  signature: G] [GroupWithZero H] (f
  body: fun x => ⟨x⁻¹, by
    obtain ⟨y, hy⟩ := x.prop
    use y⁻¹
    simp [← hy]⟩
  exists_pair_ne := ⟨⟨f 0, 0, rfl⟩, ⟨f 1, by simp [-map_one]⟩, by simp⟩
  inv_zero := Subtype.ext inv_zero
  mul_inv_cancel := by
    rintro ⟨a, ha⟩ h
    simp only [ne_eq, Subtype.ext_iff] at h
    simpa using mul_inv_cance

中文:
实例 [带零群
  签名: G] [带零群 H] (f
  定义体: fun x => ⟨x⁻¹, by
    obtain ⟨y, hy⟩ := x.prop
    use y⁻¹
    simp [← hy]⟩
  exists_pair_ne := ⟨⟨f 0, 0, rfl⟩, ⟨f 1, by simp [-map_one]⟩, by simp⟩
  inv_zero := Subtype.ext inv_zero
  mul_inv_cancel := by
    rintro ⟨a, ha⟩ h
    simp only [ne_eq, Subtype.ext_iff] at h
    simpa using mul_inv_cance

Depends on / 依赖: Subtype, Subtype.ext, Subtype.ext_iff, exists_pair_ne, ext_iff, inv_zero, map_one, mul_inv_cancel, ne_eq, x.prop
-/
instance [GroupWithZero G] [GroupWithZero H] (f : G ->*₀ H) :
    GroupWithZero (MonoidHom.mrange f) where
  inv := fun x => ⟨x⁻¹, by
    obtain ⟨y, hy⟩ := x.prop
    use y⁻¹
    simp [← hy]⟩
  exists_pair_ne := ⟨⟨f 0, 0, rfl⟩, ⟨f 1, by simp [-map_one]⟩, by simp⟩
  inv_zero := Subtype.ext inv_zero
  mul_inv_cancel := by
    rintro ⟨a, ha⟩ h
    simp only [ne_eq, Subtype.ext_iff] at h
    simpa using mul_inv_cancel₀ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GroupWithZero
  signature: G] [CommGroupWithZero H] (f

中文:
实例 [带零群
  签名: G] [带零交换群 H] (f
-/
instance [GroupWithZero G] [CommGroupWithZero H] (f : G ->*₀ H) :
    CommGroupWithZero (MonoidHom.mrange f) where

/--
lemma `mker_inverse` / 引理 `mker_inverse`

English:
lemma mker_inverse
  given: [CommGroupWithZero H]
  proof: by
  ext
  simp

中文:
引理 mker_inverse
  条件: [带零交换群 H]
  证明: by
  ext
  simp
-/
lemma mker_inverse [CommGroupWithZero H] :
    MonoidHom.mker (MonoidWithZero.inverse (M := H)) = ⊥ := by
  ext
  simp

end MonoidWithZeroHom
