/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.Ray
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Rays in a real normed vector space

In this file we prove some lemmas about the `SameRay` predicate in case of a real normed space. In
this case, for two vectors `x y` in the same ray, the norm of their sum is equal to the sum of their
norms and `‖y‖ • x = ‖x‖ • y`.
-/

public section


open Real

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Real E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F]

namespace SameRay

variable {x y : E}

/--
theorem `norm_add` / 定理 `norm_add`

English:
theorem norm_add
  given: (h : SameRay Real x y)
  statement: ‖x + y‖ = ‖x‖ + ‖y‖
  proof: by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  rw [← add_smul]; rw [norm_smul_of_nonneg (add_nonneg ha hb)]; rw [norm_smul_of_nonneg ha]; rw [norm_smul_of_nonneg hb]; rw [add_mul]

中文:
定理 norm_add
  条件: (h : SameRay 实数 x y)
  结论: ‖x + y‖ = ‖x‖ + ‖y‖
  证明: by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  rw [← add_smul]; rw [norm_smul_of_nonneg (add_nonneg ha hb)]; rw [norm_smul_of_nonneg ha]; rw [norm_smul_of_nonneg hb]; rw [add_mul]

Depends on / 依赖: add_mul, add_nonneg, add_smul, exists_eq_smul, h.exists_eq_smul, norm_smul_of_nonneg
-/
theorem norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  rw [← add_smul]; rw [norm_smul_of_nonneg (add_nonneg ha hb)]; rw [norm_smul_of_nonneg ha]; rw [norm_smul_of_nonneg hb]; rw [add_mul]

/--
theorem `norm_sub` / 定理 `norm_sub`

English:
theorem norm_sub
  given: (h : SameRay Real x y)
  statement: ‖x - y‖ = |‖x‖ - ‖y‖|
  proof: by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  wlog hab : b <= a generalizing a b with H
  · rw [SameRay.sameRay_comm] at h
    rw [norm_sub_rev]; rw [abs_sub_comm]
    exact H b a hb ha h (le_of_not_ge hab)
  rw [← sub_nonneg] at hab
  rw [← sub_smul]; rw [norm_smul_of_nonneg ha

中文:
定理 norm_sub
  条件: (h : SameRay 实数 x y)
  结论: ‖x - y‖ = |‖x‖ - ‖y‖|
  证明: by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  wlog hab : b <= a generalizing a b with H
  · rw [SameRay.sameRay_comm] at h
    rw [norm_sub_rev]; rw [abs_sub_comm]
    exact H b a hb ha h (le_of_not_ge hab)
  rw [← sub_nonneg] at hab
  rw [← sub_smul]; rw [norm_smul_of_nonneg ha

Depends on / 依赖: SameRay, SameRay.sameRay_comm, abs_of_nonneg, abs_sub_comm, exists_eq_smul, generalizing, h.exists_eq_smul, le_of_not_ge, mul_nonneg, norm_nonneg, norm_smul_of_nonneg, norm_sub_rev, sameRay_comm, sub_mul, sub_nonneg, sub_smul
-/
theorem norm_sub (h : SameRay Real x y) : ‖x - y‖ = |‖x‖ - ‖y‖| := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  wlog hab : b <= a generalizing a b with H
  · rw [SameRay.sameRay_comm] at h
    rw [norm_sub_rev]; rw [abs_sub_comm]
    exact H b a hb ha h (le_of_not_ge hab)
  rw [← sub_nonneg] at hab
  rw [← sub_smul]; rw [norm_smul_of_nonneg hab]; rw [norm_smul_of_nonneg ha]; rw [norm_smul_of_nonneg hb]; rw [←
    sub_mul]; rw [abs_of_nonneg (mul_nonneg hab (norm_nonneg _))]

/--
theorem `norm_smul_eq` / 定理 `norm_smul_eq`

English:
theorem norm_smul_eq
  given: (h : SameRay Real x y)
  statement: ‖x‖ • y = ‖y‖ • x
  proof: by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  simp only [norm_smul_of_nonneg, *, mul_smul]
  rw [smul_comm]; rw [smul_comm b]; rw [smul_comm a b u]

中文:
定理 norm_smul_eq
  条件: (h : SameRay 实数 x y)
  结论: ‖x‖ • y = ‖y‖ • x
  证明: by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  simp only [norm_smul_of_nonneg, *, mul_smul]
  rw [smul_comm]; rw [smul_comm b]; rw [smul_comm a b u]

Depends on / 依赖: exists_eq_smul, h.exists_eq_smul, mul_smul, norm_smul_of_nonneg, smul_comm
-/
theorem norm_smul_eq (h : SameRay Real x y) : ‖x‖ • y = ‖y‖ • x := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  simp only [norm_smul_of_nonneg, *, mul_smul]
  rw [smul_comm]; rw [smul_comm b]; rw [smul_comm a b u]

end SameRay

variable {x y : F}

/--
theorem `norm_injOn_ray_left` / 定理 `norm_injOn_ray_left`

English:
theorem norm_injOn_ray_left
  given: (hx : x != 0)
  statement: { y | SameRay Real x y }.InjOn norm
  proof: by
  rintro y hy z hz h
  rcases hy.exists_nonneg_left hx with ⟨r, hr, rfl⟩
  rcases hz.exists_nonneg_left hx with ⟨s, hs, rfl⟩
  rw [norm_smul]; rw [norm_smul]; rw [mul_left_inj' (norm_ne_zero_iff.2 hx)]; rw [norm_of_nonneg hr]; rw [norm_of_nonneg hs] at h
  rw [h]

中文:
定理 norm_injOn_ray_left
  条件: (hx : x != 0)
  结论: { y | SameRay 实数 x y }.单射限制 norm
  证明: by
  rintro y hy z hz h
  rcases hy.exists_nonneg_left hx with ⟨r, hr, rfl⟩
  rcases hz.exists_nonneg_left hx with ⟨s, hs, rfl⟩
  rw [norm_smul]; rw [norm_smul]; rw [mul_left_inj' (norm_ne_zero_iff.2 hx)]; rw [norm_of_nonneg hr]; rw [norm_of_nonneg hs] at h
  rw [h]

Depends on / 依赖: exists_nonneg_left, hy.exists_nonneg_left, hz.exists_nonneg_left, mul_left_inj, norm_ne_zero_iff, norm_of_nonneg, norm_smul
-/
theorem norm_injOn_ray_left (hx : x != 0) : { y | SameRay Real x y }.InjOn norm := by
  rintro y hy z hz h
  rcases hy.exists_nonneg_left hx with ⟨r, hr, rfl⟩
  rcases hz.exists_nonneg_left hx with ⟨s, hs, rfl⟩
  rw [norm_smul]; rw [norm_smul]; rw [mul_left_inj' (norm_ne_zero_iff.2 hx)]; rw [norm_of_nonneg hr]; rw [norm_of_nonneg hs] at h
  rw [h]

/--
theorem `norm_injOn_ray_right` / 定理 `norm_injOn_ray_right`

English:
theorem norm_injOn_ray_right
  given: (hy : y != 0)
  statement: { x | SameRay Real x y }.InjOn norm
  proof: by
  simpa only [SameRay.sameRay_comm] using norm_injOn_ray_left hy

中文:
定理 norm_injOn_ray_right
  条件: (hy : y != 0)
  结论: { x | SameRay 实数 x y }.单射限制 norm
  证明: by
  simpa only [SameRay.sameRay_comm] using norm_injOn_ray_left hy

Depends on / 依赖: SameRay, SameRay.sameRay_comm, norm_injOn_ray_left, sameRay_comm
-/
theorem norm_injOn_ray_right (hy : y != 0) : { x | SameRay Real x y }.InjOn norm := by
  simpa only [SameRay.sameRay_comm] using norm_injOn_ray_left hy

/--
theorem `sameRay_iff_norm_smul_eq` / 定理 `sameRay_iff_norm_smul_eq`

English:
theorem sameRay_iff_norm_smul_eq
  statement: SameRay Real x y ↔ ‖x‖ • y = ‖y‖ • x
  proof: ⟨SameRay.norm_smul_eq, fun h =>
    or_iff_not_imp_left.2 fun hx =>
      or_iff_not_imp_left.2 fun hy => ⟨‖y‖, ‖x‖, norm_pos_iff.2 hy, norm_pos_iff.2 hx, h.symm⟩⟩

中文:
定理 sameRay_iff_norm_smul_eq
  结论: SameRay 实数 x y ↔ ‖x‖ • y = ‖y‖ • x
  证明: ⟨SameRay.norm_smul_eq, fun h =>
    or_iff_not_imp_left.2 fun hx =>
      or_iff_not_imp_left.2 fun hy => ⟨‖y‖, ‖x‖, norm_pos_iff.2 hy, norm_pos_iff.2 hx, h.symm⟩⟩

Depends on / 依赖: SameRay, SameRay.norm_smul_eq, h.symm, norm_pos_iff, norm_smul_eq, or_iff_not_imp_left
-/
theorem sameRay_iff_norm_smul_eq : SameRay Real x y ↔ ‖x‖ • y = ‖y‖ • x :=
  ⟨SameRay.norm_smul_eq, fun h =>
    or_iff_not_imp_left.2 fun hx =>
      or_iff_not_imp_left.2 fun hy => ⟨‖y‖, ‖x‖, norm_pos_iff.2 hy, norm_pos_iff.2 hx, h.symm⟩⟩

/--
theorem `sameRay_iff_inv_norm_smul_eq_of_ne` / 定理 `sameRay_iff_inv_norm_smul_eq_of_ne`

English:
theorem sameRay_iff_inv_norm_smul_eq_of_ne
  given: (hx : x != 0) (hy : y != 0)
  proof: by
  rw [inv_smul_eq_iff₀]; rw [smul_comm]; rw [eq_comm]; rw [inv_smul_eq_iff₀]; rw [sameRay_iff_norm_smul_eq] <;>
    rwa [norm_ne_zero_iff]

alias ⟨SameRay.inv_norm_smul_eq, _⟩ := sameRay_iff_inv_norm_smul_eq_of_ne

中文:
定理 sameRay_iff_inv_norm_smul_eq_of_ne
  条件: (hx : x != 0) (hy : y != 0)
  证明: by
  rw [inv_smul_eq_iff₀]; rw [smul_comm]; rw [eq_comm]; rw [inv_smul_eq_iff₀]; rw [sameRay_iff_norm_smul_eq] <;>
    rwa [norm_ne_zero_iff]

alias ⟨SameRay.inv_norm_smul_eq, _⟩ := sameRay_iff_inv_norm_smul_eq_of_ne

Depends on / 依赖: eq_comm, norm_ne_zero_iff, sameRay_iff_norm_smul_eq, smul_comm
-/
theorem sameRay_iff_inv_norm_smul_eq_of_ne (hx : x != 0) (hy : y != 0) :
    SameRay Real x y ↔ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y := by
  rw [inv_smul_eq_iff₀]; rw [smul_comm]; rw [eq_comm]; rw [inv_smul_eq_iff₀]; rw [sameRay_iff_norm_smul_eq] <;>
    rwa [norm_ne_zero_iff]

alias ⟨SameRay.inv_norm_smul_eq, _⟩ := sameRay_iff_inv_norm_smul_eq_of_ne

/--
theorem `sameRay_iff_inv_norm_smul_eq` / 定理 `sameRay_iff_inv_norm_smul_eq`

English:
theorem sameRay_iff_inv_norm_smul_eq
  statement: SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx); · simp [SameRay.zero_left]
  rcases eq_or_ne y 0 with (rfl | hy); · simp [SameRay.zero_right]
  simp only [sameRay_iff_inv_norm_smul_eq_of_ne hx hy, *, false_or]

中文:
定理 sameRay_iff_inv_norm_smul_eq
  结论: SameRay 实数 x y ↔ x = 0 ∨ y = 0 ∨ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx); · simp [SameRay.zero_left]
  rcases eq_or_ne y 0 with (rfl | hy); · simp [SameRay.zero_right]
  simp only [sameRay_iff_inv_norm_smul_eq_of_ne hx hy, *, false_or]

Depends on / 依赖: SameRay, SameRay.zero_left, SameRay.zero_right, eq_or_ne, false_or, sameRay_iff_inv_norm_smul_eq_of_ne, zero_left, zero_right
-/
theorem sameRay_iff_inv_norm_smul_eq : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y := by
  rcases eq_or_ne x 0 with (rfl | hx); · simp [SameRay.zero_left]
  rcases eq_or_ne y 0 with (rfl | hy); · simp [SameRay.zero_right]
  simp only [sameRay_iff_inv_norm_smul_eq_of_ne hx hy, *, false_or]

/--
theorem `sameRay_iff_of_norm_eq` / 定理 `sameRay_iff_of_norm_eq`

English:
theorem sameRay_iff_of_norm_eq
  given: (h : ‖x‖ = ‖y‖)
  statement: SameRay Real x y ↔ x = y
  proof: by
  obtain rfl | hy := eq_or_ne y 0
  · rw [norm_zero, norm_eq_zero] at h
    exact iff_of_true (SameRay.zero_right _) h
  · exact ⟨fun hxy => norm_injOn_ray_right hy hxy SameRay.rfl h, fun hxy => hxy ▸ SameRay.rfl⟩

中文:
定理 sameRay_iff_of_norm_eq
  条件: (h : ‖x‖ = ‖y‖)
  结论: SameRay 实数 x y ↔ x = y
  证明: by
  obtain rfl | hy := eq_or_ne y 0
  · rw [norm_zero, norm_eq_zero] at h
    exact iff_of_true (SameRay.zero_right _) h
  · exact ⟨fun hxy => norm_injOn_ray_right hy hxy SameRay.rfl h, fun hxy => hxy ▸ SameRay.rfl⟩

Depends on / 依赖: SameRay, SameRay.rfl, SameRay.zero_right, eq_or_ne, iff_of_true, norm_eq_zero, norm_injOn_ray_right, norm_zero, zero_right
-/
theorem sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : SameRay Real x y ↔ x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · rw [norm_zero, norm_eq_zero] at h
    exact iff_of_true (SameRay.zero_right _) h
  · exact ⟨fun hxy => norm_injOn_ray_right hy hxy SameRay.rfl h, fun hxy => hxy ▸ SameRay.rfl⟩

/--
theorem `not_sameRay_iff_of_norm_eq` / 定理 `not_sameRay_iff_of_norm_eq`

English:
theorem not_sameRay_iff_of_norm_eq
  given: (h : ‖x‖ = ‖y‖)
  statement: ¬SameRay Real x y ↔ x != y
  proof: (sameRay_iff_of_norm_eq h).not

中文:
定理 not_sameRay_iff_of_norm_eq
  条件: (h : ‖x‖ = ‖y‖)
  结论: ¬SameRay 实数 x y ↔ x != y
  证明: (sameRay_iff_of_norm_eq h).not

Depends on / 依赖: sameRay_iff_of_norm_eq
-/
theorem not_sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : ¬SameRay Real x y ↔ x != y :=
  (sameRay_iff_of_norm_eq h).not

/--
theorem `SameRay.eq_of_norm_eq` / 定理 `SameRay.eq_of_norm_eq`

English:
theorem SameRay.eq_of_norm_eq
  given: (h : SameRay Real x y) (hn : ‖x‖ = ‖y‖)
  statement: x = y
  proof: (sameRay_iff_of_norm_eq hn).mp h

中文:
定理 SameRay.eq_of_norm_eq
  条件: (h : SameRay 实数 x y) (hn : ‖x‖ = ‖y‖)
  结论: x = y
  证明: (sameRay_iff_of_norm_eq hn).mp h

Depends on / 依赖: sameRay_iff_of_norm_eq
-/
theorem SameRay.eq_of_norm_eq (h : SameRay Real x y) (hn : ‖x‖ = ‖y‖) : x = y :=
  (sameRay_iff_of_norm_eq hn).mp h

/--
theorem `SameRay.norm_eq_iff` / 定理 `SameRay.norm_eq_iff`

English:
theorem SameRay.norm_eq_iff
  given: (h : SameRay Real x y)
  statement: ‖x‖ = ‖y‖ ↔ x = y
  proof: ⟨h.eq_of_norm_eq, fun h => h ▸ rfl⟩

中文:
定理 SameRay.norm_eq_iff
  条件: (h : SameRay 实数 x y)
  结论: ‖x‖ = ‖y‖ ↔ x = y
  证明: ⟨h.eq_of_norm_eq, fun h => h ▸ rfl⟩

Depends on / 依赖: eq_of_norm_eq, h.eq_of_norm_eq
-/
theorem SameRay.norm_eq_iff (h : SameRay Real x y) : ‖x‖ = ‖y‖ ↔ x = y :=
  ⟨h.eq_of_norm_eq, fun h => h ▸ rfl⟩
