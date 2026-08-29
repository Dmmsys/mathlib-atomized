/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Group

/-!
# Basic lemmas about group extensions

This file gives basic lemmas about group extensions.

For the main definitions, see `Mathlib/GroupTheory/GroupExtension/Defs.lean`.
-/

@[expose] public section

variable {N G : Type*} [Group N] [Group G]

namespace GroupExtension

variable {E : Type*} [Group E] (S : GroupExtension N E G)

/-- The isomorphism `E ⧸ S.rightHom.ker ≃* G` induced by `S.rightHom` -/
@[to_additive /-- The isomorphism `E ⧸ S.rightHom.ker ≃+ G` induced by `S.rightHom` -/]
/--
Definition of `quotientKerRightHomEquivRight` / `quotientKerRightHomEquivRight` 的定义

English:
definition quotientKerRightHomEquivRight
  signature: : E ⧸ S.rightHom.ker ≃* G
  body: QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective

中文:
定义 quotientKerRightHomEquivRight
  签名: : E ⧸ S.rightHom.ker ≃* G
  定义体: QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective

Depends on / 依赖: QuotientGroup, QuotientGroup.quotientKerEquivOfSurjective, S.rightHom, S.rightHom_surjective, quotientKerEquivOfSurjective, rightHom, rightHom_surjective
-/
noncomputable def quotientKerRightHomEquivRight : E ⧸ S.rightHom.ker ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective

/-- The isomorphism `E ⧸ S.inl.range ≃* G` induced by `S.rightHom` -/
@[to_additive /-- The isomorphism `E ⧸ S.inl.range ≃+ G` induced by `S.rightHom` -/]
/--
Definition of `quotientRangeInlEquivRight` / `quotientRangeInlEquivRight` 的定义

English:
definition quotientRangeInlEquivRight
  signature: : E ⧸ S.inl.range ≃* G
  body: QuotientGroup.liftEquiv _ S.rightHom_surjective S.range_inl_eq_ker_rightHom

中文:
定义 quotientRangeInlEquivRight
  签名: : E ⧸ S.inl.range ≃* G
  定义体: QuotientGroup.liftEquiv _ S.rightHom_surjective S.range_inl_eq_ker_rightHom

Depends on / 依赖: QuotientGroup, QuotientGroup.liftEquiv, S.range_inl_eq_ker_rightHom, S.rightHom_surjective, liftEquiv, range_inl_eq_ker_rightHom, rightHom_surjective
-/
noncomputable def quotientRangeInlEquivRight : E ⧸ S.inl.range ≃* G :=
  QuotientGroup.liftEquiv _ S.rightHom_surjective S.range_inl_eq_ker_rightHom

/-- An arbitrarily chosen section -/
@[to_additive surjInvRightHom /-- An arbitrarily chosen section -/]
/--
Definition of `surjInvRightHom` / `surjInvRightHom` 的定义

English:
definition surjInvRightHom
  signature: : S.Section where
  body: Function.surjInv S.rightHom_surjective
  rightInverse_rightHom := Function.surjInv_eq S.rightHom_surjective

中文:
定义 surjInvRightHom
  签名: : S.截面 where
  定义体: Function.surjInv S.rightHom_surjective
  rightInverse_rightHom := Function.surjInv_eq S.rightHom_surjective

Depends on / 依赖: Function, Function.surjInv, S.rightHom_surjective, rightHom_surjective, surjInv
-/
noncomputable def surjInvRightHom : S.Section where
  toFun := Function.surjInv S.rightHom_surjective
  rightInverse_rightHom := Function.surjInv_eq S.rightHom_surjective

namespace Section

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G} (σ σ' : S.Section) (g g₁ g₂ : G)
  (equiv : S.Equiv S')

@[to_additive]
/--
theorem `mul_inv_mem_range_inl` / 定理 `mul_inv_mem_range_inl`

English:
theorem mul_inv_mem_range_inl
  statement: σ g * (σ' g)⁻¹ in S.inl.range
  proof: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]

中文:
定理 mul_inv_mem_range_inl
  结论: σ g * (σ' g)⁻¹ in S.inl.range
  证明: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, S.range_inl_eq_ker_rightHom, map_inv, map_mul, mem_ker, mul_inv_cancel, range_inl_eq_ker_rightHom, rightHom_section
-/
theorem mul_inv_mem_range_inl : σ g * (σ' g)⁻¹ in S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
/--
theorem `inv_mul_mem_range_inl` / 定理 `inv_mul_mem_range_inl`

English:
theorem inv_mul_mem_range_inl
  statement: (σ g)⁻¹ * σ' g in S.inl.range
  proof: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    inv_mul_cancel]

@[to_additive]

中文:
定理 inv_mul_mem_range_inl
  结论: (σ g)⁻¹ * σ' g in S.inl.range
  证明: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    inv_mul_cancel]

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, S.range_inl_eq_ker_rightHom, inv_mul_cancel, map_inv, map_mul, mem_ker, range_inl_eq_ker_rightHom, rightHom_section
-/
theorem inv_mul_mem_range_inl : (σ g)⁻¹ * σ' g in S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    inv_mul_cancel]

@[to_additive]
/--
theorem `exists_eq_inl_mul` / 定理 `exists_eq_inl_mul`

English:
theorem exists_eq_inl_mul
  statement: exists n : N, σ g = S.inl n * σ' g
  proof: by
  obtain ⟨n, hn⟩ := mul_inv_mem_range_inl σ σ' g
  exact ⟨n, by rw [hn, inv_mul_cancel_right]⟩

@[to_additive]

中文:
定理 存在_eq_inl_mul
  结论: 存在 n : N, σ g = S.inl n * σ' g
  证明: by
  obtain ⟨n, hn⟩ := mul_inv_mem_range_inl σ σ' g
  exact ⟨n, by rw [hn, inv_mul_cancel_right]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_inv_mem_range_inl
-/
theorem exists_eq_inl_mul : exists n : N, σ g = S.inl n * σ' g := by
  obtain ⟨n, hn⟩ := mul_inv_mem_range_inl σ σ' g
  exact ⟨n, by rw [hn, inv_mul_cancel_right]⟩

@[to_additive]
/--
theorem `exists_eq_mul_inl` / 定理 `exists_eq_mul_inl`

English:
theorem exists_eq_mul_inl
  statement: exists n : N, σ g = σ' g * S.inl n
  proof: by
  obtain ⟨n, hn⟩ := inv_mul_mem_range_inl σ' σ g
  exact ⟨n, by rw [hn, mul_inv_cancel_left]⟩

@[to_additive]

中文:
定理 存在_eq_mul_inl
  结论: 存在 n : N, σ g = σ' g * S.inl n
  证明: by
  obtain ⟨n, hn⟩ := inv_mul_mem_range_inl σ' σ g
  exact ⟨n, by rw [hn, mul_inv_cancel_left]⟩

@[to_additive]

Depends on / 依赖: inv_mul_mem_range_inl, mul_inv_cancel_left
-/
theorem exists_eq_mul_inl : exists n : N, σ g = σ' g * S.inl n := by
  obtain ⟨n, hn⟩ := inv_mul_mem_range_inl σ' σ g
  exact ⟨n, by rw [hn, mul_inv_cancel_left]⟩

@[to_additive]
/--
theorem `mul_mul_mul_inv_mem_range_inl` / 定理 `mul_mul_mul_inv_mem_range_inl`

English:
theorem mul_mul_mul_inv_mem_range_inl
  statement: σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ in S.inl.range
  proof: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]

中文:
定理 mul_mul_mul_inv_mem_range_inl
  结论: σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ in S.inl.range
  证明: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, S.range_inl_eq_ker_rightHom, map_inv, map_mul, mem_ker, mul_inv_cancel, range_inl_eq_ker_rightHom, rightHom_section
-/
theorem mul_mul_mul_inv_mem_range_inl : σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ in S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
/--
theorem `mul_inv_mul_mul_mem_range_inl` / 定理 `mul_inv_mul_mul_mem_range_inl`

English:
theorem mul_inv_mul_mul_mem_range_inl
  statement: (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ in S.inl.range
  proof: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_assoc, inv_mul_cancel]

@[to_additive]

中文:
定理 mul_inv_mul_mul_mem_range_inl
  结论: (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ in S.inl.range
  证明: by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_assoc, inv_mul_cancel]

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, S.range_inl_eq_ker_rightHom, inv_mul_cancel, map_inv, map_mul, mem_ker, mul_assoc, range_inl_eq_ker_rightHom, rightHom_section
-/
theorem mul_inv_mul_mul_mem_range_inl : (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ in S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_assoc, inv_mul_cancel]

@[to_additive]
/--
theorem `exists_mul_eq_inl_mul_mul` / 定理 `exists_mul_eq_inl_mul_mul`

English:
theorem exists_mul_eq_inl_mul_mul
  statement: exists n : N, σ (g₁ * g₂) = S.inl n * σ g₁ * σ g₂
  proof: by
  obtain ⟨n, hn⟩ := mul_mul_mul_inv_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [mul_assoc]; rw [map_inv]; rw [eq_inv_mul_iff_mul_eq]; rw [← eq_mul_inv_iff_mul_eq]; rw [hn]

@[to_additive]

中文:
定理 存在_mul_eq_inl_mul_mul
  结论: 存在 n : N, σ (g₁ * g₂) = S.inl n * σ g₁ * σ g₂
  证明: by
  obtain ⟨n, hn⟩ := mul_mul_mul_inv_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [mul_assoc]; rw [map_inv]; rw [eq_inv_mul_iff_mul_eq]; rw [← eq_mul_inv_iff_mul_eq]; rw [hn]

@[to_additive]

Depends on / 依赖: eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq, map_inv, mul_assoc, mul_mul_mul_inv_mem_range_inl
-/
theorem exists_mul_eq_inl_mul_mul : exists n : N, σ (g₁ * g₂) = S.inl n * σ g₁ * σ g₂ := by
  obtain ⟨n, hn⟩ := mul_mul_mul_inv_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [mul_assoc]; rw [map_inv]; rw [eq_inv_mul_iff_mul_eq]; rw [← eq_mul_inv_iff_mul_eq]; rw [hn]

@[to_additive]
/--
theorem `exists_mul_eq_mul_mul_inl` / 定理 `exists_mul_eq_mul_mul_inl`

English:
theorem exists_mul_eq_mul_mul_inl
  statement: exists n : N, σ (g₁ * g₂) = σ g₁ * σ g₂ * S.inl n
  proof: by
  obtain ⟨n, hn⟩ := mul_inv_mul_mul_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [map_inv]; rw [eq_mul_inv_iff_mul_eq]; rw [← eq_inv_mul_iff_mul_eq]; rw [← mul_assoc]; rw [hn]

initialize_simps_projections AddGroupExtension.Section (toFun -> apply)
initialize_simps_projections Section (toFun -> apply)

中文:
定理 存在_mul_eq_mul_mul_inl
  结论: 存在 n : N, σ (g₁ * g₂) = σ g₁ * σ g₂ * S.inl n
  证明: by
  obtain ⟨n, hn⟩ := mul_inv_mul_mul_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [map_inv]; rw [eq_mul_inv_iff_mul_eq]; rw [← eq_inv_mul_iff_mul_eq]; rw [← mul_assoc]; rw [hn]

initialize_simps_projections AddGroupExtension.Section (toFun -> apply)
initialize_simps_projections Section (toFun -> apply)

Depends on / 依赖: eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq, map_inv, mul_assoc, mul_inv_mul_mul_mem_range_inl
-/
theorem exists_mul_eq_mul_mul_inl : exists n : N, σ (g₁ * g₂) = σ g₁ * σ g₂ * S.inl n := by
  obtain ⟨n, hn⟩ := mul_inv_mul_mul_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [map_inv]; rw [eq_mul_inv_iff_mul_eq]; rw [← eq_inv_mul_iff_mul_eq]; rw [← mul_assoc]; rw [hn]

initialize_simps_projections AddGroupExtension.Section (toFun -> apply)
initialize_simps_projections Section (toFun -> apply)

/-- The composition of an isomorphism between equivalent group extensions and a section -/
@[to_additive (attr := simps!)
/-- The composition of an isomorphism between equivalent additive group extensions and a section -/]
/--
Definition of `equivComp` / `equivComp` 的定义

English:
definition equivComp
  signature: : S'.Section where
  body: equiv ∘ σ
  rightInverse_rightHom g := by
    rw [Function.comp_apply]; rw [equiv.rightHom_map]; rw [rightHom_section]

中文:
定义 equivComp
  签名: : S'.截面 where
  定义体: equiv ∘ σ
  rightInverse_rightHom g := by
    rw [Function.comp_apply]; rw [equiv.rightHom_map]; rw [rightHom_section]
-/
def equivComp : S'.Section where
  toFun := equiv ∘ σ
  rightInverse_rightHom g := by
    rw [Function.comp_apply]; rw [equiv.rightHom_map]; rw [rightHom_section]

end Section

namespace Equiv

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G}

/-- An equivalence of group extensions from a homomorphism making a commuting diagram. Such a
homomorphism is necessarily an isomorphism. -/
@[to_additive
/-- An equivalence of additive group extensions from a homomorphism making a commuting diagram.
Such a homomorphism is necessarily an isomorphism. -/]
/--
Definition of `ofMonoidHom` / `ofMonoidHom` 的定义

English:
definition ofMonoidHom
  signature: (f : E ->* E') (comp_inl : f.comp S.inl = S'.inl)
  body: f
  invFun e' :=
    let e := Function.surjInv S.rightHom_surjective (S'.rightHom e')
    e * S.inl (Function.invFun S'.inl ((f e)⁻¹ * e'))
  left_inv e := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, ← map_inv, ← map_mul]
    obtain ⟨n, hn⟩ :
        (Function.surjInv S.rightHom_s

中文:
定义 ofMonoidHom
  签名: (f : E ->* E') (comp_inl : f.comp S.inl = S'.inl)
  定义体: f
  invFun e' :=
    let e := Function.surjInv S.rightHom_surjective (S'.rightHom e')
    e * S.inl (Function.invFun S'.inl ((f e)⁻¹ * e'))
  left_inv e := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, ← map_inv, ← map_mul]
    obtain ⟨n, hn⟩ :
        (Function.surjInv S.rightHom_s
-/
noncomputable def ofMonoidHom (f : E ->* E') (comp_inl : f.comp S.inl = S'.inl)
    (rightHom_comp : S'.rightHom.comp f = S.rightHom) : S.Equiv S' where
  __ := f
  invFun e' :=
    let e := Function.surjInv S.rightHom_surjective (S'.rightHom e')
    e * S.inl (Function.invFun S'.inl ((f e)⁻¹ * e'))
  left_inv e := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, ← map_inv, ← map_mul]
    obtain ⟨n, hn⟩ :
        (Function.surjInv S.rightHom_surjective (S'.rightHom (f e)))⁻¹ * e in S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom]; rw [MonoidHom.mem_ker]; rw [map_mul]; rw [map_inv]; rw [← MonoidHom.comp_apply]; rw [rightHom_comp]
      simpa only [Function.surjInv_eq] using inv_mul_cancel (S.rightHom e)
    rw [← eq_inv_mul_iff_mul_eq]; rw [← hn]; rw [← MonoidHom.comp_apply]; rw [comp_inl]; rw [Function.leftInverse_invFun S'.inl_injective]
  right_inv e' := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, map_mul]
    rw [← eq_inv_mul_iff_mul_eq]; rw [← MonoidHom.comp_apply]; rw [comp_inl]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range]; rw [S'.range_inl_eq_ker_rightHom]; rw [MonoidHom.mem_ker]; rw [map_mul]; rw [map_inv]; rw [← MonoidHom.comp_apply]; rw [rightHom_comp]
    simpa only [Function.surjInv_eq] using inv_mul_cancel (S'.rightHom e')
  inl_comm := congrArg DFunLike.coe comp_inl
  rightHom_comm := congrArg DFunLike.coe rightHom_comp

end Equiv

namespace Splitting

variable {S}
variable (s : S.Splitting)

/--
Definition of `conjAct` / `conjAct` 的定义

English:
definition conjAct
  signature: : G ->* MulAut N
  body: S.conjAct.comp s

中文:
定义 conjAct
  签名: : G ->* MulAut N
  定义体: S.conjAct.comp s

Depends on / 依赖: S.conjAct.comp, conjAct
-/
noncomputable def conjAct : G ->* MulAut N := S.conjAct.comp s

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `semidirectProductToGroupExtensionEquiv` / `semidirectProductToGroupExtensionEquiv` 的定义

English:
definition semidirectProductToGroupExtensionEquiv
  signature: :
  body: fun ⟨n, g⟩ => S.inl n * s g
  invFun := fun e => ⟨Function.invFun S.inl (e * (s (S.rightHom e))⁻¹), S.rightHom e⟩
  left_inv := fun ⟨n, g⟩ => by
    simp only [map_mul, rightHom_inl, rightHom_splitting, one_mul, mul_inv_cancel_right,
      Function.leftInverse_invFun S.inl_injective n]
  right_inv :

中文:
定义 semidirectProductToGroupExtensionEquiv
  签名: :
  定义体: fun ⟨n, g⟩ => S.inl n * s g
  invFun := fun e => ⟨Function.invFun S.inl (e * (s (S.rightHom e))⁻¹), S.rightHom e⟩
  left_inv := fun ⟨n, g⟩ => by
    simp only [map_mul, rightHom_inl, rightHom_splitting, one_mul, mul_inv_cancel_right,
      Function.leftInverse_invFun S.inl_injective n]
  right_inv :

Depends on / 依赖: S.inl
-/
noncomputable def semidirectProductToGroupExtensionEquiv :
    (SemidirectProduct.toGroupExtension s.conjAct).Equiv S where
  toFun := fun ⟨n, g⟩ => S.inl n * s g
  invFun := fun e => ⟨Function.invFun S.inl (e * (s (S.rightHom e))⁻¹), S.rightHom e⟩
  left_inv := fun ⟨n, g⟩ => by
    simp only [map_mul, rightHom_inl, rightHom_splitting, one_mul, mul_inv_cancel_right,
      Function.leftInverse_invFun S.inl_injective n]
  right_inv := fun e => by
    simp only [← eq_mul_inv_iff_mul_eq]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range]; rw [S.range_inl_eq_ker_rightHom]; rw [MonoidHom.mem_ker]; rw [map_mul]; rw [map_inv]; rw [rightHom_splitting]; rw [mul_inv_cancel]
  map_mul' := fun ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ => by
    simp only [conjAct, MonoidHom.comp_apply, map_mul, inl_conjAct_comm, MonoidHom.coe_coe]
    group
  inl_comm := by
    ext n
    simp only [SemidirectProduct.toGroupExtension, Function.comp_apply, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]
  rightHom_comm := by
    ext ⟨n, g⟩
    simp only [SemidirectProduct.toGroupExtension, Function.comp_apply, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, map_mul, rightHom_inl, one_mul, rightHom_splitting,
      SemidirectProduct.rightHom_eq_right]

/--
Definition of `semidirectProductMulEquiv` / `semidirectProductMulEquiv` 的定义

English:
definition semidirectProductMulEquiv
  signature: : N ⋊[s.conjAct] G ≃* E
  body: s.semidirectProductToGroupExtensionEquiv.toMulEquiv

中文:
定义 semidirectProductMulEquiv
  签名: : N ⋊[s.conjAct] G ≃* E
  定义体: s.semidirectProductToGroupExtensionEquiv.toMulEquiv

Depends on / 依赖: s.semidirectProductToGroupExtensionEquiv.toMulEquiv, semidirectProductToGroupExtensionEquiv, toMulEquiv
-/
noncomputable def semidirectProductMulEquiv : N ⋊[s.conjAct] G ≃* E :=
  s.semidirectProductToGroupExtensionEquiv.toMulEquiv

end Splitting

namespace IsConj

/-- `N`-conjugacy is reflexive. -/
@[to_additive /-- `N`-conjugacy is reflexive. -/]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (s : S.Splitting)
  statement: S.IsConj s s
  proof: ⟨1, by simp only [map_one, inv_one, one_mul, mul_one]⟩

中文:
定理 refl
  条件: (s : S.Splitting)
  结论: S.IsConj s s
  证明: ⟨1, by simp only [map_one, inv_one, one_mul, mul_one]⟩

Depends on / 依赖: inv_one, map_one, mul_one, one_mul
-/
theorem refl (s : S.Splitting) : S.IsConj s s :=
  ⟨1, by simp only [map_one, inv_one, one_mul, mul_one]⟩

/-- `N`-conjugacy is symmetric. -/
@[to_additive /-- `N`-conjugacy is symmetric. -/]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂)
  statement: S.IsConj s₂ s₁
  proof: by
  obtain ⟨n, hn⟩ := h
  exact ⟨n⁻¹, by simp only [hn, map_inv]; group⟩

中文:
定理 symm
  条件: {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂)
  结论: S.IsConj s₂ s₁
  证明: by
  obtain ⟨n, hn⟩ := h
  exact ⟨n⁻¹, by simp only [hn, map_inv]; group⟩

Depends on / 依赖: map_inv
-/
theorem symm {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂) : S.IsConj s₂ s₁ := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n⁻¹, by simp only [hn, map_inv]; group⟩

/-- `N`-conjugacy is transitive. -/
@[to_additive /-- `N`-conjugacy is transitive. -/]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃)
  proof: by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ * n₂, by simp only [hn₁, hn₂, map_mul]; group⟩

中文:
定理 trans
  条件: {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃)
  证明: by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ * n₂, by simp only [hn₁, hn₂, map_mul]; group⟩

Depends on / 依赖: map_mul
-/
theorem trans {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃) :
    S.IsConj s₁ s₃ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ * n₂, by simp only [hn₁, hn₂, map_mul]; group⟩

/-- The setoid of splittings with `N`-conjugacy -/
@[to_additive /-- The setoid of splittings with `N`-conjugacy -/]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: : Setoid S.Splitting where
  body: S.IsConj
  iseqv :=
  { refl := refl S
    symm := symm S
    trans := trans S }

中文:
定义 setoid
  签名: : 集合等价关系 S.Splitting where
  定义体: S.IsConj
  iseqv :=
  { refl := refl S
    symm := symm S
    trans := trans S }

Depends on / 依赖: IsConj, S.IsConj
-/
def setoid : Setoid S.Splitting where
  r := S.IsConj
  iseqv :=
  { refl := refl S
    symm := symm S
    trans := trans S }

end IsConj

/-- The `N`-conjugacy classes of splittings -/
@[to_additive /-- The `N`-conjugacy classes of splittings -/]
/--
Definition of `ConjClasses` / `ConjClasses` 的定义

English:
definition ConjClasses
  body: Quotient IsConj.setoid S

中文:
定义 ConjClasses
  定义体: Quotient IsConj.setoid S

Depends on / 依赖: IsConj, IsConj.setoid, Quotient, setoid
-/
def ConjClasses := Quotient IsConj.setoid S

end GroupExtension

namespace SemidirectProduct

variable {φ : G ->* MulAut N} (s : (toGroupExtension φ).Splitting)

/--
theorem `right_splitting` / 定理 `right_splitting`

English:
theorem right_splitting
  given: (g : G)
  statement: (s g).right = g
  proof: by
  rw [← rightHom_eq_right]; rw [← toGroupExtension_rightHom]; rw [s.rightHom_splitting]

中文:
定理 right_splitting
  条件: (g : G)
  结论: (s g).right = g
  证明: by
  rw [← rightHom_eq_right]; rw [← toGroupExtension_rightHom]; rw [s.rightHom_splitting]

Depends on / 依赖: rightHom_eq_right, rightHom_splitting, s.rightHom_splitting, toGroupExtension_rightHom
-/
theorem right_splitting (g : G) : (s g).right = g := by
  rw [← rightHom_eq_right]; rw [← toGroupExtension_rightHom]; rw [s.rightHom_splitting]

end SemidirectProduct
