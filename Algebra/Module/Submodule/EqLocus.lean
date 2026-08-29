/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker

/-!
# The submodule of elements `x : M` such that `f x = g x`

## Main declarations

* `LinearMap.eqLocus`: the submodule of elements `x : M` such that `f x = g x`

## Tags
linear algebra, vector space, module

-/

@[expose] public section

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]

open Submodule

variable {τ₁₂ : R ->+* R₂}

section

/--
Definition of `eqLocus` / `eqLocus` 的定义

English:
definition eqLocus
  signature: (f g : M ->ₛₗ[τ₁₂] M₂)
  body: { (f : M ->+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simpa only [map_smulₛₗ _] using congr_arg (τ₁₂ r • ·) hx }

@[simp]

中文:
定义 eqLocus
  签名: (f g : M ->ₛₗ[τ₁₂] M₂)
  定义体: { (f : M ->+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simpa only [map_smulₛₗ _] using congr_arg (τ₁₂ r • ·) hx }

@[simp]

Depends on / 依赖: carrier, eqLocusM, smul_mem
-/
def eqLocus (f g : M ->ₛₗ[τ₁₂] M₂) : Submodule R M :=
  { (f : M ->+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simpa only [map_smulₛₗ _] using congr_arg (τ₁₂ r • ·) hx }

@[simp]
/--
theorem `mem_eqLocus` / 定理 `mem_eqLocus`

English:
theorem mem_eqLocus
  given: {x : M} {f g : M ->ₛₗ[τ₁₂] M₂}
  statement: x in eqLocus f g ↔ f x = g x
  proof: Iff.rfl

中文:
定理 mem_eqLocus
  条件: {x : M} {f g : M ->ₛₗ[τ₁₂] M₂}
  结论: x in eqLocus f g ↔ f x = g x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocus {x : M} {f g : M ->ₛₗ[τ₁₂] M₂} : x in eqLocus f g ↔ f x = g x :=
  Iff.rfl

/--
theorem `eqLocus_toAddSubmonoid` / 定理 `eqLocus_toAddSubmonoid`

English:
theorem eqLocus_toAddSubmonoid
  given: (f g : M ->ₛₗ[τ₁₂] M₂)
  proof: rfl

@[simp]

中文:
定理 eqLocus_toAddSubmonoid
  条件: (f g : M ->ₛₗ[τ₁₂] M₂)
  证明: rfl

@[simp]
-/
theorem eqLocus_toAddSubmonoid (f g : M ->ₛₗ[τ₁₂] M₂) :
    (eqLocus f g).toAddSubmonoid = (f : M ->+ M₂).eqLocusM g :=
  rfl

@[simp]
/--
theorem `eqLocus_eq_top` / 定理 `eqLocus_eq_top`

English:
theorem eqLocus_eq_top
  given: {f g : M ->ₛₗ[τ₁₂] M₂}
  statement: eqLocus f g = ⊤ ↔ f = g
  proof: by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]

中文:
定理 eqLocus_eq_top
  条件: {f g : M ->ₛₗ[τ₁₂] M₂}
  结论: eqLocus f g = ⊤ ↔ f = g
  证明: by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, SetLike, SetLike.ext_iff, ext_iff
-/
theorem eqLocus_eq_top {f g : M ->ₛₗ[τ₁₂] M₂} : eqLocus f g = ⊤ ↔ f = g := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]
/--
theorem `eqLocus_same` / 定理 `eqLocus_same`

English:
theorem eqLocus_same
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: eqLocus f f = ⊤
  proof: eqLocus_eq_top.2 rfl

中文:
定理 eqLocus_same
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: eqLocus f f = ⊤
  证明: eqLocus_eq_top.2 rfl

Depends on / 依赖: eqLocus_eq_top
-/
theorem eqLocus_same (f : M ->ₛₗ[τ₁₂] M₂) : eqLocus f f = ⊤ := eqLocus_eq_top.2 rfl

/--
theorem `le_eqLocus` / 定理 `le_eqLocus`

English:
theorem le_eqLocus
  given: {f g : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M}
  proof: Iff.rfl

中文:
定理 le_eqLocus
  条件: {f g : M ->ₛₗ[τ₁₂] M₂} {S : 子模 R M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    S <= eqLocus f g ↔ Set.EqOn f g S :=
  Iff.rfl

/--
theorem `eqOn_eqLocus` / 定理 `eqOn_eqLocus`

English:
theorem eqOn_eqLocus
  given: {f g : M ->ₛₗ[τ₁₂] M₂}
  proof: fun _ h => h

中文:
定理 eqOn_eqLocus
  条件: {f g : M ->ₛₗ[τ₁₂] M₂}
  证明: fun _ h => h
-/
theorem eqOn_eqLocus {f g : M ->ₛₗ[τ₁₂] M₂} :
    Set.EqOn f g (eqLocus f g) :=
  fun _ h => h

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

include τ₁₂ in
/--
theorem `eqOn_sup` / 定理 `eqOn_sup`

English:
theorem eqOn_sup
  statement: {f g : F} {S T : Submodule R M}
  proof: by
  rw [← LinearMap.coe_coe (f := f)]; rw [← LinearMap.coe_coe (f := g)]; rw [← le_eqLocus] at hS hT ⊢
  exact sup_le hS hT

include τ₁₂ in

中文:
定理 eqOn_sup
  结论: {f g : F} {S T : 子模 R M}
  证明: by
  rw [← LinearMap.coe_coe (f := f)]; rw [← LinearMap.coe_coe (f := g)]; rw [← le_eqLocus] at hS hT ⊢
  exact sup_le hS hT

include τ₁₂ in

Depends on / 依赖: LinearMap, LinearMap.coe_coe, coe_coe, le_eqLocus, sup_le
-/
theorem eqOn_sup {f g : F} {S T : Submodule R M}
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) :
    Set.EqOn f g ↑(S ⊔ T) := by
  rw [← LinearMap.coe_coe (f := f)]; rw [← LinearMap.coe_coe (f := g)]; rw [← le_eqLocus] at hS hT ⊢
  exact sup_le hS hT

include τ₁₂ in
/--
theorem `ext_on_codisjoint` / 定理 `ext_on_codisjoint`

English:
theorem ext_on_codisjoint
  statement: {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
  proof: DFunLike.ext _ _ fun _ => eqOn_sup hS hT hST.eq_top.symm ▸ trivial

中文:
定理 ext_on_codisjoint
  结论: {f g : F} {S T : 子模 R M} (hST : Codisjoint S T)
  证明: DFunLike.ext _ _ fun _ => eqOn_sup hS hT hST.eq_top.symm ▸ trivial

Depends on / 依赖: DFunLike, DFunLike.ext, eqOn_sup, eq_top, hST.eq_top.symm
-/
theorem ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g :=
DFunLike.ext _ _ fun _ => eqOn_sup hS hT hST.eq_top.symm ▸ trivial

end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂}

open Submodule

/--
theorem `eqLocus_eq_ker_sub` / 定理 `eqLocus_eq_ker_sub`

English:
theorem eqLocus_eq_ker_sub
  given: (f g : M ->ₛₗ[τ₁₂] M₂)
  statement: eqLocus f g = ker (f - g)
  proof: SetLike.ext fun _ => sub_eq_zero.symm

中文:
定理 eqLocus_eq_ker_sub
  条件: (f g : M ->ₛₗ[τ₁₂] M₂)
  结论: eqLocus f g = ker (f - g)
  证明: SetLike.ext fun _ => sub_eq_zero.symm

Depends on / 依赖: SetLike, SetLike.ext, sub_eq_zero, sub_eq_zero.symm
-/
theorem eqLocus_eq_ker_sub (f g : M ->ₛₗ[τ₁₂] M₂) : eqLocus f g = ker (f - g) :=
  SetLike.ext fun _ => sub_eq_zero.symm

end Ring

end LinearMap
