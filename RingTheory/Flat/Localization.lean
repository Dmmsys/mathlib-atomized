/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Flatness and localization

In this file we show that localizations are flat, and flatness is a local property.

## Main result
* `IsLocalization.flat`: a localization of a commutative ring is flat over it.
* `Module.flat_iff_of_isLocalization` : Let `Rₚ` a localization of a commutative ring `R`
  and `M` be a module over `Rₚ`. Then `M` is flat over `R` if and only if `M` is flat over `Rₚ`.
* `Module.flat_of_isLocalized_maximal` : Let `M` be a module over a commutative ring `R`.
  If the localization of `M` at each maximal ideal `P` is flat over `Rₚ`, then `M` is flat over `R`.
* `Module.flat_of_isLocalized_span` : Let `M` be a module over a commutative ring `R`
  and `S` be a set that spans `R`. If the localization of `M` at each `s : S` is flat
  over `Localization.Away s`, then `M` is flat over `R`.
-/

public section

open IsLocalizedModule LocalizedModule LinearMap TensorProduct

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

set_option backward.isDefEq.respectTransparency.types false in
include p in
/--
theorem `IsLocalization.flat` / 定理 `IsLocalization.flat`

English:
theorem IsLocalization.flat
  statement: Module.Flat R S
  proof: by
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N => ?_
  have h := ((range N.subtype).isLocalizedModule S p (TensorProduct.mk R S P 1)).isBaseChange _ S
  let e := (LinearEquiv.ofInjective _ Subtype.val_injective).lTensor S ≪≫ₗ h.equiv.restrictScalars R
  have : N.subtype.lTensor S = S

中文:
定理 是Localization.flat
  结论: 模.平坦 R S
  证明: by
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N => ?_
  have h := ((range N.subtype).isLocalizedModule S p (TensorProduct.mk R S P 1)).isBaseChange _ S
  let e := (LinearEquiv.ofInjective _ Subtype.val_injective).lTensor S ≪≫ₗ h.equiv.restrictScalars R
  have : N.subtype.lTensor S = S

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, Module, Module.Flat.iff_lTensor_injective, N.subtype, N.subtype.lTensor, Submodule, Submodule.subtype, Subtype, Subtype.val_injective, TensorProduct, TensorProduct.mk, TensorProduct.smul_tmul, e.injective, e.toLinearMap, equiv_tmul, h.equiv, h.equiv.restrictScalars, h.equiv_tmul, injective
-/
theorem IsLocalization.flat : Module.Flat R S := by
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N => ?_
  have h := ((range N.subtype).isLocalizedModule S p (TensorProduct.mk R S P 1)).isBaseChange _ S
  let e := (LinearEquiv.ofInjective _ Subtype.val_injective).lTensor S ≪≫ₗ h.equiv.restrictScalars R
  have : N.subtype.lTensor S = Submodule.subtype _ ∘ₗ e.toLinearMap := by
    ext; change _ = (h.equiv _).1; simp [h.equiv_tmul, TensorProduct.smul_tmul']
  simpa [this] using! e.injective

/--
Instance `Localization.flat` / 实例 `Localization.flat`

English:
instance Localization.flat
  signature: [Module.Flat R S] (p : Submonoid S)
  body: have : Module.Flat S (Localization p) := IsLocalization.flat _ p
  .trans R S _

中文:
实例 Localization.flat
  签名: [模.平坦 R S] (p : 子幺半群 S)
  定义体: have : Module.Flat S (Localization p) := IsLocalization.flat _ p
  .trans R S _

Depends on / 依赖: IsLocalization, IsLocalization.flat, Localization, Module, Module.Flat
-/
instance Localization.flat [Module.Flat R S] (p : Submonoid S) : Module.Flat R (Localization p) :=
  have : Module.Flat S (Localization p) := IsLocalization.flat _ p
  .trans R S _

namespace Module

include p in
/--
theorem `flat_iff_of_isLocalization` / 定理 `flat_iff_of_isLocalization`

English:
theorem flat_iff_of_isLocalization
  statement: Flat S M ↔ Flat R M
  proof: have := isLocalizedModule_id p M S
  have := IsLocalization.flat S p
  ⟨fun _ => .trans R S M, fun _ => .of_isLocalizedModule S p .id⟩

中文:
定理 flat_iff_of_isLocalization
  结论: 平坦 S M ↔ 平坦 R M
  证明: have := isLocalizedModule_id p M S
  have := IsLocalization.flat S p
  ⟨fun _ => .trans R S M, fun _ => .of_isLocalizedModule S p .id⟩

Depends on / 依赖: IsLocalization, IsLocalization.flat, isLocalizedModule_id, of_isLocalizedModule
-/
theorem flat_iff_of_isLocalization : Flat S M ↔ Flat R M :=
  have := isLocalizedModule_id p M S
  have := IsLocalization.flat S p
  ⟨fun _ => .trans R S M, fun _ => .of_isLocalizedModule S p .id⟩

variable (Mₚ : forall (P : Ideal S) [P.IsMaximal], Type*)
  [forall (P : Ideal S) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [forall (P : Ideal S) [P.IsMaximal], Module R (Mₚ P)]
  [forall (P : Ideal S) [P.IsMaximal], Module S (Mₚ P)]
  [forall (P : Ideal S) [P.IsMaximal], IsScalarTower R S (Mₚ P)]
  (f : forall (P : Ideal S) [P.IsMaximal], M ->ₗ[S] Mₚ P)
  [forall (P : Ideal S) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]

include f in
/--
theorem `flat_of_isLocalized_maximal` / 定理 `flat_of_isLocalized_maximal`

English:
theorem flat_of_isLocalized_maximal
  given: (H : forall (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P))
  proof: by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N => injective_of_isLocalized_maximal _
    (fun P => AlgebraTensorModule.rTensor R _ (f P)) _
    (fun P => AlgebraTensorModule.rTensor R _ (f P)) _ fun P hP => ?_
  simpa [Is

中文:
定理 flat_of_isLocalized_maximal
  条件: (H : 对任意 (P : 理想 S) [P.是极大], 平坦 R (Mₚ P))
  证明: by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N => injective_of_isLocalized_maximal _
    (fun P => AlgebraTensorModule.rTensor R _ (f P)) _
    (fun P => AlgebraTensorModule.rTensor R _ (f P)) _ fun P hP => ?_
  simpa [Is

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.coe_lTensor, AlgebraTensorModule.rTensor, Flat.iff_lTensor_injective, IsLocalizedModule, IsLocalizedModule.map_lTensor, coe_lTensor, injective_of_isLocalized_maximal, map_lTensor, rTensor, simp_rw
-/
theorem flat_of_isLocalized_maximal (H : forall (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P)) :
    Module.Flat R M := by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N => injective_of_isLocalized_maximal _
    (fun P => AlgebraTensorModule.rTensor R _ (f P)) _
    (fun P => AlgebraTensorModule.rTensor R _ (f P)) _ fun P hP => ?_
  simpa [IsLocalizedModule.map_lTensor] using H P N

/--
theorem `flat_of_localized_maximal` / 定理 `flat_of_localized_maximal`

English:
theorem flat_of_localized_maximal
  proof: flat_of_isLocalized_maximal _ _ _ (fun _ _ => mkLinearMap _ _) h

中文:
定理 flat_of_localized_maximal
  证明: flat_of_isLocalized_maximal _ _ _ (fun _ _ => mkLinearMap _ _) h

Depends on / 依赖: flat_of_isLocalized_maximal, mkLinearMap
-/
theorem flat_of_localized_maximal
    (h : forall (P : Ideal R) [P.IsMaximal], Flat R (LocalizedModule P.primeCompl M)) :
    Flat R M :=
  flat_of_isLocalized_maximal _ _ _ (fun _ _ => mkLinearMap _ _) h

variable (s : Set S) (spn : Ideal.span s = ⊤)
  (Mₛ : forall _ : s, Type*)
  [forall r : s, AddCommMonoid (Mₛ r)]
  [forall r : s, Module R (Mₛ r)]
  [forall r : s, Module S (Mₛ r)]
  [forall r : s, IsScalarTower R S (Mₛ r)]
  (g : forall r : s, M ->ₗ[S] Mₛ r)
  [forall r : s, IsLocalizedModule.Away r.1 (g r)]
include spn

include g in
/--
theorem `flat_of_isLocalized_span` / 定理 `flat_of_isLocalized_span`

English:
theorem flat_of_isLocalized_span
  given: (H : forall r : s, Module.Flat R (Mₛ r))
  proof: by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N => injective_of_isLocalized_span s spn _
    (fun r => AlgebraTensorModule.rTensor R _ (g r)) _
    (fun r => AlgebraTensorModule.rTensor R _ (g r)) _ fun r => ?_
  simpa [Is

中文:
定理 flat_of_isLocalized_span
  条件: (H : 对任意 r : s, 模.平坦 R (Mₛ r))
  证明: by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N => injective_of_isLocalized_span s spn _
    (fun r => AlgebraTensorModule.rTensor R _ (g r)) _
    (fun r => AlgebraTensorModule.rTensor R _ (g r)) _ fun r => ?_
  simpa [Is

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.coe_lTensor, AlgebraTensorModule.rTensor, Flat.iff_lTensor_injective, IsLocalizedModule, IsLocalizedModule.map_lTensor, coe_lTensor, injective_of_isLocalized_span, map_lTensor, rTensor, simp_rw
-/
theorem flat_of_isLocalized_span (H : forall r : s, Module.Flat R (Mₛ r)) :
    Module.Flat R M := by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N => injective_of_isLocalized_span s spn _
    (fun r => AlgebraTensorModule.rTensor R _ (g r)) _
    (fun r => AlgebraTensorModule.rTensor R _ (g r)) _ fun r => ?_
  simpa [IsLocalizedModule.map_lTensor] using H r N

/--
theorem `flat_of_localized_span` / 定理 `flat_of_localized_span`

English:
theorem flat_of_localized_span
  proof: flat_of_isLocalized_span _ _ _ spn _ (fun _ => mkLinearMap _ _) h

中文:
定理 flat_of_localized_span
  证明: flat_of_isLocalized_span _ _ _ spn _ (fun _ => mkLinearMap _ _) h

Depends on / 依赖: flat_of_isLocalized_span, mkLinearMap
-/
theorem flat_of_localized_span
    (h : forall r : s, Flat S (LocalizedModule.Away r.1 M)) :
    Flat S M :=
  flat_of_isLocalized_span _ _ _ spn _ (fun _ => mkLinearMap _ _) h

end Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Flat
  signature: A B] (p
  body: by
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]
  exact Module.Flat.trans A B (Localization.AtPrime P)

中文:
实例 [模.平坦
  签名: A B] (p
  定义体: by
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]
  exact Module.Flat.trans A B (Localization.AtPrime P)

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, Module, Module.Flat.trans, Module.flat_iff_of_isLocalization, flat_iff_of_isLocalization, p.primeCompl, primeCompl
-/
instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra p P] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) := by
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]
  exact Module.Flat.trans A B (Localization.AtPrime P)

section IsSMulRegular

variable {M} in
/--
theorem `IsSMulRegular.of_isLocalizedModule` / 定理 `IsSMulRegular.of_isLocalizedModule`

English:
theorem IsSMulRegular.of_isLocalizedModule
  statement: {K : Type*} [AddCommMonoid K] [Module R K]
  proof: have : Module.Flat R S := IsLocalization.flat S p
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange p S f)

include p in

中文:
定理 IsSMulRegular.of_isLocalizedModule
  结论: {K : 类型} [加法交换幺半群 K] [模 R K]
  证明: have : Module.Flat R S := IsLocalization.flat S p
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange p S f)

include p in

Depends on / 依赖: IsLocalization, IsLocalization.flat, IsLocalizedModule, IsLocalizedModule.isBaseChange, Module, Module.Flat, isBaseChange, of_flat_of_isBaseChange, reg.of_flat_of_isBaseChange
-/
theorem IsSMulRegular.of_isLocalizedModule {K : Type*} [AddCommMonoid K] [Module R K]
    (f : K ->ₗ[R] M) [IsLocalizedModule p f] {x : R} (reg : IsSMulRegular K x) :
    IsSMulRegular M (algebraMap R S x) :=
  have : Module.Flat R S := IsLocalization.flat S p
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange p S f)

include p in
/--
theorem `IsSMulRegular.of_isLocalization` / 定理 `IsSMulRegular.of_isLocalization`

English:
theorem IsSMulRegular.of_isLocalization
  given: {x : R} (reg : IsSMulRegular R x)
  proof: reg.of_isLocalizedModule S p (Algebra.linearMap R S)

中文:
定理 IsSMulRegular.of_isLocalization
  条件: {x : R} (reg : IsSMulRegular R x)
  证明: reg.of_isLocalizedModule S p (Algebra.linearMap R S)

Depends on / 依赖: Algebra, Algebra.linearMap, linearMap, of_isLocalizedModule, reg.of_isLocalizedModule
-/
theorem IsSMulRegular.of_isLocalization {x : R} (reg : IsSMulRegular R x) :
    IsSMulRegular S (algebraMap R S x) :=
  reg.of_isLocalizedModule S p (Algebra.linearMap R S)

end IsSMulRegular
