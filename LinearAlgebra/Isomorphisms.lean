/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Isomorphism theorems for modules.

* The Noether's first, second, and third isomorphism theorems for modules are proved as
  `LinearMap.quotKerEquivRange`, `LinearMap.quotientInfEquivSupQuotient` and
  `Submodule.quotientQuotientEquivQuotient`.

-/

@[expose] public section

universe u v

variable {R M M₂ M₃ : Type*}
variable [Ring R] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable (f : M ->ₗ[R] M₂)

/-! The first and second isomorphism theorems for modules. -/

namespace LinearMap

open Submodule

section IsomorphismLaws

/--
Definition of `quotKerEquivRange` / `quotKerEquivRange` 的定义

English:
definition quotKerEquivRange
  signature: : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f
  body: -- TODO: We should fix this definition so that `fₗ.quotKerEquivRange.toAddEquiv` is definitionally
  -- equal to `QuotientAddGroup.quotientKerEquivRange f.toAddMonoidHom`.
  (LinearEquiv.ofInjective ((LinearMap.ker f).liftQ f <| le_rfl) <|
ker_eq_bot.mp Submodule.ker_liftQ_eq_bot _ _ _ (le_refl (Lin

中文:
定义 quotKerEquivRange
  签名: : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f
  定义体: -- TODO: We should fix this definition so that `fₗ.quotKerEquivRange.toAddEquiv` is definitionally
  -- equal to `QuotientAddGroup.quotientKerEquivRange f.toAddMonoidHom`.
  (LinearEquiv.ofInjective ((LinearMap.ker f).liftQ f <| le_rfl) <|
ker_eq_bot.mp Submodule.ker_liftQ_eq_bot _ _ _ (le_refl (Lin
-/
noncomputable def quotKerEquivRange : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  -- TODO: We should fix this definition so that `fₗ.quotKerEquivRange.toAddEquiv` is definitionally
  -- equal to `QuotientAddGroup.quotientKerEquivRange f.toAddMonoidHom`.
  (LinearEquiv.ofInjective ((LinearMap.ker f).liftQ f <| le_rfl) <|
ker_eq_bot.mp Submodule.ker_liftQ_eq_bot _ _ _ (le_refl (LinearMap.ker f))).trans
    (LinearEquiv.ofEq _ _ <| Submodule.range_liftQ _ _ _)

/--
Definition of `quotKerEquivOfSurjective` / `quotKerEquivOfSurjective` 的定义

English:
definition quotKerEquivOfSurjective
  signature: (f : M ->ₗ[R] M₂) (hf : Function.Surjective f)
  body: f.quotKerEquivRange.trans .ofTop (LinearMap.range f) range_eq_top.2 hf

@[simp]

中文:
定义 quotKerEquivOfSurjective
  签名: (f : M ->ₗ[R] M₂) (hf : Function.Surjective f)
  定义体: f.quotKerEquivRange.trans .ofTop (LinearMap.range f) range_eq_top.2 hf

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range, f.quotKerEquivRange.trans, quotKerEquivRange, range_eq_top
-/
noncomputable def quotKerEquivOfSurjective (f : M ->ₗ[R] M₂) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] M₂ :=
f.quotKerEquivRange.trans .ofTop (LinearMap.range f) range_eq_top.2 hf

@[simp]
/--
theorem `quotKerEquivRange_apply_mk` / 定理 `quotKerEquivRange_apply_mk`

English:
theorem quotKerEquivRange_apply_mk
  given: (x : M)
  proof: rfl

@[simp]

中文:
定理 quotKerEquivRange_apply_mk
  条件: (x : M)
  证明: rfl

@[simp]
-/
theorem quotKerEquivRange_apply_mk (x : M) :
    (f.quotKerEquivRange (Submodule.Quotient.mk x) : M₂) = f x :=
  rfl

@[simp]
/--
theorem `quotKerEquivOfSurjective_apply_mk` / 定理 `quotKerEquivOfSurjective_apply_mk`

English:
theorem quotKerEquivOfSurjective_apply_mk
  given: (hf : Function.Surjective f) (x : M)
  proof: rfl

@[simp]

中文:
定理 quotKerEquivOfSurjective_apply_mk
  条件: (hf : Function.Surjective f) (x : M)
  证明: rfl

@[simp]
-/
theorem quotKerEquivOfSurjective_apply_mk (hf : Function.Surjective f) (x : M) :
    (f.quotKerEquivOfSurjective hf (Submodule.Quotient.mk x) : M₂) = f x :=
  rfl

@[simp]
/--
theorem `quotKerEquivRange_symm_apply_image` / 定理 `quotKerEquivRange_symm_apply_image`

English:
theorem quotKerEquivRange_symm_apply_image
  given: (x : M) (h : f x in LinearMap.range f)
  proof: f.quotKerEquivRange.symm_apply_apply ((LinearMap.ker f).mkQ x)

@[simp]

中文:
定理 quotKerEquivRange_symm_apply_image
  条件: (x : M) (h : f x in LinearMap.range f)
  证明: f.quotKerEquivRange.symm_apply_apply ((LinearMap.ker f).mkQ x)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ker, f.quotKerEquivRange.symm_apply_apply, quotKerEquivRange, symm_apply_apply
-/
theorem quotKerEquivRange_symm_apply_image (x : M) (h : f x in LinearMap.range f) :
    f.quotKerEquivRange.symm ⟨f x, h⟩ = (LinearMap.ker f).mkQ x :=
  f.quotKerEquivRange.symm_apply_apply ((LinearMap.ker f).mkQ x)

@[simp]
/--
theorem `quotKerEquivOfSurjective_symm_apply` / 定理 `quotKerEquivOfSurjective_symm_apply`

English:
theorem quotKerEquivOfSurjective_symm_apply
  given: (hf : Function.Surjective f) (x : M)
  proof: by
  simp [LinearEquiv.symm_apply_eq]

中文:
定理 quotKerEquivOfSurjective_symm_apply
  条件: (hf : Function.Surjective f) (x : M)
  证明: by
  simp [LinearEquiv.symm_apply_eq]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
theorem quotKerEquivOfSurjective_symm_apply (hf : Function.Surjective f) (x : M) :
    (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x := by
  simp [LinearEquiv.symm_apply_eq]

/--
Definition of `subToSupQuotient` / `subToSupQuotient` 的定义

English:
abbreviation subToSupQuotient
  signature: (p p' : Submodule R M)
  body: (comap (p ⊔ p').subtype p').mkQ.comp (Submodule.inclusion le_sup_left)

中文:
缩写 subToSupQuotient
  签名: (p p' : Submodule R M)
  定义体: (comap (p ⊔ p').subtype p').mkQ.comp (Submodule.inclusion le_sup_left)

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion, le_sup_left, mkQ.comp, subtype
-/
abbrev subToSupQuotient (p p' : Submodule R M) :
    { x // x in p } ->ₗ[R] { x // x in p ⊔ p' } ⧸ comap (Submodule.subtype (p ⊔ p')) p' :=
  (comap (p ⊔ p').subtype p').mkQ.comp (Submodule.inclusion le_sup_left)

/--
theorem `comap_leq_ker_subToSupQuotient` / 定理 `comap_leq_ker_subToSupQuotient`

English:
theorem comap_leq_ker_subToSupQuotient
  given: (p p' : Submodule R M)
  proof: by
  rw [LinearMap.ker_comp]; rw [Submodule.inclusion]; rw [comap_codRestrict]; rw [ker_mkQ]; rw [map_comap_subtype]
  exact comap_mono (inf_le_inf_right _ le_sup_left)

中文:
定理 comap_leq_ker_subToSupQuotient
  条件: (p p' : Submodule R M)
  证明: by
  rw [LinearMap.ker_comp]; rw [Submodule.inclusion]; rw [comap_codRestrict]; rw [ker_mkQ]; rw [map_comap_subtype]
  exact comap_mono (inf_le_inf_right _ le_sup_left)

Depends on / 依赖: LinearMap, LinearMap.ker_comp, Submodule, Submodule.inclusion, comap_codRestrict, comap_mono, inclusion, inf_le_inf_right, ker_comp, ker_mkQ, le_sup_left, map_comap_subtype
-/
theorem comap_leq_ker_subToSupQuotient (p p' : Submodule R M) :
    comap (Submodule.subtype p) (p ⊓ p') <= ker (subToSupQuotient p p') := by
  rw [LinearMap.ker_comp]; rw [Submodule.inclusion]; rw [comap_codRestrict]; rw [ker_mkQ]; rw [map_comap_subtype]
  exact comap_mono (inf_le_inf_right _ le_sup_left)

/--
Definition of `quotientInfToSupQuotient` / `quotientInfToSupQuotient` 的定义

English:
definition quotientInfToSupQuotient
  signature: (p p' : Submodule R M)
  body: (comap p.subtype (p ⊓ p')).liftQ (subToSupQuotient p p') (comap_leq_ker_subToSupQuotient p p')

中文:
定义 quotientInfToSupQuotient
  签名: (p p' : Submodule R M)
  定义体: (comap p.subtype (p ⊓ p')).liftQ (subToSupQuotient p p') (comap_leq_ker_subToSupQuotient p p')

Depends on / 依赖: comap_leq_ker_subToSupQuotient, p.subtype, subToSupQuotient, subtype
-/
def quotientInfToSupQuotient (p p' : Submodule R M) :
    (↥p) ⧸ (comap p.subtype p ⊓ comap p.subtype p') ->ₗ[R]
      (↥(p ⊔ p')) ⧸ (comap (p ⊔ p').subtype p') :=
  (comap p.subtype (p ⊓ p')).liftQ (subToSupQuotient p p') (comap_leq_ker_subToSupQuotient p p')

set_option backward.isDefEq.respectTransparency false in
/--
theorem `quotientInfEquivSupQuotient_injective` / 定理 `quotientInfEquivSupQuotient_injective`

English:
theorem quotientInfEquivSupQuotient_injective
  given: (p p' : Submodule R M)
  proof: by
  rw [← ker_eq_bot]; rw [quotientInfToSupQuotient]; rw [ker_liftQ_eq_bot]
  rw [ker_comp]; rw [ker_mkQ]
  exact fun ⟨x, hx1⟩ hx2 => ⟨hx1, hx2⟩

中文:
定理 quotientInfEquivSupQuotient_injective
  条件: (p p' : Submodule R M)
  证明: by
  rw [← ker_eq_bot]; rw [quotientInfToSupQuotient]; rw [ker_liftQ_eq_bot]
  rw [ker_comp]; rw [ker_mkQ]
  exact fun ⟨x, hx1⟩ hx2 => ⟨hx1, hx2⟩

Depends on / 依赖: ker_comp, ker_eq_bot, ker_liftQ_eq_bot, ker_mkQ, quotientInfToSupQuotient
-/
theorem quotientInfEquivSupQuotient_injective (p p' : Submodule R M) :
    Function.Injective (quotientInfToSupQuotient p p') := by
  rw [← ker_eq_bot]; rw [quotientInfToSupQuotient]; rw [ker_liftQ_eq_bot]
  rw [ker_comp]; rw [ker_mkQ]
  exact fun ⟨x, hx1⟩ hx2 => ⟨hx1, hx2⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `quotientInfEquivSupQuotient_surjective` / 定理 `quotientInfEquivSupQuotient_surjective`

English:
theorem quotientInfEquivSupQuotient_surjective
  given: (p p' : Submodule R M)
  proof: by
  rw [← range_eq_top]; rw [quotientInfToSupQuotient]; rw [range_liftQ]; rw [eq_top_iff']
  rintro ⟨x, hx⟩; rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩
  use ⟨y, hy⟩; apply (Submodule.Quotient.eq _).2
  simp only [mem_comap, map_sub, coe_subtype, coe_inclusion, sub_add_cancel_left, neg_mem_iff, h

中文:
定理 quotientInfEquivSupQuotient_surjective
  条件: (p p' : Submodule R M)
  证明: by
  rw [← range_eq_top]; rw [quotientInfToSupQuotient]; rw [range_liftQ]; rw [eq_top_iff']
  rintro ⟨x, hx⟩; rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩
  use ⟨y, hy⟩; apply (Submodule.Quotient.eq _).2
  simp only [mem_comap, map_sub, coe_subtype, coe_inclusion, sub_add_cancel_left, neg_mem_iff, h

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.eq, coe_inclusion, coe_subtype, eq_top_iff, map_sub, mem_comap, mem_sup, neg_mem_iff, quotientInfToSupQuotient, range_eq_top, range_liftQ, sub_add_cancel_left
-/
theorem quotientInfEquivSupQuotient_surjective (p p' : Submodule R M) :
    Function.Surjective (quotientInfToSupQuotient p p') := by
  rw [← range_eq_top]; rw [quotientInfToSupQuotient]; rw [range_liftQ]; rw [eq_top_iff']
  rintro ⟨x, hx⟩; rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩
  use ⟨y, hy⟩; apply (Submodule.Quotient.eq _).2
  simp only [mem_comap, map_sub, coe_subtype, coe_inclusion, sub_add_cancel_left, neg_mem_iff, hz]

/--
Definition of `quotientInfEquivSupQuotient` / `quotientInfEquivSupQuotient` 的定义

English:
definition quotientInfEquivSupQuotient
  signature: (p p' : Submodule R M)
  body: LinearEquiv.ofBijective (quotientInfToSupQuotient p p')
    ⟨quotientInfEquivSupQuotient_injective p p', quotientInfEquivSupQuotient_surjective p p'⟩

@[simp]

中文:
定义 quotientInfEquivSupQuotient
  签名: (p p' : Submodule R M)
  定义体: LinearEquiv.ofBijective (quotientInfToSupQuotient p p')
    ⟨quotientInfEquivSupQuotient_injective p p', quotientInfEquivSupQuotient_surjective p p'⟩

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, ofBijective, quotientInfEquivSupQuotient_injective, quotientInfEquivSupQuotient_surjective, quotientInfToSupQuotient
-/
noncomputable def quotientInfEquivSupQuotient (p p' : Submodule R M) :
    (p ⧸ comap p.subtype p ⊓ comap p.subtype p') ≃ₗ[R] _ ⧸ comap (p ⊔ p').subtype p' :=
  LinearEquiv.ofBijective (quotientInfToSupQuotient p p')
    ⟨quotientInfEquivSupQuotient_injective p p', quotientInfEquivSupQuotient_surjective p p'⟩

@[simp]
/--
theorem `coe_quotientInfToSupQuotient` / 定理 `coe_quotientInfToSupQuotient`

English:
theorem coe_quotientInfToSupQuotient
  given: (p p' : Submodule R M)
  proof: rfl

中文:
定理 coe_quotientInfToSupQuotient
  条件: (p p' : Submodule R M)
  证明: rfl
-/
theorem coe_quotientInfToSupQuotient (p p' : Submodule R M) :
    ⇑(quotientInfToSupQuotient p p') = quotientInfEquivSupQuotient p p' :=
  rfl

/--
theorem `quotientInfEquivSupQuotient_apply_mk` / 定理 `quotientInfEquivSupQuotient_apply_mk`

English:
theorem quotientInfEquivSupQuotient_apply_mk
  given: (p p' : Submodule R M) (x : p)
  proof: inclusion (le_sup_left : p <= p ⊔ p')
    quotientInfEquivSupQuotient p p' (Submodule.Quotient.mk x) =
      @Submodule.Quotient.mk R (p ⊔ p' : Submodule R M) _ _ _ (comap (p ⊔ p').subtype p') (map x) :=
  rfl

中文:
定理 quotientInfEquivSupQuotient_apply_mk
  条件: (p p' : Submodule R M) (x : p)
  证明: inclusion (le_sup_left : p <= p ⊔ p')
    quotientInfEquivSupQuotient p p' (Submodule.Quotient.mk x) =
      @Submodule.Quotient.mk R (p ⊔ p' : Submodule R M) _ _ _ (comap (p ⊔ p').subtype p') (map x) :=
  rfl

Depends on / 依赖: inclusion, le_sup_left
-/
theorem quotientInfEquivSupQuotient_apply_mk (p p' : Submodule R M) (x : p) :
    let map := inclusion (le_sup_left : p <= p ⊔ p')
    quotientInfEquivSupQuotient p p' (Submodule.Quotient.mk x) =
      @Submodule.Quotient.mk R (p ⊔ p' : Submodule R M) _ _ _ (comap (p ⊔ p').subtype p') (map x) :=
  rfl

/--
theorem `quotientInfEquivSupQuotient_symm_apply_left` / 定理 `quotientInfEquivSupQuotient_symm_apply_left`

English:
theorem quotientInfEquivSupQuotient_symm_apply_left
  statement: (p p' : Submodule R M) (x : ↥(p ⊔ p'))
  proof: (LinearEquiv.symm_apply_eq _).2 by
    rw [quotientInfEquivSupQuotient_apply_mk]; rw [inclusion_apply]

中文:
定理 quotientInfEquivSupQuotient_symm_apply_left
  结论: (p p' : Submodule R M) (x : ↥(p ⊔ p'))
  证明: (LinearEquiv.symm_apply_eq _).2 by
    rw [quotientInfEquivSupQuotient_apply_mk]; rw [inclusion_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, inclusion_apply, quotientInfEquivSupQuotient_apply_mk, symm_apply_eq
-/
theorem quotientInfEquivSupQuotient_symm_apply_left (p p' : Submodule R M) (x : ↥(p ⊔ p'))
    (hx : (x : M) in p) :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨x, hx⟩ :=
(LinearEquiv.symm_apply_eq _).2 by
    rw [quotientInfEquivSupQuotient_apply_mk]; rw [inclusion_apply]


/--
theorem `quotientInfEquivSupQuotient_symm_apply_eq_zero_iff` / 定理 `quotientInfEquivSupQuotient_symm_apply_eq_zero_iff`

English:
theorem quotientInfEquivSupQuotient_symm_apply_eq_zero_iff
  given: {p p' : Submodule R M} {x : ↥(p ⊔ p')}
  proof: (LinearEquiv.symm_apply_eq _).trans by simp

中文:
定理 quotientInfEquivSupQuotient_symm_apply_eq_zero_iff
  条件: {p p' : Submodule R M} {x : ↥(p ⊔ p')}
  证明: (LinearEquiv.symm_apply_eq _).trans by simp

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
theorem quotientInfEquivSupQuotient_symm_apply_eq_zero_iff {p p' : Submodule R M} {x : ↥(p ⊔ p')} :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) = 0 ↔ (x : M) in p' :=
(LinearEquiv.symm_apply_eq _).trans by simp

/--
theorem `quotientInfEquivSupQuotient_symm_apply_right` / 定理 `quotientInfEquivSupQuotient_symm_apply_right`

English:
theorem quotientInfEquivSupQuotient_symm_apply_right
  statement: (p p' : Submodule R M) {x : ↥(p ⊔ p')}
  proof: quotientInfEquivSupQuotient_symm_apply_eq_zero_iff.2 hx

中文:
定理 quotientInfEquivSupQuotient_symm_apply_right
  结论: (p p' : Submodule R M) {x : ↥(p ⊔ p')}
  证明: quotientInfEquivSupQuotient_symm_apply_eq_zero_iff.2 hx

Depends on / 依赖: quotientInfEquivSupQuotient_symm_apply_eq_zero_iff
-/
theorem quotientInfEquivSupQuotient_symm_apply_right (p p' : Submodule R M) {x : ↥(p ⊔ p')}
    (hx : (x : M) in p') : (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x)
    = 0 :=
  quotientInfEquivSupQuotient_symm_apply_eq_zero_iff.2 hx

end IsomorphismLaws

end LinearMap

/-! The third isomorphism theorem for modules. -/

namespace Submodule

variable (S T : Submodule R M) (h : S <= T)

set_option backward.isDefEq.respectTransparency false in
-- @[simp]
/--
theorem `quotientQuotientEquivQuotientAux_mk_mk` / 定理 `quotientQuotientEquivQuotientAux_mk_mk`

English:
theorem quotientQuotientEquivQuotientAux_mk_mk
  given: (x : M)
  proof: rfl

中文:
定理 quotientQuotientEquivQuotientAux_mk_mk
  条件: (x : M)
  证明: rfl
-/
theorem quotientQuotientEquivQuotientAux_mk_mk (x : M) :
    quotientQuotientEquivQuotientAux S T h (Quotient.mk (Quotient.mk x)) = Quotient.mk x := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `quotientQuotientEquivQuotient` / `quotientQuotientEquivQuotient` 的定义

English:
definition quotientQuotientEquivQuotient
  signature: : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T
  body: { quotientQuotientEquivQuotientAux S T h with
    toFun := quotientQuotientEquivQuotientAux S T h
    invFun := mapQ _ _ (mkQ S) (le_comap_map _ _)
    left_inv := fun x => Submodule.Quotient.induction_on _
     x fun x => Submodule.Quotient.induction_on _ x fun x =>
      by simp
    right_inv := f

中文:
定义 quotientQuotientEquivQuotient
  签名: : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T
  定义体: { quotientQuotientEquivQuotientAux S T h with
    toFun := quotientQuotientEquivQuotientAux S T h
    invFun := mapQ _ _ (mkQ S) (le_comap_map _ _)
    left_inv := fun x => Submodule.Quotient.induction_on _
     x fun x => Submodule.Quotient.induction_on _ x fun x =>
      by simp
    right_inv := f

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.induction_on, induction_on, invFun, le_comap_map, left_inv, quotientQuotientEquivQuotientAux, right_inv
-/
def quotientQuotientEquivQuotient : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ T :=
  { quotientQuotientEquivQuotientAux S T h with
    toFun := quotientQuotientEquivQuotientAux S T h
    invFun := mapQ _ _ (mkQ S) (le_comap_map _ _)
    left_inv := fun x => Submodule.Quotient.induction_on _
     x fun x => Submodule.Quotient.induction_on _ x fun x =>
      by simp
    right_inv := fun x => Submodule.Quotient.induction_on _ x
      fun x => by simp }

/--
Definition of `quotientQuotientEquivQuotientSup` / `quotientQuotientEquivQuotientSup` 的定义

English:
definition quotientQuotientEquivQuotientSup
  signature: : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ S ⊔ T
  body: quotEquivOfEq _ _ (by rw [map_sup, mkQ_map_self, bot_sup_eq]) ≪≫ₗ
    quotientQuotientEquivQuotient S (S ⊔ T) le_sup_left

中文:
定义 quotientQuotientEquivQuotientSup
  签名: : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ S ⊔ T
  定义体: quotEquivOfEq _ _ (by rw [map_sup, mkQ_map_self, bot_sup_eq]) ≪≫ₗ
    quotientQuotientEquivQuotient S (S ⊔ T) le_sup_left

Depends on / 依赖: bot_sup_eq, le_sup_left, map_sup, mkQ_map_self, quotEquivOfEq, quotientQuotientEquivQuotient
-/
def quotientQuotientEquivQuotientSup : ((M ⧸ S) ⧸ T.map S.mkQ) ≃ₗ[R] M ⧸ S ⊔ T :=
  quotEquivOfEq _ _ (by rw [map_sup, mkQ_map_self, bot_sup_eq]) ≪≫ₗ
    quotientQuotientEquivQuotient S (S ⊔ T) le_sup_left

/--
theorem `card_quotient_mul_card_quotient` / 定理 `card_quotient_mul_card_quotient`

English:
theorem card_quotient_mul_card_quotient
  given: (S T : Submodule R M) (hST : T <= S)
  proof: by
  rw [Submodule.card_eq_card_quotient_mul_card (map T.mkQ S)]; rw [Nat.card_congr (quotientQuotientEquivQuotient T S hST).toEquiv]

中文:
定理 card_quotient_mul_card_quotient
  条件: (S T : Submodule R M) (hST : T <= S)
  证明: by
  rw [Submodule.card_eq_card_quotient_mul_card (map T.mkQ S)]; rw [Nat.card_congr (quotientQuotientEquivQuotient T S hST).toEquiv]

Depends on / 依赖: Nat.card_congr, Submodule, Submodule.card_eq_card_quotient_mul_card, T.mkQ, card_congr, card_eq_card_quotient_mul_card, quotientQuotientEquivQuotient, toEquiv
-/
theorem card_quotient_mul_card_quotient (S T : Submodule R M) (hST : T <= S) :
    Nat.card (S.map T.mkQ) * Nat.card (M ⧸ S) = Nat.card (M ⧸ T) := by
  rw [Submodule.card_eq_card_quotient_mul_card (map T.mkQ S)]; rw [Nat.card_congr (quotientQuotientEquivQuotient T S hST).toEquiv]

end Submodule
