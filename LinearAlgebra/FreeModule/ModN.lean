/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Quotienting out a free `ℤ`-module

If `G` is a rank `d` free `ℤ`-module, then `G/nG` is a finite group of cardinality `n ^ d`.
-/

@[expose] public section

open Finsupp Function Module

variable {G H M : Type*} [AddCommGroup G] {n : Nat}

variable (G n) in
/--
Definition of `ModN` / `ModN` 的定义

English:
abbreviation ModN
  signature: : Type _
  body: G ⧸ LinearMap.range (LinearMap.lsmul Int G n)

中文:
缩写 ModN
  签名: : Type _
  定义体: G ⧸ LinearMap.range (LinearMap.lsmul Int G n)

Depends on / 依赖: LinearMap, LinearMap.lsmul, LinearMap.range
-/
abbrev ModN : Type _ := G ⧸ LinearMap.range (LinearMap.lsmul Int G n)

namespace ModN

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module (ZMod n) (ModN G n)
  body: QuotientAddGroup.zmodModule (by simp)

中文:
实例 :
  签名: Module (ZMod n) (ModN G n)
  定义体: QuotientAddGroup.zmodModule (by simp)

Depends on / 依赖: QuotientAddGroup, QuotientAddGroup.zmodModule, zmodModule
-/
instance : Module (ZMod n) (ModN G n) := QuotientAddGroup.zmodModule (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: [AddMonoid M]
  body: ⟨f.comp (QuotientAddGroup.mk' _), fun g => by
    let Gn : AddSubgroup G := (LinearMap.range (LinearMap.lsmul Int G n)).toAddSubgroup
    suffices n • g in (QuotientAddGroup.mk' Gn).ker by
      simp only [AddMonoidHom.coe_comp, comp_apply, ← map_nsmul]
      change f (QuotientAddGroup.mk' Gn (n • g

中文:
定义 liftEquiv
  签名: [AddMonoid M]
  定义体: ⟨f.comp (QuotientAddGroup.mk' _), fun g => by
    let Gn : AddSubgroup G := (LinearMap.range (LinearMap.lsmul Int G n)).toAddSubgroup
    suffices n • g in (QuotientAddGroup.mk' Gn).ker by
      simp only [AddMonoidHom.coe_comp, comp_apply, ← map_nsmul]
      change f (QuotientAddGroup.mk' Gn (n • g
-/
protected def liftEquiv [AddMonoid M] : (ModN G n ->+ M) ≃ {φ : G ->+ M // forall g, n • φ g = 0} where
  toFun f := ⟨f.comp (QuotientAddGroup.mk' _), fun g => by
    let Gn : AddSubgroup G := (LinearMap.range (LinearMap.lsmul Int G n)).toAddSubgroup
    suffices n • g in (QuotientAddGroup.mk' Gn).ker by
      simp only [AddMonoidHom.coe_comp, comp_apply, ← map_nsmul]
      change f (QuotientAddGroup.mk' Gn (n • g)) = 0 -- Can we avoid `change`?
      rw [this]; rw [map_zero]
    simp [QuotientAddGroup.ker_mk', Gn]⟩
invFun φ := QuotientAddGroup.lift _ φ by rintro - ⟨g, rfl⟩; simpa using φ.property g
  left_inv f := by
    ext x
    induction x using QuotientAddGroup.induction_on
    rfl -- Should `simp` suffice here?
  right_inv φ := by aesop

/--
Definition of `liftEquiv'` / `liftEquiv'` 的定义

English:
definition liftEquiv'
  signature: [AddCommGroup H] [Module (ZMod n) H]
  body: (AddMonoidHom.toZModLinearMapEquiv n).symm.toEquiv.trans ModN.liftEquiv

中文:
定义 liftEquiv'
  签名: [AddCommGroup H] [Module (ZMod n) H]
  定义体: (AddMonoidHom.toZModLinearMapEquiv n).symm.toEquiv.trans ModN.liftEquiv
-/
protected def liftEquiv' [AddCommGroup H] [Module (ZMod n) H] :
    (ModN G n ->ₗ[ZMod n] H) ≃ {φ : G ->+ H // forall g, n • φ g = 0} :=
  (AddMonoidHom.toZModLinearMapEquiv n).symm.toEquiv.trans ModN.liftEquiv

variable (n) in
/--
Definition of `mkQ` / `mkQ` 的定义

English:
definition mkQ
  signature: : G ->+ ModN G n
  body: (LinearMap.range (LinearMap.lsmul Int G n)).mkQ

中文:
定义 mkQ
  签名: : G ->+ ModN G n
  定义体: (LinearMap.range (LinearMap.lsmul Int G n)).mkQ

Depends on / 依赖: LinearMap, LinearMap.lsmul, LinearMap.range
-/
def mkQ : G ->+ ModN G n := (LinearMap.range (LinearMap.lsmul Int G n)).mkQ

variable [NeZero n]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: {ι : Type*} (b : Basis ι Int G)
  body: by
  set nG := LinearMap.range (LinearMap.lsmul Int G n)
  set H := G ⧸ nG
  set φ : G ->ₗ[Int] H := nG.mkQ
  let mod : (ι ->₀ Int) ->ₗ[Int] (ι ->₀ ZMod n) := mapRange.linearMap (Int.castAddHom _).toIntLinearMap
  let f : G ->ₗ[Int] (ι ->₀ Int) := b.repr
  have hker : nG <= LinearMap.ker (mod.comp f

中文:
定义 basis
  签名: {ι : 类型} (b : Basis ι 整数 G)
  定义体: by
  set nG := LinearMap.range (LinearMap.lsmul Int G n)
  set H := G ⧸ nG
  set φ : G ->ₗ[Int] H := nG.mkQ
  let mod : (ι ->₀ Int) ->ₗ[Int] (ι ->₀ ZMod n) := mapRange.linearMap (Int.castAddHom _).toIntLinearMap
  let f : G ->ₗ[Int] (ι ->₀ Int) := b.repr
  have hker : nG <= LinearMap.ker (mod.comp f

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_toZModLinea, Int.castAddHom, LinearMap, LinearMap.ker, LinearMap.lsmul, LinearMap.range, b.repr, castAddHom, coe_toZModLinea, g.toAddMonoidHom.toZModLinearMap, linearMap, mapRange, mapRange.linearMap, mod.comp, nG.liftQ, nG.mkQ, ofBijective, toAddMonoidHom, toIntLinearMap
-/
noncomputable def basis {ι : Type*} (b : Basis ι Int G) : Basis ι (ZMod n) (ModN G n) := by
  set nG := LinearMap.range (LinearMap.lsmul Int G n)
  set H := G ⧸ nG
  set φ : G ->ₗ[Int] H := nG.mkQ
  let mod : (ι ->₀ Int) ->ₗ[Int] (ι ->₀ ZMod n) := mapRange.linearMap (Int.castAddHom _).toIntLinearMap
  let f : G ->ₗ[Int] (ι ->₀ Int) := b.repr
  have hker : nG <= LinearMap.ker (mod.comp f) := by
    rintro _ ⟨x, rfl⟩
    ext b
    simp [mod, f]
  let g : H ->ₗ[Int] (ι ->₀ ZMod n) := nG.liftQ (mod.comp f) hker
  refine ⟨.ofBijective (g.toAddMonoidHom.toZModLinearMap n) ⟨?_, ?_⟩⟩
  · rw [AddMonoidHom.coe_toZModLinearMap, LinearMap.toAddMonoidHom_coe, injective_iff_map_eq_zero,
      nG.mkQ_surjective.forall]
    intro x hx
    simp only [Submodule.mkQ_apply, g] at hx
    rw [Submodule.liftQ_apply] at hx
    replace hx : forall b, ↑n ∣ f x b := by
      simpa [mod, DFunLike.ext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd] using! hx
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    choose c hc using hx
    refine ⟨b.repr.symm ⟨(f x).support, c, by simp [hc, NeZero.ne]⟩, b.repr.injective ?_⟩
    simpa [DFunLike.ext_iff, eq_comm] using! hc
  · suffices mod ∘ b.repr = g ∘ nG.mkQ by
      exact (this ▸ (mapRange_surjective _ (map_zero _) ZMod.intCast_surjective).comp
        b.repr.surjective).of_comp
    ext x b
    simp [mod, g, f, H]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `basis_apply_eq_mkQ` / 引理 `basis_apply_eq_mkQ`

English:
lemma basis_apply_eq_mkQ
  given: {ι : Type*} (b : Basis ι Int G) (i : ι)
  statement: basis b i = mkQ n (b i)
  proof: by
  rw [Basis.apply_eq_iff]; simp [basis, mkQ]

中文:
引理 basis_apply_eq_mkQ
  条件: {ι : 类型} (b : Basis ι 整数 G) (i : ι)
  结论: basis b i = mkQ n (b i)
  证明: by
  rw [Basis.apply_eq_iff]; simp [basis, mkQ]

Depends on / 依赖: Basis.apply_eq_iff, apply_eq_iff
-/
lemma basis_apply_eq_mkQ {ι : Type*} (b : Basis ι Int G) (i : ι) : basis b i = mkQ n (b i) := by
  rw [Basis.apply_eq_iff]; simp [basis, mkQ]

variable [Module.Free Int G] [Module.Finite Int G]

/--
Instance `instModuleFinite` / 实例 `instModuleFinite`

English:
instance instModuleFinite
  signature: : Module.Finite (ZMod n) (ModN G n)
  body: .of_basis basis Module.Free.chooseBasis Int G

中文:
实例 instModuleFinite
  签名: : Module.Finite (ZMod n) (ModN G n)
  定义体: .of_basis basis Module.Free.chooseBasis Int G

Depends on / 依赖: IsMulLeftInvariant, IsMulLeftInvariant.isMulRightInvariant, Measure, Module, Module.Free.chooseBasis, chooseBasis, isMulRightInvariant, of_basis
-/
instance instModuleFinite : Module.Finite (ZMod n) (ModN G n) :=
.of_basis basis Module.Free.chooseBasis Int G

/--
Instance `instFinite` / 实例 `instFinite`

English:
instance instFinite
  signature: : Finite (ModN G n)
  body: Module.finite_of_finite (ZMod n)

中文:
实例 instFinite
  签名: : Finite (ModN G n)
  定义体: Module.finite_of_finite (ZMod n)

Depends on / 依赖: Module, Module.finite_of_finite, finite_of_finite
-/
instance instFinite : Finite (ModN G n) := Module.finite_of_finite (ZMod n)

variable (G n)
/--
lemma `natCard_eq` / 引理 `natCard_eq`

English:
lemma natCard_eq
  statement: Nat.card (ModN G n) = n ^ Module.finrank Int G
  proof: by
  simp [Nat.card_congr (basis <| Module.Free.chooseBasis Int G).repr.toEquiv,
    Nat.card_eq_fintype_card, Module.finrank_eq_card_chooseBasisIndex]

中文:
引理 natCard_eq
  结论: 自然数.card (ModN G n) = n ^ Module.finrank 整数 G
  证明: by
  simp [Nat.card_congr (basis <| Module.Free.chooseBasis Int G).repr.toEquiv,
    Nat.card_eq_fintype_card, Module.finrank_eq_card_chooseBasisIndex]
-/
@[simp] lemma natCard_eq : Nat.card (ModN G n) = n ^ Module.finrank Int G := by
  simp [Nat.card_congr (basis <| Module.Free.chooseBasis Int G).repr.toEquiv,
    Nat.card_eq_fintype_card, Module.finrank_eq_card_chooseBasisIndex]

end ModN
