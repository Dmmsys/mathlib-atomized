/-
Copyright (c) 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Adjoint action of a Lie algebra on itself

This file defines the *adjoint action* of a Lie algebra on itself, and establishes basic properties.

## Main definitions

- `LieDerivation.ad`: The adjoint action of a Lie algebra `L` on itself, seen as a morphism of Lie
  algebras from `L` to the Lie algebra of its derivations. The adjoint action is also defined in the
  `Mathlib/Algebra/Lie/OfAssociative.lean` file, under the name `LieAlgebra.ad`, as the morphism
  with values in the endomorphisms of `L`.

## Main statements

- `LieDerivation.coe_ad_apply_eq_ad_apply`: when seen as endomorphisms, both definitions coincide,
- `LieDerivation.ad_ker_eq_center`: the kernel of the adjoint action is the center of `L`,
- `LieDerivation.lie_der_ad_eq_ad_der`: the commutator of a derivation `D` and `ad x` is `ad (D x)`,
- `LieDerivation.ad_isIdealMorphism`: the range of the adjoint action is an ideal of the
  derivations.
-/

@[expose] public section

namespace LieDerivation

section AdjointAction

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The adjoint action of a Lie algebra `L` on itself, seen as a morphism of Lie algebras from
`L` to its derivations.
Note the minus sign: this is chosen to so that `ad ⁅x, y⁆ = ⁅ad x, ad y⁆`. -/
@[simps!]
/--
Definition of `ad` / `ad` 的定义

English:
definition ad
  signature: : L ->ₗ⁅R⁆ LieDerivation R L L
  body: { __ := - inner R L L
    map_lie' := by
      intro x y
      ext z
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.neg_apply, coe_neg,
        Pi.neg_apply, inner_apply_apply, commutator_apply]
      rw [leibniz_lie]; rw [neg_lie]; rw [neg_lie]; rw [← lie_skew x]
      abel }

中文:
定义 ad
  签名: : L ->ₗ⁅R⁆ LieDerivation R L L
  定义体: { __ := - inner R L L
    map_lie' := by
      intro x y
      ext z
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.neg_apply, coe_neg,
        Pi.neg_apply, inner_apply_apply, commutator_apply]
      rw [leibniz_lie]; rw [neg_lie]; rw [neg_lie]; rw [← lie_skew x]
      abel }

Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, LinearMap, LinearMap.coe_toAddHom, LinearMap.neg_apply, Pi.neg_apply, coe_neg, coe_toAddHom, commutator_apply, inner_apply_apply, leibniz_lie, lie_skew, map_lie, neg_apply, neg_lie, toFun_eq_coe
-/
def ad : L ->ₗ⁅R⁆ LieDerivation R L L :=
  { __ := - inner R L L
    map_lie' := by
      intro x y
      ext z
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.neg_apply, coe_neg,
        Pi.neg_apply, inner_apply_apply, commutator_apply]
      rw [leibniz_lie]; rw [neg_lie]; rw [neg_lie]; rw [← lie_skew x]
      abel }

variable {R L}

/--
lemma `coe_ad_apply_eq_ad_apply` / 引理 `coe_ad_apply_eq_ad_apply`

English:
lemma coe_ad_apply_eq_ad_apply
  given: (x : L)
  statement: ad R L x = LieAlgebra.ad R L x
  proof: by ext; simp

中文:
引理 coe_ad_apply_eq_ad_apply
  条件: (x : L)
  结论: ad R L x = Lie代数.ad R L x
  证明: by ext; simp
-/
@[simp] lemma coe_ad_apply_eq_ad_apply (x : L) : ad R L x = LieAlgebra.ad R L x := by ext; simp

/--
lemma `ad_apply_lieDerivation` / 引理 `ad_apply_lieDerivation`

English:
lemma ad_apply_lieDerivation
  given: (x : L) (D : LieDerivation R L L)
  statement: ad R L (D x) = -⁅x, D⁆
  proof: rfl

中文:
引理 ad_apply_lieDerivation
  条件: (x : L) (D : LieDerivation R L L)
  结论: ad R L (D x) = -⁅x, D⁆
  证明: rfl
-/
lemma ad_apply_lieDerivation (x : L) (D : LieDerivation R L L) : ad R L (D x) = -⁅x, D⁆ := rfl

/--
lemma `lie_ad` / 引理 `lie_ad`

English:
lemma lie_ad
  given: (x : L) (D : LieDerivation R L L)
  statement: ⁅ad R L x, D⁆ = ⁅x, D⁆
  proof: by ext; simp

中文:
引理 lie_ad
  条件: (x : L) (D : LieDerivation R L L)
  结论: ⁅ad R L x, D⁆ = ⁅x, D⁆
  证明: by ext; simp
-/
lemma lie_ad (x : L) (D : LieDerivation R L L) : ⁅ad R L x, D⁆ = ⁅x, D⁆ := by ext; simp

variable (R L) in
/--
lemma `ad_ker_eq_center` / 引理 `ad_ker_eq_center`

English:
lemma ad_ker_eq_center
  statement: (ad R L).ker = LieAlgebra.center R L
  proof: by
  ext x
  rw [← LieAlgebra.self_module_ker_eq_center]; rw [LieHom.mem_ker]; rw [LieModule.mem_ker]
  simp [DFunLike.ext_iff]

中文:
引理 ad_ker_eq_center
  结论: (ad R L).ker = Lie代数.center R L
  证明: by
  ext x
  rw [← LieAlgebra.self_module_ker_eq_center]; rw [LieHom.mem_ker]; rw [LieModule.mem_ker]
  simp [DFunLike.ext_iff]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, LieAlgebra, LieAlgebra.self_module_ker_eq_center, LieHom, LieHom.mem_ker, LieModule, LieModule.mem_ker, ext_iff, mem_ker, self_module_ker_eq_center
-/
lemma ad_ker_eq_center : (ad R L).ker = LieAlgebra.center R L := by
  ext x
  rw [← LieAlgebra.self_module_ker_eq_center]; rw [LieHom.mem_ker]; rw [LieModule.mem_ker]
  simp [DFunLike.ext_iff]

/--
lemma `injective_ad_of_center_eq_bot` / 引理 `injective_ad_of_center_eq_bot`

English:
lemma injective_ad_of_center_eq_bot
  given: (h : LieAlgebra.center R L = ⊥)
  proof: by
  rw [← LieHom.ker_eq_bot]; rw [ad_ker_eq_center]; rw [h]

中文:
引理 injective_ad_of_center_eq_bot
  条件: (h : Lie代数.center R L = ⊥)
  证明: by
  rw [← LieHom.ker_eq_bot]; rw [ad_ker_eq_center]; rw [h]

Depends on / 依赖: LieHom, LieHom.ker_eq_bot, ad_ker_eq_center, ker_eq_bot
-/
lemma injective_ad_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    Function.Injective (ad R L) := by
  rw [← LieHom.ker_eq_bot]; rw [ad_ker_eq_center]; rw [h]

/--
lemma `lie_der_ad_eq_ad_der` / 引理 `lie_der_ad_eq_ad_der`

English:
lemma lie_der_ad_eq_ad_der
  given: (D : LieDerivation R L L) (x : L)
  statement: ⁅D, ad R L x⁆ = ad R L (D x)
  proof: by
  rw [ad_apply_lieDerivation]; rw [← lie_ad]; rw [lie_skew]

中文:
引理 lie_der_ad_eq_ad_der
  条件: (D : LieDerivation R L L) (x : L)
  结论: ⁅D, ad R L x⁆ = ad R L (D x)
  证明: by
  rw [ad_apply_lieDerivation]; rw [← lie_ad]; rw [lie_skew]

Depends on / 依赖: ad_apply_lieDerivation, lie_ad, lie_skew
-/
lemma lie_der_ad_eq_ad_der (D : LieDerivation R L L) (x : L) : ⁅D, ad R L x⁆ = ad R L (D x) := by
  rw [ad_apply_lieDerivation]; rw [← lie_ad]; rw [lie_skew]

variable (R L) in
/--
lemma `ad_isIdealMorphism` / 引理 `ad_isIdealMorphism`

English:
lemma ad_isIdealMorphism
  statement: (ad R L).IsIdealMorphism
  proof: by
  simp_rw [LieHom.isIdealMorphism_iff, lie_der_ad_eq_ad_der]
  tauto

中文:
引理 ad_isIdealMorphism
  结论: (ad R L).IsIdealMorphism
  证明: by
  simp_rw [LieHom.isIdealMorphism_iff, lie_der_ad_eq_ad_der]
  tauto

Depends on / 依赖: Fintype, Fintype.ofFinite, LieHom, LieHom.isIdealMorphism_iff, isIdealMorphism_iff, lie_der_ad_eq_ad_der, ofFinite, simp_rw
-/
lemma ad_isIdealMorphism : (ad R L).IsIdealMorphism := by
  simp_rw [LieHom.isIdealMorphism_iff, lie_der_ad_eq_ad_der]
  tauto

/--
lemma `mem_ad_idealRange_iff` / 引理 `mem_ad_idealRange_iff`

English:
lemma mem_ad_idealRange_iff
  given: {D : LieDerivation R L L}
  proof: (ad R L).mem_idealRange_iff (ad_isIdealMorphism R L)

中文:
引理 mem_ad_idealRange_iff
  条件: {D : LieDerivation R L L}
  证明: (ad R L).mem_idealRange_iff (ad_isIdealMorphism R L)

Depends on / 依赖: ad_isIdealMorphism, mem_idealRange_iff
-/
lemma mem_ad_idealRange_iff {D : LieDerivation R L L} :
    D in (ad R L).idealRange ↔ exists x : L, ad R L x = D :=
  (ad R L).mem_idealRange_iff (ad_isIdealMorphism R L)

/--
lemma `maxTrivSubmodule_eq_bot_of_center_eq_bot` / 引理 `maxTrivSubmodule_eq_bot_of_center_eq_bot`

English:
lemma maxTrivSubmodule_eq_bot_of_center_eq_bot
  given: (h : LieAlgebra.center R L = ⊥)
  proof: by
  refine (LieSubmodule.eq_bot_iff _).mpr fun D hD => ext fun x => ?_
  have : ad R L (D x) = 0 := by
    rw [LieModule.mem_maxTrivSubmodule] at hD
    simp [ad_apply_lieDerivation, hD]
  rw [← LieHom.mem_ker]; rw [ad_ker_eq_center]; rw [h]; rw [LieSubmodule.mem_bot] at this
  simp [this]

中文:
引理 maxTrivSubmodule_eq_bot_of_center_eq_bot
  条件: (h : Lie代数.center R L = ⊥)
  证明: by
  refine (LieSubmodule.eq_bot_iff _).mpr fun D hD => ext fun x => ?_
  have : ad R L (D x) = 0 := by
    rw [LieModule.mem_maxTrivSubmodule] at hD
    simp [ad_apply_lieDerivation, hD]
  rw [← LieHom.mem_ker]; rw [ad_ker_eq_center]; rw [h]; rw [LieSubmodule.mem_bot] at this
  simp [this]

Depends on / 依赖: LieHom, LieHom.mem_ker, LieModule, LieModule.mem_maxTrivSubmodule, LieSubmodule, LieSubmodule.eq_bot_iff, LieSubmodule.mem_bot, ad_apply_lieDerivation, ad_ker_eq_center, eq_bot_iff, mem_bot, mem_ker, mem_maxTrivSubmodule
-/
lemma maxTrivSubmodule_eq_bot_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    LieModule.maxTrivSubmodule R L (LieDerivation R L L) = ⊥ := by
  refine (LieSubmodule.eq_bot_iff _).mpr fun D hD => ext fun x => ?_
  have : ad R L (D x) = 0 := by
    rw [LieModule.mem_maxTrivSubmodule] at hD
    simp [ad_apply_lieDerivation, hD]
  rw [← LieHom.mem_ker]; rw [ad_ker_eq_center]; rw [h]; rw [LieSubmodule.mem_bot] at this
  simp [this]

end AdjointAction

end LieDerivation
