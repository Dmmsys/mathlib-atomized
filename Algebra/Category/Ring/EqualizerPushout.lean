/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Equalizer of inclusions to pushouts in `CommRingCat`

Given a map `f : R ⟶ S` in `CommRingCat`, we prove that the equalizer of the two maps
`pushout.inl : S ⟶ pushout f f` and `pushout.inr : S ⟶ pushout f f` is canonically isomorphic
to `R` when `R ⟶ S` is a faithfully flat ring map.

Note that, under `CommRingCat.pushoutCoconeIsColimit`, the two maps `inl` and `inr` above can be
described as `s ↦ s ⊗ₜ[R] 1` and `s ↦ 1 ⊗ₜ[R] s`, respectively.
-/

@[expose] public section

open CategoryTheory Limits

namespace CommRingCat

universe u

section Fork

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/--
Definition of `isLimitForkPushoutSelfOfFaithfullyFlat` / `isLimitForkPushoutSelfOfFaithfullyFlat` 的定义

English:
definition isLimitForkPushoutSelfOfFaithfullyFlat
  signature: (hf : f.hom.FaithfullyFlat)
  body: by
  algebraize [f.hom]
  let fork : Fork (pushoutCocone R S S).inl (pushoutCocone R S S).inr :=
    Fork.ofι (ofHom (algebraMap R S)) (by rw [(PushoutCocone.condition _)])
  let isPushout : IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R S))
      (pushoutCocone R S S).inl (pushoutCocone R 

中文:
定义 isLimitForkPushoutSelfOfFaithfullyFlat
  签名: (hf : f.hom.忠实平坦)
  定义体: by
  algebraize [f.hom]
  let fork : Fork (pushoutCocone R S S).inl (pushoutCocone R S S).inr :=
    Fork.ofι (ofHom (algebraMap R S)) (by rw [(PushoutCocone.condition _)])
  let isPushout : IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R S))
      (pushoutCocone R S S).inl (pushoutCocone R 

Depends on / 依赖: Fork.isLimitEquivOfIsos, Fork.of, IsLimit, IsPushout, PushoutCocone, PushoutCocone.condition, algebraMap, algebraize, condition, equalizerFork, f.hom, isLimit, isLimitEquivOfIsos, isPushout, pushoutCocone, pushoutCoconeIsColimit
-/
noncomputable def isLimitForkPushoutSelfOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsLimit (Fork.ofι f pushout.condition) := by
  algebraize [f.hom]
  let fork : Fork (pushoutCocone R S S).inl (pushoutCocone R S S).inr :=
    Fork.ofι (ofHom (algebraMap R S)) (by rw [(PushoutCocone.condition _)])
  let isPushout : IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R S))
      (pushoutCocone R S S).inl (pushoutCocone R S S).inr :=
    ⟨⟨PushoutCocone.condition (pushoutCocone R S S)⟩, ⟨pushoutCoconeIsColimit R S S⟩⟩
  let isLimit : IsLimit fork :=
    (Fork.isLimitEquivOfIsos _
      (equalizerFork (pushoutCocone R S S).inl (pushoutCocone R S S).inr) (Iso.refl _) (Iso.refl _)
      (RingEquiv.toCommRingCatIso <| RingEquiv.ofBijective _
        (Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat R S))
      (by cat_disch) (by cat_disch) (by cat_disch)).symm
    (equalizerForkIsLimit (pushoutCocone R S S).inl (pushoutCocone R S S).inr)
  exact Fork.isLimitEquivOfIsos fork (Fork.ofι f pushout.condition) (Iso.refl _)
    (IsPushout.isoPushout isPushout) (Iso.refl _) (IsPushout.inl_isoPushout_hom isPushout).symm
    (IsPushout.inr_isoPushout_hom isPushout).symm rfl isLimit

/--
Definition of `regularMonoOfFaithfullyFlat` / `regularMonoOfFaithfullyFlat` 的定义

English:
definition regularMonoOfFaithfullyFlat
  signature: (hf : f.hom.FaithfullyFlat)
  body: pushout f f
  left := pushout.inl f f
  right := pushout.inr f f
  w := pushout.condition
  isLimit := isLimitForkPushoutSelfOfFaithfullyFlat f hf

中文:
定义 regularMonoOfFaithfullyFlat
  签名: (hf : f.hom.忠实平坦)
  定义体: pushout f f
  left := pushout.inl f f
  right := pushout.inr f f
  w := pushout.condition
  isLimit := isLimitForkPushoutSelfOfFaithfullyFlat f hf

Depends on / 依赖: pushout
-/
noncomputable def regularMonoOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    RegularMono f where
  Z := pushout f f
  left := pushout.inl f f
  right := pushout.inr f f
  w := pushout.condition
  isLimit := isLimitForkPushoutSelfOfFaithfullyFlat f hf

/--
lemma `isRegularMono_of_faithfullyFlat` / 引理 `isRegularMono_of_faithfullyFlat`

English:
lemma isRegularMono_of_faithfullyFlat
  given: (hf : f.hom.FaithfullyFlat)
  proof: isRegularMono_of_regularMono (regularMonoOfFaithfullyFlat f hf)

中文:
引理 isRegularMono_of_faithfullyFlat
  条件: (hf : f.hom.忠实平坦)
  证明: isRegularMono_of_regularMono (regularMonoOfFaithfullyFlat f hf)

Depends on / 依赖: isRegularMono_of_regularMono, regularMonoOfFaithfullyFlat
-/
lemma isRegularMono_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsRegularMono f :=
  isRegularMono_of_regularMono (regularMonoOfFaithfullyFlat f hf)

end Fork

namespace Opposite

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

/--
lemma `regularEpiOfFaithfullyFlat` / 引理 `regularEpiOfFaithfullyFlat`

English:
lemma regularEpiOfFaithfullyFlat
  given: (hf : f.unop.hom.FaithfullyFlat)
  proof: (isRegularEpi_op_iff_isRegularMono _).mpr (isRegularMono_of_faithfullyFlat _ hf)

中文:
引理 regularEpiOfFaithfullyFlat
  条件: (hf : f.unop.hom.忠实平坦)
  证明: (isRegularEpi_op_iff_isRegularMono _).mpr (isRegularMono_of_faithfullyFlat _ hf)

Depends on / 依赖: isRegularEpi_op_iff_isRegularMono, isRegularMono_of_faithfullyFlat
-/
lemma regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) :
    IsRegularEpi f :=
  (isRegularEpi_op_iff_isRegularMono _).mpr (isRegularMono_of_faithfullyFlat _ hf)

/--
lemma `effectiveEpi_of_faithfullyFlat` / 引理 `effectiveEpi_of_faithfullyFlat`

English:
lemma effectiveEpi_of_faithfullyFlat
  given: (hf : f.unop.hom.FaithfullyFlat)
  statement: EffectiveEpi f
  proof: (isRegularEpi_iff_effectiveEpi _).mp (regularEpiOfFaithfullyFlat _ hf)

中文:
引理 effectiveEpi_of_faithfullyFlat
  条件: (hf : f.unop.hom.忠实平坦)
  结论: 有效满态射 f
  证明: (isRegularEpi_iff_effectiveEpi _).mp (regularEpiOfFaithfullyFlat _ hf)

Depends on / 依赖: isRegularEpi_iff_effectiveEpi, regularEpiOfFaithfullyFlat
-/
lemma effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f :=
  (isRegularEpi_iff_effectiveEpi _).mp (regularEpiOfFaithfullyFlat _ hf)

end Opposite

end CommRingCat
