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

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then the fork
```
        S ---inl---> pushout f f
R --f-->
        S ---inr---> pushout f f
```
is an equalizer diagram. -/
/-
**CommRingCat.isLimitForkPushoutSelfOfFaithfullyFlat** 是 Mathlib 中的一个定义，位于命名空间 `
CommRingCat`。
形式化陈述：isLimitForkPushoutSelfOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) : IsLim
it (Fork.ofι f pushout.condition)
参数：hf : f.hom.FaithfullyFlat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then the fork
```
        S ---inl---> pushout f f
R --f-->
        S ---inr---> pushout f f
```
is an equalizer diagram.
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

/-- A regular monomorphism structure on a map `f : R ⟶ S` in `CommRingCat` with
faithfully flat `f.hom : R ⟶ S`. -/
/-
**CommRingCat.regularMonoOfFaithfullyFlat** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat
`。
形式化陈述：regularMonoOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) : RegularMono f wh
ere Z
参数：hf : f.hom.FaithfullyFlat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular monomorphism structure on a map `f : R ⟶ S` in `CommRingCat` with
faithfully flat `f.hom : R ⟶ S`.
-/
noncomputable def regularMonoOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    RegularMono f where
  Z := pushout f f
  left := pushout.inl f f
  right := pushout.inr f f
  w := pushout.condition
  isLimit := isLimitForkPushoutSelfOfFaithfullyFlat f hf

/-- Any map `f : R ⟶ S` in `CommRingCat` with faithfully flat `f.hom : R ⟶ S` is a regular
monomorphism. -/
/-
**CommRingCat.isRegularMono_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 `CommRin
gCat`。
形式化陈述：isRegularMono_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) : IsRegularMon
o f
参数：hf : f.hom.FaithfullyFlat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isRegularMono_of_regularMono`：isRegularMono_of_regularMon
o {f : X ⟶ Y} (h : RegularMono f) : IsRegularMono f

--- 原说明 ---
Any map `f : R ⟶ S` in `CommRingCat` with faithfully flat `f.hom : R ⟶ S` is a r
egular
monomorphism.
-/
lemma isRegularMono_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsRegularMono f :=
  isRegularMono_of_regularMono (regularMonoOfFaithfullyFlat f hf)

end Fork

namespace Opposite

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

/-- A regular epimorphism structure on a map `f : S ⟶ R` in `CommRingCatᵒᵖ` with
faithfully flat `f.unop.hom : R.unop ⟶ S.unop`. -/
/-
**CommRingCat.Opposite.regularEpiOfFaithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 `Com
mRingCat.Opposite`。
形式化陈述：regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : IsRegularEpi
 f
参数：hf : f.unop.hom.FaithfullyFlat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.isRegularEpi_op_iff_isRegularMono`：isRegularEpi_op_iff_is
RegularMono {X Y : C} (f : X ⟶ Y) : IsRegularEpi f.op ↔ IsRegularMono f
· 使用引理 `CommRingCat.isRegularMono_of_faithfullyFlat`：isRegularMono_of_faithfully
Flat (hf : f.hom.FaithfullyFlat) : IsRegularMono f

--- 原说明 ---
A regular epimorphism structure on a map `f : S ⟶ R` in `CommRingCatᵒᵖ` with
faithfully flat `f.unop.hom : R.unop ⟶ S.unop`.
-/
lemma regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) :
    IsRegularEpi f :=
  (isRegularEpi_op_iff_isRegularMono _).mpr (isRegularMono_of_faithfullyFlat _ hf)

/-- Any map `f : S ⟶ R` in `CommRingCatᵒᵖ` with faithfully flat `f.unop.hom : R.unop ⟶ S.unop` is
an effective epimorphism. -/
/-
**CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 
`CommRingCat.Opposite`。
形式化陈述：effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : Effectiv
eEpi f
参数：hf : f.unop.hom.FaithfullyFlat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.isRegularEpi_iff_effectiveEpi`：isRegularEpi_iff_effective
Epi {B X : C} (f : X ⟶ B) [HasPullback f f] : IsRegularEpi f ↔ EffectiveEpi f
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用引理 `CommRingCat.Opposite.regularEpiOfFaithfullyFlat`：regularEpiOfFaithfullyF
lat (hf : f.unop.hom.FaithfullyFlat) : IsRegularEpi f

--- 原说明 ---
Any map `f : S ⟶ R` in `CommRingCatᵒᵖ` with faithfully flat `f.unop.hom : R.unop
 ⟶ S.unop` is
an effective epimorphism.
-/
lemma effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f :=
  (isRegularEpi_iff_effectiveEpi _).mp (regularEpiOfFaithfullyFlat _ hf)

end Opposite

end CommRingCat

