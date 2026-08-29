/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Limits in `Under R` for a commutative ring `R`

We show that `Under.pushout f` is left-exact, i.e. preserves finite limits, if `f : R ⟶ S` is
flat.

-/

@[expose] public section

noncomputable section

universe v u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat.Under

section Algebra

variable [Algebra R S]

section Pi

variable {ι : Type u} (P : ι -> Under R)

/--
Definition of `piFan` / `piFan` 的定义

English:
definition piFan
  signature: : Fan P
  body: Fan.mk (Under.mk <| ofHom <| RingHom.pi (fun i => (P i).hom.hom))
    (fun i => Under.homMk (ofHom <| Pi.evalRingHom _ i))

中文:
定义 piFan
  签名: : Fan P
  定义体: Fan.mk (Under.mk <| ofHom <| RingHom.pi (fun i => (P i).hom.hom))
    (fun i => Under.homMk (ofHom <| Pi.evalRingHom _ i))

Depends on / 依赖: Fan.mk, Pi.evalRingHom, RingHom, RingHom.pi, Under.homMk, Under.mk, evalRingHom, hom.hom
-/
def piFan : Fan P :=
  Fan.mk (Under.mk <| ofHom <| RingHom.pi (fun i => (P i).hom.hom))
    (fun i => Under.homMk (ofHom <| Pi.evalRingHom _ i))

/--
Definition of `piFanIsLimit` / `piFanIsLimit` 的定义

English:
definition piFanIsLimit
  signature: : IsLimit (piFan P)
  body: isLimitOfReflects (Under.forget R)
(isLimitMapConeFanMkEquiv (Under.forget R) P _).symm
      CommRingCat.piFanIsLimit (fun i => (P i).right)

中文:
定义 piFanIsLimit
  签名: : 是极限 (piFan P)
  定义体: isLimitOfReflects (Under.forget R)
(isLimitMapConeFanMkEquiv (Under.forget R) P _).symm
      CommRingCat.piFanIsLimit (fun i => (P i).right)

Depends on / 依赖: CommRingCat, CommRingCat.piFanIsLimit, Under.forget, forget, isLimitMapConeFanMkEquiv, isLimitOfReflects, piFanIsLimit
-/
def piFanIsLimit : IsLimit (piFan P) :=
isLimitOfReflects (Under.forget R)
(isLimitMapConeFanMkEquiv (Under.forget R) P _).symm
      CommRingCat.piFanIsLimit (fun i => (P i).right)

variable (S) in
/--
Definition of `tensorProductFan` / `tensorProductFan` 的定义

English:
definition tensorProductFan
  signature: : Fan (fun i => mkUnder S (S otimes[R] (P i).right))
  body: Fan.mk (mkUnder S <| S otimes[R] forall i, (P i).right)
    (fun i => AlgHom.toUnder <|
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom R (fun j => (P j).right) i))

中文:
定义 tensorProductFan
  签名: : Fan (fun i => mkUnder S (S otimes[R] (P i).right))
  定义体: Fan.mk (mkUnder S <| S otimes[R] forall i, (P i).right)
    (fun i => AlgHom.toUnder <|
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom R (fun j => (P j).right) i))

Depends on / 依赖: AlgHom, AlgHom.id, AlgHom.toUnder, Algebra, Algebra.TensorProduct.map, Fan.mk, Pi.evalAlgHom, TensorProduct, evalAlgHom, mkUnder, otimes, toUnder
-/
def tensorProductFan : Fan (fun i => mkUnder S (S otimes[R] (P i).right)) :=
  Fan.mk (mkUnder S <| S otimes[R] forall i, (P i).right)
    (fun i => AlgHom.toUnder <|
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom R (fun j => (P j).right) i))

variable (S) in
/--
Definition of `tensorProductFan'` / `tensorProductFan'` 的定义

English:
definition tensorProductFan'
  signature: : Fan (fun i => mkUnder S (S otimes[R] (P i).right))
  body: Fan.mk (mkUnder S <| forall i, S otimes[R] (P i).right)
    (fun i => AlgHom.toUnder <| Pi.evalAlgHom S _ i)

中文:
定义 tensorProductFan'
  签名: : Fan (fun i => mkUnder S (S otimes[R] (P i).right))
  定义体: Fan.mk (mkUnder S <| forall i, S otimes[R] (P i).right)
    (fun i => AlgHom.toUnder <| Pi.evalAlgHom S _ i)

Depends on / 依赖: AlgHom, AlgHom.toUnder, Fan.mk, Pi.evalAlgHom, evalAlgHom, mkUnder, otimes, toUnder
-/
def tensorProductFan' : Fan (fun i => mkUnder S (S otimes[R] (P i).right)) :=
  Fan.mk (mkUnder S <| forall i, S otimes[R] (P i).right)
    (fun i => AlgHom.toUnder <| Pi.evalAlgHom S _ i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorProductFanIso` / `tensorProductFanIso` 的定义

English:
definition tensorProductFanIso
  signature: [Fintype ι] [DecidableEq ι]
  body: Fan.ext (Algebra.TensorProduct.piRight R S _ _).toUnder fun i => by
    dsimp only [tensorProductFan, Fan.mk_pt, fan_mk_proj, tensorProductFan']
    apply CommRingCat.mkUnder_ext
    intro c
    induction c
    · simp only [map_zero, Under.comp_right]
    · simp only [AlgHom.toUnder_right, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Pi.evalAlgHom_apply, Under.comp_right, comp_apply, AlgEquiv.toUnder_hom_right_apply,
        Algebra.TensorProduct.piRight_tmul]
    · simp_all

中文:
定义 tensorProductFanIso
  签名: [有限类型 ι] [DecidableEq ι]
  定义体: Fan.ext (Algebra.TensorProduct.piRight R S _ _).toUnder fun i => by
    dsimp only [tensorProductFan, Fan.mk_pt, fan_mk_proj, tensorProductFan']
    apply CommRingCat.mkUnder_ext
    intro c
    induction c
    · simp only [map_zero, Under.comp_right]
    · simp only [AlgHom.toUnder_right, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Pi.evalAlgHom_apply, Under.comp_right, comp_apply, AlgEquiv.toUnder_hom_right_apply,
        Algebra.TensorProduct.piRight_tmul]
    · simp_all

Depends on / 依赖: AlgEquiv, AlgEquiv.toUnder_hom_right_apply, AlgHom, AlgHom.coe_id, AlgHom.toUnder_right, Algebra, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.piRight, Algebra.TensorProduct.piRight_tmul, CommRingCat, CommRingCat.mkUnder_ext, Fan.ext, Fan.mk_pt, Pi.evalAlgHom_apply, TensorProduct, Under.comp_right, coe_id, comp_apply, comp_right, evalAlgHom_apply
-/
def tensorProductFanIso [Fintype ι] [DecidableEq ι] :
    tensorProductFan S P ≅ tensorProductFan' S P :=
Fan.ext (Algebra.TensorProduct.piRight R S _ _).toUnder fun i => by
    dsimp only [tensorProductFan, Fan.mk_pt, fan_mk_proj, tensorProductFan']
    apply CommRingCat.mkUnder_ext
    intro c
    induction c
    · simp only [map_zero, Under.comp_right]
    · simp only [AlgHom.toUnder_right, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Pi.evalAlgHom_apply, Under.comp_right, comp_apply, AlgEquiv.toUnder_hom_right_apply,
        Algebra.TensorProduct.piRight_tmul]
    · simp_all

open scoped Classical in
/--
Definition of `tensorProductFanIsLimit` / `tensorProductFanIsLimit` 的定义

English:
definition tensorProductFanIsLimit
  signature: [Finite ι]
  body: letI : Fintype ι := Fintype.ofFinite ι
  (IsLimit.equivIsoLimit (tensorProductFanIso P)).symm (Under.piFanIsLimit _)

中文:
定义 tensorProductFanIsLimit
  签名: [有限 ι]
  定义体: letI : Fintype ι := Fintype.ofFinite ι
  (IsLimit.equivIsoLimit (tensorProductFanIso P)).symm (Under.piFanIsLimit _)

Depends on / 依赖: Fintype, Fintype.ofFinite, IsLimit, IsLimit.equivIsoLimit, Under.piFanIsLimit, equivIsoLimit, ofFinite, piFanIsLimit, tensorProductFanIso
-/
def tensorProductFanIsLimit [Finite ι] : IsLimit (tensorProductFan S P) :=
  letI : Fintype ι := Fintype.ofFinite ι
  (IsLimit.equivIsoLimit (tensorProductFanIso P)).symm (Under.piFanIsLimit _)

/-- `tensorProd R S` preserves the limit of the canonical fan on `P`. -/
noncomputable -- marked noncomputable for performance (only)
/--
Definition of `piFanTensorProductIsLimit` / `piFanTensorProductIsLimit` 的定义

English:
definition piFanTensorProductIsLimit
  signature: [Finite ι]
  body: (isLimitMapConeFanMkEquiv (tensorProd R S) P _).symm tensorProductFanIsLimit P

中文:
定义 piFanTensorProductIsLimit
  签名: [有限 ι]
  定义体: (isLimitMapConeFanMkEquiv (tensorProd R S) P _).symm tensorProductFanIsLimit P

Depends on / 依赖: isLimitMapConeFanMkEquiv, tensorProd, tensorProductFanIsLimit
-/
def piFanTensorProductIsLimit [Finite ι] : IsLimit ((tensorProd R S).mapCone (Under.piFan P)) :=
(isLimitMapConeFanMkEquiv (tensorProd R S) P _).symm tensorProductFanIsLimit P

instance (J : Type u) [Finite J] (f : J -> Under R) :
    PreservesLimit (Discrete.functor f) (tensorProd R S) :=
  let c : Fan _ := Under.piFan f
  have hc : IsLimit c := Under.piFanIsLimit f
  preservesLimit_of_preserves_limit_cone hc (piFanTensorProductIsLimit f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteProducts (tensorProd R S)
  body: let J : Type u := ULift.{u} (Fin n)
    have : PreservesLimitsOfShape (Discrete J) (tensorProd R S) :=
      preservesLimitsOfShape_of_discrete (tensorProd R S)
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) (R.tensorProd S)

中文:
实例 :
  签名: 保持FiniteProducts (tensorProd R S)
  定义体: let J : Type u := ULift.{u} (Fin n)
    have : PreservesLimitsOfShape (Discrete J) (tensorProd R S) :=
      preservesLimitsOfShape_of_discrete (tensorProd R S)
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) (R.tensorProd S)

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.ulift, PreservesLimitsOfShape, R.tensorProd, equivalence, preservesLimitsOfShape_of_discrete, preservesLimitsOfShape_of_equiv, tensorProd
-/
instance : PreservesFiniteProducts (tensorProd R S) where
  preserves n :=
    let J : Type u := ULift.{u} (Fin n)
    have : PreservesLimitsOfShape (Discrete J) (tensorProd R S) :=
      preservesLimitsOfShape_of_discrete (tensorProd R S)
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) (R.tensorProd S)

end Pi

section Equalizer

/--
lemma `equalizer_comp` / 引理 `equalizer_comp`

English:
lemma equalizer_comp
  given: {A B : Under R} (f g : A ⟶ B)
  proof: by
  ext (a : AlgHom.equalizer (toAlgHom f) (toAlgHom g))
  exact a.property

中文:
引理 equalizer_comp
  条件: {A B : Under R} (f g : A ⟶ B)
  证明: by
  ext (a : AlgHom.equalizer (toAlgHom f) (toAlgHom g))
  exact a.property

Depends on / 依赖: AlgHom, AlgHom.equalizer, a.property, equalizer, property, toAlgHom
-/
lemma equalizer_comp {A B : Under R} (f g : A ⟶ B) :
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ f =
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder ≫ g := by
  ext (a : AlgHom.equalizer (toAlgHom f) (toAlgHom g))
  exact a.property

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equalizerFork` / `equalizerFork` 的定义

English:
definition equalizerFork
  signature: {A B : Under R} (f g : A ⟶ B)
  body: Fork.ofι ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)
    (by rw [equalizer_comp])

@[simp]

中文:
定义 equalizerFork
  签名: {A B : Under R} (f g : A ⟶ B)
  定义体: Fork.ofι ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)
    (by rw [equalizer_comp])

@[simp]

Depends on / 依赖: AlgHom, AlgHom.equalizer, Fork.of, equalizer, equalizer_comp, toAlgHom, toUnder, val.toUnder
-/
def equalizerFork {A B : Under R} (f g : A ⟶ B) :
    Fork f g :=
  Fork.ofι ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)
    (by rw [equalizer_comp])

@[simp]
/--
lemma `equalizerFork_ι` / 引理 `equalizerFork_ι`

English:
lemma equalizerFork_ι
  given: {A B : Under R} (f g : A ⟶ B)
  proof: rfl

中文:
引理 equalizerFork_ι
  条件: {A B : Under R} (f g : A ⟶ B)
  证明: rfl
-/
lemma equalizerFork_ι {A B : Under R} (f g : A ⟶ B) :
    (Under.equalizerFork f g).ι = (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder := rfl

/--
Definition of `equalizerFork'` / `equalizerFork'` 的定义

English:
definition equalizerFork'
  signature: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  body: Fork.ofι ((AlgHom.equalizer f g).val.toUnder) by ext a; exact a.property

@[simp]

中文:
定义 equalizerFork'
  签名: {A B : 类型u} [交换环 A] [交换环 B] [代数 R A] [代数 R B]
  定义体: Fork.ofι ((AlgHom.equalizer f g).val.toUnder) by ext a; exact a.property

@[simp]

Depends on / 依赖: AlgHom, AlgHom.equalizer, Fork.of, a.property, equalizer, property, toUnder, val.toUnder
-/
def equalizerFork' {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A ->ₐ[R] B) :
    Fork f.toUnder g.toUnder :=
Fork.ofι ((AlgHom.equalizer f g).val.toUnder) by ext a; exact a.property

@[simp]
/--
lemma `equalizerFork'_ι` / 引理 `equalizerFork'_ι`

English:
lemma equalizerFork'_ι
  statement: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  proof: rfl

中文:
引理 equalizerFork'_ι
  结论: {A B : 类型u} [交换环 A] [交换环 B] [代数 R A] [代数 R B]
  证明: rfl
-/
lemma equalizerFork'_ι {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f g : A ->ₐ[R] B) :
    (Under.equalizerFork' f g).ι = (AlgHom.equalizer f g).val.toUnder := rfl

-- marked noncomputable for performance (only)
/--
Definition of `equalizerForkIsLimit` / `equalizerForkIsLimit` 的定义

English:
definition equalizerForkIsLimit
  signature: {A B : Under R} (f g : A ⟶ B)
  body: isLimitOfReflects (Under.forget R)
(isLimitMapConeForkEquiv (Under.forget R) (equalizer_comp f g)).invFun
      CommRingCat.equalizerForkIsLimit f.right g.right

中文:
定义 equalizerForkIsLimit
  签名: {A B : Under R} (f g : A ⟶ B)
  定义体: isLimitOfReflects (Under.forget R)
(isLimitMapConeForkEquiv (Under.forget R) (equalizer_comp f g)).invFun
      CommRingCat.equalizerForkIsLimit f.right g.right

Depends on / 依赖: CommRingCat, CommRingCat.equalizerForkIsLimit, MonCat, Under.forget, equalizerForkIsLimit, equalizer_comp, f.right, forget, g.right, invFun, isLimitMapConeForkEquiv, isLimitOfReflects
-/
noncomputable def equalizerForkIsLimit {A B : Under R} (f g : A ⟶ B) :
    IsLimit (Under.equalizerFork f g) :=
isLimitOfReflects (Under.forget R)
(isLimitMapConeForkEquiv (Under.forget R) (equalizer_comp f g)).invFun
      CommRingCat.equalizerForkIsLimit f.right g.right

/--
Definition of `equalizerFork'IsLimit` / `equalizerFork'IsLimit` 的定义

English:
definition equalizerFork'IsLimit
  signature: {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
  body: Under.equalizerForkIsLimit f.toUnder g.toUnder

中文:
定义 equalizerFork'是极限
  签名: {A B : 类型u} [交换环 A] [交换环 B] [代数 R A]
  定义体: Under.equalizerForkIsLimit f.toUnder g.toUnder

Depends on / 依赖: MonCat, forget
-/
def equalizerFork'IsLimit {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f g : A ->ₐ[R] B) :
    IsLimit (Under.equalizerFork' f g) :=
  Under.equalizerForkIsLimit f.toUnder g.toUnder

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorProdEqualizer` / `tensorProdEqualizer` 的定义

English:
definition tensorProdEqualizer
  signature: {A B : Under R} (f g : A ⟶ B)
  body: Fork.ofι
((tensorProd R S).map ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)) by
    rw [← Functor.map_comp]; rw [equalizer_comp]; rw [Functor.map_comp]

@[simp]

中文:
定义 tensorProdEqualizer
  签名: {A B : Under R} (f g : A ⟶ B)
  定义体: Fork.ofι
((tensorProd R S).map ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)) by
    rw [← Functor.map_comp]; rw [equalizer_comp]; rw [Functor.map_comp]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.equalizer, FilteredColimit, Fork.of, Functor, Functor.map_comp, MonCat, Quot.eqvGen_sound, Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel, equalizer, equalizer_comp, eqvGen_colimitTypeRel_of_rel, eqvGen_sound, forget, map_comp, tensorProd, toAlgHom, toUnder, val.toUnder
-/
def tensorProdEqualizer {A B : Under R} (f g : A ⟶ B) :
    Fork ((tensorProd R S).map f) ((tensorProd R S).map g) :=
  Fork.ofι
((tensorProd R S).map ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder)) by
    rw [← Functor.map_comp]; rw [equalizer_comp]; rw [Functor.map_comp]

@[simp]
/--
lemma `tensorProdEqualizer_ι` / 引理 `tensorProdEqualizer_ι`

English:
lemma tensorProdEqualizer_ι
  given: {A B : Under R} (f g : A ⟶ B)
  proof: rfl

中文:
引理 tensorProdEqualizer_ι
  条件: {A B : Under R} (f g : A ⟶ B)
  证明: rfl
-/
lemma tensorProdEqualizer_ι {A B : Under R} (f g : A ⟶ B) :
    (tensorProdEqualizer f g).ι = (tensorProd R S).map
      ((AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder) :=
  rfl

-- marked noncomputable for performance (only)
/--
Definition of `equalizerForkTensorProdIso` / `equalizerForkTensorProdIso` 的定义

English:
definition equalizerForkTensorProdIso
  signature: [Module.Flat R S] {A B : Under R} (f g : A ⟶ B)
  body: Fork.ext (AlgHom.tensorEqualizerEquiv S S (toAlgHom f) (toAlgHom g)).toUnder by
    ext
    apply AlgHom.coe_tensorEqualizer

中文:
定义 equalizerForkTensorProdIso
  签名: [模.平坦 R S] {A B : Under R} (f g : A ⟶ B)
  定义体: Fork.ext (AlgHom.tensorEqualizerEquiv S S (toAlgHom f) (toAlgHom g)).toUnder by
    ext
    apply AlgHom.coe_tensorEqualizer

Depends on / 依赖: AlgHom, AlgHom.coe_tensorEqualizer, AlgHom.tensorEqualizerEquiv, Fork.ext, coe_tensorEqualizer, tensorEqualizerEquiv, toAlgHom, toUnder
-/
noncomputable def equalizerForkTensorProdIso [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    tensorProdEqualizer f g ≅ Under.equalizerFork'
        (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f))
        (Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom g)) :=
Fork.ext (AlgHom.tensorEqualizerEquiv S S (toAlgHom f) (toAlgHom g)).toUnder by
    ext
    apply AlgHom.coe_tensorEqualizer

/-- If `S` is `R`-flat, `tensorProd R S` preserves the equalizer of `f` and `g`. -/
noncomputable -- marked noncomputable for performance (only)
/--
Definition of `tensorProdMapEqualizerForkIsLimit` / `tensorProdMapEqualizerForkIsLimit` 的定义

English:
definition tensorProdMapEqualizerForkIsLimit
  signature: [Module.Flat R S] {A B : Under R} (f g : A ⟶ B)
  body: (isLimitMapConeForkEquiv (tensorProd R S) _).symm
(IsLimit.equivIsoLimit (equalizerForkTensorProdIso f g).symm)
    Under.equalizerFork'IsLimit _ _

中文:
定义 tensorProdMapEqualizerForkIsLimit
  签名: [模.平坦 R S] {A B : Under R} (f g : A ⟶ B)
  定义体: (isLimitMapConeForkEquiv (tensorProd R S) _).symm
(IsLimit.equivIsoLimit (equalizerForkTensorProdIso f g).symm)
    Under.equalizerFork'IsLimit _ _

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, Under.equalizerFork, equalizerFork, equalizerForkTensorProdIso, equivIsoLimit, isLimitMapConeForkEquiv, tensorProd
-/
def tensorProdMapEqualizerForkIsLimit [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    IsLimit ((tensorProd R S).mapCone <| Under.equalizerFork f g) :=
(isLimitMapConeForkEquiv (tensorProd R S) _).symm
(IsLimit.equivIsoLimit (equalizerForkTensorProdIso f g).symm)
    Under.equalizerFork'IsLimit _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Flat
  signature: R S] {A B
  body: let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let hc' : IsLimit ((tensorProd R S).mapCone c) :=
    tensorProdMapEqualizerForkIsLimit f g
  preservesLimit_of_preserves_limit_cone hc hc'

中文:
实例 [模.平坦
  签名: R S] {A B
  定义体: let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let hc' : IsLimit ((tensorProd R S).mapCone c) :=
    tensorProdMapEqualizerForkIsLimit f g
  preservesLimit_of_preserves_limit_cone hc hc'

Depends on / 依赖: IsLimit, Under.equalizerFork, Under.equalizerForkIsLimit, equalizerFork, equalizerForkIsLimit, mapCone, preservesLimit_of_preserves_limit_cone, tensorProd, tensorProdMapEqualizerForkIsLimit
-/
instance [Module.Flat R S] {A B : Under R} (f g : A ⟶ B) :
    PreservesLimit (parallelPair f g) (tensorProd R S) :=
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let hc' : IsLimit ((tensorProd R S).mapCone c) :=
    tensorProdMapEqualizerForkIsLimit f g
  preservesLimit_of_preserves_limit_cone hc hc'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Flat
  signature: R S] : PreservesLimitsOfShape WalkingParallelPair (tensorProd R S) where
  body: preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

中文:
实例 [模.平坦
  签名: R S] : 保持形状极限 WalkingParallelPair (tensorProd R S) where
  定义体: preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

Depends on / 依赖: diagramIsoParallelPair, preservesLimit_of_iso_diagram
-/
instance [Module.Flat R S] : PreservesLimitsOfShape WalkingParallelPair (tensorProd R S) where
  preservesLimit {K} :=
    preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Flat
  signature: R S] : PreservesFiniteLimits (tensorProd R S)
  body: preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (tensorProd R S)

中文:
实例 [模.平坦
  签名: R S] : 保持FiniteLimits (tensorProd R S)
  定义体: preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (tensorProd R S)

Depends on / 依赖: preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts, tensorProd
-/
instance [Module.Flat R S] : PreservesFiniteLimits (tensorProd R S) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (tensorProd R S)

end Equalizer

end Algebra

variable (f : R ⟶ S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteProducts (Under.pushout f)
  body: letI : Algebra R S := f.hom.toAlgebra
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

中文:
实例 :
  签名: 保持FiniteProducts (Under.pushout f)
  定义体: letI : Algebra R S := f.hom.toAlgebra
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

Depends on / 依赖: Algebra, f.hom.toAlgebra, preservesLimitsOfShape_of_natIso, tensorProdIsoPushout, toAlgebra
-/
instance : PreservesFiniteProducts (Under.pushout f) where
  preserves _ :=
    letI : Algebra R S := f.hom.toAlgebra
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

/--
lemma `preservesFiniteLimits_of_flat` / 引理 `preservesFiniteLimits_of_flat`

English:
lemma preservesFiniteLimits_of_flat
  given: (hf : RingHom.Flat f.hom)
  proof: letI : Algebra R S := f.hom.toAlgebra
    haveI : Module.Flat R S := hf
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

中文:
引理 preservesFiniteLimits_of_flat
  条件: (hf : 环态射.平坦 f.hom)
  证明: letI : Algebra R S := f.hom.toAlgebra
    haveI : Module.Flat R S := hf
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

Depends on / 依赖: Algebra, Module, Module.Flat, f.hom.toAlgebra, preservesLimitsOfShape_of_natIso, tensorProdIsoPushout, toAlgebra
-/
lemma preservesFiniteLimits_of_flat (hf : RingHom.Flat f.hom) :
    PreservesFiniteLimits (Under.pushout f) where
  preservesFiniteLimits _ :=
    letI : Algebra R S := f.hom.toAlgebra
    haveI : Module.Flat R S := hf
    preservesLimitsOfShape_of_natIso (tensorProdIsoPushout R S)

end CommRingCat.Under
