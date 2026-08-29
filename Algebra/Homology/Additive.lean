/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homology is an additive functor

When `V` is preadditive, `HomologicalComplex V c` is also preadditive,
and `homologyFunctor` is additive.

-/

@[expose] public section


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {W : Type*} [Category* W] [Preadditive W]
variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]
variable {c : ComplexShape ι} {C D : HomologicalComplex V c}
variable (f : C ⟶ D) (i : ι)

namespace HomologicalComplex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (C ⟶ D)
  body: ⟨{ f := fun _ => 0 }⟩

中文:
实例 :
  签名: 零 (C ⟶ D)
  定义体: ⟨{ f := fun _ => 0 }⟩

Depends on / 依赖: h.isLimit, h.isLimitEquivIsLimitKernelFork, isLimit, isLimitEquivIsLimitKernelFork
-/
instance : Zero (C ⟶ D) :=
  ⟨{ f := fun _ => 0 }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (C ⟶ D)
  body: ⟨fun f g => { f := fun i => f.f i + g.f i }⟩

中文:
实例 :
  签名: 加法 (C ⟶ D)
  定义体: ⟨fun f g => { f := fun i => f.f i + g.f i }⟩
-/
instance : Add (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i + g.f i }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (C ⟶ D)
  body: ⟨fun f => { f := fun i => -f.f i }⟩

中文:
实例 :
  签名: 取负 (C ⟶ D)
  定义体: ⟨fun f => { f := fun i => -f.f i }⟩
-/
instance : Neg (C ⟶ D) :=
  ⟨fun f => { f := fun i => -f.f i }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (C ⟶ D)
  body: ⟨fun f g => { f := fun i => f.f i - g.f i }⟩

中文:
实例 :
  签名: 减法 (C ⟶ D)
  定义体: ⟨fun f g => { f := fun i => f.f i - g.f i }⟩
-/
instance : Sub (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i - g.f i }⟩

/--
Instance `hasNatScalar` / 实例 `hasNatScalar`

English:
instance hasNatScalar
  signature: : SMul Nat (C ⟶ D)
  body: ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul] }⟩

中文:
实例 has自然数Scalar
  签名: : 标量乘法 自然数 (C ⟶ D)
  定义体: ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul] }⟩

Depends on / 依赖: Preadditive, Preadditive.comp_nsmul, Preadditive.nsmul_comp, comp_nsmul, nsmul_comp
-/
instance hasNatScalar : SMul Nat (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul] }⟩

/--
Instance `hasIntScalar` / 实例 `hasIntScalar`

English:
instance hasIntScalar
  signature: : SMul Int (C ⟶ D)
  body: ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul] }⟩

@[simp]

中文:
实例 has整数Scalar
  签名: : 标量乘法 整数 (C ⟶ D)
  定义体: ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul] }⟩

@[simp]

Depends on / 依赖: Preadditive, Preadditive.comp_zsmul, Preadditive.zsmul_comp, comp_zsmul, zsmul_comp
-/
instance hasIntScalar : SMul Int (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i
      comm' := fun i j _ => by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul] }⟩

@[simp]
/--
theorem `zero_f_apply` / 定理 `zero_f_apply`

English:
theorem zero_f_apply
  given: (i : ι)
  statement: (0 : C ⟶ D).f i = 0
  proof: rfl

@[simp]

中文:
定理 zero_f_apply
  条件: (i : ι)
  结论: (0 : C ⟶ D).f i = 0
  证明: rfl

@[simp]
-/
theorem zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

@[simp]
/--
theorem `add_f_apply` / 定理 `add_f_apply`

English:
theorem add_f_apply
  given: (f g : C ⟶ D) (i : ι)
  statement: (f + g).f i = f.f i + g.f i
  proof: rfl

@[simp]

中文:
定理 add_f_apply
  条件: (f g : C ⟶ D) (i : ι)
  结论: (f + g).f i = f.f i + g.f i
  证明: rfl

@[simp]
-/
theorem add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i :=
  rfl

@[simp]
/--
theorem `neg_f_apply` / 定理 `neg_f_apply`

English:
theorem neg_f_apply
  given: (f : C ⟶ D) (i : ι)
  statement: (-f).f i = -f.f i
  proof: rfl

@[simp]

中文:
定理 neg_f_apply
  条件: (f : C ⟶ D) (i : ι)
  结论: (-f).f i = -f.f i
  证明: rfl

@[simp]
-/
theorem neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i :=
  rfl

@[simp]
/--
theorem `sub_f_apply` / 定理 `sub_f_apply`

English:
theorem sub_f_apply
  given: (f g : C ⟶ D) (i : ι)
  statement: (f - g).f i = f.f i - g.f i
  proof: rfl

@[simp]

中文:
定理 sub_f_apply
  条件: (f g : C ⟶ D) (i : ι)
  结论: (f - g).f i = f.f i - g.f i
  证明: rfl

@[simp]
-/
theorem sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i :=
  rfl

@[simp]
/--
theorem `nsmul_f_apply` / 定理 `nsmul_f_apply`

English:
theorem nsmul_f_apply
  given: (n : Nat) (f : C ⟶ D) (i : ι)
  statement: (n • f).f i = n • f.f i
  proof: rfl

@[simp]

中文:
定理 nsmul_f_apply
  条件: (n : 自然数) (f : C ⟶ D) (i : ι)
  结论: (n • f).f i = n • f.f i
  证明: rfl

@[simp]
-/
theorem nsmul_f_apply (n : Nat) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl

@[simp]
/--
theorem `zsmul_f_apply` / 定理 `zsmul_f_apply`

English:
theorem zsmul_f_apply
  given: (n : Int) (f : C ⟶ D) (i : ι)
  statement: (n • f).f i = n • f.f i
  proof: rfl

中文:
定理 zsmul_f_apply
  条件: (n : 整数) (f : C ⟶ D) (i : ι)
  结论: (n • f).f i = n • f.f i
  证明: rfl
-/
theorem zsmul_f_apply (n : Int) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (C ⟶ D)
  body: Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective
    (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch)

中文:
实例 :
  签名: 加法交换群 (C ⟶ D)
  定义体: Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective
    (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch)

Depends on / 依赖: Function, Function.Injective.addCommGroup, Hom.f, HomologicalComplex, HomologicalComplex.hom_f_injective, Injective, addCommGroup, cat_disch, hom_f_injective
-/
instance : AddCommGroup (C ⟶ D) :=
  Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective
    (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch) (by cat_disch)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (HomologicalComplex V c)

中文:
实例 :
  签名: 预加性 (同调复形 V c)
-/
instance : Preadditive (HomologicalComplex V c) where

/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps!]
/--
Definition of `Hom.fAddMonoidHom` / `Hom.fAddMonoidHom` 的定义

English:
definition Hom.fAddMonoidHom
  signature: {C₁ C₂ : HomologicalComplex V c} (i : ι)
  body: AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl

中文:
定义 态射.fAddMonoidHom
  签名: {C₁ C₂ : 同调复形 V c} (i : ι)
  定义体: AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, Hom.f
-/
def Hom.fAddMonoidHom {C₁ C₂ : HomologicalComplex V c} (i : ι) : (C₁ ⟶ C₂) ->+ (C₁.X i ⟶ C₂.X i) :=
  AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl

/--
Instance `eval_additive` / 实例 `eval_additive`

English:
instance eval_additive
  signature: (i : ι)

中文:
实例 eval_additive
  签名: (i : ι)
-/
instance eval_additive (i : ι) : (eval V c i).Additive where

end HomologicalComplex

namespace CategoryTheory

/-- An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps]
/--
Definition of `Functor.mapHomologicalComplex` / `Functor.mapHomologicalComplex` 的定义

English:
definition Functor.mapHomologicalComplex
  signature: (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι)
  body: { X := fun i => F.obj (C.X i)
      d := fun i j => F.map (C.d i j)
      shape := fun i j w => by
        rw [C.shape _ _ w]; rw [F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map f :=
    { f := fun i => F.map (f.f i)
      comm' := fun i j _ => by
        dsimp
        rw [← F.map_comp]; rw [← F.map_comp]; rw [f.comm] }

中文:
定义 函子.mapHomologicalComplex
  签名: (F : W₁ ⥤ W₂) [F.保持ZeroMorphisms] (c : 余mplexShape ι)
  定义体: { X := fun i => F.obj (C.X i)
      d := fun i j => F.map (C.d i j)
      shape := fun i j w => by
        rw [C.shape _ _ w]; rw [F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map f :=
    { f := fun i => F.map (f.f i)
      comm' := fun i j _ => by
        dsimp
        rw [← F.map_comp]; rw [← F.map_comp]; rw [f.comm] }

Depends on / 依赖: C.d_comp_d, C.shape, F.map, F.map_comp, F.map_zero, F.obj, d_comp_d, f.comm, map_comp, map_zero
-/
def Functor.mapHomologicalComplex (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    HomologicalComplex W₁ c ⥤ HomologicalComplex W₂ c where
  obj C :=
    { X := fun i => F.obj (C.X i)
      d := fun i j => F.map (C.d i j)
      shape := fun i j w => by
        rw [C.shape _ _ w]; rw [F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map f :=
    { f := fun i => F.map (f.f i)
      comm' := fun i j _ => by
        dsimp
        rw [← F.map_comp]; rw [← F.map_comp]; rw [f.comm] }

instance (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).PreservesZeroMorphisms where

/--
Instance `Functor.map_homogical_complex_additive` / 实例 `Functor.map_homogical_complex_additive`

English:
instance Functor.map_homogical_complex_additive
  signature: (F : V ⥤ W) [F.Additive] (c : ComplexShape ι)

中文:
实例 函子.map_homogical_complex_additive
  签名: (F : V ⥤ W) [F.加性] (c : 余mplexShape ι)
-/
instance Functor.map_homogical_complex_additive (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).Additive where

variable (W₁)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor on homological complexes induced by the identity functor is
isomorphic to the identity functor. -/
@[simps!]
/--
Definition of `Functor.mapHomologicalComplexIdIso` / `Functor.mapHomologicalComplexIdIso` 的定义

English:
definition Functor.mapHomologicalComplexIdIso
  signature: (c : ComplexShape ι)
  body: NatIso.ofComponents fun K => Hom.isoOfComponents fun _ => Iso.refl _

中文:
定义 函子.mapHomologicalComplexIdIso
  签名: (c : 余mplexShape ι)
  定义体: NatIso.ofComponents fun K => Hom.isoOfComponents fun _ => Iso.refl _

Depends on / 依赖: Hom.isoOfComponents, Iso.refl, NatIso, NatIso.ofComponents, isoOfComponents, ofComponents
-/
def Functor.mapHomologicalComplexIdIso (c : ComplexShape ι) :
    (𝟭 W₁).mapHomologicalComplex c ≅ 𝟭 _ :=
  NatIso.ofComponents fun K => Hom.isoOfComponents fun _ => Iso.refl _

/--
Instance `Functor.mapHomologicalComplex_reflects_iso` / 实例 `Functor.mapHomologicalComplex_reflects_iso`

English:
instance Functor.mapHomologicalComplex_reflects_iso
  signature: (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
  body: ⟨fun f => by
    intro
    have : forall n : ι, IsIso (F.map (f.f n)) := fun n =>
        ((HomologicalComplex.eval W₂ c n).mapIso
          (asIso ((F.mapHomologicalComplex c).map f))).isIso_hom
    have := fun n => isIso_of_reflects_iso (f.f n) F
    exact HomologicalComplex.Hom.isIso_of_components f⟩

中文:
实例 函子.mapHomologicalComplex_reflects_iso
  签名: (F : W₁ ⥤ W₂) [F.保持ZeroMorphisms]
  定义体: ⟨fun f => by
    intro
    have : forall n : ι, IsIso (F.map (f.f n)) := fun n =>
        ((HomologicalComplex.eval W₂ c n).mapIso
          (asIso ((F.mapHomologicalComplex c).map f))).isIso_hom
    have := fun n => isIso_of_reflects_iso (f.f n) F
    exact HomologicalComplex.Hom.isIso_of_components f⟩

Depends on / 依赖: F.map, F.mapHomologicalComplex, HomologicalComplex, HomologicalComplex.Hom.isIso_of_components, HomologicalComplex.eval, isIso_hom, isIso_of_components, isIso_of_reflects_iso, mapHomologicalComplex, mapIso
-/
instance Functor.mapHomologicalComplex_reflects_iso (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    [ReflectsIsomorphisms F] (c : ComplexShape ι) :
    ReflectsIsomorphisms (F.mapHomologicalComplex c) :=
  ⟨fun f => by
    intro
    have : forall n : ι, IsIso (F.map (f.f n)) := fun n =>
        ((HomologicalComplex.eval W₂ c n).mapIso
          (asIso ((F.mapHomologicalComplex c).map f))).isIso_hom
    have := fun n => isIso_of_reflects_iso (f.f n) F
    exact HomologicalComplex.Hom.isIso_of_components f⟩

instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [F.Faithful] :
    (F.mapHomologicalComplex c).Faithful where
  map_injective {K L} f₁ f₂ h := by
    ext
    exact F.map_injective ((HomologicalComplex.eval W c _).congr_map h)

set_option backward.isDefEq.respectTransparency.types false in
instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [F.Faithful] [F.Full] :
    (F.mapHomologicalComplex c).Full where
  map_surjective {X Y} f := ⟨
    { f n := F.preimage (f.f n)
      comm' i j _ := by
        apply F.map_injective
        simp only [Functor.map_comp, Functor.map_preimage]
        exact f.comm i j }, by cat_disch⟩

variable {W₁}

set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
@[simps]
/--
Definition of `NatTrans.mapHomologicalComplex` / `NatTrans.mapHomologicalComplex` 的定义

English:
definition NatTrans.mapHomologicalComplex
  signature: {F G : W₁ ⥤ W₂}
  body: { f := fun _ => α.app _ }

@[simp]

中文:
定义 自然变换.mapHomologicalComplex
  签名: {F G : W₁ ⥤ W₂}
  定义体: { f := fun _ => α.app _ }

@[simp]
-/
def NatTrans.mapHomologicalComplex {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomologicalComplex c ⟶ G.mapHomologicalComplex c where
  app C := { f := fun _ => α.app _ }

@[simp]
/--
theorem `NatTrans.mapHomologicalComplex_id` / 定理 `NatTrans.mapHomologicalComplex_id`

English:
theorem NatTrans.mapHomologicalComplex_id
  proof: by cat_disch

@[simp]

中文:
定理 自然变换.mapHomologicalComplex_id
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
theorem NatTrans.mapHomologicalComplex_id
    (c : ComplexShape ι) (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] :
    NatTrans.mapHomologicalComplex (𝟙 F) c = 𝟙 (F.mapHomologicalComplex c) := by cat_disch

@[simp]
/--
theorem `NatTrans.mapHomologicalComplex_comp` / 定理 `NatTrans.mapHomologicalComplex_comp`

English:
theorem NatTrans.mapHomologicalComplex_comp
  statement: (c : ComplexShape ι) {F G H : W₁ ⥤ W₂}
  proof: by
  cat_disch

@[reassoc]

中文:
定理 自然变换.mapHomologicalComplex_comp
  结论: (c : 余mplexShape ι) {F G H : W₁ ⥤ W₂}
  证明: by
  cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
theorem NatTrans.mapHomologicalComplex_comp (c : ComplexShape ι) {F G H : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomologicalComplex (α ≫ β) c =
      NatTrans.mapHomologicalComplex α c ≫ NatTrans.mapHomologicalComplex β c := by
  cat_disch

@[reassoc]
/--
theorem `NatTrans.mapHomologicalComplex_naturality` / 定理 `NatTrans.mapHomologicalComplex_naturality`

English:
theorem NatTrans.mapHomologicalComplex_naturality
  statement: {c : ComplexShape ι} {F G : W₁ ⥤ W₂}
  proof: by
  simp

中文:
定理 自然变换.mapHomologicalComplex_naturality
  结论: {c : 余mplexShape ι} {F G : W₁ ⥤ W₂}
  证明: by
  simp
-/
theorem NatTrans.mapHomologicalComplex_naturality {c : ComplexShape ι} {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) {C D : HomologicalComplex W₁ c} (f : C ⟶ D) :
    (F.mapHomologicalComplex c).map f ≫ (NatTrans.mapHomologicalComplex α c).app D =
      (NatTrans.mapHomologicalComplex α c).app C ≫ (G.mapHomologicalComplex c).map f := by
  simp

/-- A natural isomorphism between functors induces a natural isomorphism
between those functors applied to homological complexes.
-/
@[simps!]
/--
Definition of `NatIso.mapHomologicalComplex` / `NatIso.mapHomologicalComplex` 的定义

English:
definition NatIso.mapHomologicalComplex
  signature: {F G : W₁ ⥤ W₂} [F.PreservesZeroMorphisms]
  body: NatTrans.mapHomologicalComplex α.hom c
  inv := NatTrans.mapHomologicalComplex α.inv c
  hom_inv_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id,
    NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.inv_hom_id,
    NatTrans.mapHomologicalComplex_id]

中文:
定义 自然数Iso.mapHomologicalComplex
  签名: {F G : W₁ ⥤ W₂} [F.保持ZeroMorphisms]
  定义体: NatTrans.mapHomologicalComplex α.hom c
  inv := NatTrans.mapHomologicalComplex α.inv c
  hom_inv_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id,
    NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.inv_hom_id,
    NatTrans.mapHomologicalComplex_id]

Depends on / 依赖: NatTrans, NatTrans.mapHomologicalComplex, mapHomologicalComplex
-/
def NatIso.mapHomologicalComplex {F G : W₁ ⥤ W₂} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (α : F ≅ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ≅ G.mapHomologicalComplex c where
  hom := NatTrans.mapHomologicalComplex α.hom c
  inv := NatTrans.mapHomologicalComplex α.inv c
  hom_inv_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id,
    NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by simp only [← NatTrans.mapHomologicalComplex_comp, α.inv_hom_id,
    NatTrans.mapHomologicalComplex_id]

/-- If additive functors are related by an isomorphism `F ⋙ G ≅ H`, this is
the corresponding isomorphism for the induced functors on categories
of homological complexes. -/
@[simps!]
/--
Definition of `Functor.mapHomologicalComplexCompIso` / `Functor.mapHomologicalComplexCompIso` 的定义

English:
definition Functor.mapHomologicalComplexCompIso
  signature: {W' : Type*} [Category W'] [Preadditive W']
  body: NatIso.mapHomologicalComplex e c

中文:
定义 函子.mapHomologicalComplexCompIso
  签名: {W' : 类型} [范畴 W'] [预加性 W']
  定义体: NatIso.mapHomologicalComplex e c

Depends on / 依赖: NatIso, NatIso.mapHomologicalComplex, mapHomologicalComplex
-/
def Functor.mapHomologicalComplexCompIso {W' : Type*} [Category W'] [Preadditive W']
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅ H.mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex e c

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalences between the respective categories
of homological complex.
-/
@[simps]
/--
Definition of `Equivalence.mapHomologicalComplex` / `Equivalence.mapHomologicalComplex` 的定义

English:
definition Equivalence.mapHomologicalComplex
  signature: (e : W₁ ≌ W₂) [e.functor.PreservesZeroMorphisms]
  body: e.functor.mapHomologicalComplex c
  inverse := e.inverse.mapHomologicalComplex c
  unitIso :=
    (Functor.mapHomologicalComplexIdIso W₁ c).symm ≪≫ NatIso.mapHomologicalComplex e.unitIso c
  counitIso := NatIso.mapHomologicalComplex e.counitIso c ≪≫
  Functor.mapHomologicalComplexIdIso W₂ c

中文:
定义 等价.mapHomologicalComplex
  签名: (e : W₁ ≌ W₂) [e.functor.保持ZeroMorphisms]
  定义体: e.functor.mapHomologicalComplex c
  inverse := e.inverse.mapHomologicalComplex c
  unitIso :=
    (Functor.mapHomologicalComplexIdIso W₁ c).symm ≪≫ NatIso.mapHomologicalComplex e.unitIso c
  counitIso := NatIso.mapHomologicalComplex e.counitIso c ≪≫
  Functor.mapHomologicalComplexIdIso W₂ c

Depends on / 依赖: e.functor.mapHomologicalComplex, functor, mapHomologicalComplex
-/
def Equivalence.mapHomologicalComplex (e : W₁ ≌ W₂) [e.functor.PreservesZeroMorphisms]
    (c : ComplexShape ι) :
    HomologicalComplex W₁ c ≌ HomologicalComplex W₂ c where
  functor := e.functor.mapHomologicalComplex c
  inverse := e.inverse.mapHomologicalComplex c
  unitIso :=
    (Functor.mapHomologicalComplexIdIso W₁ c).symm ≪≫ NatIso.mapHomologicalComplex e.unitIso c
  counitIso := NatIso.mapHomologicalComplex e.counitIso c ≪≫
  Functor.mapHomologicalComplexIdIso W₂ c

end CategoryTheory

namespace ChainComplex

variable {α : Type*} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `map_chain_complex_of` / 定理 `map_chain_complex_of`

English:
theorem map_chain_complex_of
  statement: (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (X : α -> W₁)
  proof: by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp

中文:
定理 map_chain_complex_of
  结论: (F : W₁ ⥤ W₂) [F.保持ZeroMorphisms] (X : α -> W₁)
  证明: by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp

Depends on / 依赖: HomologicalComplex, HomologicalComplex.ext
-/
theorem map_chain_complex_of (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (X : α -> W₁)
    (d : forall n, X (n + 1) ⟶ X n) (sq : forall n, d (n + 1) ≫ d n = 0) :
    (F.mapHomologicalComplex _).obj (ChainComplex.of X d sq) =
      ChainComplex.of (fun n => F.obj (X n)) (fun n => F.map (d n)) fun n => by
        rw [← F.map_comp]; rw [sq n]; rw [Functor.map_zero] := by
  refine HomologicalComplex.ext rfl ?_
  rintro i j (rfl : j + 1 = i)
  simp

end ChainComplex

variable [HasZeroObject W₁] [HasZeroObject W₂]

namespace HomologicalComplex

set_option backward.isDefEq.respectTransparency false in
instance (W : Type*) [Category* W] [Preadditive W] [HasZeroObject W] [DecidableEq ι] (j : ι) :
    (single W c j).Additive where
  map_add {_ _ f g} := by ext; simp [single]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `singleMapHomologicalComplex` / `singleMapHomologicalComplex` 的定义

English:
definition singleMapHomologicalComplex
  signature: (j : ι)
  body: NatIso.ofComponents
    (fun X =>
      { hom := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        inv := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        hom_inv_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · rw [zero_comp, ← F.map_id,
              (isZero_single_obj_X c j X _ h).eq_of_src (𝟙 _) 0, F.map_zero]
        inv_hom_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · apply (isZero_single_obj_X c j _ _ h).eq_of_src })
    fun f => by
      ext i
      dsimp
      split_ifs with h
      · subst h
        simp [single_map_f_self, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
      · apply (isZero_single_obj_X c j _ _ h).eq_of_tgt

中文:
定义 singleMapHomologicalComplex
  签名: (j : ι)
  定义体: NatIso.ofComponents
    (fun X =>
      { hom := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        inv := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        hom_inv_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · rw [zero_comp, ← F.map_id,
              (isZero_single_obj_X c j X _ h).eq_of_src (𝟙 _) 0, F.map_zero]
        inv_hom_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · apply (isZero_single_obj_X c j _ _ h).eq_of_src })
    fun f => by
      ext i
      dsimp
      split_ifs with h
      · subst h
        simp [single_map_f_self, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
      · apply (isZero_single_obj_X c j _ _ h).eq_of_tgt

Depends on / 依赖: F.map_id, F.map_zero, NatIso, NatIso.ofComponents, eqToHom, eq_of_src, hom_inv_id, inv_hom_id, isZero_single_obj_X, map_id, map_zero, ofComponents, single_map_f_sel, split_ifs, zero_comp
-/
noncomputable def singleMapHomologicalComplex (j : ι) :
    single W₁ c j ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single W₂ c j :=
  NatIso.ofComponents
    (fun X =>
      { hom := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        inv := { f := fun i => if h : i = j then eqToHom (by simp [h]) else 0 }
        hom_inv_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · rw [zero_comp, ← F.map_id,
              (isZero_single_obj_X c j X _ h).eq_of_src (𝟙 _) 0, F.map_zero]
        inv_hom_id := by
          ext i
          dsimp
          split_ifs with h
          · simp
          · apply (isZero_single_obj_X c j _ _ h).eq_of_src })
    fun f => by
      ext i
      dsimp
      split_ifs with h
      · subst h
        simp [single_map_f_self, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]
      · apply (isZero_single_obj_X c j _ _ h).eq_of_tgt

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `singleMapHomologicalComplex_hom_app_self` / 定理 `singleMapHomologicalComplex_hom_app_self`

English:
theorem singleMapHomologicalComplex_hom_app_self
  given: (j : ι) (X : W₁)
  proof: by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]

中文:
定理 singleMapHomologicalComplex_hom_app_self
  条件: (j : ι) (X : W₁)
  证明: by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]

Depends on / 依赖: eqToHom_map, singleMapHomologicalComplex, singleObjXIsoOfEq, singleObjXSelf
-/
theorem singleMapHomologicalComplex_hom_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f j =
      F.map (singleObjXSelf c j X).hom ≫ (singleObjXSelf c j (F.obj X)).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]
/--
theorem `singleMapHomologicalComplex_hom_app_ne` / 定理 `singleMapHomologicalComplex_hom_app_ne`

English:
theorem singleMapHomologicalComplex_hom_app_ne
  given: {i j : ι} (h : i != j) (X : W₁)
  proof: by
  simp [singleMapHomologicalComplex, h]

中文:
定理 singleMapHomologicalComplex_hom_app_ne
  条件: {i j : ι} (h : i != j) (X : W₁)
  证明: by
  simp [singleMapHomologicalComplex, h]

Depends on / 依赖: singleMapHomologicalComplex
-/
theorem singleMapHomologicalComplex_hom_app_ne {i j : ι} (h : i != j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).hom.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `singleMapHomologicalComplex_inv_app_self` / 定理 `singleMapHomologicalComplex_inv_app_self`

English:
theorem singleMapHomologicalComplex_inv_app_self
  given: (j : ι) (X : W₁)
  proof: by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]

中文:
定理 singleMapHomologicalComplex_inv_app_self
  条件: (j : ι) (X : W₁)
  证明: by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]

Depends on / 依赖: eqToHom_map, singleMapHomologicalComplex, singleObjXIsoOfEq, singleObjXSelf
-/
theorem singleMapHomologicalComplex_inv_app_self (j : ι) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f j =
      (singleObjXSelf c j (F.obj X)).hom ≫ F.map (singleObjXSelf c j X).inv := by
  simp [singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

@[simp]
/--
theorem `singleMapHomologicalComplex_inv_app_ne` / 定理 `singleMapHomologicalComplex_inv_app_ne`

English:
theorem singleMapHomologicalComplex_inv_app_ne
  given: {i j : ι} (h : i != j) (X : W₁)
  proof: by
  simp [singleMapHomologicalComplex, h]

中文:
定理 singleMapHomologicalComplex_inv_app_ne
  条件: {i j : ι} (h : i != j) (X : W₁)
  证明: by
  simp [singleMapHomologicalComplex, h]

Depends on / 依赖: singleMapHomologicalComplex
-/
theorem singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i != j) (X : W₁) :
    ((singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [singleMapHomologicalComplex, h]

end HomologicalComplex
