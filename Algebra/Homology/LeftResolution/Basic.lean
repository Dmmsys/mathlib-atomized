/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Left resolutions

Given a fully faithful functor `ι : C ⥤ A` to an abelian category,
we introduce a structure `Abelian.LeftResolution ι` which gives
a functor `F : A ⥤ C` and a natural epimorphism
`π.app X : ι.obj (F.obj X) ⟶ X` for all `X : A`.
This is used in order to construct a resolution functor
`LeftResolution.chainComplexFunctor : A ⥤ ChainComplex C ℕ`.

This shall be used in order to construct functorial flat resolutions.

-/

@[expose] public section

namespace CategoryTheory.Abelian

open Category Limits Preadditive ZeroObject

variable {A C : Type*} [Category* C] [Category* A] (ι : C ⥤ A)

/--
Definition of `LeftResolution` / `LeftResolution` 的定义

English:
structure LeftResolution
  parameters: where
  axioms and operations (3):
    - F : A ⥤ C
    - π : F ⋙ ι ⟶ 𝟭 A
    - epi_π_app((X : A)) : Epi (π.app X)  [default: by infer_instance]

中文:
结构 LeftResolution
  参数: where
  公理与运算 (3 个):
    - F : A ⥤ C
    - π : F ⋙ ι ⟶ 𝟭 A
    - epi_π_app((X : A)) : Epi (π.app X)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure LeftResolution where
  /-- a functor which sends `X : A` to an object `F.obj X` with an epimorphism
    `π.app X : ι.obj (F.obj X) ⟶ X` -/
  F : A ⥤ C
  /-- the natural epimorphism -/
  π : F ⋙ ι ⟶ 𝟭 A
  epi_π_app (X : A) : Epi (π.app X) := by infer_instance

namespace LeftResolution

attribute [instance] epi_π_app

variable {ι} (Λ : LeftResolution ι) (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)

@[reassoc (attr := simp)]
/--
lemma `π_naturality` / 引理 `π_naturality`

English:
lemma π_naturality
  statement: ι.map (Λ.F.map f) ≫ Λ.π.app Y = Λ.π.app X ≫ f
  proof: Λ.π.naturality f

中文:
引理 π_naturality
  结论: ι.map (Λ.F.map f) ≫ Λ.π.app Y = Λ.π.app X ≫ f
  证明: Λ.π.naturality f

Depends on / 依赖: naturality
-/
lemma π_naturality : ι.map (Λ.F.map f) ≫ Λ.π.app Y = Λ.π.app X ≫ f :=
  Λ.π.naturality f

variable [ι.Full] [ι.Faithful] [HasZeroMorphisms C] [Abelian A]

/--
Definition of `chainComplex` / `chainComplex` 的定义

English:
definition chainComplex
  signature: : ChainComplex C Nat
  body: ChainComplex.mk' _ _ (ι.preimage (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _))
    (fun f => ⟨_, ι.preimage (Λ.π.app (kernel (ι.map f)) ≫ kernel.ι _),
      ι.map_injective (by simp)⟩)

中文:
定义 chainComplex
  签名: : ChainComplex C 自然数
  定义体: ChainComplex.mk' _ _ (ι.preimage (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _))
    (fun f => ⟨_, ι.preimage (Λ.π.app (kernel (ι.map f)) ≫ kernel.ι _),
      ι.map_injective (by simp)⟩)

Depends on / 依赖: ChainComplex, ChainComplex.mk, kernel, map_injective, preimage
-/
noncomputable def chainComplex : ChainComplex C Nat :=
  ChainComplex.mk' _ _ (ι.preimage (Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _))
    (fun f => ⟨_, ι.preimage (Λ.π.app (kernel (ι.map f)) ≫ kernel.ι _),
      ι.map_injective (by simp)⟩)

/--
Definition of `chainComplexXZeroIso` / `chainComplexXZeroIso` 的定义

English:
definition chainComplexXZeroIso
  signature: :
  body: Iso.refl _

中文:
定义 chainComplexXZeroIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def chainComplexXZeroIso :
    (Λ.chainComplex X).X 0 ≅ Λ.F.obj X := Iso.refl _

/--
Definition of `chainComplexXOneIso` / `chainComplexXOneIso` 的定义

English:
definition chainComplexXOneIso
  signature: :
  body: Iso.refl _

中文:
定义 chainComplexXOneIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def chainComplexXOneIso :
    (Λ.chainComplex X).X 1 ≅ Λ.F.obj (kernel (Λ.π.app X)) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `map_chainComplex_d_1_0` / 引理 `map_chainComplex_d_1_0`

English:
lemma map_chainComplex_d_1_0
  proof: by
  simp [chainComplexXOneIso, chainComplexXZeroIso, chainComplex]

中文:
引理 map_chainComplex_d_1_0
  证明: by
  simp [chainComplexXOneIso, chainComplexXZeroIso, chainComplex]

Depends on / 依赖: chainComplex, chainComplexXOneIso, chainComplexXZeroIso
-/
lemma map_chainComplex_d_1_0 :
    ι.map ((Λ.chainComplex X).d 1 0) =
      ι.map (Λ.chainComplexXOneIso X).hom ≫ Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι _ ≫
      ι.map (Λ.chainComplexXZeroIso X).inv := by
  simp [chainComplexXOneIso, chainComplexXZeroIso, chainComplex]

/--
Definition of `chainComplexXIso` / `chainComplexXIso` 的定义

English:
definition chainComplexXIso
  signature: (n : Nat)
  body: by
  apply ChainComplex.mk'XIso

中文:
定义 chainComplexXIso
  签名: (n : 自然数)
  定义体: by
  apply ChainComplex.mk'XIso

Depends on / 依赖: ChainComplex, ChainComplex.mk
-/
noncomputable def chainComplexXIso (n : Nat) :
    (Λ.chainComplex X).X (n + 2) ≅ Λ.F.obj (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) := by
  apply ChainComplex.mk'XIso

/--
lemma `map_chainComplex_d` / 引理 `map_chainComplex_d`

English:
lemma map_chainComplex_d
  given: (n : Nat)
  proof: by
  have := ι.map_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))
  dsimp at this
  rw [← this]; rw [← Functor.map_comp]
  congr 1
  apply ChainComplex.mk'_d

中文:
引理 map_chainComplex_d
  条件: (n : 自然数)
  证明: by
  have := ι.map_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))
  dsimp at this
  rw [← this]; rw [← Functor.map_comp]
  congr 1
  apply ChainComplex.mk'_d

Depends on / 依赖: ChainComplex, ChainComplex.mk, Functor, Functor.map_comp, chainComplex, kernel, map_comp, map_preimage
-/
lemma map_chainComplex_d (n : Nat) :
    ι.map ((Λ.chainComplex X).d (n + 2) (n + 1)) =
    ι.map (Λ.chainComplexXIso X n).hom ≫ Λ.π.app (kernel (ι.map ((Λ.chainComplex X).d (n + 1) n))) ≫
      kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)) := by
  have := ι.map_preimage (Λ.π.app _ ≫ kernel.ι (ι.map ((Λ.chainComplex X).d (n + 1) n)))
  dsimp at this
  rw [← this]; rw [← Functor.map_comp]
  congr 1
  apply ChainComplex.mk'_d

attribute [irreducible] chainComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `exactAt_map_chainComplex_succ` / 引理 `exactAt_map_chainComplex_succ`

English:
lemma exactAt_map_chainComplex_succ
  given: (n : Nat)
  proof: by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by dsimp; lia)) (by simp)]; rw [ShortComplex.exact_iff_epi_kernel_lift]
  convert! epi_comp (ι.map (Λ.chainComplexXIso X n).hom) (Λ.π.app _)
  rw [← cancel_mono (kernel.ι _)]; rw [kernel.lift_ι]
  simp [map_ch

中文:
引理 exactAt_map_chainComplex_succ
  条件: (n : 自然数)
  证明: by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by dsimp; lia)) (by simp)]; rw [ShortComplex.exact_iff_epi_kernel_lift]
  convert! epi_comp (ι.map (Λ.chainComplexXIso X n).hom) (Λ.π.app _)
  rw [← cancel_mono (kernel.ι _)]; rw [kernel.lift_ι]
  simp [map_ch

Depends on / 依赖: ComplexShape, ComplexShape.prev_eq, HomologicalComplex, HomologicalComplex.exactAt_iff, ShortComplex, ShortComplex.exact_iff_epi_kernel_lift, cancel_mono, chainComplexXIso, convert, epi_comp, exactAt_iff, exact_iff_epi_kernel_lift, kernel, kernel.lift_, map_chainComplex_d, prev_eq
-/
lemma exactAt_map_chainComplex_succ (n : Nat) :
    ((ι.mapHomologicalComplex _).obj (Λ.chainComplex X)).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by dsimp; lia)) (by simp)]; rw [ShortComplex.exact_iff_epi_kernel_lift]
  convert! epi_comp (ι.map (Λ.chainComplexXIso X n).hom) (Λ.π.app _)
  rw [← cancel_mono (kernel.ι _)]; rw [kernel.lift_ι]
  simp [map_chainComplex_d]

variable {X Y Z}

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `chainComplexMap` / `chainComplexMap` 的定义

English:
definition chainComplexMap
  signature: : Λ.chainComplex X ⟶ Λ.chainComplex Y
  body: ChainComplex.mkHom _ _
    ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
    ((Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv)
    (ι.map_injective (by
        dsimp
   

中文:
定义 chainComplexMap
  签名: : Λ.chainComplex X ⟶ Λ.chainComplex Y
  定义体: ChainComplex.mkHom _ _
    ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
    ((Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv)
    (ι.map_injective (by
        dsimp
   

Depends on / 依赖: Category, Category.assoc, ChainComplex, ChainComplex.mkHom, F.map, Functor, Functor.map_comp, chainComplexXIso, chainComplexXOneIso, chainComplexXZeroIso, kernel, kernel.map, map_chainComplex_d_1_0, map_com, map_comp, map_comp_assoc, map_injective, naturality
-/
noncomputable def chainComplexMap : Λ.chainComplex X ⟶ Λ.chainComplex Y :=
  ChainComplex.mkHom _ _
    ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv)
    ((Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv)
    (ι.map_injective (by
        dsimp
        simp only [Category.assoc, Functor.map_comp, map_chainComplex_d_1_0]
        simp only [← ι.map_comp, ← ι.map_comp_assoc]
        simp))
    (fun n p =>
      ⟨(Λ.chainComplexXIso X n).hom ≫ (Λ.F.map
        (kernel.map _ _ (ι.map p.2.1) (ι.map p.1) (by
          rw [← ι.map_comp]; rw [← ι.map_comp]; rw [p.2.2]))) ≫ (Λ.chainComplexXIso Y n).inv,
            ι.map_injective (by simp [map_chainComplex_d])⟩)

@[simp]
/--
lemma `chainComplexMap_f_0` / 引理 `chainComplexMap_f_0`

English:
lemma chainComplexMap_f_0
  proof: rfl

@[simp]

中文:
引理 chainComplexMap_f_0
  证明: rfl

@[simp]
-/
lemma chainComplexMap_f_0 :
    (Λ.chainComplexMap f).f 0 =
      ((Λ.chainComplexXZeroIso X).hom ≫ Λ.F.map f ≫ (Λ.chainComplexXZeroIso Y).inv) := rfl

@[simp]
/--
lemma `chainComplexMap_f_1` / 引理 `chainComplexMap_f_1`

English:
lemma chainComplexMap_f_1
  proof: rfl

@[simp]

中文:
引理 chainComplexMap_f_1
  证明: rfl

@[simp]
-/
lemma chainComplexMap_f_1 :
    (Λ.chainComplexMap f).f 1 =
    (Λ.chainComplexXOneIso X).hom ≫
      Λ.F.map (kernel.map _ _ (ι.map (Λ.F.map f)) f (Λ.π.naturality f).symm) ≫
      (Λ.chainComplexXOneIso Y).inv := rfl

@[simp]
/--
lemma `chainComplexMap_f_succ_succ` / 引理 `chainComplexMap_f_succ_succ`

English:
lemma chainComplexMap_f_succ_succ
  given: (n : Nat)
  proof: by
  apply ChainComplex.mkHom_f_succ_succ

中文:
引理 chainComplexMap_f_succ_succ
  条件: (n : 自然数)
  证明: by
  apply ChainComplex.mkHom_f_succ_succ

Depends on / 依赖: ChainComplex, ChainComplex.mkHom_f_succ_succ, mkHom_f_succ_succ
-/
lemma chainComplexMap_f_succ_succ (n : Nat) :
    (Λ.chainComplexMap f).f (n + 2) =
      (Λ.chainComplexXIso X n).hom ≫
        Λ.F.map (kernel.map _ _ (ι.map ((Λ.chainComplexMap f).f (n + 1)))
          (ι.map ((Λ.chainComplexMap f).f n))
          (by rw [← ι.map_comp, ← ι.map_comp, HomologicalComplex.Hom.comm])) ≫
          (Λ.chainComplexXIso Y n).inv := by
  apply ChainComplex.mkHom_f_succ_succ

set_option backward.defeqAttrib.useBackward true in
variable (X) in
@[simp]
/--
lemma `chainComplexMap_id` / 引理 `chainComplexMap_id`

English:
lemma chainComplexMap_id
  statement: Λ.chainComplexMap (𝟙 X) = 𝟙 _
  proof: by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

中文:
引理 chainComplexMap_id
  结论: Λ.chainComplexMap (𝟙 X) = 𝟙 _
  证明: by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]
-/
lemma chainComplexMap_id : Λ.chainComplexMap (𝟙 X) = 𝟙 _ := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

set_option backward.defeqAttrib.useBackward true in
variable (X Y) in
@[simp]
/--
lemma `chainComplexMap_zero` / 引理 `chainComplexMap_zero`

English:
lemma chainComplexMap_zero
  given: [Λ.F.PreservesZeroMorphisms]
  proof: by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

中文:
引理 chainComplexMap_zero
  条件: [Λ.F.PreservesZeroMorphisms]
  证明: by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]
-/
lemma chainComplexMap_zero [Λ.F.PreservesZeroMorphisms] :
    Λ.chainComplexMap (0 : X ⟶ Y) = 0 := by
  ext n
  induction n with
  | zero => simp
  | succ n hn => obtain _ | n := n <;> simp [hn]

set_option backward.defeqAttrib.useBackward true in
@[reassoc, simp]
/--
lemma `chainComplexMap_comp` / 引理 `chainComplexMap_comp`

English:
lemma chainComplexMap_comp
  proof: by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
    obtain _ | n := n
    all_goals
      dsimp
      simp only [chainComplexMap_f_succ_succ, assoc, Iso.cancel_iso_hom_left,
        Iso.inv_hom_id_assoc, ← Λ.F.map_comp_assoc, Iso.cancel_iso_inv_right_assoc]
      congr 1
      cat_di

中文:
引理 chainComplexMap_comp
  证明: by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
    obtain _ | n := n
    all_goals
      dsimp
      simp only [chainComplexMap_f_succ_succ, assoc, Iso.cancel_iso_hom_left,
        Iso.inv_hom_id_assoc, ← Λ.F.map_comp_assoc, Iso.cancel_iso_inv_right_assoc]
      congr 1
      cat_di

Depends on / 依赖: F.map_comp_assoc, Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right_assoc, Iso.inv_hom_id_assoc, all_goals, cancel_iso_hom_left, cancel_iso_inv_right_assoc, cat_disch, chainComplexMap_f_succ_succ, inv_hom_id_assoc, map_comp_assoc
-/
lemma chainComplexMap_comp :
    Λ.chainComplexMap (f ≫ g) = Λ.chainComplexMap f ≫ Λ.chainComplexMap g := by
  ext n
  induction n with
  | zero => simp
  | succ n hn =>
    obtain _ | n := n
    all_goals
      dsimp
      simp only [chainComplexMap_f_succ_succ, assoc, Iso.cancel_iso_hom_left,
        Iso.inv_hom_id_assoc, ← Λ.F.map_comp_assoc, Iso.cancel_iso_inv_right_assoc]
      congr 1
      cat_disch

/--
Definition of `chainComplexFunctor` / `chainComplexFunctor` 的定义

English:
definition chainComplexFunctor
  signature: : A ⥤ ChainComplex C Nat where
  body: Λ.chainComplex X
  map f := Λ.chainComplexMap f

中文:
定义 chainComplexFunctor
  签名: : A ⥤ ChainComplex C 自然数 where
  定义体: Λ.chainComplex X
  map f := Λ.chainComplexMap f

Depends on / 依赖: chainComplex
-/
noncomputable def chainComplexFunctor : A ⥤ ChainComplex C Nat where
  obj X := Λ.chainComplex X
  map f := Λ.chainComplexMap f

end LeftResolution

end CategoryTheory.Abelian
