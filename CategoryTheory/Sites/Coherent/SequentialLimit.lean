/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Subcanonical
/-!

# Limits of epimorphisms in coherent topoi

This file proves that a sequential limit of epimorphisms is epimorphic in the category of sheaves
for the coherent topology on a preregular finitary extensive category where sequential limits of
effective epimorphisms are effective epimorphisms.

In other words, given epimorphisms of sheaves

`⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`,

the projection map `lim Xₙ ⟶ X₀` is an epimorphism (see `coherentTopology.epi_π_app_zero_of_epi`).

This is deduced from the corresponding statement about locally surjective morphisms of sheaves
(see `coherentTopology.isLocallySurjective_π_app_zero_of_isLocallySurjective_map`).
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.coherentTopology

variable {C : Type u} [Category.{v} C] [Preregular C] [FinitaryExtensive C]
variable {F : Natᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)} {c : Cone F}
    (hc : IsLimit c)
    (hF : forall n, Sheaf.IsLocallySurjective (F.map (homOfLE (Nat.le_succ n)).op))

/--
Definition of `struct` / `struct` 的定义

English:
structure struct
  parameters: (F : Natᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v))
  axioms and operations (5):
    - X((n : Nat)) : C
    - x((n : Nat)) : (F.obj ⟨n⟩).obj.obj ⟨X n⟩
    - map((n : Nat)) : X (n + 1) ⟶ X n
    - effectiveEpi((n : Nat)) : EffectiveEpi (map n)
    - w((n : Nat)) : (F.map (homOfLE (n.le_add_right 1)).op).hom.app (op (X (n + 1))) (x (n + 1)) = (F.obj (op n)).obj.map (map n).op (x n)

中文:
结构 struct
  参数: (F : 自然数ᵒᵖ ⥤ Sheaf (coherentTopology C) (类型v))
  公理与运算 (5 个):
    - X((n : 自然数)) : C
    - x((n : 自然数)) : (F.obj ⟨n⟩).obj.obj ⟨X n⟩
    - map((n : 自然数)) : X (n + 1) ⟶ X n
    - effectiveEpi((n : 自然数)) : EffectiveEpi (map n)
    - w((n : 自然数)) : (F.map (homOfLE (n.le_add_right 1)).op).hom.app (op (X (n + 1))) (x (n + 1)) = (F.obj (op n)).obj.map (map n).op (x n)
-/
private structure struct (F : Natᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)) where
  X (n : Nat) : C
  x (n : Nat) : (F.obj ⟨n⟩).obj.obj ⟨X n⟩
  map (n : Nat) : X (n + 1) ⟶ X n
  effectiveEpi (n : Nat) : EffectiveEpi (map n)
  w (n : Nat) : (F.map (homOfLE (n.le_add_right 1)).op).hom.app (op (X (n + 1))) (x (n + 1)) =
      (F.obj (op n)).obj.map (map n).op (x n)

include hF in
/--
lemma `exists_effectiveEpi` / 引理 `exists_effectiveEpi`

English:
lemma exists_effectiveEpi
  given: (n : Nat) (X : C) (y : (F.obj ⟨n⟩).obj.obj ⟨X⟩)
  proof: by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff] at this
  exact this X y

中文:
引理 exists_effectiveEpi
  条件: (n : 自然数) (X : C) (y : (F.obj ⟨n⟩).obj.obj ⟨X⟩)
  证明: by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff] at this
  exact this X y
-/
private lemma exists_effectiveEpi (n : Nat) (X : C) (y : (F.obj ⟨n⟩).obj.obj ⟨X⟩) :
    exists (X' : C) (φ : X' ⟶ X) (_ : EffectiveEpi φ) (x : (F.obj ⟨n + 1⟩).obj.obj ⟨X'⟩),
      ((F.map (homOfLE (n.le_add_right 1)).op).hom.app ⟨X'⟩) x = ((F.obj ⟨n⟩).obj.map φ.op) y := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff] at this
  exact this X y

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def preimage (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)

中文:
定义 noncomputable
  签名: def preimage (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)
-/
private noncomputable def preimage (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩) :
    (n : Nat) -> ((Y : C) × (F.obj ⟨n⟩).obj.obj ⟨Y⟩)
  | 0 => ⟨X, y⟩
  | (n + 1) => ⟨(exists_effectiveEpi hF n (preimage X y n).1 (preimage X y n).2).choose,
      (exists_effectiveEpi hF n
        (preimage X y n).1 (preimage X y n).2).choose_spec.choose_spec.choose_spec.choose⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def preimageStruct (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)
  body: (preimage hF X y n).1
  x n := (preimage hF X y n).2
  map n := (exists_effectiveEpi hF n _ _).choose_spec.choose
  effectiveEpi n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose
  w n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose_spec.choose_spec

中文:
定义 noncomputable
  签名: def preimageStruct (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)
  定义体: (preimage hF X y n).1
  x n := (preimage hF X y n).2
  map n := (exists_effectiveEpi hF n _ _).choose_spec.choose
  effectiveEpi n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose
  w n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose_spec.choose_spec
-/
private noncomputable def preimageStruct (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩) : struct F where
  X n := (preimage hF X y n).1
  x n := (preimage hF X y n).2
  map n := (exists_effectiveEpi hF n _ _).choose_spec.choose
  effectiveEpi n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose
  w n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose_spec.choose_spec

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)
  body: Functor.ofOpSequence (preimageStruct hF X y).map

中文:
定义 noncomputable
  签名: def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)
  定义体: Functor.ofOpSequence (preimageStruct hF X y).map
-/
private noncomputable def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩) : Natᵒᵖ ⥤ C :=
  Functor.ofOpSequence (preimageStruct hF X y).map

variable [HasLimitsOfShape Natᵒᵖ C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def cone (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)
  body: ((coherentTopology C).yoneda).obj (limit (preimageDiagram hF X y))
  π := NatTrans.ofOpSequence
    (fun n => (coherentTopology C).yoneda.map
      (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm ((preimageStruct hF X y).x n)) (by
    intro n
    simp only [Functor.const_obj_obj, homOfLE_l

中文:
定义 noncomputable
  签名: def cone (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩)
  定义体: ((coherentTopology C).yoneda).obj (limit (preimageDiagram hF X y))
  π := NatTrans.ofOpSequence
    (fun n => (coherentTopology C).yoneda.map
      (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm ((preimageStruct hF X y).x n)) (by
    intro n
    simp only [Functor.const_obj_obj, homOfLE_l
-/
private noncomputable def cone (X : C) (y : (F.obj ⟨0⟩).obj.obj ⟨X⟩) : Cone F where
  pt := ((coherentTopology C).yoneda).obj (limit (preimageDiagram hF X y))
  π := NatTrans.ofOpSequence
    (fun n => (coherentTopology C).yoneda.map
      (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm ((preimageStruct hF X y).x n)) (by
    intro n
    simp only [Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, Category.id_comp,
      Category.assoc, ← limit.w (preimageDiagram hF X y) (homOfLE (n.le_add_right 1)).op,
      homOfLE_leOfHom, Functor.map_comp]
    simp [GrothendieckTopology.yonedaEquiv_symm_naturality_left,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right,
      preimageDiagram, (preimageStruct hF X y).w n])

variable (h : forall (G : Natᵒᵖ ⥤ C),
  (forall n, EffectiveEpi (G.map (homOfLE (Nat.le_succ n)).op)) -> EffectiveEpi (limit.π G ⟨0⟩))

set_option backward.isDefEq.respectTransparency false in
include hF h hc in
/--
lemma `isLocallySurjective_π_app_zero_of_isLocallySurjective_map` / 引理 `isLocallySurjective_π_app_zero_of_isLocallySurjective_map`

English:
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map
  proof: by
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  intro X y
  have hh : EffectiveEpi (limit.π (preimageDiagram hF X y) ⟨0⟩) :=
    h _ fun n => by simpa [preimageDiagram] using (preimageStruct hF X y).effectiveEpi n
  refine ⟨limit (preimageDiagram hF

中文:
引理 isLocallySurjective_π_app_zero_of_isLocallySurjective_map
  证明: by
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  intro X y
  have hh : EffectiveEpi (limit.π (preimageDiagram hF X y) ⟨0⟩) :=
    h _ fun n => by simpa [preimageDiagram] using (preimageStruct hF X y).effectiveEpi n
  refine ⟨limit (preimageDiagram hF

Depends on / 依赖: EffectiveEpi, coherentTopology, coherentTopology.isLocallySurjective_iff, effectiveEpi, hc.lift, hom.app, isLocallySurjective_iff, preimageDiagram, preimageStruct, regularTopology, regularTopology.isLocallySurjective_iff, yonedaEquiv, yonedaEquiv_comp
-/
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map :
    Sheaf.IsLocallySurjective (c.π.app ⟨0⟩) := by
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  intro X y
  have hh : EffectiveEpi (limit.π (preimageDiagram hF X y) ⟨0⟩) :=
    h _ fun n => by simpa [preimageDiagram] using (preimageStruct hF X y).effectiveEpi n
  refine ⟨limit (preimageDiagram hF X y), limit.π (preimageDiagram hF X y) ⟨0⟩, hh,
    (coherentTopology C).yonedaEquiv (hc.lift (cone hF X y )),
    (?_ : (c.π.app (op 0)).hom.app _ _ = _)⟩
  simp only [← (coherentTopology C).yonedaEquiv_comp, cone,
    IsLimit.fac, NatTrans.ofOpSequence_app, (coherentTopology C).yonedaEquiv_comp,
    (coherentTopology C).yonedaEquiv_yoneda_map]
  rfl

include h in
/--
lemma `epi_π_app_zero_of_epi` / 引理 `epi_π_app_zero_of_epi`

English:
lemma epi_π_app_zero_of_epi
  statement: [HasSheafify (coherentTopology C) (Type v)]
  proof: by
  simp_rw [← Sheaf.isLocallySurjective_iff_epi'] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF h

中文:
引理 epi_π_app_zero_of_epi
  结论: [HasSheafify (coherentTopology C) (类型v)]
  证明: by
  simp_rw [← Sheaf.isLocallySurjective_iff_epi'] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF h

Depends on / 依赖: Sheaf.isLocallySurjective_iff_epi, isLocallySurjective_iff_epi, simp_rw
-/
lemma epi_π_app_zero_of_epi [HasSheafify (coherentTopology C) (Type v)]
    [Balanced (Sheaf (coherentTopology C) (Type v))]
    [(coherentTopology C).WEqualsLocallyBijective (Type v)]
    {F : Natᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)}
    {c : Cone F} (hc : IsLimit c)
    (hF : forall n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) : Epi (c.π.app ⟨0⟩) := by
  simp_rw [← Sheaf.isLocallySurjective_iff_epi'] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF h

end CategoryTheory.coherentTopology
