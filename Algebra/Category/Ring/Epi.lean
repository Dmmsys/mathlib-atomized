/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Epimorphisms in `CommRingCat`

## Main results
- `RingHom.surjective_iff_epi_and_finite`: surjective <=> epi + finite
-/

public section

open CategoryTheory TensorProduct

universe u

/--
lemma `CommRingCat.epi_iff_epi` / 引理 `CommRingCat.epi_iff_epi`

English:
lemma CommRingCat.epi_iff_epi
  given: {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  proof: by
  simp_rw [Algebra.isEpi_iff_forall_one_tmul_eq, eq_comm]
  constructor
  · intro H
    have := H.1 (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom <| (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom)
      (by ext r; change algebraMap R S 

中文:
引理 交换环范畴.epi_iff_epi
  条件: {R S : 类型u} [交换环 R] [交换环 S] [代数 R S]
  证明: by
  simp_rw [Algebra.isEpi_iff_forall_one_tmul_eq, eq_comm]
  constructor
  · intro H
    have := H.1 (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom <| (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom)
      (by ext r; change algebraMap R S 

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.includeRight, Algebra.algebraMap_eq_smul_one, Algebra.isEpi_iff_forall_one_tmul_eq, CommRingCat, CommRingCat.ofHom, Hom.hom, RingHom, RingHom.congr_fun, TensorProduct, algebraM, algebraMap, algebraMap_eq_smul_one, congr_fun, eq_comm, includeLeftRingHom, includeRight, isEpi_iff_forall_one_tmul_eq, simp_rw
-/
lemma CommRingCat.epi_iff_epi {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Epi (CommRingCat.ofHom (algebraMap R S)) ↔ Algebra.IsEpi R S := by
  simp_rw [Algebra.isEpi_iff_forall_one_tmul_eq, eq_comm]
  constructor
  · intro H
    have := H.1 (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom <| (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom)
      (by ext r; change algebraMap R S r otimesₜ 1 = 1 otimesₜ algebraMap R S r;
          simp only [Algebra.algebraMap_eq_smul_one, smul_tmul])
    exact RingHom.congr_fun (congrArg Hom.hom this)
  · refine fun H => ⟨fun {T} f g e => ?_⟩
    let : Algebra R T := (ofHom (algebraMap R S) ≫ g).hom.toAlgebra
    let f' : S ->ₐ[R] T := ⟨f.hom, RingHom.congr_fun (congrArg Hom.hom e)⟩
    let g' : S ->ₐ[R] T := ⟨g.hom, fun _ => rfl⟩
    ext s
    simpa using! congr(Algebra.TensorProduct.lift f' g' (fun _ _ => .all _ _) $(H s))

@[deprecated (since := "2026-01-13")]
alias CommRingCat.epi_iff_tmul_eq_tmul := CommRingCat.epi_iff_epi

/--
lemma `RingHom.surjective_of_epi_of_finite` / 引理 `RingHom.surjective_of_epi_of_finite`

English:
lemma RingHom.surjective_of_epi_of_finite
  statement: {R S : CommRingCat} (f : R ⟶ S) [Epi f]
  proof: by
  algebraize [f.hom]
have : Algebra.IsEpi R S := CommRingCat.epi_iff_epi.mp inferInstanceAs (Epi f)
  rwa [Algebra.isEpi_iff_surjective_algebraMap_of_finite] at this

中文:
引理 环态射.surjective_of_epi_of_finite
  结论: {R S : 交换环范畴} (f : R ⟶ S) [满态射 f]
  证明: by
  algebraize [f.hom]
have : Algebra.IsEpi R S := CommRingCat.epi_iff_epi.mp inferInstanceAs (Epi f)
  rwa [Algebra.isEpi_iff_surjective_algebraMap_of_finite] at this

Depends on / 依赖: Algebra, Algebra.IsEpi, Algebra.isEpi_iff_surjective_algebraMap_of_finite, CommRingCat, CommRingCat.epi_iff_epi.mp, algebraize, epi_iff_epi, f.hom, isEpi_iff_surjective_algebraMap_of_finite
-/
lemma RingHom.surjective_of_epi_of_finite {R S : CommRingCat} (f : R ⟶ S) [Epi f]
    (h₂ : RingHom.Finite f.hom) : Function.Surjective f := by
  algebraize [f.hom]
have : Algebra.IsEpi R S := CommRingCat.epi_iff_epi.mp inferInstanceAs (Epi f)
  rwa [Algebra.isEpi_iff_surjective_algebraMap_of_finite] at this

/--
lemma `RingHom.surjective_iff_epi_and_finite` / 引理 `RingHom.surjective_iff_epi_and_finite`

English:
lemma RingHom.surjective_iff_epi_and_finite
  given: {R S : CommRingCat} {f : R ⟶ S}
  proof: ⟨ConcreteCategory.epi_of_surjective f h, .of_surjective f.hom h⟩
  mpr := fun ⟨_, h⟩ => surjective_of_epi_of_finite f h

中文:
引理 环态射.surjective_iff_epi_and_finite
  条件: {R S : 交换环范畴} {f : R ⟶ S}
  证明: ⟨ConcreteCategory.epi_of_surjective f h, .of_surjective f.hom h⟩
  mpr := fun ⟨_, h⟩ => surjective_of_epi_of_finite f h

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, IsFinite, epi_of_surjective, f.hom, ofIsIso, of_surjective, presentation
-/
lemma RingHom.surjective_iff_epi_and_finite {R S : CommRingCat} {f : R ⟶ S} :
    Function.Surjective f ↔ Epi f ∧ RingHom.Finite f.hom where
  mp h := ⟨ConcreteCategory.epi_of_surjective f h, .of_surjective f.hom h⟩
  mpr := fun ⟨_, h⟩ => surjective_of_epi_of_finite f h
