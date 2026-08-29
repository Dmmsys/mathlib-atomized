/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway

/-!
# Basis of cotangent space can be realized as a presentation

Let `S` be a finitely presented `R`-algebra and suppose `P : R[X] → S` generates `S` with
kernel `I`.

In this file we show `Algebra.Generators.exists_presentation_of_free`: If `I/I²` is free, there
exists an `R`-presentation `P'` of `S` extending `P` with kernel `I'`, such that `I'/I'²` is
free on the images of the relations of `P'`.

## References

- https://stacks.math.columbia.edu/tag/07CF
-/

open scoped Pointwise
open MvPolynomial TensorProduct

namespace Algebra.Generators

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ : Type*}

noncomputable section

namespace PresentationOfFreeCotangent

variable {ι : Type*} (P : Generators R S ι) {σ : Type*}
  (b : Module.Basis σ S P.toExtension.Cotangent)

/--
Definition of `Aux` / `Aux` 的定义

English:
structure Aux
  parameters: where
  axioms and operations (5):
    - f : P.toExtension.Cotangent -> P.toExtension.ker
    - hf : forall (b : P.toExtension.Cotangent), Extension.Cotangent.mk (f b) = b
    - g : P.Ring
    - hgmem : g - 1 in P.ker
    - hg : g • P.ker <= Ideal.span (Set.range <| Subtype.val ∘ f ∘ b)

中文:
结构 Aux
  参数: where
  公理与运算 (5 个):
    - f : P.toExtension.Cotangent -> P.toExtension.ker
    - hf : 对任意 (b : P.toExtension.Cotangent), Extension.Cotangent.mk (f b) = b
    - g : P.Ring
    - hgmem : g - 1 in P.ker
    - hg : g • P.ker <= Ideal.span (Set.range <| Subtype.val ∘ f ∘ b)
-/
structure Aux where
  /-- A section of the projection `I → I/I²`. -/
  f : P.toExtension.Cotangent -> P.toExtension.ker
  hf : forall (b : P.toExtension.Cotangent), Extension.Cotangent.mk (f b) = b
  /-- An element `g` that becomes invertible in `S = R[X₁, ..., Xₙ] / I`. -/
  g : P.Ring
  hgmem : g - 1 in P.ker
  hg : g • P.ker <= Ideal.span (Set.range <| Subtype.val ∘ f ∘ b)

namespace Aux

variable {P} {b}
variable (D : Aux P b)

/--
Definition of `T` / `T` 的定义

English:
abbreviation T
  body: MvPolynomial ι R ⧸ (Ideal.span <| Set.range <| Subtype.val ∘ D.f ∘ b)

中文:
缩写 T
  定义体: MvPolynomial ι R ⧸ (Ideal.span <| Set.range <| Subtype.val ∘ D.f ∘ b)

Depends on / 依赖: Ideal.span, MvPolynomial, Set.range, Subtype, Subtype.val
-/
abbrev T :=
  MvPolynomial ι R ⧸ (Ideal.span <| Set.range <| Subtype.val ∘ D.f ∘ b)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : D.T ->ₐ[R] S
  body: Ideal.Quotient.liftₐ _ (aeval P.val) by
  simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
  intro i
  simpa only [Generators.toExtension_Ring, Generators.toExtension_commRing, Function.comp_apply,
    SetLike.mem_coe, RingHom.mem_ker, ← P.algebraMap_apply] using (D

中文:
定义 hom
  签名: : D.T ->ₐ[R] S
  定义体: Ideal.Quotient.liftₐ _ (aeval P.val) by
  simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
  intro i
  simpa only [Generators.toExtension_Ring, Generators.toExtension_commRing, Function.comp_apply,
    SetLike.mem_coe, RingHom.mem_ker, ← P.algebraMap_apply] using (D

Depends on / 依赖: Function, Function.comp_apply, Generators, Generators.toExtension_Ring, Generators.toExtension_commRing, Ideal.Quotient.lift, Ideal.span_le, P.algebraMap_apply, P.val, Quotient, RingHom, RingHom.mem_ker, Set.range_subset_iff, SetLike, SetLike.le_def, SetLike.mem_coe, algebraMap_apply, comp_apply, le_def, mem_coe
-/
def hom : D.T ->ₐ[R] S := Ideal.Quotient.liftₐ _ (aeval P.val) by
  simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
  intro i
  simpa only [Generators.toExtension_Ring, Generators.toExtension_commRing, Function.comp_apply,
    SetLike.mem_coe, RingHom.mem_ker, ← P.algebraMap_apply] using (D.f _).property

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra D.T S
  body: D.hom.toAlgebra

中文:
实例 :
  签名: Algebra D.T S
  定义体: D.hom.toAlgebra

Depends on / 依赖: D.hom.toAlgebra, toAlgebra
-/
instance : Algebra D.T S := D.hom.toAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: S] : Nontrivial D.T
  body: RingHom.domain_nontrivial (algebraMap D.T S)

中文:
实例 [Nontrivial
  签名: S] : Nontrivial D.T
  定义体: RingHom.domain_nontrivial (algebraMap D.T S)

Depends on / 依赖: RingHom, RingHom.domain_nontrivial, algebraMap, domain_nontrivial, fields, include, instSomething
-/
instance [Nontrivial S] : Nontrivial D.T := RingHom.domain_nontrivial (algebraMap D.T S)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower P.Ring D.T S
  body: by
  refine ⟨fun x y z => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := P.algebraMap_surjective z
  simp only [Algebra.smul_def, map_mul, Generators.algebraMap_apply, ← mul_assoc]
  rfl

中文:
实例 :
  签名: IsScalarTower P.Ring D.T S
  定义体: by
  refine ⟨fun x y z => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := P.algebraMap_surjective z
  simp only [Algebra.smul_def, map_mul, Generators.algebraMap_apply, ← mul_assoc]
  rfl

Depends on / 依赖: Algebra, Algebra.smul_def, Generators, Generators.algebraMap_apply, Ideal.Quotient.mk_surjective, P.algebraMap_surjective, Quotient, algebraMap_apply, algebraMap_surjective, map_mul, mk_surjective, mul_assoc, smul_def
-/
instance : IsScalarTower P.Ring D.T S := by
  refine ⟨fun x y z => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := P.algebraMap_surjective z
  simp only [Algebra.smul_def, map_mul, Generators.algebraMap_apply, ← mul_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `gbar` / `gbar` 的定义

English:
abbreviation gbar
  signature: : D.T
  body: D.g

中文:
缩写 gbar
  签名: : D.T
  定义体: D.g
-/
abbrev gbar : D.T := D.g

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization.Away D.gbar S
  body: by
  refine .of_surjective_of_isScalarTower (n := 1) ?_ ?_ _ ?_ (by simpa using! D.hg)
  · refine .of_comp (g := algebraMap P.Ring D.T) ?_
    convert! P.algebraMap_surjective
    ext x
    exact (IsScalarTower.algebraMap_apply _ D.T S x).symm
  · simp [T, Ideal.Quotient.mk_surjective]
  · suffices 

中文:
实例 :
  签名: IsLocalization.Away D.gbar S
  定义体: by
  refine .of_surjective_of_isScalarTower (n := 1) ?_ ?_ _ ?_ (by simpa using! D.hg)
  · refine .of_comp (g := algebraMap P.Ring D.T) ?_
    convert! P.algebraMap_surjective
    ext x
    exact (IsScalarTower.algebraMap_apply _ D.T S x).symm
  · simp [T, Ideal.Quotient.mk_surjective]
  · suffices 

Depends on / 依赖: D.hg, D.hgmem, Ideal.Quotient.mk_surjective, IsScalarTower, IsScalarTower.algebraMap_apply, P.Ring, P.algebraMap_surjective, Quotient, RingHom, RingHom.mem_ker, algebraMap, algebraMap_apply, algebraMap_surjective, convert, map_one, map_sub, mem_ker, mk_surjective, of_comp, of_surjective_of_isScalarTower
-/
instance : IsLocalization.Away D.gbar S := by
  refine .of_surjective_of_isScalarTower (n := 1) ?_ ?_ _ ?_ (by simpa using! D.hg)
  · refine .of_comp (g := algebraMap P.Ring D.T) ?_
    convert! P.algebraMap_surjective
    ext x
    exact (IsScalarTower.algebraMap_apply _ D.T S x).symm
  · simp [T, Ideal.Quotient.mk_surjective]
  · suffices h : (algebraMap P.Ring S) D.g = 1 by simp [h]
    rw [← map_one (algebraMap P.Ring S)]; rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom.mem_ker]
    exact D.hgmem

open scoped Classical in
/--
Definition of `presLeft` / `presLeft` 的定义

English:
definition presLeft
  signature: : Presentation R D.T ι σ
  body: .naive (fun x => if x = 0 then 0 else if x = -1 then -1 else
      Function.surjInv Ideal.Quotient.mk_surjective x) fun x => by
    split_ifs
    · next h => subst h; rfl
    · next h => subst h; rfl
    · simp [Function.surjInv_eq]

中文:
定义 presLeft
  签名: : Presentation R D.T ι σ
  定义体: .naive (fun x => if x = 0 then 0 else if x = -1 then -1 else
      Function.surjInv Ideal.Quotient.mk_surjective x) fun x => by
    split_ifs
    · next h => subst h; rfl
    · next h => subst h; rfl
    · simp [Function.surjInv_eq]

Depends on / 依赖: Function, Function.surjInv, Function.surjInv_eq, Ideal.Quotient.mk_surjective, Quotient, mk_surjective, split_ifs, surjInv, surjInv_eq
-/
def presLeft : Presentation R D.T ι σ :=
  .naive (fun x => if x = 0 then 0 else if x = -1 then -1 else
      Function.surjInv Ideal.Quotient.mk_surjective x) fun x => by
    split_ifs
    · next h => subst h; rfl
    · next h => subst h; rfl
    · simp [Function.surjInv_eq]

/--
Definition of `kerGen` / `kerGen` 的定义

English:
definition kerGen
  signature: (i : σ)
  body: ⟨(D.f (b i)).val, Presentation.mem_ker_naive _ _ i⟩

中文:
定义 kerGen
  签名: (i : σ)
  定义体: ⟨(D.f (b i)).val, Presentation.mem_ker_naive _ _ i⟩

Depends on / 依赖: Presentation, Presentation.mem_ker_naive, mem_ker_naive
-/
def kerGen (i : σ) : D.presLeft.toExtension.ker :=
  ⟨(D.f (b i)).val, Presentation.mem_ker_naive _ _ i⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fhom` / `fhom` 的定义

English:
definition fhom
  signature: : D.presLeft.Hom P where
  body: X i
  aeval_val i := by simp [RingHom.algebraMap_toAlgebra, presLeft, hom, T]

@[simp]

中文:
定义 fhom
  签名: : D.presLeft.Hom P where
  定义体: X i
  aeval_val i := by simp [RingHom.algebraMap_toAlgebra, presLeft, hom, T]

@[simp]
-/
def fhom : D.presLeft.Hom P where
  val i := X i
  aeval_val i := by simp [RingHom.algebraMap_toAlgebra, presLeft, hom, T]

@[simp]
/--
lemma `toAlgHom_fhom` / 引理 `toAlgHom_fhom`

English:
lemma toAlgHom_fhom
  statement: D.fhom.toAlgHom = AlgHom.id R P.Ring
  proof: by
  ext : 1
  simp [fhom]

中文:
引理 toAlgHom_fhom
  结论: D.fhom.toAlgHom = AlgHom.id R P.Ring
  证明: by
  ext : 1
  simp [fhom]
-/
lemma toAlgHom_fhom : D.fhom.toAlgHom = AlgHom.id R P.Ring := by
  ext : 1
  simp [fhom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ker_presLeft_le` / 引理 `ker_presLeft_le`

English:
lemma ker_presLeft_le
  statement: D.presLeft.ker <= P.ker
  proof: by
  intro x hx
  simpa only [toExtension_commRing, toExtension_Ring, RingHom.mem_ker,
    toExtension_algebra₂, algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    map_zero] using! (algebraMap D.T S).congr_arg hx

中文:
引理 ker_presLeft_le
  结论: D.presLeft.ker <= P.ker
  证明: by
  intro x hx
  simpa only [toExtension_commRing, toExtension_Ring, RingHom.mem_ker,
    toExtension_algebra₂, algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    map_zero] using! (algebraMap D.T S).congr_arg hx

Depends on / 依赖: Ideal.Quotient.algebraMap_eq, Quotient, RingHom, RingHom.mem_ker, algebraMap, algebraMap_apply, algebraMap_eq, congr_arg, map_zero, mem_ker, toExtension_Ring, toExtension_commRing
-/
lemma ker_presLeft_le : D.presLeft.ker <= P.ker := by
  intro x hx
  simpa only [toExtension_commRing, toExtension_Ring, RingHom.mem_ker,
    toExtension_algebra₂, algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    map_zero] using! (algebraMap D.T S).congr_arg hx

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `tensorCotangentHom` / `tensorCotangentHom` 的定义

English:
definition tensorCotangentHom
  signature: : S otimes[D.T] D.presLeft.toExtension.Cotangent ->ₗ[S] P.toExtension.Cotangent
  body: LinearMap.liftBaseChange _ (Extension.Cotangent.map D.fhom.toExtensionHom)

中文:
定义 tensorCotangentHom
  签名: : S otimes[D.T] D.presLeft.toExtension.Cotangent ->ₗ[S] P.toExtension.Cotangent
  定义体: LinearMap.liftBaseChange _ (Extension.Cotangent.map D.fhom.toExtensionHom)

Depends on / 依赖: Cotangent, D.fhom.toExtensionHom, Extension, Extension.Cotangent.map, LinearMap, LinearMap.liftBaseChange, liftBaseChange, toExtensionHom
-/
def tensorCotangentHom : S otimes[D.T] D.presLeft.toExtension.Cotangent ->ₗ[S] P.toExtension.Cotangent :=
  LinearMap.liftBaseChange _ (Extension.Cotangent.map D.fhom.toExtensionHom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `tensorCotangentHom_tmul` / 引理 `tensorCotangentHom_tmul`

English:
lemma tensorCotangentHom_tmul
  given: (x : D.presLeft.toExtension.ker)
  proof: by
  simp_rw +instances [tensorCotangentHom, LinearMap.liftBaseChange_tmul, one_smul, presLeft,
    Extension.Cotangent.map_mk, Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom,
    toAlgHom_fhom, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, toExtension_Ring,
    toExtension_commRing, toE

中文:
引理 tensorCotangentHom_tmul
  条件: (x : D.presLeft.toExtension.ker)
  证明: by
  simp_rw +instances [tensorCotangentHom, LinearMap.liftBaseChange_tmul, one_smul, presLeft,
    Extension.Cotangent.map_mk, Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom,
    toAlgHom_fhom, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, toExtension_Ring,
    toExtension_commRing, toE

Depends on / 依赖: AlgHom, AlgHom.id_toRingHom, AlgHom.toRingHom_eq_coe, Cotangent, Extension, Extension.Cotangent.map_mk, Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom, LinearMap, LinearMap.liftBaseChange_tmul, Presentation, Presentation.naive_toGenerators, RingHom, RingHom.id_apply, id_apply, id_toRingHom, instances, liftBaseChange_tmul, map_mk, naive_toGenerators
-/
lemma tensorCotangentHom_tmul (x : D.presLeft.toExtension.ker) :
    D.tensorCotangentHom (1 otimesₜ[D.T] Extension.Cotangent.mk x) =
      .mk ⟨x.val, D.ker_presLeft_le x.2⟩ := by
  simp_rw +instances [tensorCotangentHom, LinearMap.liftBaseChange_tmul, one_smul, presLeft,
    Extension.Cotangent.map_mk, Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom,
    toAlgHom_fhom, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, toExtension_Ring,
    toExtension_commRing, toExtension_algebra₂, Presentation.naive_toGenerators, RingHom.id_apply]

/--
Definition of `tensorCotangentInv` / `tensorCotangentInv` 的定义

English:
definition tensorCotangentInv
  signature: : P.toExtension.Cotangent ->ₗ[S] S otimes[D.T] D.presLeft.toExtension.Cotangent
  body: b.constr S fun i : σ => 1 otimesₜ Extension.Cotangent.mk (D.kerGen i)

@[simp]

中文:
定义 tensorCotangentInv
  签名: : P.toExtension.Cotangent ->ₗ[S] S otimes[D.T] D.presLeft.toExtension.Cotangent
  定义体: b.constr S fun i : σ => 1 otimesₜ Extension.Cotangent.mk (D.kerGen i)

@[simp]

Depends on / 依赖: Cotangent, D.kerGen, Extension, Extension.Cotangent.mk, b.constr, constr, kerGen
-/
def tensorCotangentInv : P.toExtension.Cotangent ->ₗ[S] S otimes[D.T] D.presLeft.toExtension.Cotangent :=
  b.constr S fun i : σ => 1 otimesₜ Extension.Cotangent.mk (D.kerGen i)

@[simp]
/--
lemma `tensorCotangentInv_apply` / 引理 `tensorCotangentInv_apply`

English:
lemma tensorCotangentInv_apply
  given: (i : σ)
  proof: Module.Basis.constr_basis _ _ _ _

中文:
引理 tensorCotangentInv_apply
  条件: (i : σ)
  证明: Module.Basis.constr_basis _ _ _ _

Depends on / 依赖: Module, Module.Basis.constr_basis, constr_basis
-/
lemma tensorCotangentInv_apply (i : σ) :
    D.tensorCotangentInv (b i) = 1 otimesₜ Extension.Cotangent.mk (D.kerGen i) :=
  Module.Basis.constr_basis _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `span_range_mk_kerGen` / 引理 `span_range_mk_kerGen`

English:
lemma span_range_mk_kerGen
  statement: Submodule.span D.T
  proof: by
  refine Extension.Cotangent.span_eq_top_of_span_eq_ker _ ?_
  dsimp only [presLeft, Presentation.naive_toGenerators]
  exact (Generators.ker_naive _ _).symm

中文:
引理 span_range_mk_kerGen
  结论: Submodule.span D.T
  证明: by
  refine Extension.Cotangent.span_eq_top_of_span_eq_ker _ ?_
  dsimp only [presLeft, Presentation.naive_toGenerators]
  exact (Generators.ker_naive _ _).symm

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.span_eq_top_of_span_eq_ker, Generators, Generators.ker_naive, Presentation, Presentation.naive_toGenerators, ker_naive, naive_toGenerators, presLeft, span_eq_top_of_span_eq_ker
-/
lemma span_range_mk_kerGen : Submodule.span D.T
    (Set.range fun i => Extension.Cotangent.mk (D.kerGen i)) = ⊤ := by
  refine Extension.Cotangent.span_eq_top_of_span_eq_ker _ ?_
  dsimp only [presLeft, Presentation.naive_toGenerators]
  exact (Generators.ker_naive _ _).symm

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorCotangentEquiv` / `tensorCotangentEquiv` 的定义

English:
definition tensorCotangentEquiv
  signature: :
  body: by
  refine LinearEquiv.ofLinearMap D.tensorCotangentHom D.tensorCotangentInv ?_ ?_
  · refine b.ext fun i => ?_
    simpa only [LinearMap.coe_comp, Function.comp_apply, tensorCotangentInv_apply,
      tensorCotangentHom_tmul] using! D.hf (b i)
  · ext : 2
    refine LinearMap.ext_on_range D.span_ra

中文:
定义 tensorCotangentEquiv
  签名: :
  定义体: by
  refine LinearEquiv.ofLinearMap D.tensorCotangentHom D.tensorCotangentInv ?_ ?_
  · refine b.ext fun i => ?_
    simpa only [LinearMap.coe_comp, Function.comp_apply, tensorCotangentInv_apply,
      tensorCotangentHom_tmul] using! D.hf (b i)
  · ext : 2
    refine LinearMap.ext_on_range D.span_ra

Depends on / 依赖: D.hf, D.span_range_mk_kerGen, D.tensorCotangentHom, D.tensorCotangentInv, Function, Function.comp_apply, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.coe_comp, LinearMap.ext_on_range, b.ext, coe_comp, comp_apply, ext_on_range, kerGen, ofLinearMap, span_range_mk_kerGen, tensorCotangentHom, tensorCotangentHom_tmul
-/
def tensorCotangentEquiv :
    S otimes[D.T] D.presLeft.toExtension.Cotangent ≃ₗ[S] P.toExtension.Cotangent := by
  refine LinearEquiv.ofLinearMap D.tensorCotangentHom D.tensorCotangentInv ?_ ?_
  · refine b.ext fun i => ?_
    simpa only [LinearMap.coe_comp, Function.comp_apply, tensorCotangentInv_apply,
      tensorCotangentHom_tmul] using! D.hf (b i)
  · ext : 2
    refine LinearMap.ext_on_range D.span_range_mk_kerGen fun i => ?_
    simp [-toExtension_commRing, -toExtension_Ring, -toExtension_algebra₂, tensorCotangentHom_tmul,
      kerGen, D.hf]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `tensorCotangentEquiv_symm_apply` / 引理 `tensorCotangentEquiv_symm_apply`

English:
lemma tensorCotangentEquiv_symm_apply
  given: (i : σ)
  proof: D.tensorCotangentInv_apply i

中文:
引理 tensorCotangentEquiv_symm_apply
  条件: (i : σ)
  证明: D.tensorCotangentInv_apply i

Depends on / 依赖: D.tensorCotangentInv_apply, tensorCotangentInv_apply
-/
lemma tensorCotangentEquiv_symm_apply (i : σ) :
    D.tensorCotangentEquiv.symm (b i) = 1 otimesₜ Extension.Cotangent.mk (D.kerGen i) :=
  D.tensorCotangentInv_apply i

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `presRight` / `presRight` 的定义

English:
definition presRight
  signature: : Presentation D.T S Unit Unit
  body: Presentation.localizationAway S D.gbar

中文:
定义 presRight
  签名: : Presentation D.T S Unit Unit
  定义体: Presentation.localizationAway S D.gbar

Depends on / 依赖: D.gbar, Presentation, Presentation.localizationAway, localizationAway
-/
def presRight : Presentation D.T S Unit Unit :=
  Presentation.localizationAway S D.gbar

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pres` / `pres` 的定义

English:
definition pres
  signature: : Presentation R S (Unit oplus ι) (Unit oplus σ)
  body: D.presRight.comp D.presLeft

中文:
定义 pres
  签名: : Presentation R S (Unit oplus ι) (Unit oplus σ)
  定义体: D.presRight.comp D.presLeft

Depends on / 依赖: D.presLeft, D.presRight.comp, presLeft, presRight
-/
def pres : Presentation R S (Unit oplus ι) (Unit oplus σ) :=
  D.presRight.comp D.presLeft

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_ofComp_mk` / 引理 `map_ofComp_mk`

English:
lemma map_ofComp_mk
  given: [Nontrivial S]
  proof: by
  simp_rw [Extension.Cotangent.map_mk, Generators.Hom.toExtensionHom_toAlgHom_apply]
  congr 2
  have : Nontrivial D.T := inferInstance
  dsimp only [T, Generators.toExtension_Ring, Generators.toExtension_commRing] at this
  rw [pres]; rw [presLeft]; rw [presRight]; rw [Presentation.relation_comp

中文:
引理 map_ofComp_mk
  条件: [Nontrivial S]
  证明: by
  simp_rw [Extension.Cotangent.map_mk, Generators.Hom.toExtensionHom_toAlgHom_apply]
  congr 2
  have : Nontrivial D.T := inferInstance
  dsimp only [T, Generators.toExtension_Ring, Generators.toExtension_commRing] at this
  rw [pres]; rw [presLeft]; rw [presRight]; rw [Presentation.relation_comp

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.map_mk, Generators, Generators.Hom.toExtensionHom_toAlgHom_apply, Generators.naive_, Generators.toAlgHom_ofComp_localizationAway, Generators.toExtension_Ring, Generators.toExtension_commRing, Nontrivial, Presentation, Presentation.naive, Presentation.relation_comp_localizationAway_inl, map_mk, presLeft, presRight, relation_comp_localizationAway_inl, simp_rw, toAlgHom_ofComp_localizationAway, toExtensionHom_toAlgHom_apply
-/
lemma map_ofComp_mk [Nontrivial S] :
    (Extension.Cotangent.map
      ((localizationAway S D.gbar).ofComp D.presLeft.toGenerators).toExtensionHom)
      (Extension.Cotangent.mk ⟨D.pres.relation (Sum.inl ()), D.pres.relation_mem_ker _⟩) =
      Generators.cMulXSubOneCotangent S D.gbar := by
  simp_rw [Extension.Cotangent.map_mk, Generators.Hom.toExtensionHom_toAlgHom_apply]
  congr 2
  have : Nontrivial D.T := inferInstance
  dsimp only [T, Generators.toExtension_Ring, Generators.toExtension_commRing] at this
  rw [pres]; rw [presLeft]; rw [presRight]; rw [Presentation.relation_comp_localizationAway_inl]
  · exact Generators.toAlgHom_ofComp_localizationAway _ _
  · rw [Presentation.naive, Generators.naive_σ];
    simp
  · rw [Presentation.naive, Generators.naive_σ]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cotangentEquivProd` / `cotangentEquivProd` 的定义

English:
definition cotangentEquivProd
  signature: [Nontrivial S]
  body: (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.map_ofComp_mk) ≪≫ₗ
    LinearEquiv.prodComm _ _ _

中文:
定义 cotangentEquivProd
  签名: [Nontrivial S]
  定义体: (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.map_ofComp_mk) ≪≫ₗ
    LinearEquiv.prodComm _ _ _

Depends on / 依赖: D.gbar, D.map_ofComp_mk, D.presLeft.cotangentCompLocalizationAwayEquiv, LinearEquiv, LinearEquiv.prodComm, cotangentCompLocalizationAwayEquiv, map_ofComp_mk, presLeft, prodComm
-/
def cotangentEquivProd [Nontrivial S] : D.pres.toExtension.Cotangent ≃ₗ[S]
    D.presRight.toExtension.Cotangent × S otimes[D.T] D.presLeft.toExtension.Cotangent :=
  (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.map_ofComp_mk) ≪≫ₗ
    LinearEquiv.prodComm _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cotangentEquivProd_symm_apply` / 引理 `cotangentEquivProd_symm_apply`

English:
lemma cotangentEquivProd_symm_apply
  statement: [Nontrivial S] (x : D.presRight.toExtension.Cotangent)
  proof: rfl

中文:
引理 cotangentEquivProd_symm_apply
  结论: [Nontrivial S] (x : D.presRight.toExtension.Cotangent)
  证明: rfl

Depends on / 依赖: D.gbar, D.map_ofComp_mk, map_ofComp_mk
-/
lemma cotangentEquivProd_symm_apply [Nontrivial S] (x : D.presRight.toExtension.Cotangent)
      (y : S otimes[D.T] D.presLeft.toExtension.Cotangent) :
    D.cotangentEquivProd.symm (x, y) =
      (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.map_ofComp_mk).symm (y, x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `basisLeft` / `basisLeft` 的定义

English:
definition basisLeft
  signature: : Module.Basis σ S (S otimes[D.T] D.presLeft.toExtension.Cotangent)
  body: b.map D.tensorCotangentEquiv.symm

中文:
定义 basisLeft
  签名: : Module.Basis σ S (S otimes[D.T] D.presLeft.toExtension.Cotangent)
  定义体: b.map D.tensorCotangentEquiv.symm

Depends on / 依赖: D.tensorCotangentEquiv.symm, b.map, tensorCotangentEquiv
-/
def basisLeft : Module.Basis σ S (S otimes[D.T] D.presLeft.toExtension.Cotangent) :=
  b.map D.tensorCotangentEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `basisRight` / `basisRight` 的定义

English:
definition basisRight
  signature: : Module.Basis Unit S D.presRight.toExtension.Cotangent
  body: Generators.basisCotangentAway S D.gbar

中文:
定义 basisRight
  签名: : Module.Basis Unit S D.presRight.toExtension.Cotangent
  定义体: Generators.basisCotangentAway S D.gbar

Depends on / 依赖: D.gbar, Generators, Generators.basisCotangentAway, basisCotangentAway
-/
def basisRight : Module.Basis Unit S D.presRight.toExtension.Cotangent :=
  Generators.basisCotangentAway S D.gbar

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: [Nontrivial S]
  body: (Module.Basis.prod D.basisRight D.basisLeft).map D.cotangentEquivProd.symm

中文:
定义 basis
  签名: [Nontrivial S]
  定义体: (Module.Basis.prod D.basisRight D.basisLeft).map D.cotangentEquivProd.symm

Depends on / 依赖: D.basisLeft, D.basisRight, D.cotangentEquivProd.symm, Module, Module.Basis.prod, basisLeft, basisRight, cotangentEquivProd
-/
def basis [Nontrivial S] : Module.Basis (Unit oplus σ) S D.pres.toExtension.Cotangent :=
  (Module.Basis.prod D.basisRight D.basisLeft).map D.cotangentEquivProd.symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `basis_inl` / 引理 `basis_inl`

English:
lemma basis_inl
  given: [Nontrivial S]
  proof: by
  simpa [basis] using! Generators.basisCotangentAway_apply _ _

中文:
引理 basis_inl
  条件: [Nontrivial S]
  证明: by
  simpa [basis] using! Generators.basisCotangentAway_apply _ _

Depends on / 依赖: Generators, Generators.basisCotangentAway_apply, basisCotangentAway_apply
-/
lemma basis_inl [Nontrivial S] :
    D.basis (.inl ()) =
      D.cotangentEquivProd.symm (Generators.cMulXSubOneCotangent S D.gbar, 0) := by
  simpa [basis] using! Generators.basisCotangentAway_apply _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `basis_inr` / 引理 `basis_inr`

English:
lemma basis_inr
  given: [Nontrivial S] (i : σ)
  proof: by
  simp [basis]

中文:
引理 basis_inr
  条件: [Nontrivial S] (i : σ)
  证明: by
  simp [basis]
-/
lemma basis_inr [Nontrivial S] (i : σ) :
    D.basis (.inr i) = D.cotangentEquivProd.symm (0, D.basisLeft i) := by
  simp [basis]

/--
lemma `pres_val_comp_inr` / 引理 `pres_val_comp_inr`

English:
lemma pres_val_comp_inr
  statement: D.pres.val ∘ Sum.inr = P.val
  proof: funext (aeval_X _)

中文:
引理 pres_val_comp_inr
  结论: D.pres.val ∘ Sum.inr = P.val
  证明: funext (aeval_X _)

Depends on / 依赖: aeval_X
-/
lemma pres_val_comp_inr : D.pres.val ∘ Sum.inr = P.val := funext (aeval_X _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `basis_apply` / 引理 `basis_apply`

English:
lemma basis_apply
  given: [Nontrivial S] (r : Unit oplus σ)
  proof: by
  obtain (r | r) := r
  · rw [basis_inl, cotangentEquivProd_symm_apply]
    exact cotangentCompLocalizationAwayEquiv_symm_inr _ _ _
  · rw [basis_inr, cotangentEquivProd_symm_apply, cotangentCompLocalizationAwayEquiv_symm_inl,
      basisLeft, Module.Basis.map_apply, tensorCotangentEquiv_symm_app

中文:
引理 basis_apply
  条件: [Nontrivial S] (r : Unit oplus σ)
  证明: by
  obtain (r | r) := r
  · rw [basis_inl, cotangentEquivProd_symm_apply]
    exact cotangentCompLocalizationAwayEquiv_symm_inr _ _ _
  · rw [basis_inr, cotangentEquivProd_symm_apply, cotangentCompLocalizationAwayEquiv_symm_inl,
      basisLeft, Module.Basis.map_apply, tensorCotangentEquiv_symm_app

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Cotangent, Extension, Extension.Cotangent.map_mk, Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom, LinearMap, LinearMap.liftBaseChange_tmul, Module, Module.Basis.map_apply, Presentation, Presentation.comp_r, basisLeft, basis_inl, basis_inr, comp_r, cotangentCompLocalizationAwayEquiv_symm_inl, cotangentCompLocalizationAwayEquiv_symm_inr, cotangentEquivProd_symm_apply
-/
lemma basis_apply [Nontrivial S] (r : Unit oplus σ) :
    D.basis r = Extension.Cotangent.mk ⟨D.pres.relation r, D.pres.relation_mem_ker r⟩ := by
  obtain (r | r) := r
  · rw [basis_inl, cotangentEquivProd_symm_apply]
    exact cotangentCompLocalizationAwayEquiv_symm_inr _ _ _
  · rw [basis_inr, cotangentEquivProd_symm_apply, cotangentCompLocalizationAwayEquiv_symm_inl,
      basisLeft, Module.Basis.map_apply, tensorCotangentEquiv_symm_apply,
      LinearMap.liftBaseChange_tmul, one_smul, Extension.Cotangent.map_mk]
    simp only [Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom, AlgHom.toRingHom_eq_coe]
    congr! 2 with x
    simp [pres, Presentation.comp_relation_inr, kerGen, presLeft, Generators.toComp_toAlgHom]
    rfl

end PresentationOfFreeCotangent.Aux

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open PresentationOfFreeCotangent in
/--
Version of `Algebra.Generators.exists_presentation_of_free_cotangent` taking a basis instead
of a `Module.Free` assumption.
Note that the basis `b₀` only serves as a way of saying
that `I/I²` is free of rank `σ`, which gives more definitional control over `σ`.
If this does not matter, use `Algebra.Generators.exists_presentation_of_free_cotangent` instead.
-/
@[stacks 07CF]
public lemma exists_presentation_of_basis_cotangent [Algebra.FinitePresentation R S]
    {α : Type*} (P : Generators R S α) [Finite α] {σ : Type*}
    (b₀ : Module.Basis σ S P.toExtension.Cotangent) :
    exists (P' : Presentation R S (Unit oplus α) (Unit oplus σ))
      (b : Module.Basis (Unit oplus σ) S P'.toExtension.Cotangent),
      P'.val ∘ Sum.inr = P.val ∧
      forall r, b r = Extension.Cotangent.mk ⟨P'.relation r, P'.relation_mem_ker r⟩ := by
  cases subsingleton_or_nontrivial S
  · let P' : Presentation R S (Unit oplus α) (Unit oplus σ) :=
      { toGenerators := .ofSurjective (fun i : Unit oplus α => 0) (Function.surjective_to_subsingleton _)
        relation _ := 1
        span_range_relation_eq_ker := by simpa using (RingHom.ker_eq_top_of_subsingleton _).symm }
    have : Subsingleton P'.toExtension.Cotangent := Module.subsingleton S _
    exact ⟨P', default, by subsingleton, by subsingleton⟩
  choose f hf using Extension.Cotangent.mk_surjective (P := P.toExtension)
  let v (i : σ) : P.ker := f (b₀ i)
  let J : Ideal P.Ring := Ideal.span (Set.range <| Subtype.val ∘ v)
  have hJfg : P.ker.FG := by
    rw [P.ker_eq_ker_aeval_val]
    apply FinitePresentation.ker_fG_of_surjective
    convert! P.algebraMap_surjective
    simp [P.algebraMap_eq]
  have hJ : J <= P.ker := by simp [J, Ideal.span_le, Set.range_subset_iff]
  suffices hJ : P.ker <= J ⊔ P.ker • P.ker by
    obtain ⟨g, hgmem, hg⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hJfg le_rfl hJ
    let D : Aux P b₀ := { f := f, hf := hf, g := g, hgmem := hgmem, hg := hg }
    exact ⟨D.pres, D.basis, D.pres_val_comp_inr, D.basis_apply⟩
  rw [← Submodule.comap_le_comap_iff_of_le_range (f := P.ker.subtype) (by simp)]; rw [Submodule.comap_subtype_self]; rw [Submodule.comap_sup_of_injective P.ker.subtype_injective (by simpa using hJ)
    (by simp [Ideal.mul_le_right]),
    Submodule.comap_smul'' P.ker.subtype_injective (by simp)]
  simp only [Submodule.comap_subtype_self, J]
  rw [← Submodule.coe_subtype]; rw [Ideal.span]; rw [Set.range_comp]; rw [← Submodule.map_span]; rw [Submodule.comap_map_eq_of_injective P.ker.subtype_injective]; rw [← Extension.Cotangent.ker_mk]
  dsimp
  simp only [← LinearMap.map_le_map_iff, Submodule.map_span, ← Set.range_comp,
    Function.comp_def, ← Submodule.restrictScalars_span P.Ring S P.algebraMap_surjective]
  refine le_trans le_top (top_le_iff.mpr ?_)
  rw [Submodule.restrictScalars_eq_top_iff]
  convert! b₀.span_eq
  exact hf _

open PresentationOfFreeCotangent in
/-- Let `S` be a finitely presented `R`-algebra and suppose `P : R[X] → S` generates `S` with
kernel `I`. If `I/I²` is free, there exists an `R`-presentation `P'` of `S` extending `P` with
kernel `I'`, such that `I'/I'²` is free on the images of the relations of `P'`.
See `Algebra.Generators.exists_presentation_of_basis_cotangent` for a version taking
a basis of `I/I²` instead. -/
@[stacks 07CF]
public lemma exists_presentation_of_free_cotangent [Algebra.FinitePresentation R S]
    {α : Type*} (P : Generators R S α) [Finite α]
    [Module.Free S P.toExtension.Cotangent] :
    exists (P' : Presentation R S (Unit oplus α) (Unit oplus Fin (Module.finrank S P.toExtension.Cotangent)))
      (b : Module.Basis (Unit oplus Fin (Module.finrank S P.toExtension.Cotangent))
        S P'.toExtension.Cotangent),
      P'.val ∘ Sum.inr = P.val ∧
      forall r, b r = Extension.Cotangent.mk ⟨P'.relation r, P'.relation_mem_ker r⟩ := by
  cases subsingleton_or_nontrivial S
  · let P' : Presentation R S (Unit oplus α) (Unit oplus Fin (Module.finrank S P.toExtension.Cotangent)) :=
      { toGenerators := .ofSurjective (fun i : Unit oplus α => 0) (Function.surjective_to_subsingleton _)
        relation _ := 1
        span_range_relation_eq_ker := by simpa using! (RingHom.ker_eq_top_of_subsingleton _).symm }
    have : Subsingleton P'.toExtension.Cotangent := Module.subsingleton S _
    exact ⟨P', default, by subsingleton, by subsingleton⟩
  have : Module.Finite S P.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite P.fg_ker_of_finitePresentation
exact exists_presentation_of_basis_cotangent _ Module.finBasis S P.toExtension.Cotangent

end Algebra.Generators
