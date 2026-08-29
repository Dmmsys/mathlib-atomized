/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Cofibrations and fibrations in the category of simplicial sets

We endow `SSet` with `CategoryWithCofibrations` and `CategoryWithFibrations`
instances. Cofibrations are monomorphisms, and fibrations are morphisms
having the right lifting property with respect to horn inclusions.

We have an instance `mono_of_cofibration` (but only a lemma `cofibration_of_mono`).
Then, when stating lemmas about cofibrations of simplicial sets, it is advisable
to use the assumption `[Mono f]` instead of `[Cofibration f]`.

-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty Simplicial

universe u

namespace SSet

namespace modelCategoryQuillen

/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: : MorphismProperty SSet.{u}
  body: .ofHoms (fun n => ∂Δ[n].ι)

中文:
定义 I
  签名: : Morphism命题erty SSet.{u}
  定义体: .ofHoms (fun n => ∂Δ[n].ι)

Depends on / 依赖: ofHoms
-/
def I : MorphismProperty SSet.{u} :=
  .ofHoms (fun n => ∂Δ[n].ι)

/--
lemma `boundary_ι_mem_I` / 引理 `boundary_ι_mem_I`

English:
lemma boundary_ι_mem_I
  given: (n : Nat)
  proof: by constructor

中文:
引理 boundary_ι_mem_I
  条件: (n : 自然数)
  证明: by constructor
-/
lemma boundary_ι_mem_I (n : Nat) :
    I (boundary.{u} n).ι := by constructor

/--
Definition of `J` / `J` 的定义

English:
definition J
  signature: : MorphismProperty SSet.{u}
  body: ⨆ n, .ofHoms (fun (i : Fin (n + 2)) => Λ[n + 1, i].ι)

中文:
定义 J
  签名: : Morphism命题erty SSet.{u}
  定义体: ⨆ n, .ofHoms (fun (i : Fin (n + 2)) => Λ[n + 1, i].ι)

Depends on / 依赖: ofHoms
-/
def J : MorphismProperty SSet.{u} :=
  ⨆ n, .ofHoms (fun (i : Fin (n + 2)) => Λ[n + 1, i].ι)

/--
lemma `horn_ι_mem_J` / 引理 `horn_ι_mem_J`

English:
lemma horn_ι_mem_J
  given: (n : Nat) [NeZero n] (i : Fin (n + 1))
  proof: by
  obtain _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · simp only [J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

中文:
引理 horn_ι_mem_J
  条件: (n : 自然数) [NeZero n] (i : Fin (n + 1))
  证明: by
  obtain _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · simp only [J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

Depends on / 依赖: NeZero, NeZero.ne, iSup_iff
-/
lemma horn_ι_mem_J (n : Nat) [NeZero n] (i : Fin (n + 1)) :
    J (horn.{u} n i).ι := by
  obtain _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · simp only [J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

/--
lemma `I_le_monomorphisms` / 引理 `I_le_monomorphisms`

English:
lemma I_le_monomorphisms
  statement: I.{u} <= monomorphisms _
  proof: by
  rintro _ _ _ ⟨n⟩
  exact monomorphisms.infer_property _

中文:
引理 I_le_monomorphisms
  结论: I.{u} <= monomorphisms _
  证明: by
  rintro _ _ _ ⟨n⟩
  exact monomorphisms.infer_property _

Depends on / 依赖: infer_property, monomorphisms, monomorphisms.infer_property
-/
lemma I_le_monomorphisms : I.{u} <= monomorphisms _ := by
  rintro _ _ _ ⟨n⟩
  exact monomorphisms.infer_property _

/--
lemma `J_le_monomorphisms` / 引理 `J_le_monomorphisms`

English:
lemma J_le_monomorphisms
  statement: J.{u} <= monomorphisms _
  proof: by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact monomorphisms.infer_property _

中文:
引理 J_le_monomorphisms
  结论: J.{u} <= monomorphisms _
  证明: by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact monomorphisms.infer_property _

Depends on / 依赖: iSup_iff, infer_property, monomorphisms, monomorphisms.infer_property
-/
lemma J_le_monomorphisms : J.{u} <= monomorphisms _ := by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact monomorphisms.infer_property _

/-- The cofibrations for the Quillen model category structure (TODO)
on `SSet` are monomorphisms. -/
scoped instance : CategoryWithCofibrations SSet.{u} where
  cofibrations := .monomorphisms _

/-- The fibrations for the Quillen model category structure (TODO)
on `SSet` are the morphisms which have the right lifting property
with respect to horn inclusions. -/
scoped instance : CategoryWithFibrations SSet.{u} where
  fibrations := J.rlp

/--
lemma `cofibrations_eq` / 引理 `cofibrations_eq`

English:
lemma cofibrations_eq
  statement: cofibrations SSet.{u} = monomorphisms _
  proof: rfl

中文:
引理 cofibrations_eq
  结论: cofibrations SSet.{u} = monomorphisms _
  证明: rfl
-/
lemma cofibrations_eq : cofibrations SSet.{u} = monomorphisms _ := rfl

/--
lemma `fibrations_eq` / 引理 `fibrations_eq`

English:
lemma fibrations_eq
  statement: fibrations SSet.{u} = J.rlp
  proof: rfl

中文:
引理 fibrations_eq
  结论: fibrations SSet.{u} = J.rlp
  证明: rfl
-/
lemma fibrations_eq : fibrations SSet.{u} = J.rlp := rfl

section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/--
lemma `cofibration_iff` / 引理 `cofibration_iff`

English:
lemma cofibration_iff
  statement: Cofibration f ↔ Mono f
  proof: by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

中文:
引理 cofibration_iff
  结论: Cofibration f ↔ Mono f
  证明: by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.cofibration_iff, cofibration_iff
-/
lemma cofibration_iff : Cofibration f ↔ Mono f := by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

/--
lemma `fibration_iff` / 引理 `fibration_iff`

English:
lemma fibration_iff
  statement: Fibration f ↔ J.rlp f
  proof: by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

中文:
引理 fibration_iff
  结论: Fibration f ↔ J.rlp f
  证明: by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.fibration_iff, fibration_iff
-/
lemma fibration_iff : Fibration f ↔ J.rlp f := by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

/--
Instance `mono_of_cofibration` / 实例 `mono_of_cofibration`

English:
instance mono_of_cofibration
  signature: [Cofibration f]
  body: by rwa [← cofibration_iff]

中文:
实例 mono_of_cofibration
  签名: [Cofibration f]
  定义体: by rwa [← cofibration_iff]

Depends on / 依赖: cofibration_iff
-/
instance mono_of_cofibration [Cofibration f] : Mono f := by rwa [← cofibration_iff]

/--
lemma `cofibration_of_mono` / 引理 `cofibration_of_mono`

English:
lemma cofibration_of_mono
  given: [Mono f]
  statement: Cofibration f
  proof: by rwa [cofibration_iff]

中文:
引理 cofibration_of_mono
  条件: [Mono f]
  结论: Cofibration f
  证明: by rwa [cofibration_iff]

Depends on / 依赖: cofibration_iff
-/
lemma cofibration_of_mono [Mono f] : Cofibration f := by rwa [cofibration_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hf
  signature: : Fibration f] {n : Nat} (i : Fin (n + 2)) :
  body: by
  rw [fibration_iff] at hf
  exact hf _ (horn_ι_mem_J _ _)

中文:
实例 [hf
  签名: : Fibration f] {n : 自然数} (i : Fin (n + 2)) :
  定义体: by
  rw [fibration_iff] at hf
  exact hf _ (horn_ι_mem_J _ _)

Depends on / 依赖: fibration_iff
-/
instance [hf : Fibration f] {n : Nat} (i : Fin (n + 2)) :
    HasLiftingProperty (horn (n + 1) i).ι f := by
  rw [fibration_iff] at hf
  exact hf _ (horn_ι_mem_J _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fibrations SSet.{u}).IsMultiplicative
  body: by
  rw [fibrations_eq]
  infer_instance

中文:
实例 :
  签名: (fibrations SSet.{u}).IsMultiplicative
  定义体: by
  rw [fibrations_eq]
  infer_instance

Depends on / 依赖: fibrations_eq, infer_instance
-/
instance : (fibrations SSet.{u}).IsMultiplicative := by
  rw [fibrations_eq]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fibrations SSet.{u}).IsStableUnderRetracts
  body: by
  rw [fibrations_eq]
  infer_instance

中文:
实例 :
  签名: (fibrations SSet.{u}).IsStableUnderRetracts
  定义体: by
  rw [fibrations_eq]
  infer_instance

Depends on / 依赖: fibrations_eq, infer_instance
-/
instance : (fibrations SSet.{u}).IsStableUnderRetracts := by
  rw [fibrations_eq]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cofibrations SSet.{u}).IsMultiplicative
  body: by
  rw [cofibrations_eq]
  infer_instance

中文:
实例 :
  签名: (cofibrations SSet.{u}).IsMultiplicative
  定义体: by
  rw [cofibrations_eq]
  infer_instance

Depends on / 依赖: cofibrations_eq, infer_instance
-/
instance : (cofibrations SSet.{u}).IsMultiplicative := by
  rw [cofibrations_eq]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cofibrations SSet.{u}).IsStableUnderRetracts
  body: by
  rw [cofibrations_eq]
  infer_instance

中文:
实例 :
  签名: (cofibrations SSet.{u}).IsStableUnderRetracts
  定义体: by
  rw [cofibrations_eq]
  infer_instance

Depends on / 依赖: cofibrations_eq, infer_instance
-/
instance : (cofibrations SSet.{u}).IsStableUnderRetracts := by
  rw [cofibrations_eq]
  infer_instance

instance {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] : Fibration f := by
  rw [fibration_iff]
  apply rlp_of_isIso

end

end modelCategoryQuillen

open modelCategoryQuillen in
/--
lemma `rlp_monomorphisms` / 引理 `rlp_monomorphisms`

English:
lemma rlp_monomorphisms
  proof: le_antisymm (antitone_rlp I_le_monomorphisms)
    (fun _ _ _ hp _ _ i _ =>
      transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp.{u} I Nat i
        ⟨(relativeCellComplexOfMono i).transfiniteCompositionOfShape' (fun _ => ⟨_⟩)⟩ _ hp)

中文:
引理 rlp_monomorphisms
  证明: le_antisymm (antitone_rlp I_le_monomorphisms)
    (fun _ _ _ hp _ _ i _ =>
      transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp.{u} I Nat i
        ⟨(relativeCellComplexOfMono i).transfiniteCompositionOfShape' (fun _ => ⟨_⟩)⟩ _ hp)

Depends on / 依赖: I_le_monomorphisms, antitone_rlp, le_antisymm, relativeCellComplexOfMono, transfiniteCompositionOfShape, transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
-/
lemma rlp_monomorphisms :
    (MorphismProperty.monomorphisms SSet.{u}).rlp = I.rlp :=
  le_antisymm (antitone_rlp I_le_monomorphisms)
    (fun _ _ _ hp _ _ i _ =>
      transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp.{u} I Nat i
        ⟨(relativeCellComplexOfMono i).transfiniteCompositionOfShape' (fun _ => ⟨_⟩)⟩ _ hp)

namespace horn.IsCompatible

open modelCategoryQuillen

variable {X : SSet.{u}} {n : Nat}
  {i : Fin (n + 2)} {f : forall (j : Fin (n + 2)) (_ : j != i), Δ[n] ⟶ X}
  (hf : horn.IsCompatible f) {Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
  (b : Δ[n + 1] ⟶ Y)
  (comm : forall (j : Fin (n + 2)) (hj : j != i), f j hj ≫ p = stdSimplex.δ j ≫ b)

include hf comm in
/--
lemma `exists_lift` / 引理 `exists_lift`

English:
lemma exists_lift
  proof: by
  have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
    ⟨horn.hom_ext' (fun j hj => by simpa using comm j hj)⟩
  exact ⟨sq.lift, fun j hj => by simp [← ι_ι_assoc i j hj], by simp⟩

中文:
引理 exists_lift
  证明: by
  have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
    ⟨horn.hom_ext' (fun j hj => by simpa using comm j hj)⟩
  exact ⟨sq.lift, fun j hj => by simp [← ι_ι_assoc i j hj], by simp⟩

Depends on / 依赖: CommSq, hf.desc, hom_ext, horn.hom_ext, sq.lift
-/
lemma exists_lift :
    exists (φ : Δ[n + 1] ⟶ X),
      (forall (j : Fin (n + 2)) (hj : j != i), stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ p = b := by
  have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
    ⟨horn.hom_ext' (fun j hj => by simpa using comm j hj)⟩
  exact ⟨sq.lift, fun j hj => by simp [← ι_ι_assoc i j hj], by simp⟩

/-- If `f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X` is a compatible family
of morphisms (which defines a morphism `Λ[n + 1, i] ⟶ X`), `p : X ⟶ Y` a Kan fibration
and `b : Δ[n + 1] ⟶ Y` such that for all `j ≠ i`, `f j _ ≫ p = stdSimplex.δ j ≫ b`,
then this is a lifting `Δ[n + 1] ⟶ X`. -/
@[no_expose]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : Δ[n + 1] ⟶ X
  body: (hf.exists_lift p b comm).choose

@[reassoc]

中文:
定义 lift
  签名: : Δ[n + 1] ⟶ X
  定义体: (hf.exists_lift p b comm).choose

@[reassoc]

Depends on / 依赖: exists_lift, hf.exists_lift
-/
noncomputable def lift : Δ[n + 1] ⟶ X := (hf.exists_lift p b comm).choose

@[reassoc]
/--
lemma `δ_lift` / 引理 `δ_lift`

English:
lemma δ_lift
  given: (j : Fin (n + 2)) (hj : j != i := by grind)
  proof: ((hf.exists_lift p b comm).choose_spec).1 j hj

@[reassoc (attr := simp)]

中文:
引理 δ_lift
  条件: (j : Fin (n + 2)) (hj : j != i := by grind)
  证明: ((hf.exists_lift p b comm).choose_spec).1 j hj

@[reassoc (attr := simp)]

Depends on / 依赖: choose_spec, exists_lift, hf.exists_lift, hf.lift, stdSimplex
-/
lemma δ_lift (j : Fin (n + 2)) (hj : j != i := by grind) :
    stdSimplex.δ j ≫ hf.lift p b comm = f j hj :=
  ((hf.exists_lift p b comm).choose_spec).1 j hj

@[reassoc (attr := simp)]
/--
lemma `lift_comp` / 引理 `lift_comp`

English:
lemma lift_comp
  statement: hf.lift p b comm ≫ p = b
  proof: ((hf.exists_lift p b comm).choose_spec).2

中文:
引理 lift_comp
  结论: hf.lift p b comm ≫ p = b
  证明: ((hf.exists_lift p b comm).choose_spec).2

Depends on / 依赖: choose_spec, exists_lift, hf.exists_lift
-/
lemma lift_comp : hf.lift p b comm ≫ p = b :=
  ((hf.exists_lift p b comm).choose_spec).2

end horn.IsCompatible

end SSet
