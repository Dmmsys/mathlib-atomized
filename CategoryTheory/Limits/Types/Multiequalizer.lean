/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Multiequalizers in Type

Given `J : MulticospanShape` and `I : MulticospanIndex J (Type u)`,
we define a type `I.sections`. When `c : Multifork I`, we show
that `c` is a limit iff the canonical map
`c.toSections : c.pt → I.sections` is a bijection.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {J : MulticospanShape} (I : MulticospanIndex J (Type u))

/-- Given `I : MulticospanIndex J (Type u)`, this is a type which identifies
to the sections of the functor `I.multicospan`. -/
@[ext]
/--
Definition of `MulticospanIndex.sections` / `MulticospanIndex.sections` 的定义

English:
structure MulticospanIndex.sections
  parameters: where
  axioms and operations (2):
    - val((i : J.L)) : I.left i
    - property((r : J.R)) : I.fst r (val _) = I.snd r (val _)

中文:
结构 MulticospanIndex.sections
  参数: where
  公理与运算 (2 个):
    - val((i : J.L)) : I.left i
    - property((r : J.R)) : I.fst r (val _) = I.snd r (val _)
-/
structure MulticospanIndex.sections where
  /-- The data of an element in `I.left i` for each `i : J.L`. -/
  val (i : J.L) : I.left i
  property (r : J.R) : I.fst r (val _) = I.snd r (val _)

/-- The bijection `I.sections ≃ I.multicospan.sections` when `I : MulticospanIndex (Type u)`
is a multiequalizer diagram in the category of types. -/
@[simps]
/--
Definition of `MulticospanIndex.sectionsEquiv` / `MulticospanIndex.sectionsEquiv` 的定义

English:
definition MulticospanIndex.sectionsEquiv
  signature: :
  body: { val := fun i => match i with
        | .left i => s.val i
        | .right j => I.fst j (s.val _)
      property := by
        rintro _ _ (_ | _ | r)
        · rfl
        · rfl
        · exact (s.property r).symm }
  invFun s :=
    { val := fun i => s.val (.left i)
      property := fun r => (s.

中文:
定义 MulticospanIndex.sectionsEquiv
  签名: :
  定义体: { val := fun i => match i with
        | .left i => s.val i
        | .right j => I.fst j (s.val _)
      property := by
        rintro _ _ (_ | _ | r)
        · rfl
        · rfl
        · exact (s.property r).symm }
  invFun s :=
    { val := fun i => s.val (.left i)
      property := fun r => (s.

Depends on / 依赖: I.fst, invFun, property, right_inv, s.property, s.val
-/
def MulticospanIndex.sectionsEquiv :
    I.sections ≃ I.multicospan.sections where
  toFun s :=
    { val := fun i => match i with
        | .left i => s.val i
        | .right j => I.fst j (s.val _)
      property := by
        rintro _ _ (_ | _ | r)
        · rfl
        · rfl
        · exact (s.property r).symm }
  invFun s :=
    { val := fun i => s.val (.left i)
      property := fun r => (s.property (.fst r)).trans (s.property (.snd r)).symm }
  right_inv s := by
    ext (_ | r)
    · rfl
    · exact s.property (.fst r)

namespace Multifork

variable {I}
variable (c : Multifork I)

/-- Given a multiequalizer diagram `I : MulticospanIndex (Type u)` in the category of
types and `c` a multifork for `I`, this is the canonical map `c.pt → I.sections`. -/
@[simps]
/--
Definition of `toSections` / `toSections` 的定义

English:
definition toSections
  signature: (x : c.pt)
  body: c.ι i x
  property r := ConcreteCategory.congr_hom (c.condition r) x

中文:
定义 toSections
  签名: (x : c.pt)
  定义体: c.ι i x
  property r := ConcreteCategory.congr_hom (c.condition r) x
-/
def toSections (x : c.pt) : I.sections where
  val i := c.ι i x
  property r := ConcreteCategory.congr_hom (c.condition r) x

/--
lemma `toSections_fac` / 引理 `toSections_fac`

English:
lemma toSections_fac
  statement: I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSections
  proof: rfl

中文:
引理 toSections_fac
  结论: I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSections
  证明: rfl
-/
lemma toSections_fac : I.sectionsEquiv.symm ∘ Types.sectionOfCone c = c.toSections := rfl

/--
lemma `isLimit_types_iff` / 引理 `isLimit_types_iff`

English:
lemma isLimit_types_iff
  statement: Nonempty (IsLimit c) ↔ Function.Bijective c.toSections
  proof: by
  rw [Types.isLimit_iff_bijective_sectionOfCone]; rw [← toSections_fac]; rw [EquivLike.comp_bijective]

中文:
引理 isLimit_types_iff
  结论: Nonempty (IsLimit c) ↔ Function.Bijective c.toSections
  证明: by
  rw [Types.isLimit_iff_bijective_sectionOfCone]; rw [← toSections_fac]; rw [EquivLike.comp_bijective]

Depends on / 依赖: EquivLike, EquivLike.comp_bijective, Types.isLimit_iff_bijective_sectionOfCone, comp_bijective, isLimit_iff_bijective_sectionOfCone, toSections_fac
-/
lemma isLimit_types_iff : Nonempty (IsLimit c) ↔ Function.Bijective c.toSections := by
  rw [Types.isLimit_iff_bijective_sectionOfCone]; rw [← toSections_fac]; rw [EquivLike.comp_bijective]

namespace IsLimit

variable {c} (hc : IsLimit c)

/--
Definition of `sectionsEquiv` / `sectionsEquiv` 的定义

English:
definition sectionsEquiv
  signature: : I.sections ≃ c.pt
  body: (Equiv.ofBijective _ (c.isLimit_types_iff.1 ⟨hc⟩)).symm

@[simp]

中文:
定义 sectionsEquiv
  签名: : I.sections ≃ c.pt
  定义体: (Equiv.ofBijective _ (c.isLimit_types_iff.1 ⟨hc⟩)).symm

@[simp]

Depends on / 依赖: Equiv.ofBijective, c.isLimit_types_iff, isLimit_types_iff, ofBijective
-/
noncomputable def sectionsEquiv : I.sections ≃ c.pt :=
  (Equiv.ofBijective _ (c.isLimit_types_iff.1 ⟨hc⟩)).symm

@[simp]
/--
lemma `sectionsEquiv_symm_apply_val` / 引理 `sectionsEquiv_symm_apply_val`

English:
lemma sectionsEquiv_symm_apply_val
  given: (x : c.pt) (i : J.L)
  proof: rfl

@[simp]

中文:
引理 sectionsEquiv_symm_apply_val
  条件: (x : c.pt) (i : J.L)
  证明: rfl

@[simp]
-/
lemma sectionsEquiv_symm_apply_val (x : c.pt) (i : J.L) :
    ((sectionsEquiv hc).symm x).val i = c.ι i x := rfl

@[simp]
/--
lemma `sectionsEquiv_apply_val` / 引理 `sectionsEquiv_apply_val`

English:
lemma sectionsEquiv_apply_val
  given: (s : I.sections) (i : J.L)
  proof: by
  obtain ⟨x, rfl⟩ := (sectionsEquiv hc).symm.surjective s
  simp

中文:
引理 sectionsEquiv_apply_val
  条件: (s : I.sections) (i : J.L)
  证明: by
  obtain ⟨x, rfl⟩ := (sectionsEquiv hc).symm.surjective s
  simp

Depends on / 依赖: sectionsEquiv, surjective, symm.surjective
-/
lemma sectionsEquiv_apply_val (s : I.sections) (i : J.L) :
    c.ι i (sectionsEquiv hc s) = s.val i := by
  obtain ⟨x, rfl⟩ := (sectionsEquiv hc).symm.surjective s
  simp

end IsLimit

end Multifork

end CategoryTheory.Limits
