/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Images in the category of types

In this file, it is shown that the category of types has categorical images,
and that these agree with the range of a function.

-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits.Types

variable {α β : Type u} (f : α ⟶ β)

section

-- implementation of `HasImage`
/--
Definition of `Image` / `Image` 的定义

English:
definition Image
  signature: : Type u
  body: Set.range f

中文:
定义 Image
  签名: : 类型u
  定义体: Set.range f

Depends on / 依赖: Set.range
-/
def Image : Type u :=
  Set.range f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Image f) where default
  body: ⟨f default, ⟨_, rfl⟩⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited (Image f) where default
  定义体: ⟨f default, ⟨_, rfl⟩⟩
-/
instance [Inhabited α] : Inhabited (Image f) where default := ⟨f default, ⟨_, rfl⟩⟩

/--
Definition of `Image.ι` / `Image.ι` 的定义

English:
definition Image.ι
  signature: : Image f ⟶ β
  body: ↾(Subtype.val)

中文:
定义 Image.ι
  签名: : Image f ⟶ β
  定义体: ↾(Subtype.val)

Depends on / 依赖: Subtype, Subtype.val
-/
def Image.ι : Image f ⟶ β :=
  ↾(Subtype.val)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (Image.ι f)
  body: (mono_iff_injective _).2 Subtype.val_injective

中文:
实例 :
  签名: Mono (Image.ι f)
  定义体: (mono_iff_injective _).2 Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, mono_iff_injective, val_injective
-/
instance : Mono (Image.ι f) :=
  (mono_iff_injective _).2 Subtype.val_injective

variable {f}

/--
Definition of `Image.lift` / `Image.lift` 的定义

English:
definition Image.lift
  signature: (F' : MonoFactorisation f)
  body: ↾fun x => F'.e (Classical.indefiniteDescription _ x.2).1

中文:
定义 Image.lift
  签名: (F' : MonoFactorisation f)
  定义体: ↾fun x => F'.e (Classical.indefiniteDescription _ x.2).1

Depends on / 依赖: Classical, Classical.indefiniteDescription, indefiniteDescription
-/
noncomputable def Image.lift (F' : MonoFactorisation f) : Image f ⟶ F'.I :=
  ↾fun x => F'.e (Classical.indefiniteDescription _ x.2).1

/--
theorem `Image.lift_fac` / 定理 `Image.lift_fac`

English:
theorem Image.lift_fac
  given: (F' : MonoFactorisation f)
  statement: Image.lift F' ≫ F'.m = Image.ι f
  proof: by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac]; rw [(Classical.indefiniteDescription _ x.2).2]
  rfl

中文:
定理 Image.lift_fac
  条件: (F' : MonoFactorisation f)
  结论: Image.lift F' ≫ F'.m = Image.ι f
  证明: by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac]; rw [(Classical.indefiniteDescription _ x.2).2]
  rfl

Depends on / 依赖: Classical, Classical.indefiniteDescription, indefiniteDescription
-/
theorem Image.lift_fac (F' : MonoFactorisation f) : Image.lift F' ≫ F'.m = Image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac]; rw [(Classical.indefiniteDescription _ x.2).2]
  rfl

end

/--
Definition of `monoFactorisation` / `monoFactorisation` 的定义

English:
definition monoFactorisation
  signature: : MonoFactorisation f where
  body: Image f
  m := Image.ι f
  e := ↾(Set.rangeFactorization f)

中文:
定义 monoFactorisation
  签名: : MonoFactorisation f where
  定义体: Image f
  m := Image.ι f
  e := ↾(Set.rangeFactorization f)
-/
def monoFactorisation : MonoFactorisation f where
  I := Image f
  m := Image.ι f
  e := ↾(Set.rangeFactorization f)

/--
Definition of `isImage` / `isImage` 的定义

English:
definition isImage
  signature: : IsImage (monoFactorisation f) where
  body: Image.lift
  lift_fac := Image.lift_fac

中文:
定义 isImage
  签名: : IsImage (monoFactorisation f) where
  定义体: Image.lift
  lift_fac := Image.lift_fac

Depends on / 依赖: Image.lift
-/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := Image.lift
  lift_fac := Image.lift_fac

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasImage f
  body: HasImage.mk ⟨_, isImage f⟩

中文:
实例 :
  签名: HasImage f
  定义体: HasImage.mk ⟨_, isImage f⟩

Depends on / 依赖: HasImage, HasImage.mk, isImage
-/
instance : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasImages (Type u)
  body: by infer_instance

中文:
实例 :
  签名: HasImages (类型u)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : HasImages (Type u) where
  has_image := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasImageMaps (Type u)
  body: HasImageMap.transport st (monoFactorisation f.hom) (isImage g.hom)
      (↾fun x => ⟨st.right x.val, ⟨st.left (Classical.choose x.2), by
        rw [elementwise_of% st.w]
        rw [Classical.choose_spec x.property]⟩⟩) rfl

中文:
实例 :
  签名: HasImageMaps (类型u)
  定义体: HasImageMap.transport st (monoFactorisation f.hom) (isImage g.hom)
      (↾fun x => ⟨st.right x.val, ⟨st.left (Classical.choose x.2), by
        rw [elementwise_of% st.w]
        rw [Classical.choose_spec x.property]⟩⟩) rfl

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, HasImageMap, HasImageMap.transport, choose_spec, elementwise_of, f.hom, g.hom, isImage, monoFactorisation, property, st.left, st.right, st.w, transport, x.property, x.val
-/
instance : HasImageMaps (Type u) where
  has_image_map {f g} st :=
    HasImageMap.transport st (monoFactorisation f.hom) (isImage g.hom)
      (↾fun x => ⟨st.right x.val, ⟨st.left (Classical.choose x.2), by
        rw [elementwise_of% st.w]
        rw [Classical.choose_spec x.property]⟩⟩) rfl

variable {F : Natᵒᵖ ⥤ Type u} {c : Cone F}
  (hF : forall n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def limitOfSurjectionsSurjective.preimage

中文:
定义 noncomputable
  签名: def limitOfSurjectionsSurjective.preimage

Depends on / 依赖: Equiv.addCommGroup, addCommGroup, fast_instance, opEquiv
-/
private noncomputable def limitOfSurjectionsSurjective.preimage
    (a : F.obj ⟨0⟩) : (n : Nat) -> F.obj ⟨n⟩
    | 0 => a
    | n + 1 => (hF n (preimage a n)).choose

include hF in
open limitOfSurjectionsSurjective in
/--
lemma `surjective_π_app_zero_of_surjective_map_aux` / 引理 `surjective_π_app_zero_of_surjective_map_aux`

English:
lemma surjective_π_app_zero_of_surjective_map_aux
  proof: by
  intro a
  refine ⟨⟨fun ⟨n⟩ => preimage hF a n, ?_⟩, rfl⟩
  intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m <= n)⟩⟩⟩
  induction h with
  | refl =>
    erw [CategoryTheory.Functor.map_id, id_apply]
  | @step p h ih =>
    rw [← ih]
    have h' : m <= p := h
    erw [CategoryTheory.Functor.map_comp (f := (homOfLE (Nat.l

中文:
引理 surjective_π_app_zero_of_surjective_map_aux
  证明: by
  intro a
  refine ⟨⟨fun ⟨n⟩ => preimage hF a n, ?_⟩, rfl⟩
  intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m <= n)⟩⟩⟩
  induction h with
  | refl =>
    erw [CategoryTheory.Functor.map_id, id_apply]
  | @step p h ih =>
    rw [← ih]
    have h' : m <= p := h
    erw [CategoryTheory.Functor.map_comp (f := (homOfLE (Nat.l

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, Functor, Nat.le_succ, choose_spec, comp_apply, homOfLE, id_apply, le_succ, map_comp, map_id, preimage
-/
lemma surjective_π_app_zero_of_surjective_map_aux :
    Function.Surjective ((limitCone F).π.app ⟨0⟩) := by
  intro a
  refine ⟨⟨fun ⟨n⟩ => preimage hF a n, ?_⟩, rfl⟩
  intro ⟨n⟩ ⟨m⟩ ⟨⟨⟨(h : m <= n)⟩⟩⟩
  induction h with
  | refl =>
    erw [CategoryTheory.Functor.map_id, id_apply]
  | @step p h ih =>
    rw [← ih]
    have h' : m <= p := h
    erw [CategoryTheory.Functor.map_comp (f := (homOfLE (Nat.le_succ p)).op) (g := (homOfLE h').op),
      comp_apply, (hF p _).choose_spec]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `surjective_π_app_zero_of_surjective_map` / 引理 `surjective_π_app_zero_of_surjective_map`

English:
lemma surjective_π_app_zero_of_surjective_map
  proof: by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]; rfl
  rw [this]; rw [types_comp]
  apply Function.Surjective.comp
  · exact surjective_π_app_zero_of_surjective_map_aux hF
  · rw [← epi_iff_surjective]
    infer_insta

中文:
引理 surjective_π_app_zero_of_surjective_map
  证明: by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]; rfl
  rw [this]; rw [types_comp]
  apply Function.Surjective.comp
  · exact surjective_π_app_zero_of_surjective_map_aux hF
  · rw [← epi_iff_surjective]
    infer_insta

Depends on / 依赖: Function, Function.Surjective.comp, Surjective, conePointUniqueUpToIso, epi_iff_surjective, hc.conePointUniqueUpToIso, i.hom, infer_instance, limitCone, limitConeIsLimit, types_comp
-/
lemma surjective_π_app_zero_of_surjective_map
    (hc : IsLimit c)
    (hF : forall n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) := by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]; rfl
  rw [this]; rw [types_comp]
  apply Function.Surjective.comp
  · exact surjective_π_app_zero_of_surjective_map_aux hF
  · rw [← epi_iff_surjective]
    infer_instance

end CategoryTheory.Limits.Types
