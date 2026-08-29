/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The image of a subfunctor

Given a morphism of type-valued functors `p : F' ⟶ F`, we define its range
`Subfunctor.range p`. More generally, if `G' : Subfunctor F'`, we
define `G'.image p : Subfunctor F` as the image of `G'` by `f`, and
if `G : Subfunctor F`, we define its preimage `G.preimage f : Subfunctor F'`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F F' F'' : C ⥤ Type w}

namespace Subfunctor

section range

/-- The range of a morphism of type-valued functors, as a subfunctor of the target. -/
@[simps]
/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (p : F' ⟶ F)
  body: Set.range (p.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    exact ⟨_, NatTrans.naturality_apply p i x⟩

中文:
定义 range
  签名: (p : F' ⟶ F)
  定义体: Set.range (p.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    exact ⟨_, NatTrans.naturality_apply p i x⟩

Depends on / 依赖: Set.range, p.app
-/
def range (p : F' ⟶ F) : Subfunctor F where
  obj U := Set.range (p.app U)
  map := by
    rintro U V i _ ⟨x, rfl⟩
    exact ⟨_, NatTrans.naturality_apply p i x⟩

variable (F) in
/--
lemma `range_id` / 引理 `range_id`

English:
lemma range_id
  statement: range (𝟙 F) = ⊤
  proof: by aesop

中文:
引理 range_id
  结论: range (𝟙 F) = ⊤
  证明: by aesop
-/
lemma range_id : range (𝟙 F) = ⊤ := by aesop

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `range_ι` / 引理 `range_ι`

English:
lemma range_ι
  given: (G : Subfunctor F)
  statement: range G.ι = G
  proof: by aesop

中文:
引理 range_ι
  条件: (G : 子函子 F)
  结论: range G.ι = G
  证明: by aesop
-/
lemma range_ι (G : Subfunctor F) : range G.ι = G := by aesop

end range

section lift

variable (f : F' ⟶ F) {G : Subfunctor F} (hf : range f <= G)

set_option backward.defeqAttrib.useBackward true in
/-- If the image of a morphism falls in a subfunctor, then the morphism factors through it. -/
@[simps! app]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : F' ⟶ G.toFunctor where
  body: ↾fun x => ⟨f.app U x, hf U (by simp)⟩
  naturality _ _ g := by
    ext x
    simpa [Subtype.ext_iff, -NatTrans.naturality_apply] using NatTrans.naturality_apply f g x

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: : F' ⟶ G.toFunctor where
  定义体: ↾fun x => ⟨f.app U x, hf U (by simp)⟩
  naturality _ _ g := by
    ext x
    simpa [Subtype.ext_iff, -NatTrans.naturality_apply] using NatTrans.naturality_apply f g x

@[reassoc (attr := simp)]

Depends on / 依赖: f.app
-/
def lift : F' ⟶ G.toFunctor where
  app U := ↾fun x => ⟨f.app U x, hf U (by simp)⟩
  naturality _ _ g := by
    ext x
    simpa [Subtype.ext_iff, -NatTrans.naturality_apply] using NatTrans.naturality_apply f g x

@[reassoc (attr := simp)]
/--
theorem `lift_ι` / 定理 `lift_ι`

English:
theorem lift_ι
  statement: lift f hf ≫ G.ι = f
  proof: rfl

中文:
定理 lift_ι
  结论: lift f hf ≫ G.ι = f
  证明: rfl
-/
theorem lift_ι : lift f hf ≫ G.ι = f := rfl

end lift

section range

variable (p : F' ⟶ F)

/--
Definition of `toRange` / `toRange` 的定义

English:
definition toRange
  signature: :
  body: lift p (by rfl)

@[reassoc (attr := simp)]

中文:
定义 toRange
  签名: :
  定义体: lift p (by rfl)

@[reassoc (attr := simp)]
-/
def toRange :
    F' ⟶ (range p).toFunctor :=
  lift p (by rfl)

@[reassoc (attr := simp)]
/--
lemma `toRange_ι` / 引理 `toRange_ι`

English:
lemma toRange_ι
  statement: toRange p ≫ (range p).ι = p
  proof: rfl

中文:
引理 toRange_ι
  结论: toRange p ≫ (range p).ι = p
  证明: rfl
-/
lemma toRange_ι : toRange p ≫ (range p).ι = p := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toRange_app_val` / 引理 `toRange_app_val`

English:
lemma toRange_app_val
  given: {i : C} (x : F'.obj i)
  proof: by
  simp [toRange]

中文:
引理 toRange_app_val
  条件: {i : C} (x : F'.obj i)
  证明: by
  simp [toRange]

Depends on / 依赖: toRange
-/
lemma toRange_app_val {i : C} (x : F'.obj i) :
    ((toRange p).app i x).val = p.app i x := by
  simp [toRange]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `range_toRange` / 引理 `range_toRange`

English:
lemma range_toRange
  statement: range (toRange p) = ⊤
  proof: by
  ext i ⟨x, hx⟩
  dsimp at hx ⊢
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  simp only [Set.range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

中文:
引理 range_toRange
  结论: range (toRange p) = ⊤
  证明: by
  ext i ⟨x, hx⟩
  dsimp at hx ⊢
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  simp only [Set.range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

Depends on / 依赖: Set.mem_range, Set.mem_univ, Set.range, iff_true, mem_range, mem_univ
-/
lemma range_toRange : range (toRange p) = ⊤ := by
  ext i ⟨x, hx⟩
  dsimp at hx ⊢
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  simp only [Set.range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

/--
lemma `epi_iff_range_eq_top` / 引理 `epi_iff_range_eq_top`

English:
lemma epi_iff_range_eq_top
  proof: by
  simp [NatTrans.epi_iff_epi_app, epi_iff_surjective, Subfunctor.ext_iff, funext_iff,
    Set.range_eq_univ]

中文:
引理 epi_iff_range_eq_top
  证明: by
  simp [NatTrans.epi_iff_epi_app, epi_iff_surjective, Subfunctor.ext_iff, funext_iff,
    Set.range_eq_univ]

Depends on / 依赖: NatTrans, NatTrans.epi_iff_epi_app, Set.range_eq_univ, Subfunctor, Subfunctor.ext_iff, epi_iff_epi_app, epi_iff_surjective, ext_iff, funext_iff, range_eq_univ
-/
lemma epi_iff_range_eq_top :
    Epi p ↔ range p = ⊤ := by
  simp [NatTrans.epi_iff_epi_app, epi_iff_surjective, Subfunctor.ext_iff, funext_iff,
    Set.range_eq_univ]

/--
lemma `range_eq_top` / 引理 `range_eq_top`

English:
lemma range_eq_top
  given: [Epi p]
  statement: range p = ⊤
  proof: by rwa [← epi_iff_range_eq_top]

中文:
引理 range_eq_top
  条件: [满态射 p]
  结论: range p = ⊤
  证明: by rwa [← epi_iff_range_eq_top]

Depends on / 依赖: epi_iff_range_eq_top
-/
lemma range_eq_top [Epi p] : range p = ⊤ := by rwa [← epi_iff_range_eq_top]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (toRange p)
  body: by simp [epi_iff_range_eq_top]

中文:
实例 :
  签名: 满态射 (toRange p)
  定义体: by simp [epi_iff_range_eq_top]

Depends on / 依赖: epi_iff_range_eq_top
-/
instance : Epi (toRange p) := by simp [epi_iff_range_eq_top]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: p] : IsIso (toRange p)
  body: by
  have := mono_of_mono_fac (toRange_ι p)
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  rw [isIso_iff_bijective]
  constructor
  · rw [← mono_iff_injective]
    infer_instance
  · rw [← epi_iff_surjective]
    infer_instance

中文:
实例 [单态射
  签名: p] : 是同构 (toRange p)
  定义体: by
  have := mono_of_mono_fac (toRange_ι p)
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  rw [isIso_iff_bijective]
  constructor
  · rw [← mono_iff_injective]
    infer_instance
  · rw [← epi_iff_surjective]
    infer_instance

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, epi_iff_surjective, infer_instance, isIso_iff_bijective, isIso_iff_isIso_app, mono_iff_injective, mono_of_mono_fac
-/
instance [Mono p] : IsIso (toRange p) := by
  have := mono_of_mono_fac (toRange_ι p)
  rw [NatTrans.isIso_iff_isIso_app]
  intro i
  rw [isIso_iff_bijective]
  constructor
  · rw [← mono_iff_injective]
    infer_instance
  · rw [← epi_iff_surjective]
    infer_instance

/--
lemma `range_comp_le` / 引理 `range_comp_le`

English:
lemma range_comp_le
  given: (f : F ⟶ F') (g : F' ⟶ F'')
  proof: fun _ _ _ => by aesop

中文:
引理 range_comp_le
  条件: (f : F ⟶ F') (g : F' ⟶ F'')
  证明: fun _ _ _ => by aesop
-/
lemma range_comp_le (f : F ⟶ F') (g : F' ⟶ F'') :
    range (f ≫ g) <= range g := fun _ _ _ => by aesop

end range

section image

variable (G : Subfunctor F) (f : F ⟶ F')

/-- The image of a subfunctor by a morphism of type-valued functors. -/
@[simps]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: : Subfunctor F' where
  body: (f.app i) '' (G.obj i)
  map := by
    rintro Δ Δ' φ _ ⟨x, hx, rfl⟩
    exact ⟨F.map φ x, G.map φ hx, by apply NatTrans.naturality_apply⟩

中文:
定义 像
  签名: : 子函子 F' where
  定义体: (f.app i) '' (G.obj i)
  map := by
    rintro Δ Δ' φ _ ⟨x, hx, rfl⟩
    exact ⟨F.map φ x, G.map φ hx, by apply NatTrans.naturality_apply⟩

Depends on / 依赖: G.obj, f.app
-/
def image : Subfunctor F' where
  obj i := (f.app i) '' (G.obj i)
  map := by
    rintro Δ Δ' φ _ ⟨x, hx, rfl⟩
    exact ⟨F.map φ x, G.map φ hx, by apply NatTrans.naturality_apply⟩

/--
lemma `image_top` / 引理 `image_top`

English:
lemma image_top
  statement: (⊤ : Subfunctor F).image f = range f
  proof: by aesop

@[simp]

中文:
引理 image_top
  结论: (⊤ : 子函子 F).像 f = range f
  证明: by aesop

@[simp]
-/
lemma image_top : (⊤ : Subfunctor F).image f = range f := by aesop

@[simp]
/--
lemma `image_iSup` / 引理 `image_iSup`

English:
lemma image_iSup
  given: {ι : Type*} (G : ι -> Subfunctor F) (f : F ⟶ F')
  proof: by aesop

中文:
引理 image_iSup
  条件: {ι : 类型} (G : ι -> 子函子 F) (f : F ⟶ F')
  证明: by aesop
-/
lemma image_iSup {ι : Type*} (G : ι -> Subfunctor F) (f : F ⟶ F') :
    (⨆ i, G i).image f = ⨆ i, (G i).image f := by aesop

/--
lemma `image_comp` / 引理 `image_comp`

English:
lemma image_comp
  given: (g : F' ⟶ F'')
  proof: by aesop

中文:
引理 image_comp
  条件: (g : F' ⟶ F'')
  证明: by aesop
-/
lemma image_comp (g : F' ⟶ F'') :
    G.image (f ≫ g) = (G.image f).image g := by aesop

/--
lemma `range_comp` / 引理 `range_comp`

English:
lemma range_comp
  given: (g : F' ⟶ F'')
  proof: by aesop

中文:
引理 range_comp
  条件: (g : F' ⟶ F'')
  证明: by aesop
-/
lemma range_comp (g : F' ⟶ F'') :
    range (f ≫ g) = (range f).image g := by aesop

end image

section preimage

/-- The preimage of a subfunctor by a morphism of type-valued functors. -/
@[simps]
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (G : Subfunctor F) (p : F' ⟶ F)
  body: p.app n ⁻¹' (G.obj n)
  map f := (Set.preimage_mono (G.map f)).trans (by
    simp only [Set.preimage_preimage, NatTrans.naturality_apply]
    rfl)

@[simp]

中文:
定义 原像
  签名: (G : 子函子 F) (p : F' ⟶ F)
  定义体: p.app n ⁻¹' (G.obj n)
  map f := (Set.preimage_mono (G.map f)).trans (by
    simp only [Set.preimage_preimage, NatTrans.naturality_apply]
    rfl)

@[simp]

Depends on / 依赖: G.obj, p.app
-/
def preimage (G : Subfunctor F) (p : F' ⟶ F) : Subfunctor F' where
  obj n := p.app n ⁻¹' (G.obj n)
  map f := (Set.preimage_mono (G.map f)).trans (by
    simp only [Set.preimage_preimage, NatTrans.naturality_apply]
    rfl)

@[simp]
/--
lemma `preimage_id` / 引理 `preimage_id`

English:
lemma preimage_id
  given: (G : Subfunctor F)
  proof: by aesop

中文:
引理 preimage_id
  条件: (G : 子函子 F)
  证明: by aesop
-/
lemma preimage_id (G : Subfunctor F) :
    G.preimage (𝟙 F) = G := by aesop

/--
lemma `preimage_comp` / 引理 `preimage_comp`

English:
lemma preimage_comp
  given: (G : Subfunctor F) (f : F'' ⟶ F') (g : F' ⟶ F)
  proof: by aesop

中文:
引理 preimage_comp
  条件: (G : 子函子 F) (f : F'' ⟶ F') (g : F' ⟶ F)
  证明: by aesop
-/
lemma preimage_comp (G : Subfunctor F) (f : F'' ⟶ F') (g : F' ⟶ F) :
    G.preimage (f ≫ g) = (G.preimage g).preimage f := by aesop

/--
lemma `image_le_iff` / 引理 `image_le_iff`

English:
lemma image_le_iff
  given: (G : Subfunctor F) (f : F ⟶ F') (G' : Subfunctor F')
  proof: by
  simp [Subfunctor.le_def]

中文:
引理 image_le_iff
  条件: (G : 子函子 F) (f : F ⟶ F') (G' : 子函子 F')
  证明: by
  simp [Subfunctor.le_def]

Depends on / 依赖: Subfunctor, Subfunctor.le_def, le_def
-/
lemma image_le_iff (G : Subfunctor F) (f : F ⟶ F') (G' : Subfunctor F') :
    G.image f <= G' ↔ G <= G'.preimage f := by
  simp [Subfunctor.le_def]

/--
Definition of `fromPreimage` / `fromPreimage` 的定义

English:
definition fromPreimage
  signature: (G : Subfunctor F) (p : F' ⟶ F)
  body: lift ((G.preimage p).ι ≫ p) (by
    rw [range_comp]; rw [range_ι]; rw [image_le_iff])

@[reassoc]

中文:
定义 fromPreimage
  签名: (G : 子函子 F) (p : F' ⟶ F)
  定义体: lift ((G.preimage p).ι ≫ p) (by
    rw [range_comp]; rw [range_ι]; rw [image_le_iff])

@[reassoc]

Depends on / 依赖: G.preimage, image_le_iff, preimage, range_comp
-/
def fromPreimage (G : Subfunctor F) (p : F' ⟶ F) :
    (G.preimage p).toFunctor ⟶ G.toFunctor :=
  lift ((G.preimage p).ι ≫ p) (by
    rw [range_comp]; rw [range_ι]; rw [image_le_iff])

@[reassoc]
/--
lemma `fromPreimage_ι` / 引理 `fromPreimage_ι`

English:
lemma fromPreimage_ι
  given: (G : Subfunctor F) (p : F' ⟶ F)
  proof: rfl

中文:
引理 fromPreimage_ι
  条件: (G : 子函子 F) (p : F' ⟶ F)
  证明: rfl
-/
lemma fromPreimage_ι (G : Subfunctor F) (p : F' ⟶ F) :
    G.fromPreimage p ≫ G.ι = (G.preimage p).ι ≫ p := rfl

/--
lemma `preimage_eq_top_iff` / 引理 `preimage_eq_top_iff`

English:
lemma preimage_eq_top_iff
  given: (G : Subfunctor F) (p : F' ⟶ F)
  proof: by
  rw [← image_top]; rw [image_le_iff]
  simp

@[simp]

中文:
引理 preimage_eq_top_iff
  条件: (G : 子函子 F) (p : F' ⟶ F)
  证明: by
  rw [← image_top]; rw [image_le_iff]
  simp

@[simp]

Depends on / 依赖: image_le_iff, image_top
-/
lemma preimage_eq_top_iff (G : Subfunctor F) (p : F' ⟶ F) :
    G.preimage p = ⊤ ↔ range p <= G := by
  rw [← image_top]; rw [image_le_iff]
  simp

@[simp]
/--
lemma `preimage_image_of_epi` / 引理 `preimage_image_of_epi`

English:
lemma preimage_image_of_epi
  given: (G : Subfunctor F) (p : F' ⟶ F) [hp : Epi p]
  proof: by
  apply le_antisymm
  · rw [image_le_iff]
  · intro i x hx
    simp only [NatTrans.epi_iff_epi_app, epi_iff_surjective] at hp
    obtain ⟨y, rfl⟩ := hp _ x
    exact ⟨y, hx, rfl⟩

中文:
引理 preimage_image_of_epi
  条件: (G : 子函子 F) (p : F' ⟶ F) [hp : 满态射 p]
  证明: by
  apply le_antisymm
  · rw [image_le_iff]
  · intro i x hx
    simp only [NatTrans.epi_iff_epi_app, epi_iff_surjective] at hp
    obtain ⟨y, rfl⟩ := hp _ x
    exact ⟨y, hx, rfl⟩

Depends on / 依赖: NatTrans, NatTrans.epi_iff_epi_app, epi_iff_epi_app, epi_iff_surjective, image_le_iff, le_antisymm
-/
lemma preimage_image_of_epi (G : Subfunctor F) (p : F' ⟶ F) [hp : Epi p] :
    (G.preimage p).image p = G := by
  apply le_antisymm
  · rw [image_le_iff]
  · intro i x hx
    simp only [NatTrans.epi_iff_epi_app, epi_iff_surjective] at hp
    obtain ⟨y, rfl⟩ := hp _ x
    exact ⟨y, hx, rfl⟩

end preimage

end Subfunctor

end CategoryTheory
