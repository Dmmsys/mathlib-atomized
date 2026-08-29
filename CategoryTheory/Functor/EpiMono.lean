/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Preservation and reflection of monomorphisms and epimorphisms

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/

@[expose] public section


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

to_dual_name_hint Left Right

/--
Definition of `PreservesMonomorphisms` / `PreservesMonomorphisms` 的定义

English:
class PreservesMonomorphisms
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves : forall {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)

中文:
类 保持Monomorphisms
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves : 对任意 {X Y : C} (f : X ⟶ Y) [单态射 f], 单态射 (F.map f)
-/
class PreservesMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
  preserves : forall {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
@[to_dual]
/--
Definition of `PreservesEpimorphisms` / `PreservesEpimorphisms` 的定义

English:
class PreservesEpimorphisms
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves : forall {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)

中文:
类 保持Epimorphisms
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves : 对任意 {X Y : C} (f : X ⟶ Y) [满态射 f], 满态射 (F.map f)
-/
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
  preserves : forall {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)

@[to_dual]
/--
Instance `map_epi` / 实例 `map_epi`

English:
instance map_epi
  signature: (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f]
  body: PreservesEpimorphisms.preserves f

中文:
实例 map_epi
  签名: (F : C ⥤ D) [保持Epimorphisms F] {X Y : C} (f : X ⟶ Y) [满态射 f]
  定义体: PreservesEpimorphisms.preserves f

Depends on / 依赖: PreservesEpimorphisms, PreservesEpimorphisms.preserves, preserves
-/
instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (F.map f) :=
  PreservesEpimorphisms.preserves f

/--
Definition of `ReflectsMonomorphisms` / `ReflectsMonomorphisms` 的定义

English:
class ReflectsMonomorphisms
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall {X Y : C} (f : X ⟶ Y), Mono (F.map f) -> Mono f

中文:
类 反映单态射
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 {X Y : C} (f : X ⟶ Y), 单态射 (F.map f) -> 单态射 f
-/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
  monomorphisms. -/
  reflects : forall {X Y : C} (f : X ⟶ Y), Mono (F.map f) -> Mono f

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
epimorphisms. -/
@[to_dual]
/--
Definition of `ReflectsEpimorphisms` / `ReflectsEpimorphisms` 的定义

English:
class ReflectsEpimorphisms
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall {X Y : C} (f : X ⟶ Y), Epi (F.map f) -> Epi f

中文:
类 反映满态射
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 {X Y : C} (f : X ⟶ Y), 满态射 (F.map f) -> 满态射 f
-/
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
  epimorphisms. -/
  reflects : forall {X Y : C} (f : X ⟶ Y), Epi (F.map f) -> Epi f

@[to_dual]
/--
theorem `epi_of_epi_map` / 定理 `epi_of_epi_map`

English:
theorem epi_of_epi_map
  statement: (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
  proof: ReflectsEpimorphisms.reflects f h

@[to_dual]

中文:
定理 epi_of_epi_map
  结论: (F : C ⥤ D) [反映满态射 F] {X Y : C} {f : X ⟶ Y}
  证明: ReflectsEpimorphisms.reflects f h

@[to_dual]

Depends on / 依赖: ReflectsEpimorphisms, ReflectsEpimorphisms.reflects, reflects
-/
theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h

@[to_dual]
/--
Instance `preservesMonomorphisms_comp` / 实例 `preservesMonomorphisms_comp`

English:
instance preservesMonomorphisms_comp
  signature: (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
  body: by
    rw [comp_map]
    exact inferInstance

@[to_dual]

中文:
实例 preservesMonomorphisms_comp
  签名: (F : C ⥤ D) (G : D ⥤ E) [保持Monomorphisms F]
  定义体: by
    rw [comp_map]
    exact inferInstance

@[to_dual]

Depends on / 依赖: comp_map
-/
instance preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
    [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G) where
  preserves f h := by
    rw [comp_map]
    exact inferInstance

@[to_dual]
/--
Instance `reflectsMonomorphisms_comp` / 实例 `reflectsMonomorphisms_comp`

English:
instance reflectsMonomorphisms_comp
  signature: (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
  body: F.mono_of_mono_map (G.mono_of_mono_map h)

@[to_dual]

中文:
实例 reflectsMonomorphisms_comp
  签名: (F : C ⥤ D) (G : D ⥤ E) [反映单态射 F]
  定义体: F.mono_of_mono_map (G.mono_of_mono_map h)

@[to_dual]

Depends on / 依赖: F.mono_of_mono_map, G.mono_of_mono_map, mono_of_mono_map
-/
instance reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
    [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G) where
  reflects _ h := F.mono_of_mono_map (G.mono_of_mono_map h)

@[to_dual]
/--
theorem `preservesEpimorphisms_of_preserves_of_reflects` / 定理 `preservesEpimorphisms_of_preserves_of_reflects`

English:
theorem preservesEpimorphisms_of_preserves_of_reflects
  statement: (F : C ⥤ D) (G : D ⥤ E)
  proof: ⟨fun f _ => G.epi_of_epi_map show Epi ((F ⋙ G).map f) from inferInstance⟩

@[to_dual]

中文:
定理 preservesEpimorphisms_of_preserves_of_reflects
  结论: (F : C ⥤ D) (G : D ⥤ E)
  证明: ⟨fun f _ => G.epi_of_epi_map show Epi ((F ⋙ G).map f) from inferInstance⟩

@[to_dual]

Depends on / 依赖: G.epi_of_epi_map, epi_of_epi_map
-/
theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
⟨fun f _ => G.epi_of_epi_map show Epi ((F ⋙ G).map f) from inferInstance⟩

@[to_dual]
/--
theorem `reflectsEpimorphisms_of_preserves_of_reflects` / 定理 `reflectsEpimorphisms_of_preserves_of_reflects`

English:
theorem reflectsEpimorphisms_of_preserves_of_reflects
  statement: (F : C ⥤ D) (G : D ⥤ E)
  proof: ⟨fun f _ => (F ⋙ G).epi_of_epi_map show Epi (G.map (F.map f)) from inferInstance⟩

@[to_dual]

中文:
定理 reflectsEpimorphisms_of_preserves_of_reflects
  结论: (F : C ⥤ D) (G : D ⥤ E)
  证明: ⟨fun f _ => (F ⋙ G).epi_of_epi_map show Epi (G.map (F.map f)) from inferInstance⟩

@[to_dual]

Depends on / 依赖: F.map, G.map, epi_of_epi_map
-/
theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
⟨fun f _ => (F ⋙ G).epi_of_epi_map show Epi (G.map (F.map f)) from inferInstance⟩

@[to_dual]
/--
lemma `PreservesMonomorphisms.of_natTrans` / 引理 `PreservesMonomorphisms.of_natTrans`

English:
lemma PreservesMonomorphisms.of_natTrans
  statement: {F G : C ⥤ D} [PreservesMonomorphisms F]
  proof: by
    suffices Mono (G.map π ≫ f.app Y) from mono_of_mono (G.map π) (f.app Y)
    rw [f.naturality π]
    infer_instance

@[to_dual]

中文:
引理 保持Monomorphisms.of_natTrans
  结论: {F G : C ⥤ D} [保持Monomorphisms F]
  证明: by
    suffices Mono (G.map π ≫ f.app Y) from mono_of_mono (G.map π) (f.app Y)
    rw [f.naturality π]
    infer_instance

@[to_dual]

Depends on / 依赖: G.map, f.app, f.naturality, infer_instance, mono_of_mono, naturality
-/
lemma PreservesMonomorphisms.of_natTrans {F G : C ⥤ D} [PreservesMonomorphisms F]
    (f : G ⟶ F) [forall X, Mono (f.app X)] :
    PreservesMonomorphisms G where
  preserves {X Y} π hπ := by
    suffices Mono (G.map π ≫ f.app Y) from mono_of_mono (G.map π) (f.app Y)
    rw [f.naturality π]
    infer_instance

@[to_dual]
/--
theorem `PreservesMonomorphisms.of_iso` / 定理 `PreservesMonomorphisms.of_iso`

English:
theorem PreservesMonomorphisms.of_iso
  given: {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G)
  proof: of_natTrans α.inv

@[to_dual]

中文:
定理 保持Monomorphisms.of_iso
  条件: {F G : C ⥤ D} [保持Monomorphisms F] (α : F ≅ G)
  证明: of_natTrans α.inv

@[to_dual]

Depends on / 依赖: of_natTrans
-/
theorem PreservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  of_natTrans α.inv

@[to_dual]
/--
theorem `PreservesMonomorphisms.iso_iff` / 定理 `PreservesMonomorphisms.iso_iff`

English:
theorem PreservesMonomorphisms.iso_iff
  given: {F G : C ⥤ D} (α : F ≅ G)
  proof: ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[to_dual]

中文:
定理 保持Monomorphisms.iso_iff
  条件: {F G : C ⥤ D} (α : F ≅ G)
  证明: ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[to_dual]

Depends on / 依赖: of_iso
-/
theorem PreservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[to_dual]
/--
theorem `ReflectsMonomorphisms.of_iso` / 定理 `ReflectsMonomorphisms.of_iso`

English:
theorem ReflectsMonomorphisms.of_iso
  given: {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G)
  proof: by
    apply F.mono_of_mono_map
    suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ mono_comp _ _
    simp

@[to_dual]

中文:
定理 反映单态射.of_iso
  条件: {F G : C ⥤ D} [反映单态射 F] (α : F ≅ G)
  证明: by
    apply F.mono_of_mono_map
    suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ mono_comp _ _
    simp

@[to_dual]

Depends on / 依赖: F.map, F.mono_of_mono_map, G.map, mono_comp, mono_of_mono_map
-/
theorem ReflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G where
  reflects {X Y} f h := by
    apply F.mono_of_mono_map
    suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ mono_comp _ _
    simp

@[to_dual]
/--
theorem `ReflectsMonomorphisms.iso_iff` / 定理 `ReflectsMonomorphisms.iso_iff`

English:
theorem ReflectsMonomorphisms.iso_iff
  given: {F G : C ⥤ D} (α : F ≅ G)
  proof: ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_natTrans := PreservesMonomorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_iso := PreservesMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.iso_iff := PreservesMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.of_iso := ReflectsMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.iso_iff := ReflectsMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_natTrans := PreservesEpimorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_iso := PreservesEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.iso_iff := PreservesEpimorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.of_iso := ReflectsEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.iso_iff := ReflectsEpimorphisms.iso_iff

@[to_dual]

中文:
定理 反映单态射.iso_iff
  条件: {F G : C ⥤ D} (α : F ≅ G)
  证明: ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_natTrans := PreservesMonomorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_iso := PreservesMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.iso_iff := PreservesMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.of_iso := ReflectsMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.iso_iff := ReflectsMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_natTrans := PreservesEpimorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_iso := PreservesEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.iso_iff := PreservesEpimorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.of_iso := ReflectsEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.iso_iff := ReflectsEpimorphisms.iso_iff

@[to_dual]

Depends on / 依赖: of_iso
-/
theorem ReflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_natTrans := PreservesMonomorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.of_iso := PreservesMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.iso_iff := PreservesMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.of_iso := ReflectsMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.iso_iff := ReflectsMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_natTrans := PreservesEpimorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.of_iso := PreservesEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.iso_iff := PreservesEpimorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.of_iso := ReflectsEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.iso_iff := ReflectsEpimorphisms.iso_iff

@[to_dual]
/--
theorem `preservesEpimorphisms_of_adjunction` / 定理 `preservesEpimorphisms_of_adjunction`

English:
theorem preservesEpimorphisms_of_adjunction
  given: {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  proof: ⟨by
    intro Z g h H
    replace H := congr_arg (adj.homEquiv X Z) H
    rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
      Equiv.apply_eq_iff_eq] at H⟩

@[to_dual]

中文:
定理 preservesEpimorphisms_of_adjunction
  条件: {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  证明: ⟨by
    intro Z g h H
    replace H := congr_arg (adj.homEquiv X Z) H
    rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
      Equiv.apply_eq_iff_eq] at H⟩

@[to_dual]

Depends on / 依赖: Equiv.apply_eq_iff_eq, adj.homEquiv, adj.homEquiv_naturality_left, apply_eq_iff_eq, cancel_epi, congr_arg, homEquiv, homEquiv_naturality_left, replace
-/
theorem preservesEpimorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F where
  preserves {X Y} f hf := ⟨by
    intro Z g h H
    replace H := congr_arg (adj.homEquiv X Z) H
    rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
      Equiv.apply_eq_iff_eq] at H⟩

@[to_dual]
instance (priority := 100) preservesEpimorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preservesEpimorphisms_of_adjunction (Adjunction.ofIsLeftAdjoint F)

@[to_dual]
instance (priority := 100) reflectsMonomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms F where
  reflects {X} {Y} f _ :=
    ⟨fun {Z} g h hgh =>
      F.map_injective ((cancel_mono (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩

@[to_dual]
instance {F G : C ⥤ D} (f : F ⟶ G) [IsSplitEpi f] (X : C) : IsSplitEpi (f.app X) :=
  inferInstanceAs (IsSplitEpi (((evaluation C D).obj X).map f))

@[to_dual]
/--
lemma `PreservesEpimorphisms.ofRetract` / 引理 `PreservesEpimorphisms.ofRetract`

English:
lemma PreservesEpimorphisms.ofRetract
  given: {F G : C ⥤ D} (r : Retract G F) [F.PreservesEpimorphisms]
  proof: (PreservesEpimorphisms.of_natTrans r.r).preserves

@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.ofRetract := PreservesEpimorphisms.ofRetract
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.ofRetract := PreservesMonomorphisms.ofRetract

中文:
引理 保持Epimorphisms.ofRetract
  条件: {F G : C ⥤ D} (r : 收缩 G F) [F.保持Epimorphisms]
  证明: (PreservesEpimorphisms.of_natTrans r.r).preserves

@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.ofRetract := PreservesEpimorphisms.ofRetract
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.ofRetract := PreservesMonomorphisms.ofRetract

Depends on / 依赖: PreservesEpimorphisms, PreservesEpimorphisms.of_natTrans, of_natTrans, preserves
-/
lemma PreservesEpimorphisms.ofRetract {F G : C ⥤ D} (r : Retract G F) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves := (PreservesEpimorphisms.of_natTrans r.r).preserves

@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.ofRetract := PreservesEpimorphisms.ofRetract
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.ofRetract := PreservesMonomorphisms.ofRetract

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
@[to_dual
/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/]
/--
Definition of `splitEpiEquiv` / `splitEpiEquiv` 的定义

English:
definition splitEpiEquiv
  signature: [Full F] [Faithful F]
  body: f.map F
  invFun s := ⟨F.preimage s.section_, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitEpi.id⟩
  left_inv := by cat_disch
  right_inv x := by cat_disch

@[to_dual (attr := simp)]

中文:
定义 splitEpiEquiv
  签名: [满 F] [忠实 F]
  定义体: f.map F
  invFun s := ⟨F.preimage s.section_, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitEpi.id⟩
  left_inv := by cat_disch
  right_inv x := by cat_disch

@[to_dual (attr := simp)]

Depends on / 依赖: f.map
-/
noncomputable def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f) where
  toFun f := f.map F
  invFun s := ⟨F.preimage s.section_, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitEpi.id⟩
  left_inv := by cat_disch
  right_inv x := by cat_disch

@[to_dual (attr := simp)]
/--
theorem `isSplitEpi_iff` / 定理 `isSplitEpi_iff`

English:
theorem isSplitEpi_iff
  given: [Full F] [Faithful F]
  statement: IsSplitEpi (F.map f) ↔ IsSplitEpi f
  proof: by
  constructor
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).invFun h.exists_splitEpi.some)
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).toFun h.exists_splitEpi.some)

@[to_dual (attr := simp)]

中文:
定理 isSplitEpi_iff
  条件: [满 F] [忠实 F]
  结论: 是分裂满态射 (F.map f) ↔ 是分裂满态射 f
  证明: by
  constructor
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).invFun h.exists_splitEpi.some)
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).toFun h.exists_splitEpi.some)

@[to_dual (attr := simp)]

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, exists_splitEpi, h.exists_splitEpi.some, invFun, splitEpiEquiv
-/
theorem isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f := by
  constructor
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).invFun h.exists_splitEpi.some)
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).toFun h.exists_splitEpi.some)

@[to_dual (attr := simp)]
/--
theorem `epi_map_iff_epi` / 定理 `epi_map_iff_epi`

English:
theorem epi_map_iff_epi
  given: [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F]
  proof: by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f

中文:
定理 epi_map_iff_epi
  条件: [hF₁ : 保持Epimorphisms F] [hF₂ : 反映满态射 F]
  证明: by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f

Depends on / 依赖: F.epi_of_epi_map, F.map_epi, epi_of_epi_map, map_epi
-/
theorem epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F] :
    Epi (F.map f) ↔ Epi f := by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f

/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `SplitEpiCategory`,
then `D` also is. -/
@[to_dual
/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `SplitMonoCategory`,
then `D` also is. -/]
/--
theorem `splitEpiCategoryImpOfIsEquivalence` / 定理 `splitEpiCategoryImpOfIsEquivalence`

English:
theorem splitEpiCategoryImpOfIsEquivalence
  given: [IsEquivalence F] [SplitEpiCategory C]
  proof: ⟨fun {X} {Y} f => by
    intro
    rw [← F.inv.isSplitEpi_iff f]
    apply isSplitEpi_of_epi⟩

中文:
定理 splitEpiCategoryImpOfIsEquivalence
  条件: [是等价 F] [分裂满态射范畴 C]
  证明: ⟨fun {X} {Y} f => by
    intro
    rw [← F.inv.isSplitEpi_iff f]
    apply isSplitEpi_of_epi⟩

Depends on / 依赖: F.inv.isSplitEpi_iff, isSplitEpi_iff, isSplitEpi_of_epi
-/
theorem splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun {X} {Y} f => by
    intro
    rw [← F.inv.isSplitEpi_iff f]
    apply isSplitEpi_of_epi⟩

end

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

@[to_dual]
/--
theorem `strongEpi_map_of_strongEpi` / 定理 `strongEpi_map_of_strongEpi`

English:
theorem strongEpi_map_of_strongEpi
  statement: (adj : F ⊣ F') (f : A ⟶ B) [F'.PreservesMonomorphisms]
  proof: ⟨inferInstance, fun X Y Z => by
    intro
    rw [adj.hasLiftingProperty_iff]
    infer_instance⟩

@[to_dual]

中文:
定理 strongEpi_map_of_strongEpi
  结论: (adj : F ⊣ F') (f : A ⟶ B) [F'.保持Monomorphisms]
  证明: ⟨inferInstance, fun X Y Z => by
    intro
    rw [adj.hasLiftingProperty_iff]
    infer_instance⟩

@[to_dual]

Depends on / 依赖: adj.hasLiftingProperty_iff, hasLiftingProperty_iff, infer_instance
-/
theorem strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [F'.PreservesMonomorphisms]
    [F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f) :=
  ⟨inferInstance, fun X Y Z => by
    intro
    rw [adj.hasLiftingProperty_iff]
    infer_instance⟩

@[to_dual]
/--
Instance `strongEpi_map_of_isEquivalence` / 实例 `strongEpi_map_of_isEquivalence`

English:
instance strongEpi_map_of_isEquivalence
  signature: [F.IsEquivalence] (f : A ⟶ B) [_h : StrongEpi f]
  body: F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f

@[to_dual]

中文:
实例 strongEpi_map_of_isEquivalence
  签名: [F.是等价] (f : A ⟶ B) [_h : 强满态射 f]
  定义体: F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f

@[to_dual]

Depends on / 依赖: F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi, asEquivalence, strongEpi_map_of_strongEpi, toAdjunction
-/
instance strongEpi_map_of_isEquivalence [F.IsEquivalence] (f : A ⟶ B) [_h : StrongEpi f] :
    StrongEpi (F.map f) :=
  F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f

@[to_dual]
instance (adj : F ⊣ F') {X : C} {Y : D} (f : F.obj X ⟶ Y) [hf : Mono f] [F.ReflectsMonomorphisms] :
    Mono (adj.homEquiv _ _ f) :=
F.mono_of_mono_map by
    rw [← (homEquiv adj X Y).symm_apply_apply f] at hf
    exact mono_of_mono_fac (adj.homEquiv_counit _ _ _).symm

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

@[to_dual (attr := simp)]
/--
theorem `strongEpi_map_iff_strongEpi_of_isEquivalence` / 定理 `strongEpi_map_iff_strongEpi_of_isEquivalence`

English:
theorem strongEpi_map_iff_strongEpi_of_isEquivalence
  given: [IsEquivalence F]
  proof: by
  constructor
  · intro
    have e : Arrow.mk f ≅ Arrow.mk (F.inv.map (F.map f)) :=
      Arrow.isoOfNatIso F.asEquivalence.unitIso (Arrow.mk f)
    rw [StrongEpi.iff_of_arrow_iso e]
    infer_instance
  · intro
    infer_instance

中文:
定理 strongEpi_map_iff_strongEpi_of_isEquivalence
  条件: [是等价 F]
  证明: by
  constructor
  · intro
    have e : Arrow.mk f ≅ Arrow.mk (F.inv.map (F.map f)) :=
      Arrow.isoOfNatIso F.asEquivalence.unitIso (Arrow.mk f)
    rw [StrongEpi.iff_of_arrow_iso e]
    infer_instance
  · intro
    infer_instance

Depends on / 依赖: Arrow.isoOfNatIso, Arrow.mk, F.asEquivalence.unitIso, F.inv.map, F.map, StrongEpi, StrongEpi.iff_of_arrow_iso, asEquivalence, iff_of_arrow_iso, infer_instance, isoOfNatIso, unitIso
-/
theorem strongEpi_map_iff_strongEpi_of_isEquivalence [IsEquivalence F] :
    StrongEpi (F.map f) ↔ StrongEpi f := by
  constructor
  · intro
    have e : Arrow.mk f ≅ Arrow.mk (F.inv.map (F.map f)) :=
      Arrow.isoOfNatIso F.asEquivalence.unitIso (Arrow.mk f)
    rw [StrongEpi.iff_of_arrow_iso e]
    infer_instance
  · intro
    infer_instance

end CategoryTheory.Functor
