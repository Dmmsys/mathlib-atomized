/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Properties of morphisms in a path category.

We provide a formulation of induction principles for morphisms in a path category in terms of
`MorphismProperty`. This file is separate from `Mathlib/CategoryTheory/PathCategory/Basic.lean` in
order to reduce transitive imports.

We also define a morpism property `W.paths : MorphismProperty (Paths C)` for any
`W : MorphismProperty C`, consisting of all paths in `C` that consist only of morphisms in `W`. -/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory.Paths

section
variable (V : Type u₁) [Quiver.{v₁} V]

/--
lemma `morphismProperty_eq_top` / 引理 `morphismProperty_eq_top`

English:
lemma morphismProperty_eq_top
  proof: by
  ext; constructor
  · simp
  · exact fun _ => induction (fun f => P f) id comp _

中文:
引理 morphismProperty_eq_top
  证明: by
  ext; constructor
  · simp
  · exact fun _ => induction (fun f => P f) id comp _
-/
lemma morphismProperty_eq_top
    (P : MorphismProperty (Paths V))
    (id : forall {v : V}, P (𝟙 ((of V).obj v)))
    (comp : forall {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p -> P (p ≫ (of V).map q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ => induction (fun f => P f) id comp _

/--
lemma `morphismProperty_eq_top'` / 引理 `morphismProperty_eq_top'`

English:
lemma morphismProperty_eq_top'
  proof: by
  ext; constructor
  · simp
  · exact fun _ => induction' (fun f => P f) id comp _

中文:
引理 morphismProperty_eq_top'
  证明: by
  ext; constructor
  · simp
  · exact fun _ => induction' (fun f => P f) id comp _
-/
lemma morphismProperty_eq_top'
    (P : MorphismProperty (Paths V))
    (id : forall {v : V}, P (𝟙 ((of V).obj v)))
    (comp : forall {u v w : V}
      (p : u ⟶ v) (q : (of V).obj v ⟶ (of V).obj w), P q -> P ((of V).map p ≫ q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ => induction' (fun f => P f) id comp _

/--
lemma `morphismProperty_eq_top_of_isMultiplicative` / 引理 `morphismProperty_eq_top_of_isMultiplicative`

English:
lemma morphismProperty_eq_top_of_isMultiplicative
  statement: (P : MorphismProperty (Paths V))
  proof: morphismProperty_eq_top _ _ (P.id_mem _) (fun _ q hp => P.comp_mem _ _ hp (hP q))

中文:
引理 morphismProperty_eq_top_of_isMultiplicative
  结论: (P : Morphism命题erty (Paths V))
  证明: morphismProperty_eq_top _ _ (P.id_mem _) (fun _ q hp => P.comp_mem _ _ hp (hP q))

Depends on / 依赖: P.comp_mem, P.id_mem, comp_mem, id_mem, morphismProperty_eq_top
-/
lemma morphismProperty_eq_top_of_isMultiplicative (P : MorphismProperty (Paths V))
    [P.IsMultiplicative]
    (hP : forall {u v : V} (p : u ⟶ v), P ((of V).map p)) : P = ⊤ :=
  morphismProperty_eq_top _ _ (P.id_mem _) (fun _ q hp => P.comp_mem _ _ hp (hP q))
end
section

variable {C : Type*} [Category* C] {V : Type u₁} [Quiver.{v₁} V]

set_option backward.isDefEq.respectTransparency.types false in
/-- A natural transformation between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps]
/--
Definition of `liftNatTrans` / `liftNatTrans` 的定义

English:
definition liftNatTrans
  signature: {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.obj v ⟶ G.obj v))
  body: α_app
  naturality := by
    apply MorphismProperty.of_eq_top
      (P := MorphismProperty.naturalityProperty (F₁ := F) α_app)
    exact morphismProperty_eq_top_of_isMultiplicative _ _ α_nat

中文:
定义 liftNatTrans
  签名: {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.obj v ⟶ G.obj v))
  定义体: α_app
  naturality := by
    apply MorphismProperty.of_eq_top
      (P := MorphismProperty.naturalityProperty (F₁ := F) α_app)
    exact morphismProperty_eq_top_of_isMultiplicative _ _ α_nat
-/
def liftNatTrans {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.obj v ⟶ G.obj v))
    (α_nat : {X Y : V} -> (f : X ⟶ Y) ->
      F.map (Quiver.Hom.toPath f) ≫ α_app Y = α_app X ≫ G.map (Quiver.Hom.toPath f)) : F ⟶ G where
  app := α_app
  naturality := by
    apply MorphismProperty.of_eq_top
      (P := MorphismProperty.naturalityProperty (F₁ := F) α_app)
    exact morphismProperty_eq_top_of_isMultiplicative _ _ α_nat

/-- A natural isomorphism between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps!]
/--
Definition of `liftNatIso` / `liftNatIso` 的定义

English:
definition liftNatIso
  signature: {C} [Category* C] {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.obj v ≅ G.obj v))
  body: NatIso.ofComponents α_app (fun f => (liftNatTrans (fun v => (α_app v).hom) α_nat).naturality f)

中文:
定义 liftNatIso
  签名: {C} [Category* C] {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.obj v ≅ G.obj v))
  定义体: NatIso.ofComponents α_app (fun f => (liftNatTrans (fun v => (α_app v).hom) α_nat).naturality f)

Depends on / 依赖: NatIso, NatIso.ofComponents, liftNatTrans, naturality, ofComponents
-/
def liftNatIso {C} [Category* C] {F G : Paths V ⥤ C} (α_app : (v : V) -> (F.obj v ≅ G.obj v))
    (α_nat : {X Y : V} -> (f : X ⟶ Y) ->
      F.map (Quiver.Hom.toPath f) ≫ (α_app Y).hom = (α_app X).hom ≫ G.map (Quiver.Hom.toPath f)) :
    F ≅ G :=
  NatIso.ofComponents α_app (fun f => (liftNatTrans (fun v => (α_app v).hom) α_nat).naturality f)

end

end CategoryTheory.Paths

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

open Quiver

/--
Definition of `paths` / `paths` 的定义

English:
definition paths
  signature: (W : MorphismProperty C)
  body: fun _ _ p => p.rec True fun _ f P => P ∧ W f

@[simp]

中文:
定义 paths
  签名: (W : Morphism命题erty C)
  定义体: fun _ _ p => p.rec True fun _ f P => P ∧ W f

@[simp]

Depends on / 依赖: p.rec
-/
def paths (W : MorphismProperty C) : MorphismProperty (Paths C) :=
  fun _ _ p => p.rec True fun _ f P => P ∧ W f

@[simp]
/--
lemma `nil_mem_paths` / 引理 `nil_mem_paths`

English:
lemma nil_mem_paths
  given: {W : MorphismProperty C} {X : C}
  statement: W.paths (.nil (a := X))
  proof: trivial

中文:
引理 nil_mem_paths
  条件: {W : Morphism命题erty C} {X : C}
  结论: W.paths (.nil (a := X))
  证明: trivial
-/
lemma nil_mem_paths {W : MorphismProperty C} {X : C} : W.paths (.nil (a := X)) := trivial

/--
lemma `cons_mem_paths` / 引理 `cons_mem_paths`

English:
lemma cons_mem_paths
  statement: {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z}
  proof: ⟨hp, hf⟩

@[simp]

中文:
引理 cons_mem_paths
  结论: {W : Morphism命题erty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z}
  证明: ⟨hp, hf⟩

@[simp]
-/
lemma cons_mem_paths {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z}
    (hp : W.paths p) (hf : W f) : W.paths (p.cons f) :=
  ⟨hp, hf⟩

@[simp]
/--
lemma `cons_mem_paths_iff` / 引理 `cons_mem_paths_iff`

English:
lemma cons_mem_paths_iff
  given: {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z}
  proof: Iff.rfl

中文:
引理 cons_mem_paths_iff
  条件: {W : Morphism命题erty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma cons_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z} :
    W.paths (p.cons f) ↔ W.paths p ∧ W f :=
  Iff.rfl

/--
lemma `toPath_mem_paths` / 引理 `toPath_mem_paths`

English:
lemma toPath_mem_paths
  given: {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} (hf : W f)
  proof: ⟨trivial, hf⟩

@[simp]

中文:
引理 toPath_mem_paths
  条件: {W : Morphism命题erty C} {X Y : C} {f : X ⟶ Y} (hf : W f)
  证明: ⟨trivial, hf⟩

@[simp]
-/
lemma toPath_mem_paths {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} (hf : W f) :
    W.paths f.toPath :=
  ⟨trivial, hf⟩

@[simp]
/--
lemma `toPath_mem_paths_iff` / 引理 `toPath_mem_paths_iff`

English:
lemma toPath_mem_paths_iff
  given: {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y}
  proof: ⟨fun h => h.2, toPath_mem_paths⟩

@[simp]

中文:
引理 toPath_mem_paths_iff
  条件: {W : Morphism命题erty C} {X Y : C} {f : X ⟶ Y}
  证明: ⟨fun h => h.2, toPath_mem_paths⟩

@[simp]

Depends on / 依赖: toPath_mem_paths
-/
lemma toPath_mem_paths_iff {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} :
    W.paths f.toPath ↔ W f :=
  ⟨fun h => h.2, toPath_mem_paths⟩

@[simp]
/--
lemma `comp_mem_paths_iff` / 引理 `comp_mem_paths_iff`

English:
lemma comp_mem_paths_iff
  given: {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {q : Path Y Z}
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hp, hq⟩ => ?_⟩
  · induction q with
    | nil => simpa using h
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact h' h.1
  · induction q with
    | nil => simp
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact ⟨h' h.1, h.2⟩
  · induct

中文:
引理 comp_mem_paths_iff
  条件: {W : Morphism命题erty C} {X Y Z : C} {p : Path X Y} {q : Path Y Z}
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hp, hq⟩ => ?_⟩
  · induction q with
    | nil => simpa using h
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact h' h.1
  · induction q with
    | nil => simp
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact ⟨h' h.1, h.2⟩
  · induct

Depends on / 依赖: Path.comp_cons, comp_cons
-/
lemma comp_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {q : Path Y Z} :
    W.paths (p.comp q) ↔ W.paths p ∧ W.paths q := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hp, hq⟩ => ?_⟩
  · induction q with
    | nil => simpa using h
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact h' h.1
  · induction q with
    | nil => simp
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact ⟨h' h.1, h.2⟩
  · induction q with
    | nil => exact hp
    | cons q q' h => exact ⟨h ⟨hp, hq.1⟩ hq.1, hq.2⟩

@[simp]
/--
lemma `comp_mem_paths_iff'` / 引理 `comp_mem_paths_iff'`

English:
lemma comp_mem_paths_iff'
  given: {W : MorphismProperty C} {X Y Z : Paths C} {p : X ⟶ Y} {q : Y ⟶ Z}
  proof: W.comp_mem_paths_iff

中文:
引理 comp_mem_paths_iff'
  条件: {W : Morphism命题erty C} {X Y Z : Paths C} {p : X ⟶ Y} {q : Y ⟶ Z}
  证明: W.comp_mem_paths_iff

Depends on / 依赖: W.comp_mem_paths_iff, comp_mem_paths_iff
-/
lemma comp_mem_paths_iff' {W : MorphismProperty C} {X Y Z : Paths C} {p : X ⟶ Y} {q : Y ⟶ Z} :
    W.paths (p ≫ q) ↔ W.paths p ∧ W.paths q :=
  W.comp_mem_paths_iff

instance (W : MorphismProperty C) : W.paths.IsMultiplicative where
  id_mem _ := nil_mem_paths
  comp_mem _ _ hf hg := W.comp_mem_paths_iff'.2 ⟨hf, hg⟩

/-- If `W` and `W'` are morphism properties on `C` such that `W ≤ W'`, then `W.paths ≤ W'.paths`. -/
@[gcongr]
/--
lemma `monotone_paths` / 引理 `monotone_paths`

English:
lemma monotone_paths
  statement: Monotone (paths (C := C))
  proof: fun _ _ h _ _ p => p.rec (fun _ => trivial) (fun _ _ hp' hp => ⟨hp' hp.1, h _ hp.2⟩)

中文:
引理 monotone_paths
  结论: Monotone (paths (C := C))
  证明: fun _ _ h _ _ p => p.rec (fun _ => trivial) (fun _ _ hp' hp => ⟨hp' hp.1, h _ hp.2⟩)
-/
lemma monotone_paths : Monotone (paths (C := C)) :=
  fun _ _ h _ _ p => p.rec (fun _ => trivial) (fun _ _ hp' hp => ⟨hp' hp.1, h _ hp.2⟩)

/--
lemma `composePath_mem_of_id_mem` / 引理 `composePath_mem_of_id_mem`

English:
lemma composePath_mem_of_id_mem
  statement: (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
  proof: by
  revert hp
  exact p.rec (by simpa) fun p f hp hp' => W.comp_mem _ _ (hp hp'.1) hp'.2

中文:
引理 composePath_mem_of_id_mem
  结论: (W : Morphism命题erty C) [W.IsStableUnderComposition] {X Y : C}
  证明: by
  revert hp
  exact p.rec (by simpa) fun p f hp hp' => W.comp_mem _ _ (hp hp'.1) hp'.2

Depends on / 依赖: W.comp_mem, comp_mem, p.rec, revert
-/
lemma composePath_mem_of_id_mem (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
    {p : Path X Y} (hp : W.paths p) (h : W (𝟙 X)) : W (composePath p) := by
  revert hp
  exact p.rec (by simpa) fun p f hp hp' => W.comp_mem _ _ (hp hp'.1) hp'.2

/--
lemma `composePath_mem_of_length_pos` / 引理 `composePath_mem_of_length_pos`

English:
lemma composePath_mem_of_length_pos
  statement: (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
  proof: by
  revert hp h
  refine p.rec (by simp) fun p f hp hp' hp'' => ?_
  cases p
  · simpa [paths] using hp'
  · refine W.comp_mem _ _ (hp hp'.1 (by simp)) hp'.2

中文:
引理 composePath_mem_of_length_pos
  结论: (W : Morphism命题erty C) [W.IsStableUnderComposition] {X Y : C}
  证明: by
  revert hp h
  refine p.rec (by simp) fun p f hp hp' hp'' => ?_
  cases p
  · simpa [paths] using hp'
  · refine W.comp_mem _ _ (hp hp'.1 (by simp)) hp'.2

Depends on / 依赖: W.comp_mem, comp_mem, p.rec, revert
-/
lemma composePath_mem_of_length_pos (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
    {p : Path X Y} (hp : W.paths p) (h : 0 < p.length) : W (composePath p) := by
  revert hp h
  refine p.rec (by simp) fun p f hp hp' hp'' => ?_
  cases p
  · simpa [paths] using hp'
  · refine W.comp_mem _ _ (hp hp'.1 (by simp)) hp'.2

/--
lemma `composePath_mem` / 引理 `composePath_mem`

English:
lemma composePath_mem
  statement: (W : MorphismProperty C) [W.IsMultiplicative] {X Y : C}
  proof: W.composePath_mem_of_id_mem hp W.id_mem X

中文:
引理 composePath_mem
  结论: (W : Morphism命题erty C) [W.IsMultiplicative] {X Y : C}
  证明: W.composePath_mem_of_id_mem hp W.id_mem X

Depends on / 依赖: W.composePath_mem_of_id_mem, W.id_mem, composePath_mem_of_id_mem, id_mem
-/
lemma composePath_mem (W : MorphismProperty C) [W.IsMultiplicative] {X Y : C}
    {p : Path X Y} (hp : W.paths p) : W (composePath p) :=
W.composePath_mem_of_id_mem hp W.id_mem X

/--
lemma `paths_le_inverseImage` / 引理 `paths_le_inverseImage`

English:
lemma paths_le_inverseImage
  given: (W : MorphismProperty C) [W.IsMultiplicative]
  proof: fun _ _ _ => W.composePath_mem

中文:
引理 paths_le_inverseImage
  条件: (W : Morphism命题erty C) [W.IsMultiplicative]
  证明: fun _ _ _ => W.composePath_mem

Depends on / 依赖: W.composePath_mem, composePath_mem
-/
lemma paths_le_inverseImage (W : MorphismProperty C) [W.IsMultiplicative] :
    W.paths <= W.inverseImage (pathComposition C) :=
  fun _ _ _ => W.composePath_mem

set_option backward.isDefEq.respectTransparency.types false in
instance (W : MorphismProperty C) : IsMultiplicative (W.paths.strictMap (pathComposition C)) where
  id_mem X := W.paths.map_mem_strictMap (pathComposition C) _ (W.paths.id_mem X)
  comp_mem := fun _ _ ⟨hp⟩ ⟨hq⟩ => by
simpa using! W.paths.map_mem_strictMap (pathComposition C) _ W.paths.comp_mem _ _ hp hq

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `multiplicativeClosure_eq_strictMap_paths` / 引理 `multiplicativeClosure_eq_strictMap_paths`

English:
lemma multiplicativeClosure_eq_strictMap_paths
  given: (W : MorphismProperty C)
  proof: by
  refine le_antisymm ?_ fun _ _ _ ⟨h⟩ => ?_
  · refine (W.multiplicativeClosure_le_iff _).2 fun X Y f hf => ?_
    simpa using! W.paths.map_mem_strictMap (pathComposition C) f.toPath (by simpa)
· exact composePath_mem _ monotone_paths W.le_multiplicativeClosure _ h

中文:
引理 multiplicativeClosure_eq_strictMap_paths
  条件: (W : Morphism命题erty C)
  证明: by
  refine le_antisymm ?_ fun _ _ _ ⟨h⟩ => ?_
  · refine (W.multiplicativeClosure_le_iff _).2 fun X Y f hf => ?_
    simpa using! W.paths.map_mem_strictMap (pathComposition C) f.toPath (by simpa)
· exact composePath_mem _ monotone_paths W.le_multiplicativeClosure _ h

Depends on / 依赖: W.le_multiplicativeClosure, W.multiplicativeClosure_le_iff, W.paths.map_mem_strictMap, composePath_mem, f.toPath, le_antisymm, le_multiplicativeClosure, map_mem_strictMap, monotone_paths, multiplicativeClosure_le_iff, pathComposition, toPath
-/
lemma multiplicativeClosure_eq_strictMap_paths (W : MorphismProperty C) :
    W.multiplicativeClosure = W.paths.strictMap (pathComposition C) := by
  refine le_antisymm ?_ fun _ _ _ ⟨h⟩ => ?_
  · refine (W.multiplicativeClosure_le_iff _).2 fun X Y f hf => ?_
    simpa using! W.paths.map_mem_strictMap (pathComposition C) f.toPath (by simpa)
· exact composePath_mem _ monotone_paths W.le_multiplicativeClosure _ h

end CategoryTheory.MorphismProperty
