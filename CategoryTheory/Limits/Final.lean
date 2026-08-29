/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Grothendieck

/-!
# Final and initial functors

A functor `F : C ⥤ D` is final if for every `d : D`,
the comma category of morphisms `d ⟶ F.obj c` is connected.

Dually, a functor `F : C ⥤ D` is initial if for every `d : D`,
the comma category of morphisms `F.obj c ⟶ d` is connected.

We show that right adjoints are examples of final functors, while
left adjoints are examples of initial functors.

For final functors, we prove that the following three statements are equivalent:
1. `F : C ⥤ D` is final.
2. Every functor `G : D ⥤ E` has a colimit if and only if `F ⋙ G` does,
   and these colimits are isomorphic via `colimit.pre G F`.
3. `colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit`.

Starting at 1. we show (in `coconesEquiv`) that
the categories of cocones over `G : D ⥤ E` and over `F ⋙ G` are equivalent.
(In fact, via an equivalence which does not change the cocone point.)
This readily implies 2., as `comp_hasColimit`, `hasColimit_of_comp`, and `colimitIso`.

From 2. we can specialize to `G = coyoneda.obj (op d)` to obtain 3., as `colimitCompCoyonedaIso`.

From 3., we prove 1. directly in `final_of_colimit_comp_coyoneda_iso_pUnit`.

Dually, we prove that if a functor `F : C ⥤ D` is initial, then any functor `G : D ⥤ E` has a
limit if and only if `F ⋙ G` does, and these limits are isomorphic via `limit.pre G F`.

In the end of the file, we characterize the finality of some important induced functors on the
(co)structured arrow category (`StructuredArrow.pre` and `CostructuredArrow.pre`) and on the
Grothendieck construction (`Grothendieck.pre` and `Grothendieck.map`).

## Naming
There is some discrepancy in the literature about naming; some say 'cofinal' instead of 'final'.
The explanation for this is that the 'co' prefix here is *not* the usual category-theoretic one
indicating duality, but rather indicating the sense of "along with".

## See also
In `CategoryTheory.Filtered.Final` we give additional equivalent conditions in the case that
`C` is filtered.

## Future work
Dualise condition 3 above and the implications 2 ⇒ 3 and 3 ⇒ 1 to initial functors.

## References
* https://stacks.math.columbia.edu/tag/09WN
* https://ncatlab.org/nlab/show/final+functor
* Borceux, Handbook of Categorical Algebra I, Section 2.11.
  (Note he reverses the roles of definition and main result relative to here!)
-/

@[expose] public section


noncomputable section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

namespace Functor

open Opposite

open CategoryTheory.Limits

section ArbitraryUniverse

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/--
A functor `F : C ⥤ D` is final if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c`
is connected. -/
@[stacks 04E6]
/--
Definition of `Final` / `Final` 的定义

English:
class Final
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - out((d : D)) : IsConnected (StructuredArrow d F)

中文:
类 Final
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - out((d : D)) : IsConnected (StructuredArrow d F)
-/
class Final (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (StructuredArrow d F)

attribute [instance] Final.out

/--
Definition of `Initial` / `Initial` 的定义

English:
class Initial
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - out((d : D)) : IsConnected (CostructuredArrow F d)

中文:
类 Initial
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - out((d : D)) : IsConnected (CostructuredArrow F d)
-/
class Initial (F : C ⥤ D) : Prop where
  out (d : D) : IsConnected (CostructuredArrow F d)

attribute [instance] Initial.out

/--
Instance `final_op_of_initial` / 实例 `final_op_of_initial`

English:
instance final_op_of_initial
  signature: (F : C ⥤ D) [Initial F]
  body: isConnected_of_equivalent (costructuredArrowOpEquivalence F (unop d))

中文:
实例 final_op_of_initial
  签名: (F : C ⥤ D) [Initial F]
  定义体: isConnected_of_equivalent (costructuredArrowOpEquivalence F (unop d))

Depends on / 依赖: costructuredArrowOpEquivalence, isConnected_of_equivalent
-/
instance final_op_of_initial (F : C ⥤ D) [Initial F] : Final F.op where
  out d := isConnected_of_equivalent (costructuredArrowOpEquivalence F (unop d))

/--
Instance `initial_op_of_final` / 实例 `initial_op_of_final`

English:
instance initial_op_of_final
  signature: (F : C ⥤ D) [Final F]
  body: isConnected_of_equivalent (structuredArrowOpEquivalence F (unop d))

中文:
实例 initial_op_of_final
  签名: (F : C ⥤ D) [Final F]
  定义体: isConnected_of_equivalent (structuredArrowOpEquivalence F (unop d))

Depends on / 依赖: isConnected_of_equivalent, structuredArrowOpEquivalence
-/
instance initial_op_of_final (F : C ⥤ D) [Final F] : Initial F.op where
  out d := isConnected_of_equivalent (structuredArrowOpEquivalence F (unop d))

/--
theorem `final_of_initial_op` / 定理 `final_of_initial_op`

English:
theorem final_of_initial_op
  given: (F : C ⥤ D) [Initial F.op]
  statement: Final F
  proof: {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (structuredArrowOpEquivalence F d).symm) }

中文:
定理 final_of_initial_op
  条件: (F : C ⥤ D) [Initial F.op]
  结论: Final F
  证明: {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (structuredArrowOpEquivalence F d).symm) }

Depends on / 依赖: isConnected_of_equivalent, isConnected_of_isConnected_op, structuredArrowOpEquivalence
-/
theorem final_of_initial_op (F : C ⥤ D) [Initial F.op] : Final F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (structuredArrowOpEquivalence F d).symm) }

/--
theorem `initial_of_final_op` / 定理 `initial_of_final_op`

English:
theorem initial_of_final_op
  given: (F : C ⥤ D) [Final F.op]
  statement: Initial F
  proof: {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (costructuredArrowOpEquivalence F d).symm) }

中文:
定理 initial_of_final_op
  条件: (F : C ⥤ D) [Final F.op]
  结论: Initial F
  证明: {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (costructuredArrowOpEquivalence F d).symm) }

Depends on / 依赖: costructuredArrowOpEquivalence, isConnected_of_equivalent, isConnected_of_isConnected_op
-/
theorem initial_of_final_op (F : C ⥤ D) [Final F.op] : Initial F :=
  {
    out := fun d =>
      @isConnected_of_isConnected_op _ _
        (isConnected_of_equivalent (costructuredArrowOpEquivalence F d).symm) }

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

/--
theorem `final_of_adjunction` / 定理 `final_of_adjunction`

English:
theorem final_of_adjunction
  given: {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  statement: Final R
  proof: { out := fun c =>
      let u : StructuredArrow c R := StructuredArrow.mk (adj.unit.app c)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inr ⟨StructuredArrow.homMk ((adj.homEqui

中文:
定理 final_of_adjunction
  条件: {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  结论: Final R
  证明: { out := fun c =>
      let u : StructuredArrow c R := StructuredArrow.mk (adj.unit.app c)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inr ⟨StructuredArrow.homMk ((adj.homEqui

Depends on / 依赖: Or.inl, Or.inr, ReflTransGen, Relation, Relation.ReflTransGen.single, Relation.ReflTransGen.trans, StructuredArrow, StructuredArrow.homMk, StructuredArrow.mk, adj.homEquiv, adj.unit.app, f.hom, f.right, g.hom, g.right, homEquiv, single, zigzag_isConnected
-/
theorem final_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Final R :=
  { out := fun c =>
      let u : StructuredArrow c R := StructuredArrow.mk (adj.unit.app c)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inr ⟨StructuredArrow.homMk ((adj.homEquiv c f.right).symm f.hom) (by simp [u])⟩))
          (Relation.ReflTransGen.single
            (show Zag u g from
              Or.inl ⟨StructuredArrow.homMk ((adj.homEquiv c g.right).symm g.hom) (by simp [u])⟩)) }

set_option backward.defeqAttrib.useBackward true in
/--
theorem `initial_of_adjunction` / 定理 `initial_of_adjunction`

English:
theorem initial_of_adjunction
  given: {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  statement: Initial L
  proof: { out := fun d =>
      let u : CostructuredArrow L d := CostructuredArrow.mk (adj.counit.app d)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inl ⟨CostructuredArrow.homMk (adj.

中文:
定理 initial_of_adjunction
  条件: {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  结论: Initial L
  证明: { out := fun d =>
      let u : CostructuredArrow L d := CostructuredArrow.mk (adj.counit.app d)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inl ⟨CostructuredArrow.homMk (adj.

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, Or.inl, Or.inr, ReflTransGen, Relation, Relation.ReflTransGen.single, Relation.ReflTransGen.trans, adj.counit.app, adj.homEquiv, counit, f.hom, f.left, g.hom, g.left, homEquiv, single, zigzag_isConnected
-/
theorem initial_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : Initial L :=
  { out := fun d =>
      let u : CostructuredArrow L d := CostructuredArrow.mk (adj.counit.app d)
      @zigzag_isConnected _ _ ⟨u⟩ fun f g =>
        Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            (show Zag f u from
              Or.inl ⟨CostructuredArrow.homMk (adj.homEquiv f.left d f.hom) (by simp [u])⟩))
          (Relation.ReflTransGen.single
            (show Zag u g from
              Or.inr ⟨CostructuredArrow.homMk (adj.homEquiv g.left d g.hom) (by simp [u])⟩)) }

instance (priority := 100) final_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] : Final F :=
  final_of_adjunction (Adjunction.ofIsRightAdjoint F)

instance (priority := 100) initial_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] : Initial F :=
  initial_of_adjunction (Adjunction.ofIsLeftAdjoint F)

/--
theorem `final_of_natIso` / 定理 `final_of_natIso`

English:
theorem final_of_natIso
  given: {F F' : C ⥤ D} [Final F] (i : F ≅ F')
  statement: Final F' where
  proof: isConnected_of_equivalent (StructuredArrow.mapNatIso i)

中文:
定理 final_of_natIso
  条件: {F F' : C ⥤ D} [Final F] (i : F ≅ F')
  结论: Final F' where
  证明: isConnected_of_equivalent (StructuredArrow.mapNatIso i)

Depends on / 依赖: StructuredArrow, StructuredArrow.mapNatIso, isConnected_of_equivalent, mapNatIso
-/
theorem final_of_natIso {F F' : C ⥤ D} [Final F] (i : F ≅ F') : Final F' where
  out _ := isConnected_of_equivalent (StructuredArrow.mapNatIso i)

/--
theorem `final_natIso_iff` / 定理 `final_natIso_iff`

English:
theorem final_natIso_iff
  given: {F F' : C ⥤ D} (i : F ≅ F')
  statement: Final F ↔ Final F'
  proof: ⟨fun _ => final_of_natIso i, fun _ => final_of_natIso i.symm⟩

中文:
定理 final_natIso_iff
  条件: {F F' : C ⥤ D} (i : F ≅ F')
  结论: Final F ↔ Final F'
  证明: ⟨fun _ => final_of_natIso i, fun _ => final_of_natIso i.symm⟩

Depends on / 依赖: final_of_natIso, i.symm
-/
theorem final_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Final F ↔ Final F' :=
  ⟨fun _ => final_of_natIso i, fun _ => final_of_natIso i.symm⟩

/--
theorem `initial_of_natIso` / 定理 `initial_of_natIso`

English:
theorem initial_of_natIso
  given: {F F' : C ⥤ D} [Initial F] (i : F ≅ F')
  statement: Initial F' where
  proof: isConnected_of_equivalent (CostructuredArrow.mapNatIso i)

中文:
定理 initial_of_natIso
  条件: {F F' : C ⥤ D} [Initial F] (i : F ≅ F')
  结论: Initial F' where
  证明: isConnected_of_equivalent (CostructuredArrow.mapNatIso i)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mapNatIso, isConnected_of_equivalent, mapNatIso
-/
theorem initial_of_natIso {F F' : C ⥤ D} [Initial F] (i : F ≅ F') : Initial F' where
  out _ := isConnected_of_equivalent (CostructuredArrow.mapNatIso i)

/--
theorem `initial_natIso_iff` / 定理 `initial_natIso_iff`

English:
theorem initial_natIso_iff
  given: {F F' : C ⥤ D} (i : F ≅ F')
  statement: Initial F ↔ Initial F'
  proof: ⟨fun _ => initial_of_natIso i, fun _ => initial_of_natIso i.symm⟩

中文:
定理 initial_natIso_iff
  条件: {F F' : C ⥤ D} (i : F ≅ F')
  结论: Initial F ↔ Initial F'
  证明: ⟨fun _ => initial_of_natIso i, fun _ => initial_of_natIso i.symm⟩

Depends on / 依赖: i.symm, initial_of_natIso
-/
theorem initial_natIso_iff {F F' : C ⥤ D} (i : F ≅ F') : Initial F ↔ Initial F' :=
  ⟨fun _ => initial_of_natIso i, fun _ => initial_of_natIso i.symm⟩

namespace Final

variable (F : C ⥤ D) [Final F]

instance (d : D) : Nonempty (StructuredArrow d F) :=
  IsConnected.is_nonempty

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (d : D)
  body: (Classical.arbitrary (StructuredArrow d F)).right

中文:
定义 lift
  签名: (d : D)
  定义体: (Classical.arbitrary (StructuredArrow d F)).right

Depends on / 依赖: Classical, Classical.arbitrary, StructuredArrow, arbitrary
-/
def lift (d : D) : C :=
  (Classical.arbitrary (StructuredArrow d F)).right

/--
Definition of `homToLift` / `homToLift` 的定义

English:
definition homToLift
  signature: (d : D)
  body: (Classical.arbitrary (StructuredArrow d F)).hom

中文:
定义 homToLift
  签名: (d : D)
  定义体: (Classical.arbitrary (StructuredArrow d F)).hom

Depends on / 依赖: Classical, Classical.arbitrary, StructuredArrow, arbitrary
-/
def homToLift (d : D) : d ⟶ F.obj (lift F d) :=
  (Classical.arbitrary (StructuredArrow d F)).hom

/--
Definition of `induction` / `induction` 的定义

English:
definition induction
  signature: {d : D} (Z : forall (X : C) (_ : d ⟶ F.obj X), Sort*)
  body: by
  apply Nonempty.some
  refine isPreconnected_induction (Z := fun Y : StructuredArrow d F => Z Y.right Y.hom)
    ?_ ?_ (j₀ := StructuredArrow.mk k₀) z _
  · exact fun f a => h₁ _ _ _ _ f.right f.w a
  · exact fun f a => h₂ _ _ _ _ f.right f.w a

中文:
定义 induction
  签名: {d : D} (Z : 对任意 (X : C) (_ : d ⟶ F.obj X), Sort*)
  定义体: by
  apply Nonempty.some
  refine isPreconnected_induction (Z := fun Y : StructuredArrow d F => Z Y.right Y.hom)
    ?_ ?_ (j₀ := StructuredArrow.mk k₀) z _
  · exact fun f a => h₁ _ _ _ _ f.right f.w a
  · exact fun f a => h₂ _ _ _ _ f.right f.w a

Depends on / 依赖: Nonempty, Nonempty.some, StructuredArrow, StructuredArrow.mk, Y.hom, Y.right, f.right, isPreconnected_induction
-/
def induction {d : D} (Z : forall (X : C) (_ : d ⟶ F.obj X), Sort*)
    (h₁ :
      forall (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
        k₁ ≫ F.map f = k₂ -> Z X₁ k₁ -> Z X₂ k₂)
    (h₂ :
      forall (X₁ X₂) (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
        k₁ ≫ F.map f = k₂ -> Z X₂ k₂ -> Z X₁ k₁)
    {X₀ : C} {k₀ : d ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d) := by
  apply Nonempty.some
  refine isPreconnected_induction (Z := fun Y : StructuredArrow d F => Z Y.right Y.hom)
    ?_ ?_ (j₀ := StructuredArrow.mk k₀) z _
  · exact fun f a => h₁ _ _ _ _ f.right f.w a
  · exact fun f a => h₂ _ _ _ _ f.right f.w a

variable {F G}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a cocone over `F ⋙ G`, we can construct a `Cocone G` with the same cocone point.
-/
@[simps]
/--
Definition of `extendCocone` / `extendCocone` 的定义

English:
definition extendCocone
  signature: : Cocone (F ⋙ G) ⥤ Cocone G where
  body: { pt := c.pt
      ι :=
        { app := fun X => G.map (homToLift F X) ≫ c.ι.app (lift F X)
          naturality := fun X Y f => by
            dsimp; simp only [Category.comp_id]
            -- This would be true if we'd chosen `lift F X` to be `lift F Y`
            -- and `homToLift F X` to be `

中文:
定义 extendCocone
  签名: : Cocone (F ⋙ G) ⥤ Cocone G where
  定义体: { pt := c.pt
      ι :=
        { app := fun X => G.map (homToLift F X) ≫ c.ι.app (lift F X)
          naturality := fun X Y f => by
            dsimp; simp only [Category.comp_id]
            -- This would be true if we'd chosen `lift F X` to be `lift F Y`
            -- and `homToLift F X` to be `

Depends on / 依赖: Category, Category.comp_id, G.map, Nonempty, Nonempty.intro, WeakLimitCone, WeakLimitCone.ofLimitCone, c.pt, comp_id, getLimitCone, homToLift, naturality, ofLimitCone
-/
def extendCocone : Cocone (F ⋙ G) ⥤ Cocone G where
  obj c :=
    { pt := c.pt
      ι :=
        { app := fun X => G.map (homToLift F X) ≫ c.ι.app (lift F X)
          naturality := fun X Y f => by
            dsimp; simp only [Category.comp_id]
            -- This would be true if we'd chosen `lift F X` to be `lift F Y`
            -- and `homToLift F X` to be `f ≫ homToLift F Y`.
            apply
              induction F fun Z k =>
                G.map f ≫ G.map (homToLift F Y) ≫ c.ι.app (lift F Y) = G.map k ≫ c.ι.app Z
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a]; rw [Functor.map_comp]; rw [Category.assoc]; rw [← Functor.comp_map]; rw [c.w]; rw [z]
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a]; rw [Functor.map_comp]; rw [Category.assoc]; rw [← Functor.comp_map]; rw [c.w] at z
              rw [z]
            · rw [← Functor.map_comp_assoc] } }
  map f := { hom := f.hom }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `extendCocone_obj_ι_app'` / 引理 `extendCocone_obj_ι_app'`

English:
lemma extendCocone_obj_ι_app'
  given: (c : Cocone (F ⋙ G)) {X : D} {Y : C} (f : X ⟶ F.obj Y)
  proof: by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    G.map g ≫ c.ι.app Z = G.map f ≫ c.ι.app Y
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, c.ι.naturality, h₂]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map, c.ι.naturality]

@[simp]

中文:
引理 extendCocone_obj_ι_app'
  条件: (c : Cocone (F ⋙ G)) {X : D} {Y : C} (f : X ⟶ F.obj Y)
  证明: by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    G.map g ≫ c.ι.app Z = G.map f ≫ c.ι.app Y
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, c.ι.naturality, h₂]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map, c.ι.naturality]

@[simp]

Depends on / 依赖: Functor, Functor.comp_map, G.map, comp_map, naturality
-/
lemma extendCocone_obj_ι_app' (c : Cocone (F ⋙ G)) {X : D} {Y : C} (f : X ⟶ F.obj Y) :
    (extendCocone.obj c).ι.app X = G.map f ≫ c.ι.app Y := by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    G.map g ≫ c.ι.app Z = G.map f ≫ c.ι.app Y
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, c.ι.naturality, h₂]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map, c.ι.naturality]

@[simp]
/--
theorem `colimit_cocone_comp_aux` / 定理 `colimit_cocone_comp_aux`

English:
theorem colimit_cocone_comp_aux
  given: (s : Cocone (F ⋙ G)) (j : C)
  proof: by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => G.map k ≫ s.ι.app X = (s.ι.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w]
    rw [← s.w f] at h
    simpa using! h
  · intro 

中文:
定理 colimit_cocone_comp_aux
  条件: (s : Cocone (F ⋙ G)) (j : C)
  证明: by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => G.map k ≫ s.ι.app X = (s.ι.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w]
    rw [← s.w f] at h
    simpa using! h
  · intro 
-/
theorem colimit_cocone_comp_aux (s : Cocone (F ⋙ G)) (j : C) :
    G.map (homToLift F (F.obj j)) ≫ s.ι.app (lift F (F.obj j)) = s.ι.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => G.map k ≫ s.ι.app X = (s.ι.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w]
    rw [← s.w f] at h
    simpa using! h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← w] at h
    rw [← s.w f]
    simpa using! h
  · exact s.w (𝟙 _)

variable (F G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is final,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
/--
Definition of `coconesEquiv` / `coconesEquiv` 的定义

English:
definition coconesEquiv
  signature: : Cocone (F ⋙ G) ≌ Cocone G where
  body: extendCocone
  inverse := Cocone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)

中文:
定义 coconesEquiv
  签名: : Cocone (F ⋙ G) ≌ Cocone G where
  定义体: extendCocone
  inverse := Cocone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)

Depends on / 依赖: extendCocone
-/
def coconesEquiv : Cocone (F ⋙ G) ≌ Cocone G where
  functor := extendCocone
  inverse := Cocone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cocone.ext (Iso.refl _)

variable {G}

/--
Definition of `isColimitWhiskerEquiv` / `isColimitWhiskerEquiv` 的定义

English:
definition isColimitWhiskerEquiv
  signature: (t : Cocone G)
  body: IsColimit.ofCoconeEquiv (coconesEquiv F G).symm

中文:
定义 isColimitWhiskerEquiv
  签名: (t : Cocone G)
  定义体: IsColimit.ofCoconeEquiv (coconesEquiv F G).symm

Depends on / 依赖: HasLimitsOfShape, HasWeakLimitsOfShape, IsColimit, IsColimit.ofCoconeEquiv, coconesEquiv, ofCoconeEquiv
-/
def isColimitWhiskerEquiv (t : Cocone G) : IsColimit (t.whisker F) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G).symm

/--
Definition of `isColimitExtendCoconeEquiv` / `isColimitExtendCoconeEquiv` 的定义

English:
definition isColimitExtendCoconeEquiv
  signature: (t : Cocone (F ⋙ G))
  body: IsColimit.ofCoconeEquiv (coconesEquiv F G)

中文:
定义 isColimitExtendCoconeEquiv
  签名: (t : Cocone (F ⋙ G))
  定义体: IsColimit.ofCoconeEquiv (coconesEquiv F G)

Depends on / 依赖: IsColimit, IsColimit.ofCoconeEquiv, coconesEquiv, ofCoconeEquiv
-/
def isColimitExtendCoconeEquiv (t : Cocone (F ⋙ G)) :
    IsColimit (extendCocone.obj t) ≃ IsColimit t :=
  IsColimit.ofCoconeEquiv (coconesEquiv F G)

/-- Given a colimit cocone over `G : D ⥤ E` we can construct a colimit cocone over `F ⋙ G`. -/
@[simps]
/--
Definition of `colimitCoconeComp` / `colimitCoconeComp` 的定义

English:
definition colimitCoconeComp
  signature: (t : ColimitCocone G)
  body: _
  isColimit := (isColimitWhiskerEquiv F _).symm t.isColimit

中文:
定义 colimitCoconeComp
  签名: (t : ColimitCocone G)
  定义体: _
  isColimit := (isColimitWhiskerEquiv F _).symm t.isColimit
-/
def colimitCoconeComp (t : ColimitCocone G) : ColimitCocone (F ⋙ G) where
  cocone := _
  isColimit := (isColimitWhiskerEquiv F _).symm t.isColimit

instance (priority := 100) comp_hasColimit [HasColimit G] : HasColimit (F ⋙ G) :=
  HasColimit.mk (colimitCoconeComp F (getColimitCocone G))

set_option backward.defeqAttrib.useBackward true in
instance (priority := 100) comp_preservesColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesColimit G H] : PreservesColimit (F ⋙ G) H where
  preserves {c} hc := by
    refine ⟨isColimitExtendCoconeEquiv (G := G ⋙ H) F (H.mapCocone c) ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitExtendCoconeEquiv F c).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
instance (priority := 100) comp_reflectsColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsColimit G H] : ReflectsColimit (F ⋙ G) H where
  reflects {c} hc := by
    refine ⟨isColimitExtendCoconeEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitExtendCoconeEquiv (G := G ⋙ H) F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

instance (priority := 100) compCreatesColimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesColimit G H] : CreatesColimit (F ⋙ G) H where
  lifts {c} hc := by
    refine ⟨(liftColimit ((isColimitExtendCoconeEquiv F (G := G ⋙ H) _).symm hc)).whisker F, ?_⟩
    let i := liftedColimitMapsToOriginal ((isColimitExtendCoconeEquiv F (G := G ⋙ H) _).symm hc)
    exact (Cocone.whiskering F).mapIso i ≪≫ ((coconesEquiv F (G ⋙ H)).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `colimit_pre_isIso` / 实例 `colimit_pre_isIso`

English:
instance colimit_pre_isIso
  signature: [HasColimit G]
  body: by
  simp only [colimit.pre_eq (colimitCoconeComp F (getColimitCocone G)) (getColimitCocone G),
    colimitCoconeComp_cocone, IsColimit.desc_self]
  infer_instance

中文:
实例 colimit_pre_isIso
  签名: [HasColimit G]
  定义体: by
  simp only [colimit.pre_eq (colimitCoconeComp F (getColimitCocone G)) (getColimitCocone G),
    colimitCoconeComp_cocone, IsColimit.desc_self]
  infer_instance

Depends on / 依赖: IsColimit, IsColimit.desc_self, colimit, colimit.pre_eq, colimitCoconeComp, colimitCoconeComp_cocone, desc_self, getColimitCocone, infer_instance, pre_eq
-/
instance colimit_pre_isIso [HasColimit G] : IsIso (colimit.pre G F) := by
  simp only [colimit.pre_eq (colimitCoconeComp F (getColimitCocone G)) (getColimitCocone G),
    colimitCoconeComp_cocone, IsColimit.desc_self]
  infer_instance

section

variable (G)

/-- When `F : C ⥤ D` is final, and `G : D ⥤ E` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`. -/
@[simps! -isSimp, stacks 04E7]
/--
Definition of `colimitIso` / `colimitIso` 的定义

English:
definition colimitIso
  signature: [HasColimit G]
  body: asIso (colimit.pre G F)

@[reassoc (attr := simp)]

中文:
定义 colimitIso
  签名: [HasColimit G]
  定义体: asIso (colimit.pre G F)

@[reassoc (attr := simp)]

Depends on / 依赖: colimit, colimit.pre
-/
def colimitIso [HasColimit G] : colimit (F ⋙ G) ≅ colimit G :=
  asIso (colimit.pre G F)

@[reassoc (attr := simp)]
/--
theorem `ι_colimitIso_hom` / 定理 `ι_colimitIso_hom`

English:
theorem ι_colimitIso_hom
  given: [HasColimit G] (X : C)
  proof: by
  simp [colimitIso]

@[reassoc (attr := simp)]

中文:
定理 ι_colimitIso_hom
  条件: [HasColimit G] (X : C)
  证明: by
  simp [colimitIso]

@[reassoc (attr := simp)]

Depends on / 依赖: colimitIso
-/
theorem ι_colimitIso_hom [HasColimit G] (X : C) :
    colimit.ι (F ⋙ G) X ≫ (colimitIso F G).hom = colimit.ι G (F.obj X) := by
  simp [colimitIso]

@[reassoc (attr := simp)]
/--
theorem `ι_colimitIso_inv` / 定理 `ι_colimitIso_inv`

English:
theorem ι_colimitIso_inv
  given: [HasColimit G] (X : C)
  proof: by
  simp [colimitIso]

中文:
定理 ι_colimitIso_inv
  条件: [HasColimit G] (X : C)
  证明: by
  simp [colimitIso]

Depends on / 依赖: colimitIso
-/
theorem ι_colimitIso_inv [HasColimit G] (X : C) :
    colimit.ι G (F.obj X) ≫ (colimitIso F G).inv = colimit.ι (F ⋙ G) X := by
  simp [colimitIso]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `colimIso` / `colimIso` 的定义

English:
definition colimIso
  signature: [HasColimitsOfShape D E] [HasColimitsOfShape C E]
  body: NatIso.ofComponents (fun G => colimitIso F G) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, colim_obj, comp_map, whiskeringLeft_obj_map,
      colim_map, colimitIso_hom]
    ext
    simp only [comp_obj, ι_colimMap_assoc, whiskerLeft_app, colimit.ι_pre, colimit.ι_pre_assoc,
      ι_col

中文:
定义 colimIso
  签名: [HasColimitsOfShape D E] [HasColimitsOfShape C E]
  定义体: NatIso.ofComponents (fun G => colimitIso F G) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, colim_obj, comp_map, whiskeringLeft_obj_map,
      colim_map, colimitIso_hom]
    ext
    simp only [comp_obj, ι_colimMap_assoc, whiskerLeft_app, colimit.ι_pre, colimit.ι_pre_assoc,
      ι_col
-/
def colimIso [HasColimitsOfShape D E] [HasColimitsOfShape C E] :
    (whiskeringLeft _ _ _).obj F ⋙ colim ≅ colim (J := D) (C := E) :=
  NatIso.ofComponents (fun G => colimitIso F G) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, colim_obj, comp_map, whiskeringLeft_obj_map,
      colim_map, colimitIso_hom]
    ext
    simp only [comp_obj, ι_colimMap_assoc, whiskerLeft_app, colimit.ι_pre, colimit.ι_pre_assoc,
      ι_colimMap]

end

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simps]
/--
Definition of `colimitCoconeOfComp` / `colimitCoconeOfComp` 的定义

English:
definition colimitCoconeOfComp
  signature: (t : ColimitCocone (F ⋙ G))
  body: extendCocone.obj t.cocone
  isColimit := (isColimitExtendCoconeEquiv F _).symm t.isColimit

中文:
定义 colimitCoconeOfComp
  签名: (t : ColimitCocone (F ⋙ G))
  定义体: extendCocone.obj t.cocone
  isColimit := (isColimitExtendCoconeEquiv F _).symm t.isColimit

Depends on / 依赖: cocone, extendCocone, extendCocone.obj, t.cocone
-/
def colimitCoconeOfComp (t : ColimitCocone (F ⋙ G)) : ColimitCocone G where
  cocone := extendCocone.obj t.cocone
  isColimit := (isColimitExtendCoconeEquiv F _).symm t.isColimit

/--
theorem `hasColimit_of_comp` / 定理 `hasColimit_of_comp`

English:
theorem hasColimit_of_comp
  given: [HasColimit (F ⋙ G)]
  statement: HasColimit G
  proof: HasColimit.mk (colimitCoconeOfComp F (getColimitCocone (F ⋙ G)))

中文:
定理 hasColimit_of_comp
  条件: [HasColimit (F ⋙ G)]
  结论: HasColimit G
  证明: HasColimit.mk (colimitCoconeOfComp F (getColimitCocone (F ⋙ G)))

Depends on / 依赖: HasColimit, HasColimit.mk, colimitCoconeOfComp, getColimitCocone
-/
theorem hasColimit_of_comp [HasColimit (F ⋙ G)] : HasColimit G :=
  HasColimit.mk (colimitCoconeOfComp F (getColimitCocone (F ⋙ G)))

/--
lemma `hasColimit_comp_iff` / 引理 `hasColimit_comp_iff`

English:
lemma hasColimit_comp_iff
  proof: ⟨fun _ => Functor.Final.hasColimit_of_comp F, fun _ => inferInstance⟩

中文:
引理 hasColimit_comp_iff
  证明: ⟨fun _ => Functor.Final.hasColimit_of_comp F, fun _ => inferInstance⟩

Depends on / 依赖: Functor, Functor.Final.hasColimit_of_comp, hasColimit_of_comp
-/
lemma hasColimit_comp_iff :
    HasColimit (F ⋙ G) ↔ HasColimit G :=
  ⟨fun _ => Functor.Final.hasColimit_of_comp F, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `preservesColimit_of_comp` / 定理 `preservesColimit_of_comp`

English:
theorem preservesColimit_of_comp
  statement: {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
  proof: by
    refine ⟨isColimitWhiskerEquiv F _ ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitWhiskerEquiv F _).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

中文:
定理 preservesColimit_of_comp
  结论: {B : 类型u₄} [Category.{v₄} B] {H : E ⥤ B}
  证明: by
    refine ⟨isColimitWhiskerEquiv F _ ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitWhiskerEquiv F _).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, isColimitOfPreserves, isColimitWhiskerEquiv, ofIsoColimit
-/
theorem preservesColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesColimit (F ⋙ G) H] : PreservesColimit G H where
  preserves {c} hc := by
    refine ⟨isColimitWhiskerEquiv F _ ?_⟩
    let hc' := isColimitOfPreserves H ((isColimitWhiskerEquiv F _).symm hc)
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `reflectsColimit_of_comp` / 定理 `reflectsColimit_of_comp`

English:
theorem reflectsColimit_of_comp
  statement: {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
  proof: by
    refine ⟨isColimitWhiskerEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitWhiskerEquiv F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

中文:
定理 reflectsColimit_of_comp
  结论: {B : 类型u₄} [Category.{v₄} B] {H : E ⥤ B}
  证明: by
    refine ⟨isColimitWhiskerEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitWhiskerEquiv F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, isColimitOfReflects, isColimitWhiskerEquiv, ofIsoColimit
-/
theorem reflectsColimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsColimit (F ⋙ G) H] : ReflectsColimit G H where
  reflects {c} hc := by
    refine ⟨isColimitWhiskerEquiv F _ (isColimitOfReflects H ?_)⟩
    let hc' := (isColimitWhiskerEquiv F _).symm hc
    exact IsColimit.ofIsoColimit hc' (Cocone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is final and `F ⋙ G` creates colimits of `H`, then so does `G`. -/
@[instance_reducible]
/--
Definition of `createsColimitOfComp` / `createsColimitOfComp` 的定义

English:
definition createsColimitOfComp
  signature: {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
  body: (reflectsColimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCocone (F := F)).obj (liftColimit ((isColimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedColimitMapsToOriginal (K := (F ⋙ G)) ((isColimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCocone (F := F)).mapIso i)

中文:
定义 createsColimitOfComp
  签名: {B : 类型u₄} [Category.{v₄} B] {H : E ⥤ B}
  定义体: (reflectsColimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCocone (F := F)).obj (liftColimit ((isColimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedColimitMapsToOriginal (K := (F ⋙ G)) ((isColimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCocone (F := F)).mapIso i)

Depends on / 依赖: reflects, reflectsColimit_of_comp
-/
def createsColimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesColimit (F ⋙ G) H] : CreatesColimit G H where
  reflects := (reflectsColimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCocone (F := F)).obj (liftColimit ((isColimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedColimitMapsToOriginal (K := (F ⋙ G)) ((isColimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCocone (F := F)).mapIso i) ≪≫ ((coconesEquiv F (G ⋙ H)).counitIso.app _)
    exact Cocone.ext (Iso.refl _)

include F in
/--
theorem `hasColimitsOfShape_of_final` / 定理 `hasColimitsOfShape_of_final`

English:
theorem hasColimitsOfShape_of_final
  given: [HasColimitsOfShape C E]
  statement: HasColimitsOfShape D E where
  proof: fun _ => hasColimit_of_comp F

include F in

中文:
定理 hasColimitsOfShape_of_final
  条件: [HasColimitsOfShape C E]
  结论: HasColimitsOfShape D E where
  证明: fun _ => hasColimit_of_comp F

include F in

Depends on / 依赖: hasColimit_of_comp
-/
theorem hasColimitsOfShape_of_final [HasColimitsOfShape C E] : HasColimitsOfShape D E where
  has_colimit := fun _ => hasColimit_of_comp F

include F in
/--
theorem `preservesColimitsOfShape_of_final` / 定理 `preservesColimitsOfShape_of_final`

English:
theorem preservesColimitsOfShape_of_final
  statement: {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
  proof: preservesColimit_of_comp F

include F in

中文:
定理 preservesColimitsOfShape_of_final
  结论: {B : 类型u₄} [Category.{v₄} B] (H : E ⥤ B)
  证明: preservesColimit_of_comp F

include F in

Depends on / 依赖: preservesColimit_of_comp
-/
theorem preservesColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [PreservesColimitsOfShape C H] : PreservesColimitsOfShape D H where
  preservesColimit := preservesColimit_of_comp F

include F in
/--
theorem `reflectsColimitsOfShape_of_final` / 定理 `reflectsColimitsOfShape_of_final`

English:
theorem reflectsColimitsOfShape_of_final
  statement: {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
  proof: reflectsColimit_of_comp F

include F in

中文:
定理 reflectsColimitsOfShape_of_final
  结论: {B : 类型u₄} [Category.{v₄} B] (H : E ⥤ B)
  证明: reflectsColimit_of_comp F

include F in

Depends on / 依赖: reflectsColimit_of_comp
-/
theorem reflectsColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [ReflectsColimitsOfShape C H] : ReflectsColimitsOfShape D H where
  reflectsColimit := reflectsColimit_of_comp F

include F in
/-- If `H` creates colimits of shape `C` and `F : C ⥤ D` is final, then `H` creates colimits of
shape `D`. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOfFinal` / `createsColimitsOfShapeOfFinal` 的定义

English:
definition createsColimitsOfShapeOfFinal
  signature: {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
  body: createsColimitOfComp F

中文:
定义 createsColimitsOfShapeOfFinal
  签名: {B : 类型u₄} [Category.{v₄} B] (H : E ⥤ B)
  定义体: createsColimitOfComp F

Depends on / 依赖: createsColimitOfComp
-/
def createsColimitsOfShapeOfFinal {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [CreatesColimitsOfShape C H] : CreatesColimitsOfShape D H where
  CreatesColimit := createsColimitOfComp F

end Final

end ArbitraryUniverse

section LocallySmall

variable {C : Type v} [Category.{v} C] {D : Type u₁} [Category.{v} D] (F : C ⥤ D)

namespace Final

/--
theorem `zigzag_of_eqvGen_colimitTypeRel` / 定理 `zigzag_of_eqvGen_colimitTypeRel`

English:
theorem zigzag_of_eqvGen_colimitTypeRel
  statement: {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X}
  proof: by
  induction t with
  | rel x y r =>
    obtain ⟨f, w⟩ := r
    fconstructor
    swap
    · fconstructor
    left; fconstructor
    exact StructuredArrow.homMk f
  | refl => fconstructor
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

中文:
定理 zigzag_of_eqvGen_colimitTypeRel
  结论: {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X}
  证明: by
  induction t with
  | rel x y r =>
    obtain ⟨f, w⟩ := r
    fconstructor
    swap
    · fconstructor
    left; fconstructor
    exact StructuredArrow.homMk f
  | refl => fconstructor
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

Depends on / 依赖: StructuredArrow, StructuredArrow.homMk, fconstructor, ih.symm
-/
theorem zigzag_of_eqvGen_colimitTypeRel {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X}
    (t : Relation.EqvGen (Functor.ColimitTypeRel (F ⋙ coyoneda.obj (op d))) f₁ f₂) :
    Zigzag (StructuredArrow.mk f₁.2) (StructuredArrow.mk f₂.2) := by
  induction t with
  | rel x y r =>
    obtain ⟨f, w⟩ := r
    fconstructor
    swap
    · fconstructor
    left; fconstructor
    exact StructuredArrow.homMk f
  | refl => fconstructor
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Final

/--
theorem `final_of_colimit_comp_coyoneda_iso_pUnit` / 定理 `final_of_colimit_comp_coyoneda_iso_pUnit`

English:
theorem final_of_colimit_comp_coyoneda_iso_pUnit
  proof: ⟨fun d => by
    have : Nonempty (StructuredArrow d F) := by
      have := (I d).inv PUnit.unit
      obtain ⟨j, y, rfl⟩ := Limits.Types.jointly_surjective'.{v, v} this
      exact ⟨StructuredArrow.mk y⟩
    apply zigzag_isConnected
    rintro ⟨⟨⟨⟩⟩, X₁, f₁⟩ ⟨⟨⟨⟩⟩, X₂, f₂⟩
    let y₁ := colimit.ι (F

中文:
定理 final_of_colimit_comp_coyoneda_iso_pUnit
  证明: ⟨fun d => by
    have : Nonempty (StructuredArrow d F) := by
      have := (I d).inv PUnit.unit
      obtain ⟨j, y, rfl⟩ := Limits.Types.jointly_surjective'.{v, v} this
      exact ⟨StructuredArrow.mk y⟩
    apply zigzag_isConnected
    rintro ⟨⟨⟨⟩⟩, X₁, f₁⟩ ⟨⟨⟨⟩⟩, X₂, f₂⟩
    let y₁ := colimit.ι (F

Depends on / 依赖: Final.zigzag_of_eqvGen_colimitTypeRel, Limits, Limits.Types.jointly_surjective, Nonempty, PUnit.unit, StructuredArrow, StructuredArrow.mk, Types.colimit_eq, colimit, colimit_eq, coyoneda, coyoneda.obj, injective, jointly_surjective, toEquiv, toEquiv.injective, zigzag_isConnected, zigzag_of_eqvGen_colimitTypeRel
-/
theorem final_of_colimit_comp_coyoneda_iso_pUnit
    (I : forall d, colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit) : Final F :=
  ⟨fun d => by
    have : Nonempty (StructuredArrow d F) := by
      have := (I d).inv PUnit.unit
      obtain ⟨j, y, rfl⟩ := Limits.Types.jointly_surjective'.{v, v} this
      exact ⟨StructuredArrow.mk y⟩
    apply zigzag_isConnected
    rintro ⟨⟨⟨⟩⟩, X₁, f₁⟩ ⟨⟨⟨⟩⟩, X₂, f₂⟩
    let y₁ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₁ f₁
    let y₂ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₂ f₂
    have e : y₁ = y₂ := by
      apply (I d).toEquiv.injective
      ext
    have t := Types.colimit_eq.{v, v} e
    clear e y₁ y₂
    exact Final.zigzag_of_eqvGen_colimitTypeRel t⟩

/--
theorem `final_of_isTerminal_colimit_comp_yoneda` / 定理 `final_of_isTerminal_colimit_comp_yoneda`

English:
theorem final_of_isTerminal_colimit_comp_yoneda
  proof: by
  refine final_of_colimit_comp_coyoneda_iso_pUnit _ (fun d => ?_)
  refine Types.isTerminalEquivIsoPUnit _ ?_
  let b := IsTerminal.isTerminalObj ((evaluation _ _).obj (Opposite.op d)) _ h
exact b.ofIso preservesColimitIso ((evaluation _ _).obj (Opposite.op d)) (F ⋙ yoneda)

中文:
定理 final_of_isTerminal_colimit_comp_yoneda
  证明: by
  refine final_of_colimit_comp_coyoneda_iso_pUnit _ (fun d => ?_)
  refine Types.isTerminalEquivIsoPUnit _ ?_
  let b := IsTerminal.isTerminalObj ((evaluation _ _).obj (Opposite.op d)) _ h
exact b.ofIso preservesColimitIso ((evaluation _ _).obj (Opposite.op d)) (F ⋙ yoneda)

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalObj, Opposite, Opposite.op, Types.isTerminalEquivIsoPUnit, b.ofIso, evaluation, final_of_colimit_comp_coyoneda_iso_pUnit, isTerminalEquivIsoPUnit, isTerminalObj, preservesColimitIso, yoneda
-/
theorem final_of_isTerminal_colimit_comp_yoneda
    (h : IsTerminal (colimit (F ⋙ yoneda))) : Final F := by
  refine final_of_colimit_comp_coyoneda_iso_pUnit _ (fun d => ?_)
  refine Types.isTerminalEquivIsoPUnit _ ?_
  let b := IsTerminal.isTerminalObj ((evaluation _ _).obj (Opposite.op d)) _ h
exact b.ofIso preservesColimitIso ((evaluation _ _).obj (Opposite.op d)) (F ⋙ yoneda)

/--
Definition of `Final.colimitCompCoyonedaIso` / `Final.colimitCompCoyonedaIso` 的定义

English:
definition Final.colimitCompCoyonedaIso
  signature: (d : D) [IsIso (colimit.pre (coyoneda.obj (op d)) F)]
  body: asIso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ Coyoneda.colimitCoyonedaIso (op d)

中文:
定义 Final.colimitCompCoyonedaIso
  签名: (d : D) [IsIso (colimit.pre (coyoneda.obj (op d)) F)]
  定义体: asIso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ Coyoneda.colimitCoyonedaIso (op d)

Depends on / 依赖: Coyoneda, Coyoneda.colimitCoyonedaIso, colimit, colimit.pre, colimitCoyonedaIso, coyoneda, coyoneda.obj
-/
def Final.colimitCompCoyonedaIso (d : D) [IsIso (colimit.pre (coyoneda.obj (op d)) F)] :
    colimit (F ⋙ coyoneda.obj (op d)) ≅ PUnit :=
  asIso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ Coyoneda.colimitCoyonedaIso (op d)

end LocallySmall

section SmallCategory

variable {C : Type v} [Category.{v} C] {D : Type v} [Category.{v} D] (F : C ⥤ D)

/--
theorem `final_iff_isIso_colimit_pre` / 定理 `final_iff_isIso_colimit_pre`

English:
theorem final_iff_isIso_colimit_pre
  statement: Final F ↔ forall G : D ⥤ Type v, IsIso (colimit.pre G F)
  proof: ⟨fun _ => inferInstance,
   fun _ => final_of_colimit_comp_coyoneda_iso_pUnit _ fun _ => Final.colimitCompCoyonedaIso _ _⟩

中文:
定理 final_iff_isIso_colimit_pre
  结论: Final F ↔ 对任意 G : D ⥤ 类型v, IsIso (colimit.pre G F)
  证明: ⟨fun _ => inferInstance,
   fun _ => final_of_colimit_comp_coyoneda_iso_pUnit _ fun _ => Final.colimitCompCoyonedaIso _ _⟩

Depends on / 依赖: Final.colimitCompCoyonedaIso, colimitCompCoyonedaIso, final_of_colimit_comp_coyoneda_iso_pUnit
-/
theorem final_iff_isIso_colimit_pre : Final F ↔ forall G : D ⥤ Type v, IsIso (colimit.pre G F) :=
  ⟨fun _ => inferInstance,
   fun _ => final_of_colimit_comp_coyoneda_iso_pUnit _ fun _ => Final.colimitCompCoyonedaIso _ _⟩

end SmallCategory

namespace Initial

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) [Initial F]

instance (d : D) : Nonempty (CostructuredArrow F d) :=
  IsConnected.is_nonempty

variable {E : Type u₃} [Category.{v₃} E] (G : D ⥤ E)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (d : D)
  body: (Classical.arbitrary (CostructuredArrow F d)).left

中文:
定义 lift
  签名: (d : D)
  定义体: (Classical.arbitrary (CostructuredArrow F d)).left

Depends on / 依赖: Classical, Classical.arbitrary, CostructuredArrow, arbitrary
-/
def lift (d : D) : C :=
  (Classical.arbitrary (CostructuredArrow F d)).left

/--
Definition of `homToLift` / `homToLift` 的定义

English:
definition homToLift
  signature: (d : D)
  body: (Classical.arbitrary (CostructuredArrow F d)).hom

中文:
定义 homToLift
  签名: (d : D)
  定义体: (Classical.arbitrary (CostructuredArrow F d)).hom

Depends on / 依赖: Classical, Classical.arbitrary, CostructuredArrow, arbitrary
-/
def homToLift (d : D) : F.obj (lift F d) ⟶ d :=
  (Classical.arbitrary (CostructuredArrow F d)).hom

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `induction` / `induction` 的定义

English:
definition induction
  signature: {d : D} (Z : forall (X : C) (_ : F.obj X ⟶ d), Sort*)
  body: by
  apply Nonempty.some
  apply
    @isPreconnected_induction _ _ _ (fun Y : CostructuredArrow F d => Z Y.left Y.hom) _ _
      (CostructuredArrow.mk k₀) z
  · intro j₁ j₂ f a
    fapply h₁ _ _ _ _ f.left _ a
    convert! f.w
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.left _ a
    convert

中文:
定义 induction
  签名: {d : D} (Z : 对任意 (X : C) (_ : F.obj X ⟶ d), Sort*)
  定义体: by
  apply Nonempty.some
  apply
    @isPreconnected_induction _ _ _ (fun Y : CostructuredArrow F d => Z Y.left Y.hom) _ _
      (CostructuredArrow.mk k₀) z
  · intro j₁ j₂ f a
    fapply h₁ _ _ _ _ f.left _ a
    convert! f.w
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.left _ a
    convert

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, Nonempty, Nonempty.some, Y.hom, Y.left, convert, f.left, fapply, isPreconnected_induction
-/
def induction {d : D} (Z : forall (X : C) (_ : F.obj X ⟶ d), Sort*)
    (h₁ :
      forall (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
        F.map f ≫ k₂ = k₁ -> Z X₁ k₁ -> Z X₂ k₂)
    (h₂ :
      forall (X₁ X₂) (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
        F.map f ≫ k₂ = k₁ -> Z X₂ k₂ -> Z X₁ k₁)
    {X₀ : C} {k₀ : F.obj X₀ ⟶ d} (z : Z X₀ k₀) : Z (lift F d) (homToLift F d) := by
  apply Nonempty.some
  apply
    @isPreconnected_induction _ _ _ (fun Y : CostructuredArrow F d => Z Y.left Y.hom) _ _
      (CostructuredArrow.mk k₀) z
  · intro j₁ j₂ f a
    fapply h₁ _ _ _ _ f.left _ a
    convert! f.w
    simp
  · intro j₁ j₂ f a
    fapply h₂ _ _ _ _ f.left _ a
    convert! f.w
    simp

variable {F G}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a cone over `F ⋙ G`, we can construct a `Cone G` with the same cocone point.
-/
@[simps]
/--
Definition of `extendCone` / `extendCone` 的定义

English:
definition extendCone
  signature: : Cone (F ⋙ G) ⥤ Cone G where
  body: { pt := c.pt
      π :=
        { app := fun d => c.π.app (lift F d) ≫ G.map (homToLift F d)
          naturality := fun X Y f => by
            dsimp; simp only [Category.id_comp, Category.assoc]
            -- This would be true if we'd chosen `lift F Y` to be `lift F X`
            -- and `homToL

中文:
定义 extendCone
  签名: : Cone (F ⋙ G) ⥤ Cone G where
  定义体: { pt := c.pt
      π :=
        { app := fun d => c.π.app (lift F d) ≫ G.map (homToLift F d)
          naturality := fun X Y f => by
            dsimp; simp only [Category.id_comp, Category.assoc]
            -- This would be true if we'd chosen `lift F Y` to be `lift F X`
            -- and `homToL

Depends on / 依赖: Category, Category.assoc, Category.id_comp, G.map, c.pt, homToLift, id_comp, naturality
-/
def extendCone : Cone (F ⋙ G) ⥤ Cone G where
  obj c :=
    { pt := c.pt
      π :=
        { app := fun d => c.π.app (lift F d) ≫ G.map (homToLift F d)
          naturality := fun X Y f => by
            dsimp; simp only [Category.id_comp, Category.assoc]
            -- This would be true if we'd chosen `lift F Y` to be `lift F X`
            -- and `homToLift F Y` to be `homToLift F X ≫ f`.
            apply
              induction F fun Z k =>
                (c.π.app Z ≫ G.map k : c.pt ⟶ _) =
                  c.π.app (lift F X) ≫ G.map (homToLift F X) ≫ G.map f
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a]; rw [Functor.map_comp]; rw [← Functor.comp_map]; rw [← Category.assoc]; rw [← Category.assoc]; rw [c.w] at z
              rw [z]; rw [Category.assoc]
            · intro Z₁ Z₂ k₁ k₂ g a z
              rw [← a]; rw [Functor.map_comp]; rw [← Functor.comp_map]; rw [← Category.assoc]; rw [← Category.assoc]; rw [c.w]; rw [z]; rw [Category.assoc]
            · rw [← Functor.map_comp] } }
  map f := { hom := f.hom }

set_option backward.isDefEq.respectTransparency false in
/--
lemma `extendCone_obj_π_app'` / 引理 `extendCone_obj_π_app'`

English:
lemma extendCone_obj_π_app'
  given: (c : Cone (F ⋙ G)) {X : C} {Y : D} (f : F.obj X ⟶ Y)
  proof: by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    c.π.app Z ≫ G.map g = c.π.app X ≫ G.map f
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, h₂]

中文:
引理 extendCone_obj_π_app'
  条件: (c : Cone (F ⋙ G)) {X : C} {Y : D} (f : F.obj X ⟶ Y)
  证明: by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    c.π.app Z ≫ G.map g = c.π.app X ≫ G.map f
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, h₂]

Depends on / 依赖: Functor, Functor.comp_map, G.map, comp_map
-/
lemma extendCone_obj_π_app' (c : Cone (F ⋙ G)) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    (extendCone.obj c).π.app Y = c.π.app X ≫ G.map f := by
  apply induction (k₀ := f) (z := rfl) F fun Z g =>
    c.π.app Z ≫ G.map g = c.π.app X ≫ G.map f
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₂, ← h₁, ← Functor.comp_map]
  · intro _ _ _ _ _ h₁ h₂
    simp [← h₁, ← Functor.comp_map, h₂]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `limit_cone_comp_aux` / 定理 `limit_cone_comp_aux`

English:
theorem limit_cone_comp_aux
  given: (s : Cone (F ⋙ G)) (j : C)
  proof: by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => s.π.app X ≫ G.map k = (s.π.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f]
    rw [← w] at h
    simpa using h
  · intro j

中文:
定理 limit_cone_comp_aux
  条件: (s : Cone (F ⋙ G)) (j : C)
  证明: by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => s.π.app X ≫ G.map k = (s.π.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f]
    rw [← w] at h
    simpa using h
  · intro j
-/
theorem limit_cone_comp_aux (s : Cone (F ⋙ G)) (j : C) :
    s.π.app (lift F (F.obj j)) ≫ G.map (homToLift F (F.obj j)) = s.π.app j := by
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `homToLift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F fun X k => s.π.app X ≫ G.map k = (s.π.app j :)
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f]
    rw [← w] at h
    simpa using h
  · intro j₁ j₂ k₁ k₂ f w h
    rw [← s.w f] at h
    rw [← w]
    simpa using h
  · exact s.w (𝟙 _)

variable (F G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is initial,
the category of cones on `F ⋙ G` is equivalent to the category of cones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
/--
Definition of `conesEquiv` / `conesEquiv` 的定义

English:
definition conesEquiv
  signature: : Cone (F ⋙ G) ≌ Cone G where
  body: extendCone
  inverse := Cone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)

中文:
定义 conesEquiv
  签名: : Cone (F ⋙ G) ≌ Cone G where
  定义体: extendCone
  inverse := Cone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)

Depends on / 依赖: extendCone
-/
def conesEquiv : Cone (F ⋙ G) ≌ Cone G where
  functor := extendCone
  inverse := Cone.whiskering F
  unitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun c => Cone.ext (Iso.refl _)

variable {G}

/--
Definition of `isLimitWhiskerEquiv` / `isLimitWhiskerEquiv` 的定义

English:
definition isLimitWhiskerEquiv
  signature: (t : Cone G)
  body: IsLimit.ofConeEquiv (conesEquiv F G).symm

中文:
定义 isLimitWhiskerEquiv
  签名: (t : Cone G)
  定义体: IsLimit.ofConeEquiv (conesEquiv F G).symm

Depends on / 依赖: IsLimit, IsLimit.ofConeEquiv, conesEquiv, ofConeEquiv
-/
def isLimitWhiskerEquiv (t : Cone G) : IsLimit (t.whisker F) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G).symm

/--
Definition of `isLimitExtendConeEquiv` / `isLimitExtendConeEquiv` 的定义

English:
definition isLimitExtendConeEquiv
  signature: (t : Cone (F ⋙ G))
  body: IsLimit.ofConeEquiv (conesEquiv F G)

中文:
定义 isLimitExtendConeEquiv
  签名: (t : Cone (F ⋙ G))
  定义体: IsLimit.ofConeEquiv (conesEquiv F G)

Depends on / 依赖: IsLimit, IsLimit.ofConeEquiv, conesEquiv, ofConeEquiv
-/
def isLimitExtendConeEquiv (t : Cone (F ⋙ G)) : IsLimit (extendCone.obj t) ≃ IsLimit t :=
  IsLimit.ofConeEquiv (conesEquiv F G)

/-- Given a limit cone over `G : D ⥤ E` we can construct a limit cone over `F ⋙ G`. -/
@[simps]
/--
Definition of `limitConeComp` / `limitConeComp` 的定义

English:
definition limitConeComp
  signature: (t : LimitCone G)
  body: _
  isLimit := (isLimitWhiskerEquiv F _).symm t.isLimit

中文:
定义 limitConeComp
  签名: (t : LimitCone G)
  定义体: _
  isLimit := (isLimitWhiskerEquiv F _).symm t.isLimit
-/
def limitConeComp (t : LimitCone G) : LimitCone (F ⋙ G) where
  cone := _
  isLimit := (isLimitWhiskerEquiv F _).symm t.isLimit

instance (priority := 100) comp_hasLimit [HasLimit G] : HasLimit (F ⋙ G) :=
  HasLimit.mk (limitConeComp F (getLimitCone G))

set_option backward.defeqAttrib.useBackward true in
instance (priority := 100) comp_preservesLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesLimit G H] : PreservesLimit (F ⋙ G) H where
  preserves {c} hc := by
    refine ⟨isLimitExtendConeEquiv (G := G ⋙ H) F (H.mapCone c) ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitExtendConeEquiv F c).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
instance (priority := 100) comp_reflectsLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsLimit G H] : ReflectsLimit (F ⋙ G) H where
  reflects {c} hc := by
    refine ⟨isLimitExtendConeEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitExtendConeEquiv (G := G ⋙ H) F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

instance (priority := 100) compCreatesLimit {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesLimit G H] : CreatesLimit (F ⋙ G) H where
  lifts {c} hc := by
    refine ⟨(liftLimit ((isLimitExtendConeEquiv F (G := G ⋙ H) _).symm hc)).whisker F, ?_⟩
    let i := liftedLimitMapsToOriginal ((isLimitExtendConeEquiv F (G := G ⋙ H) _).symm hc)
    exact (Cone.whiskering F).mapIso i ≪≫ ((conesEquiv F (G ⋙ H)).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `limit_pre_isIso` / 实例 `limit_pre_isIso`

English:
instance limit_pre_isIso
  signature: [HasLimit G]
  body: by
  rw [limit.pre_eq (limitConeComp F (getLimitCone G)) (getLimitCone G)]
  simp only [limitConeComp_cone, Cone.whisker_pt, limitConeComp_isLimit, IsLimit.lift_self,
    Category.id_comp, isIso_comp_left_iff]
  infer_instance

中文:
实例 limit_pre_isIso
  签名: [HasLimit G]
  定义体: by
  rw [limit.pre_eq (limitConeComp F (getLimitCone G)) (getLimitCone G)]
  simp only [limitConeComp_cone, Cone.whisker_pt, limitConeComp_isLimit, IsLimit.lift_self,
    Category.id_comp, isIso_comp_left_iff]
  infer_instance

Depends on / 依赖: Category, Category.id_comp, Cone.whisker_pt, IsLimit, IsLimit.lift_self, getLimitCone, id_comp, infer_instance, isIso_comp_left_iff, lift_self, limit.pre_eq, limitConeComp, limitConeComp_cone, limitConeComp_isLimit, pre_eq, whisker_pt
-/
instance limit_pre_isIso [HasLimit G] : IsIso (limit.pre G F) := by
  rw [limit.pre_eq (limitConeComp F (getLimitCone G)) (getLimitCone G)]
  simp only [limitConeComp_cone, Cone.whisker_pt, limitConeComp_isLimit, IsLimit.lift_self,
    Category.id_comp, isIso_comp_left_iff]
  infer_instance

section

variable (G)

/-- When `F : C ⥤ D` is initial, and `G : D ⥤ E` has a limit, then `F ⋙ G` has a limit also and
`limit (F ⋙ G) ≅ limit G`. -/
@[simps! -isSimp, stacks 04E7]
/--
Definition of `limitIso` / `limitIso` 的定义

English:
definition limitIso
  signature: [HasLimit G]
  body: (asIso (limit.pre G F)).symm

中文:
定义 limitIso
  签名: [HasLimit G]
  定义体: (asIso (limit.pre G F)).symm

Depends on / 依赖: limit.pre
-/
def limitIso [HasLimit G] : limit (F ⋙ G) ≅ limit G :=
  (asIso (limit.pre G F)).symm

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `limIso` / `limIso` 的定义

English:
definition limIso
  signature: [HasLimitsOfShape D E] [HasLimitsOfShape C E]
  body: Iso.symm NatIso.ofComponents (fun G => (limitIso F G).symm) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, lim_obj, comp_map, whiskeringLeft_obj_map, lim_map,
      Iso.symm_hom, limitIso_inv]
    ext
    simp

中文:
定义 limIso
  签名: [HasLimitsOfShape D E] [HasLimitsOfShape C E]
  定义体: Iso.symm NatIso.ofComponents (fun G => (limitIso F G).symm) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, lim_obj, comp_map, whiskeringLeft_obj_map, lim_map,
      Iso.symm_hom, limitIso_inv]
    ext
    simp
-/
def limIso [HasLimitsOfShape D E] [HasLimitsOfShape C E] :
    (whiskeringLeft _ _ _).obj F ⋙ lim ≅ lim (J := D) (C := E) :=
Iso.symm NatIso.ofComponents (fun G => (limitIso F G).symm) fun f => by
    simp only [comp_obj, whiskeringLeft_obj_obj, lim_obj, comp_map, whiskeringLeft_obj_map, lim_map,
      Iso.symm_hom, limitIso_inv]
    ext
    simp

end

/-- Given a limit cone over `F ⋙ G` we can construct a limit cone over `G`. -/
@[simps]
/--
Definition of `limitConeOfComp` / `limitConeOfComp` 的定义

English:
definition limitConeOfComp
  signature: (t : LimitCone (F ⋙ G))
  body: extendCone.obj t.cone
  isLimit := (isLimitExtendConeEquiv F _).symm t.isLimit

中文:
定义 limitConeOfComp
  签名: (t : LimitCone (F ⋙ G))
  定义体: extendCone.obj t.cone
  isLimit := (isLimitExtendConeEquiv F _).symm t.isLimit

Depends on / 依赖: extendCone, extendCone.obj, t.cone
-/
def limitConeOfComp (t : LimitCone (F ⋙ G)) : LimitCone G where
  cone := extendCone.obj t.cone
  isLimit := (isLimitExtendConeEquiv F _).symm t.isLimit

/--
theorem `hasLimit_of_comp` / 定理 `hasLimit_of_comp`

English:
theorem hasLimit_of_comp
  given: [HasLimit (F ⋙ G)]
  statement: HasLimit G
  proof: HasLimit.mk (limitConeOfComp F (getLimitCone (F ⋙ G)))

中文:
定理 hasLimit_of_comp
  条件: [HasLimit (F ⋙ G)]
  结论: HasLimit G
  证明: HasLimit.mk (limitConeOfComp F (getLimitCone (F ⋙ G)))

Depends on / 依赖: HasEqualizers, HasLimit, HasLimit.mk, HasWeakEqualizersOfHasEqualizers, getLimitCone, limitConeOfComp
-/
theorem hasLimit_of_comp [HasLimit (F ⋙ G)] : HasLimit G :=
  HasLimit.mk (limitConeOfComp F (getLimitCone (F ⋙ G)))

/--
lemma `hasLimit_comp_iff` / 引理 `hasLimit_comp_iff`

English:
lemma hasLimit_comp_iff
  proof: ⟨fun _ => Functor.Initial.hasLimit_of_comp F, fun _ => inferInstance⟩

中文:
引理 hasLimit_comp_iff
  证明: ⟨fun _ => Functor.Initial.hasLimit_of_comp F, fun _ => inferInstance⟩

Depends on / 依赖: Functor, Functor.Initial.hasLimit_of_comp, Initial, hasLimit_of_comp
-/
lemma hasLimit_comp_iff :
    HasLimit (F ⋙ G) ↔ HasLimit G :=
  ⟨fun _ => Functor.Initial.hasLimit_of_comp F, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `preservesLimit_of_comp` / 定理 `preservesLimit_of_comp`

English:
theorem preservesLimit_of_comp
  statement: {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
  proof: by
    refine ⟨isLimitWhiskerEquiv F _ ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitWhiskerEquiv F _).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

中文:
定理 preservesLimit_of_comp
  结论: {B : 类型u₄} [Category.{v₄} B] {H : E ⥤ B}
  证明: by
    refine ⟨isLimitWhiskerEquiv F _ ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitWhiskerEquiv F _).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, isLimitOfPreserves, isLimitWhiskerEquiv, ofIsoLimit
-/
theorem preservesLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [PreservesLimit (F ⋙ G) H] : PreservesLimit G H where
  preserves {c} hc := by
    refine ⟨isLimitWhiskerEquiv F _ ?_⟩
    let hc' := isLimitOfPreserves H ((isLimitWhiskerEquiv F _).symm hc)
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `reflectsLimit_of_comp` / 定理 `reflectsLimit_of_comp`

English:
theorem reflectsLimit_of_comp
  statement: {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
  proof: by
    refine ⟨isLimitWhiskerEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitWhiskerEquiv F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

中文:
定理 reflectsLimit_of_comp
  结论: {B : 类型u₄} [Category.{v₄} B] {H : E ⥤ B}
  证明: by
    refine ⟨isLimitWhiskerEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitWhiskerEquiv F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, isLimitOfReflects, isLimitWhiskerEquiv, ofIsoLimit
-/
theorem reflectsLimit_of_comp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [ReflectsLimit (F ⋙ G) H] : ReflectsLimit G H where
  reflects {c} hc := by
    refine ⟨isLimitWhiskerEquiv F _ (isLimitOfReflects H ?_)⟩
    let hc' := (isLimitWhiskerEquiv F _).symm hc
    exact IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is initial and `F ⋙ G` creates limits of `H`, then so does `G`. -/
@[instance_reducible]
/--
Definition of `createsLimitOfComp` / `createsLimitOfComp` 的定义

English:
definition createsLimitOfComp
  signature: {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
  body: (reflectsLimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCone (F := F)).obj (liftLimit ((isLimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedLimitMapsToOriginal (K := (F ⋙ G)) ((isLimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCone (F := F)).mapIso i) ≪≫ ((conesEqu

中文:
定义 createsLimitOfComp
  签名: {B : 类型u₄} [Category.{v₄} B] {H : E ⥤ B}
  定义体: (reflectsLimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCone (F := F)).obj (liftLimit ((isLimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedLimitMapsToOriginal (K := (F ⋙ G)) ((isLimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCone (F := F)).mapIso i) ≪≫ ((conesEqu

Depends on / 依赖: reflects, reflectsLimit_of_comp
-/
def createsLimitOfComp {B : Type u₄} [Category.{v₄} B] {H : E ⥤ B}
    [CreatesLimit (F ⋙ G) H] : CreatesLimit G H where
  reflects := (reflectsLimit_of_comp F).reflects
  lifts {c} hc := by
    refine ⟨(extendCone (F := F)).obj (liftLimit ((isLimitWhiskerEquiv F _).symm hc)), ?_⟩
    let i := liftedLimitMapsToOriginal (K := (F ⋙ G)) ((isLimitWhiskerEquiv F _).symm hc)
    refine ?_ ≪≫ ((extendCone (F := F)).mapIso i) ≪≫ ((conesEquiv F (G ⋙ H)).counitIso.app _)
    exact Cone.ext (Iso.refl _)

include F in
/--
theorem `hasLimitsOfShape_of_initial` / 定理 `hasLimitsOfShape_of_initial`

English:
theorem hasLimitsOfShape_of_initial
  given: [HasLimitsOfShape C E]
  statement: HasLimitsOfShape D E where
  proof: fun _ => hasLimit_of_comp F

include F in

中文:
定理 hasLimitsOfShape_of_initial
  条件: [HasLimitsOfShape C E]
  结论: HasLimitsOfShape D E where
  证明: fun _ => hasLimit_of_comp F

include F in

Depends on / 依赖: hasLimit_of_comp
-/
theorem hasLimitsOfShape_of_initial [HasLimitsOfShape C E] : HasLimitsOfShape D E where
  has_limit := fun _ => hasLimit_of_comp F

include F in
/--
theorem `preservesLimitsOfShape_of_initial` / 定理 `preservesLimitsOfShape_of_initial`

English:
theorem preservesLimitsOfShape_of_initial
  statement: {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
  proof: preservesLimit_of_comp F

include F in

中文:
定理 preservesLimitsOfShape_of_initial
  结论: {B : 类型u₄} [Category.{v₄} B] (H : E ⥤ B)
  证明: preservesLimit_of_comp F

include F in

Depends on / 依赖: HasKernels, HasWeakKernelsOfHasKernels, preservesLimit_of_comp
-/
theorem preservesLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [PreservesLimitsOfShape C H] : PreservesLimitsOfShape D H where
  preservesLimit := preservesLimit_of_comp F

include F in
/--
theorem `reflectsLimitsOfShape_of_initial` / 定理 `reflectsLimitsOfShape_of_initial`

English:
theorem reflectsLimitsOfShape_of_initial
  statement: {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
  proof: reflectsLimit_of_comp F

include F in

中文:
定理 reflectsLimitsOfShape_of_initial
  结论: {B : 类型u₄} [Category.{v₄} B] (H : E ⥤ B)
  证明: reflectsLimit_of_comp F

include F in

Depends on / 依赖: reflectsLimit_of_comp
-/
theorem reflectsLimitsOfShape_of_initial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [ReflectsLimitsOfShape C H] : ReflectsLimitsOfShape D H where
  reflectsLimit := reflectsLimit_of_comp F

include F in
/-- If `H` creates limits of shape `C` and `F : C ⥤ D` is initial, then `H` creates limits of shape
`D`. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeOfInitial` / `createsLimitsOfShapeOfInitial` 的定义

English:
definition createsLimitsOfShapeOfInitial
  signature: {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
  body: createsLimitOfComp F

中文:
定义 createsLimitsOfShapeOfInitial
  签名: {B : 类型u₄} [Category.{v₄} B] (H : E ⥤ B)
  定义体: createsLimitOfComp F

Depends on / 依赖: createsLimitOfComp
-/
def createsLimitsOfShapeOfInitial {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B)
    [CreatesLimitsOfShape C H] : CreatesLimitsOfShape D H where
  CreatesLimit := createsLimitOfComp F

end Initial

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)

/--
theorem `final_of_comp_full_faithful` / 定理 `final_of_comp_full_faithful`

English:
theorem final_of_comp_full_faithful
  given: [Full G] [Faithful G] [Final (F ⋙ G)]
  statement: Final F where
  proof: isConnected_of_equivalent (StructuredArrow.post d F G).asEquivalence.symm

中文:
定理 final_of_comp_full_faithful
  条件: [Full G] [Faithful G] [Final (F ⋙ G)]
  结论: Final F where
  证明: isConnected_of_equivalent (StructuredArrow.post d F G).asEquivalence.symm

Depends on / 依赖: StructuredArrow, StructuredArrow.post, asEquivalence, asEquivalence.symm, isConnected_of_equivalent
-/
theorem final_of_comp_full_faithful [Full G] [Faithful G] [Final (F ⋙ G)] : Final F where
  out d := isConnected_of_equivalent (StructuredArrow.post d F G).asEquivalence.symm

/--
theorem `initial_of_comp_full_faithful` / 定理 `initial_of_comp_full_faithful`

English:
theorem initial_of_comp_full_faithful
  given: [Full G] [Faithful G] [Initial (F ⋙ G)]
  statement: Initial F where
  proof: isConnected_of_equivalent (CostructuredArrow.post F G d).asEquivalence.symm

中文:
定理 initial_of_comp_full_faithful
  条件: [Full G] [Faithful G] [Initial (F ⋙ G)]
  结论: Initial F where
  证明: isConnected_of_equivalent (CostructuredArrow.post F G d).asEquivalence.symm

Depends on / 依赖: CostructuredArrow, CostructuredArrow.post, asEquivalence, asEquivalence.symm, isConnected_of_equivalent
-/
theorem initial_of_comp_full_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where
  out d := isConnected_of_equivalent (CostructuredArrow.post F G d).asEquivalence.symm

/--
theorem `final_comp_equivalence` / 定理 `final_comp_equivalence`

English:
theorem final_comp_equivalence
  given: [Final F] [IsEquivalence G]
  statement: Final (F ⋙ G)
  proof: let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Final ((F ⋙ G) ⋙ G.inv) := final_of_natIso i
  final_of_comp_full_faithful (F ⋙ G) G.inv

中文:
定理 final_comp_equivalence
  条件: [Final F] [IsEquivalence G]
  结论: Final (F ⋙ G)
  证明: let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Final ((F ⋙ G) ⋙ G.inv) := final_of_natIso i
  final_of_comp_full_faithful (F ⋙ G) G.inv

Depends on / 依赖: G.asEquivalence.unitIso, G.inv, asEquivalence, final_of_comp_full_faithful, final_of_natIso, isoWhiskerLeft, unitIso
-/
theorem final_comp_equivalence [Final F] [IsEquivalence G] : Final (F ⋙ G) :=
  let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Final ((F ⋙ G) ⋙ G.inv) := final_of_natIso i
  final_of_comp_full_faithful (F ⋙ G) G.inv

/--
theorem `initial_comp_equivalence` / 定理 `initial_comp_equivalence`

English:
theorem initial_comp_equivalence
  given: [Initial F] [IsEquivalence G]
  statement: Initial (F ⋙ G)
  proof: let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Initial ((F ⋙ G) ⋙ G.inv) := initial_of_natIso i
  initial_of_comp_full_faithful (F ⋙ G) G.inv

中文:
定理 initial_comp_equivalence
  条件: [Initial F] [IsEquivalence G]
  结论: Initial (F ⋙ G)
  证明: let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Initial ((F ⋙ G) ⋙ G.inv) := initial_of_natIso i
  initial_of_comp_full_faithful (F ⋙ G) G.inv

Depends on / 依赖: G.asEquivalence.unitIso, G.inv, Initial, asEquivalence, initial_of_comp_full_faithful, initial_of_natIso, isoWhiskerLeft, unitIso
-/
theorem initial_comp_equivalence [Initial F] [IsEquivalence G] : Initial (F ⋙ G) :=
  let i : F ≅ (F ⋙ G) ⋙ G.inv := isoWhiskerLeft F G.asEquivalence.unitIso
  have : Initial ((F ⋙ G) ⋙ G.inv) := initial_of_natIso i
  initial_of_comp_full_faithful (F ⋙ G) G.inv

/--
theorem `final_equivalence_comp` / 定理 `final_equivalence_comp`

English:
theorem final_equivalence_comp
  given: [IsEquivalence F] [Final G]
  statement: Final (F ⋙ G) where
  proof: isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence.symm

中文:
定理 final_equivalence_comp
  条件: [IsEquivalence F] [Final G]
  结论: Final (F ⋙ G) where
  证明: isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence.symm

Depends on / 依赖: StructuredArrow, StructuredArrow.pre, asEquivalence, asEquivalence.symm, isConnected_of_equivalent
-/
theorem final_equivalence_comp [IsEquivalence F] [Final G] : Final (F ⋙ G) where
  out d := isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence.symm

/--
theorem `initial_equivalence_comp` / 定理 `initial_equivalence_comp`

English:
theorem initial_equivalence_comp
  given: [IsEquivalence F] [Initial G]
  statement: Initial (F ⋙ G) where
  proof: isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence.symm

中文:
定理 initial_equivalence_comp
  条件: [IsEquivalence F] [Initial G]
  结论: Initial (F ⋙ G) where
  证明: isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence.symm

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, asEquivalence, asEquivalence.symm, isConnected_of_equivalent
-/
theorem initial_equivalence_comp [IsEquivalence F] [Initial G] : Initial (F ⋙ G) where
  out d := isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence.symm

/--
theorem `final_of_equivalence_comp` / 定理 `final_of_equivalence_comp`

English:
theorem final_of_equivalence_comp
  given: [IsEquivalence F] [Final (F ⋙ G)]
  statement: Final G where
  proof: isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence

中文:
定理 final_of_equivalence_comp
  条件: [IsEquivalence F] [Final (F ⋙ G)]
  结论: Final G where
  证明: isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence

Depends on / 依赖: StructuredArrow, StructuredArrow.pre, asEquivalence, isConnected_of_equivalent
-/
theorem final_of_equivalence_comp [IsEquivalence F] [Final (F ⋙ G)] : Final G where
  out d := isConnected_of_equivalent (StructuredArrow.pre d F G).asEquivalence

/--
theorem `initial_of_equivalence_comp` / 定理 `initial_of_equivalence_comp`

English:
theorem initial_of_equivalence_comp
  given: [IsEquivalence F] [Initial (F ⋙ G)]
  statement: Initial G where
  proof: isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence

中文:
定理 initial_of_equivalence_comp
  条件: [IsEquivalence F] [Initial (F ⋙ G)]
  结论: Initial G where
  证明: isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, asEquivalence, isConnected_of_equivalent
-/
theorem initial_of_equivalence_comp [IsEquivalence F] [Initial (F ⋙ G)] : Initial G where
  out d := isConnected_of_equivalent (CostructuredArrow.pre F G d).asEquivalence

/--
theorem `final_iff_comp_equivalence` / 定理 `final_iff_comp_equivalence`

English:
theorem final_iff_comp_equivalence
  given: [IsEquivalence G]
  statement: Final F ↔ Final (F ⋙ G)
  proof: ⟨fun _ => final_comp_equivalence _ _, fun _ => final_of_comp_full_faithful _ G⟩

中文:
定理 final_iff_comp_equivalence
  条件: [IsEquivalence G]
  结论: Final F ↔ Final (F ⋙ G)
  证明: ⟨fun _ => final_comp_equivalence _ _, fun _ => final_of_comp_full_faithful _ G⟩

Depends on / 依赖: final_comp_equivalence, final_of_comp_full_faithful
-/
theorem final_iff_comp_equivalence [IsEquivalence G] : Final F ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp_equivalence _ _, fun _ => final_of_comp_full_faithful _ G⟩

/--
theorem `final_iff_equivalence_comp` / 定理 `final_iff_equivalence_comp`

English:
theorem final_iff_equivalence_comp
  given: [IsEquivalence F]
  statement: Final G ↔ Final (F ⋙ G)
  proof: ⟨fun _ => final_equivalence_comp _ _, fun _ => final_of_equivalence_comp F _⟩

中文:
定理 final_iff_equivalence_comp
  条件: [IsEquivalence F]
  结论: Final G ↔ Final (F ⋙ G)
  证明: ⟨fun _ => final_equivalence_comp _ _, fun _ => final_of_equivalence_comp F _⟩

Depends on / 依赖: final_equivalence_comp, final_of_equivalence_comp
-/
theorem final_iff_equivalence_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_equivalence_comp _ _, fun _ => final_of_equivalence_comp F _⟩

/--
theorem `initial_iff_comp_equivalence` / 定理 `initial_iff_comp_equivalence`

English:
theorem initial_iff_comp_equivalence
  given: [IsEquivalence G]
  statement: Initial F ↔ Initial (F ⋙ G)
  proof: ⟨fun _ => initial_comp_equivalence _ _, fun _ => initial_of_comp_full_faithful _ G⟩

中文:
定理 initial_iff_comp_equivalence
  条件: [IsEquivalence G]
  结论: Initial F ↔ Initial (F ⋙ G)
  证明: ⟨fun _ => initial_comp_equivalence _ _, fun _ => initial_of_comp_full_faithful _ G⟩

Depends on / 依赖: initial_comp_equivalence, initial_of_comp_full_faithful
-/
theorem initial_iff_comp_equivalence [IsEquivalence G] : Initial F ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp_equivalence _ _, fun _ => initial_of_comp_full_faithful _ G⟩

/--
theorem `initial_iff_equivalence_comp` / 定理 `initial_iff_equivalence_comp`

English:
theorem initial_iff_equivalence_comp
  given: [IsEquivalence F]
  statement: Initial G ↔ Initial (F ⋙ G)
  proof: ⟨fun _ => initial_equivalence_comp _ _, fun _ => initial_of_equivalence_comp F _⟩

中文:
定理 initial_iff_equivalence_comp
  条件: [IsEquivalence F]
  结论: Initial G ↔ Initial (F ⋙ G)
  证明: ⟨fun _ => initial_equivalence_comp _ _, fun _ => initial_of_equivalence_comp F _⟩

Depends on / 依赖: initial_equivalence_comp, initial_of_equivalence_comp
-/
theorem initial_iff_equivalence_comp [IsEquivalence F] : Initial G ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_equivalence_comp _ _, fun _ => initial_of_equivalence_comp F _⟩

/--
Instance `final_comp` / 实例 `final_comp`

English:
instance final_comp
  signature: [hF : Final F] [hG : Final G]
  body: by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G

中文:
实例 final_comp
  签名: [hF : Final F] [hG : Final G]
  定义体: by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G

Depends on / 依赖: AsSmall, AsSmall.equiv, final_iff_comp_equivalence, final_iff_equivalence_comp, final_natIso_iff, functor, inverse, isoWhiskerLeft, isoWhiskerRight, unitIso
-/
instance final_comp [hF : Final F] [hG : Final G] : Final (F ⋙ G) := by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G ⋙ s₃.functor) :=
    isoWhiskerLeft (s₁.inverse ⋙ F) (isoWhiskerRight s₂.unitIso (G ⋙ s₃.functor))
  rw [final_iff_comp_equivalence (F ⋙ G) s₃.functor]; rw [final_iff_equivalence_comp s₁.inverse]; rw [final_natIso_iff i]; rw [final_iff_isIso_colimit_pre]
  rw [final_iff_comp_equivalence F s₂.functor]; rw [final_iff_equivalence_comp s₁.inverse]; rw [final_iff_isIso_colimit_pre] at hF
  rw [final_iff_comp_equivalence G s₃.functor]; rw [final_iff_equivalence_comp s₂.inverse]; rw [final_iff_isIso_colimit_pre] at hG
  intro H
  rw [← colimit.pre_pre]
  infer_instance

/--
Instance `initial_comp` / 实例 `initial_comp`

English:
instance initial_comp
  signature: [Initial F] [Initial G]
  body: by
  suffices Final (F ⋙ G).op from initial_of_final_op _
  exact final_comp F.op G.op

中文:
实例 initial_comp
  签名: [Initial F] [Initial G]
  定义体: by
  suffices Final (F ⋙ G).op from initial_of_final_op _
  exact final_comp F.op G.op

Depends on / 依赖: F.op, G.op, final_comp, initial_of_final_op
-/
instance initial_comp [Initial F] [Initial G] : Initial (F ⋙ G) := by
  suffices Final (F ⋙ G).op from initial_of_final_op _
  exact final_comp F.op G.op

/--
theorem `final_of_final_comp` / 定理 `final_of_final_comp`

English:
theorem final_of_final_comp
  given: [hF : Final F] [hFG : Final (F ⋙ G)]
  statement: Final G
  proof: by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let _i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ 

中文:
定理 final_of_final_comp
  条件: [hF : Final F] [hFG : Final (F ⋙ G)]
  结论: Final G
  证明: by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let _i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ 

Depends on / 依赖: AsSmall, AsSmall.equiv, final_iff_comp_equivalence, final_iff_equivalence_comp, final_iff_isIso_colimit, functor, inverse, isoWhiskerLeft, isoWhiskerRight, unitIso
-/
theorem final_of_final_comp [hF : Final F] [hFG : Final (F ⋙ G)] : Final G := by
  let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} C := AsSmall.equiv
  let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} D := AsSmall.equiv
  let s₃ : E ≌ AsSmall.{max u₁ v₁ u₂ v₂ u₃ v₃} E := AsSmall.equiv
  let _i : s₁.inverse ⋙ (F ⋙ G) ⋙ s₃.functor ≅
      (s₁.inverse ⋙ F ⋙ s₂.functor) ⋙ (s₂.inverse ⋙ G ⋙ s₃.functor) :=
    isoWhiskerLeft (s₁.inverse ⋙ F) (isoWhiskerRight s₂.unitIso (G ⋙ s₃.functor))
  rw [final_iff_comp_equivalence G s₃.functor]; rw [final_iff_equivalence_comp s₂.inverse]; rw [final_iff_isIso_colimit_pre]
  rw [final_iff_comp_equivalence F s₂.functor]; rw [final_iff_equivalence_comp s₁.inverse]; rw [final_iff_isIso_colimit_pre] at hF
  rw [final_iff_comp_equivalence (F ⋙ G) s₃.functor]; rw [final_iff_equivalence_comp s₁.inverse]; rw [final_natIso_iff _i]; rw [final_iff_isIso_colimit_pre] at hFG
  intro H
  replace hFG := hFG H
  rw [← colimit.pre_pre] at hFG
  exact IsIso.of_isIso_comp_left (colimit.pre _ (s₁.inverse ⋙ F ⋙ s₂.functor)) _

/--
theorem `initial_of_initial_comp` / 定理 `initial_of_initial_comp`

English:
theorem initial_of_initial_comp
  given: [Initial F] [Initial (F ⋙ G)]
  statement: Initial G
  proof: by
  suffices Final G.op from initial_of_final_op _
  have : Final (F.op ⋙ G.op) := show Final (F ⋙ G).op from inferInstance
  exact final_of_final_comp F.op G.op

中文:
定理 initial_of_initial_comp
  条件: [Initial F] [Initial (F ⋙ G)]
  结论: Initial G
  证明: by
  suffices Final G.op from initial_of_final_op _
  have : Final (F.op ⋙ G.op) := show Final (F ⋙ G).op from inferInstance
  exact final_of_final_comp F.op G.op

Depends on / 依赖: F.op, G.op, final_of_final_comp, initial_of_final_op
-/
theorem initial_of_initial_comp [Initial F] [Initial (F ⋙ G)] : Initial G := by
  suffices Final G.op from initial_of_final_op _
  have : Final (F.op ⋙ G.op) := show Final (F ⋙ G).op from inferInstance
  exact final_of_final_comp F.op G.op

/--
theorem `final_of_comp_full_faithful'` / 定理 `final_of_comp_full_faithful'`

English:
theorem final_of_comp_full_faithful'
  given: [Full G] [Faithful G] [Final (F ⋙ G)]
  statement: Final G
  proof: have := final_of_comp_full_faithful F G
  final_of_final_comp F G

中文:
定理 final_of_comp_full_faithful'
  条件: [Full G] [Faithful G] [Final (F ⋙ G)]
  结论: Final G
  证明: have := final_of_comp_full_faithful F G
  final_of_final_comp F G

Depends on / 依赖: final_of_comp_full_faithful, final_of_final_comp
-/
theorem final_of_comp_full_faithful' [Full G] [Faithful G] [Final (F ⋙ G)] : Final G :=
  have := final_of_comp_full_faithful F G
  final_of_final_comp F G

/--
theorem `initial_of_comp_full_faithful'` / 定理 `initial_of_comp_full_faithful'`

English:
theorem initial_of_comp_full_faithful'
  given: [Full G] [Faithful G] [Initial (F ⋙ G)]
  statement: Initial G
  proof: have := initial_of_comp_full_faithful F G
  initial_of_initial_comp F G

中文:
定理 initial_of_comp_full_faithful'
  条件: [Full G] [Faithful G] [Initial (F ⋙ G)]
  结论: Initial G
  证明: have := initial_of_comp_full_faithful F G
  initial_of_initial_comp F G

Depends on / 依赖: initial_of_comp_full_faithful, initial_of_initial_comp
-/
theorem initial_of_comp_full_faithful' [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial G :=
  have := initial_of_comp_full_faithful F G
  initial_of_initial_comp F G

/--
theorem `final_iff_comp_final_full_faithful` / 定理 `final_iff_comp_final_full_faithful`

English:
theorem final_iff_comp_final_full_faithful
  given: [Final G] [Full G] [Faithful G]
  proof: ⟨fun _ => final_comp _ _, fun _ => final_of_comp_full_faithful F G⟩

中文:
定理 final_iff_comp_final_full_faithful
  条件: [Final G] [Full G] [Faithful G]
  证明: ⟨fun _ => final_comp _ _, fun _ => final_of_comp_full_faithful F G⟩

Depends on / 依赖: final_comp, final_of_comp_full_faithful
-/
theorem final_iff_comp_final_full_faithful [Final G] [Full G] [Faithful G] :
    Final F ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp _ _, fun _ => final_of_comp_full_faithful F G⟩

/--
theorem `initial_iff_comp_initial_full_faithful` / 定理 `initial_iff_comp_initial_full_faithful`

English:
theorem initial_iff_comp_initial_full_faithful
  given: [Initial G] [Full G] [Faithful G]
  proof: ⟨fun _ => initial_comp _ _, fun _ => initial_of_comp_full_faithful F G⟩

中文:
定理 initial_iff_comp_initial_full_faithful
  条件: [Initial G] [Full G] [Faithful G]
  证明: ⟨fun _ => initial_comp _ _, fun _ => initial_of_comp_full_faithful F G⟩

Depends on / 依赖: initial_comp, initial_of_comp_full_faithful
-/
theorem initial_iff_comp_initial_full_faithful [Initial G] [Full G] [Faithful G] :
    Initial F ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp _ _, fun _ => initial_of_comp_full_faithful F G⟩

/--
theorem `final_iff_final_comp` / 定理 `final_iff_final_comp`

English:
theorem final_iff_final_comp
  given: [Final F]
  statement: Final G ↔ Final (F ⋙ G)
  proof: ⟨fun _ => final_comp _ _, fun _ => final_of_final_comp F G⟩

中文:
定理 final_iff_final_comp
  条件: [Final F]
  结论: Final G ↔ Final (F ⋙ G)
  证明: ⟨fun _ => final_comp _ _, fun _ => final_of_final_comp F G⟩

Depends on / 依赖: final_comp, final_of_final_comp
-/
theorem final_iff_final_comp [Final F] : Final G ↔ Final (F ⋙ G) :=
  ⟨fun _ => final_comp _ _, fun _ => final_of_final_comp F G⟩

/--
theorem `initial_iff_initial_comp` / 定理 `initial_iff_initial_comp`

English:
theorem initial_iff_initial_comp
  given: [Initial F]
  statement: Initial G ↔ Initial (F ⋙ G)
  proof: ⟨fun _ => initial_comp _ _, fun _ => initial_of_initial_comp F G⟩

中文:
定理 initial_iff_initial_comp
  条件: [Initial F]
  结论: Initial G ↔ Initial (F ⋙ G)
  证明: ⟨fun _ => initial_comp _ _, fun _ => initial_of_initial_comp F G⟩

Depends on / 依赖: initial_comp, initial_of_initial_comp
-/
theorem initial_iff_initial_comp [Initial F] : Initial G ↔ Initial (F ⋙ G) :=
  ⟨fun _ => initial_comp _ _, fun _ => initial_of_initial_comp F G⟩

end

section

variable {C : Type u₁} [Category.{v₁} C] {c : C}

/--
lemma `final_fromPUnit_of_isTerminal` / 引理 `final_fromPUnit_of_isTerminal`

English:
lemma final_fromPUnit_of_isTerminal
  given: (hc : Limits.IsTerminal c)
  statement: (fromPUnit c).Final where
  proof: by
    let : Inhabited (StructuredArrow c' (fromPUnit c)) := ⟨.mk (Y := default) (hc.from c')⟩
    let : Subsingleton (StructuredArrow c' (fromPUnit c)) :=
      ⟨fun i j => StructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance

中文:
引理 final_fromPUnit_of_isTerminal
  条件: (hc : Limits.IsTerminal c)
  结论: (fromPUnit c).Final where
  证明: by
    let : Inhabited (StructuredArrow c' (fromPUnit c)) := ⟨.mk (Y := default) (hc.from c')⟩
    let : Subsingleton (StructuredArrow c' (fromPUnit c)) :=
      ⟨fun i j => StructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance

Depends on / 依赖: Inhabited, StructuredArrow, StructuredArrow.obj_ext, Subsingleton, cat_disch, fromPUnit, hc.from, hc.hom_ext, hom_ext, infer_instance, obj_ext
-/
lemma final_fromPUnit_of_isTerminal (hc : Limits.IsTerminal c) : (fromPUnit c).Final where
  out c' := by
    let : Inhabited (StructuredArrow c' (fromPUnit c)) := ⟨.mk (Y := default) (hc.from c')⟩
    let : Subsingleton (StructuredArrow c' (fromPUnit c)) :=
      ⟨fun i j => StructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance

/--
lemma `initial_fromPUnit_of_isInitial` / 引理 `initial_fromPUnit_of_isInitial`

English:
lemma initial_fromPUnit_of_isInitial
  given: (hc : Limits.IsInitial c)
  statement: (fromPUnit c).Initial where
  proof: by
    let : Inhabited (CostructuredArrow (fromPUnit c) c') := ⟨.mk (Y := default) (hc.to c')⟩
    let : Subsingleton (CostructuredArrow (fromPUnit c) c') :=
      ⟨fun i j => CostructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance

中文:
引理 initial_fromPUnit_of_isInitial
  条件: (hc : Limits.IsInitial c)
  结论: (fromPUnit c).Initial where
  证明: by
    let : Inhabited (CostructuredArrow (fromPUnit c) c') := ⟨.mk (Y := default) (hc.to c')⟩
    let : Subsingleton (CostructuredArrow (fromPUnit c) c') :=
      ⟨fun i j => CostructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance

Depends on / 依赖: CostructuredArrow, CostructuredArrow.obj_ext, Inhabited, Subsingleton, cat_disch, fromPUnit, hc.hom_ext, hc.to, hom_ext, infer_instance, obj_ext
-/
lemma initial_fromPUnit_of_isInitial (hc : Limits.IsInitial c) : (fromPUnit c).Initial where
  out c' := by
    let : Inhabited (CostructuredArrow (fromPUnit c) c') := ⟨.mk (Y := default) (hc.to c')⟩
    let : Subsingleton (CostructuredArrow (fromPUnit c) c') :=
      ⟨fun i j => CostructuredArrow.obj_ext _ _ (by cat_disch) (hc.hom_ext _ _)⟩
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasTerminal
  signature: C] {D
  body: have : (fromPUnit.{0} (⊤_ C)).Final := final_fromPUnit_of_isTerminal terminalIsTerminal
  have : (fromPUnit.{0} (F.obj (⊤_ C))).Final := final_fromPUnit_of_isTerminal
    (terminalIsTerminal.isTerminalObj F (⊤_ C))
  have : ((fromPUnit.{0} (⊤_ C)) ⋙ F).Final := final_of_natIso (F := fromPUnit.{0} (F

中文:
实例 [HasTerminal
  签名: C] {D
  定义体: have : (fromPUnit.{0} (⊤_ C)).Final := final_fromPUnit_of_isTerminal terminalIsTerminal
  have : (fromPUnit.{0} (F.obj (⊤_ C))).Final := final_fromPUnit_of_isTerminal
    (terminalIsTerminal.isTerminalObj F (⊤_ C))
  have : ((fromPUnit.{0} (⊤_ C)) ⋙ F).Final := final_of_natIso (F := fromPUnit.{0} (F

Depends on / 依赖: Discrete, Discrete.natIso, F.obj, Iso.refl, final_fromPUnit_of_isTerminal, final_of_final_comp, final_of_natIso, fromPUnit, isTerminalObj, natIso, terminalIsTerminal, terminalIsTerminal.isTerminalObj
-/
instance [HasTerminal C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesLimit (Functor.empty.{0} C) F] : F.Final :=
  have : (fromPUnit.{0} (⊤_ C)).Final := final_fromPUnit_of_isTerminal terminalIsTerminal
  have : (fromPUnit.{0} (F.obj (⊤_ C))).Final := final_fromPUnit_of_isTerminal
    (terminalIsTerminal.isTerminalObj F (⊤_ C))
  have : ((fromPUnit.{0} (⊤_ C)) ⋙ F).Final := final_of_natIso (F := fromPUnit.{0} (F.obj (⊤_ C)))
    (Discrete.natIso (fun _ => Iso.refl _))
  final_of_final_comp (fromPUnit.{0} (⊤_ C)) F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasInitial
  signature: C] {D
  body: have : (fromPUnit.{0} (⊥_ C)).Initial := initial_fromPUnit_of_isInitial initialIsInitial
  have : (fromPUnit.{0} (F.obj (⊥_ C))).Initial := initial_fromPUnit_of_isInitial
    (initialIsInitial.isInitialObj F (⊥_ C))
  have : ((fromPUnit.{0} (⊥_ C)) ⋙ F).Initial := initial_of_natIso
    (F := fromPUn

中文:
实例 [HasInitial
  签名: C] {D
  定义体: have : (fromPUnit.{0} (⊥_ C)).Initial := initial_fromPUnit_of_isInitial initialIsInitial
  have : (fromPUnit.{0} (F.obj (⊥_ C))).Initial := initial_fromPUnit_of_isInitial
    (initialIsInitial.isInitialObj F (⊥_ C))
  have : ((fromPUnit.{0} (⊥_ C)) ⋙ F).Initial := initial_of_natIso
    (F := fromPUn

Depends on / 依赖: Discrete, Discrete.natIso, F.obj, Initial, Iso.refl, fromPUnit, initialIsInitial, initialIsInitial.isInitialObj, initial_fromPUnit_of_isInitial, initial_of_initial_comp, initial_of_natIso, isInitialObj, natIso
-/
instance [HasInitial C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesColimit (Functor.empty.{0} C) F] : F.Initial :=
  have : (fromPUnit.{0} (⊥_ C)).Initial := initial_fromPUnit_of_isInitial initialIsInitial
  have : (fromPUnit.{0} (F.obj (⊥_ C))).Initial := initial_fromPUnit_of_isInitial
    (initialIsInitial.isInitialObj F (⊥_ C))
  have : ((fromPUnit.{0} (⊥_ C)) ⋙ F).Initial := initial_of_natIso
    (F := fromPUnit.{0} (F.obj (⊥_ C))) (Discrete.natIso (fun _ => Iso.refl _))
  initial_of_initial_comp (fromPUnit.{0} (⊥_ C)) F

end

section

variable {C D : Type*} [Category* C] [Category* D]

instance (F : C ⥤ Dᵒᵖ) [Initial F] : F.leftOp.Final :=
  inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).Final

instance (F : C ⥤ Dᵒᵖ) [Final F] : F.leftOp.Initial :=
  inferInstanceAs (F.op ⋙ (opOpEquivalence D).functor).Initial

instance (F : Cᵒᵖ ⥤ D) [Initial F] : F.rightOp.Final :=
  inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).Final

instance (F : Cᵒᵖ ⥤ D) [Final F] : F.rightOp.Initial :=
  inferInstanceAs ((opOpEquivalence C).inverse ⋙ F.op).Initial

end


end Functor

section Filtered
open CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsFilteredOrEmpty.of_final` / 定理 `IsFilteredOrEmpty.of_final`

English:
theorem IsFilteredOrEmpty.of_final
  given: (F : C ⥤ D) [Final F] [IsFilteredOrEmpty C]
  proof: ⟨F.obj (IsFiltered.max (Final.lift F X) (Final.lift F Y)),
    Final.homToLift F X ≫ F.map (IsFiltered.leftToMax _ _),
    ⟨Final.homToLift F Y ≫ F.map (IsFiltered.rightToMax _ _), trivial⟩⟩
  cocone_maps {X Y} f g := by
    let P : StructuredArrow X F -> Prop := fun h => exists (Z : C) (q₁ : h.righ

中文:
定理 IsFilteredOrEmpty.of_final
  条件: (F : C ⥤ D) [Final F] [IsFilteredOrEmpty C]
  证明: ⟨F.obj (IsFiltered.max (Final.lift F X) (Final.lift F Y)),
    Final.homToLift F X ≫ F.map (IsFiltered.leftToMax _ _),
    ⟨Final.homToLift F Y ≫ F.map (IsFiltered.rightToMax _ _), trivial⟩⟩
  cocone_maps {X Y} f g := by
    let P : StructuredArrow X F -> Prop := fun h => exists (Z : C) (q₁ : h.righ

Depends on / 依赖: F.obj, Final.lift, IsFiltered, IsFiltered.max
-/
theorem IsFilteredOrEmpty.of_final (F : C ⥤ D) [Final F] [IsFilteredOrEmpty C] :
    IsFilteredOrEmpty D where
  cocone_objs X Y := ⟨F.obj (IsFiltered.max (Final.lift F X) (Final.lift F Y)),
    Final.homToLift F X ≫ F.map (IsFiltered.leftToMax _ _),
    ⟨Final.homToLift F Y ≫ F.map (IsFiltered.rightToMax _ _), trivial⟩⟩
  cocone_maps {X Y} f g := by
    let P : StructuredArrow X F -> Prop := fun h => exists (Z : C) (q₁ : h.right ⟶ Z)
      (q₂ : Final.lift F Y ⟶ Z), h.hom ≫ F.map q₁ = f ≫ Final.homToLift F Y ≫ F.map q₂
    rsuffices ⟨Z, q₁, q₂, h⟩ : Nonempty (P (StructuredArrow.mk (g ≫ Final.homToLift F Y)))
    · refine ⟨F.obj (IsFiltered.coeq q₁ q₂),
        Final.homToLift F Y ≫ F.map (q₁ ≫ IsFiltered.coeqHom q₁ q₂), ?_⟩
      conv_lhs => rw [IsFiltered.coeq_condition]
      simp only [F.map_comp, ← reassoc_of% h, StructuredArrow.mk_hom_eq_self, Category.assoc]
    have h₀ : P (StructuredArrow.mk (f ≫ Final.homToLift F Y)) := ⟨_, 𝟙 _, 𝟙 _, by simp⟩
    refine isPreconnected_induction P ?_ ?_ h₀ _
    · rintro U V h ⟨Z, q₁, q₂, hq⟩
      obtain ⟨W, q₃, q₄, hq'⟩ := IsFiltered.span q₁ h.right
      refine ⟨W, q₄, q₂ ≫ q₃, ?_⟩
      rw [F.map_comp]; rw [← reassoc_of% hq]; rw [← F.map_comp]; rw [hq']; rw [F.map_comp]; rw [StructuredArrow.w_assoc]
    · rintro U V h ⟨Z, q₁, q₂, hq⟩
      exact ⟨Z, h.right ≫ q₁, q₂, by simp only [F.map_comp, StructuredArrow.w_assoc, hq]⟩

/--
theorem `IsFiltered.of_final` / 定理 `IsFiltered.of_final`

English:
theorem IsFiltered.of_final
  given: (F : C ⥤ D) [Final F] [IsFiltered C]
  statement: IsFiltered D
  proof: { IsFilteredOrEmpty.of_final F with
  nonempty := Nonempty.map F.obj IsFiltered.nonempty }

中文:
定理 IsFiltered.of_final
  条件: (F : C ⥤ D) [Final F] [IsFiltered C]
  结论: IsFiltered D
  证明: { IsFilteredOrEmpty.of_final F with
  nonempty := Nonempty.map F.obj IsFiltered.nonempty }

Depends on / 依赖: F.obj, IsFiltered, IsFiltered.nonempty, IsFilteredOrEmpty, IsFilteredOrEmpty.of_final, Nonempty, Nonempty.map, nonempty, of_final
-/
theorem IsFiltered.of_final (F : C ⥤ D) [Final F] [IsFiltered C] : IsFiltered D :=
{ IsFilteredOrEmpty.of_final F with
  nonempty := Nonempty.map F.obj IsFiltered.nonempty }

/--
theorem `IsCofilteredOrEmpty.of_initial` / 定理 `IsCofilteredOrEmpty.of_initial`

English:
theorem IsCofilteredOrEmpty.of_initial
  given: (F : C ⥤ D) [Initial F] [IsCofilteredOrEmpty C]
  proof: have : IsFilteredOrEmpty Dᵒᵖ := IsFilteredOrEmpty.of_final F.op
  isCofilteredOrEmpty_of_isFilteredOrEmpty_op _

中文:
定理 IsCofilteredOrEmpty.of_initial
  条件: (F : C ⥤ D) [Initial F] [IsCofilteredOrEmpty C]
  证明: have : IsFilteredOrEmpty Dᵒᵖ := IsFilteredOrEmpty.of_final F.op
  isCofilteredOrEmpty_of_isFilteredOrEmpty_op _

Depends on / 依赖: F.op, IsFilteredOrEmpty, IsFilteredOrEmpty.of_final, isCofilteredOrEmpty_of_isFilteredOrEmpty_op, of_final
-/
theorem IsCofilteredOrEmpty.of_initial (F : C ⥤ D) [Initial F] [IsCofilteredOrEmpty C] :
    IsCofilteredOrEmpty D :=
  have : IsFilteredOrEmpty Dᵒᵖ := IsFilteredOrEmpty.of_final F.op
  isCofilteredOrEmpty_of_isFilteredOrEmpty_op _

/--
theorem `IsCofiltered.of_initial` / 定理 `IsCofiltered.of_initial`

English:
theorem IsCofiltered.of_initial
  given: (F : C ⥤ D) [Initial F] [IsCofiltered C]
  statement: IsCofiltered D
  proof: have : IsFiltered Dᵒᵖ := IsFiltered.of_final F.op
  isCofiltered_of_isFiltered_op _

中文:
定理 IsCofiltered.of_initial
  条件: (F : C ⥤ D) [Initial F] [IsCofiltered C]
  结论: IsCofiltered D
  证明: have : IsFiltered Dᵒᵖ := IsFiltered.of_final F.op
  isCofiltered_of_isFiltered_op _

Depends on / 依赖: F.op, IsFiltered, IsFiltered.of_final, isCofiltered_of_isFiltered_op, of_final
-/
theorem IsCofiltered.of_initial (F : C ⥤ D) [Initial F] [IsCofiltered C] : IsCofiltered D :=
  have : IsFiltered Dᵒᵖ := IsFiltered.of_final F.op
  isCofiltered_of_isFiltered_op _

end Filtered

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

open CategoryTheory.Functor

/--
Instance `StructuredArrow.final_pre` / 实例 `StructuredArrow.final_pre`

English:
instance StructuredArrow.final_pre
  signature: (T : C ⥤ D) [Final T] (S : D ⥤ E) (X : E)
  body: by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (StructuredArrow.preEquivalence T f)]
  exact Final.out f.right

中文:
实例 StructuredArrow.final_pre
  签名: (T : C ⥤ D) [Final T] (S : D ⥤ E) (X : E)
  定义体: by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (StructuredArrow.preEquivalence T f)]
  exact Final.out f.right

Depends on / 依赖: Final.out, StructuredArrow, StructuredArrow.preEquivalence, f.right, isConnected_iff_of_equivalence, preEquivalence
-/
instance StructuredArrow.final_pre (T : C ⥤ D) [Final T] (S : D ⥤ E) (X : E) :
    Final (pre X T S) := by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (StructuredArrow.preEquivalence T f)]
  exact Final.out f.right

/--
Instance `CostructuredArrow.initial_pre` / 实例 `CostructuredArrow.initial_pre`

English:
instance CostructuredArrow.initial_pre
  signature: (T : C ⥤ D) [Initial T] (S : D ⥤ E) (X : E)
  body: by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (CostructuredArrow.preEquivalence T f)]
  exact Initial.out f.left

中文:
实例 CostructuredArrow.initial_pre
  签名: (T : C ⥤ D) [Initial T] (S : D ⥤ E) (X : E)
  定义体: by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (CostructuredArrow.preEquivalence T f)]
  exact Initial.out f.left

Depends on / 依赖: CostructuredArrow, CostructuredArrow.preEquivalence, Initial, Initial.out, f.left, isConnected_iff_of_equivalence, preEquivalence
-/
instance CostructuredArrow.initial_pre (T : C ⥤ D) [Initial T] (S : D ⥤ E) (X : E) :
    Initial (CostructuredArrow.pre T S X) := by
  refine ⟨fun f => ?_⟩
  rw [isConnected_iff_of_equivalence (CostructuredArrow.preEquivalence T f)]
  exact Initial.out f.left

end

section Grothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : D ⥤ Cat) (G : C ⥤ D)

open CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Grothendieck.structuredArrowToStructuredArrowPre` / `Grothendieck.structuredArrowToStructuredArrowPre` 的定义

English:
definition Grothendieck.structuredArrowToStructuredArrowPre
  signature: (d : D) (f : F.obj d)
  body: fun X => StructuredArrow.mk (Y := ⟨X.right, (F.map X.hom).toFunctor.obj f⟩)
    (Grothendieck.Hom.mk (by exact X.hom) (by dsimp; exact 𝟙 _))
  map := fun g => StructuredArrow.homMk
    (Grothendieck.Hom.mk (by exact g.right)
      (eqToHom (by
        dsimp +instances
        rw [← StructuredArrow.w

中文:
定义 Grothendieck.structuredArrowToStructuredArrowPre
  签名: (d : D) (f : F.obj d)
  定义体: fun X => StructuredArrow.mk (Y := ⟨X.right, (F.map X.hom).toFunctor.obj f⟩)
    (Grothendieck.Hom.mk (by exact X.hom) (by dsimp; exact 𝟙 _))
  map := fun g => StructuredArrow.homMk
    (Grothendieck.Hom.mk (by exact g.right)
      (eqToHom (by
        dsimp +instances
        rw [← StructuredArrow.w

Depends on / 依赖: F.map, StructuredArrow, StructuredArrow.mk, X.hom, X.right, toFunctor, toFunctor.obj
-/
def Grothendieck.structuredArrowToStructuredArrowPre (d : D) (f : F.obj d) :
    StructuredArrow d G ⥤q StructuredArrow ⟨d, f⟩ (pre F G) where
  obj := fun X => StructuredArrow.mk (Y := ⟨X.right, (F.map X.hom).toFunctor.obj f⟩)
    (Grothendieck.Hom.mk (by exact X.hom) (by dsimp; exact 𝟙 _))
  map := fun g => StructuredArrow.homMk
    (Grothendieck.Hom.mk (by exact g.right)
      (eqToHom (by
        dsimp +instances
        rw [← StructuredArrow.w g]; rw [map_comp]; rw [Cat.Hom.comp_obj])))
    (by
      simp only [StructuredArrow.mk_right]
      generalize_proofs
      apply Grothendieck.ext <;> simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `Grothendieck.final_pre` / 实例 `Grothendieck.final_pre`

English:
instance Grothendieck.final_pre
  signature: [hG : Final G]
  body: by
  constructor
  rintro ⟨d, f⟩
  let ⟨u, c, g⟩ : Nonempty (StructuredArrow d G) := inferInstance
  let : Nonempty (StructuredArrow ⟨d, f⟩ (pre F G)) :=
    ⟨u, ⟨c, (F.map g).toFunctor.obj f⟩, ⟨(by exact g), (by exact 𝟙 _)⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨⟨⟩⟩, ⟨bi, fi⟩, ⟨gbi, gfi⟩⟩ ⟨⟨⟨⟩⟩, ⟨b

中文:
实例 Grothendieck.final_pre
  签名: [hG : Final G]
  定义体: by
  constructor
  rintro ⟨d, f⟩
  let ⟨u, c, g⟩ : Nonempty (StructuredArrow d G) := inferInstance
  let : Nonempty (StructuredArrow ⟨d, f⟩ (pre F G)) :=
    ⟨u, ⟨c, (F.map g).toFunctor.obj f⟩, ⟨(by exact g), (by exact 𝟙 _)⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨⟨⟩⟩, ⟨bi, fi⟩, ⟨gbi, gfi⟩⟩ ⟨⟨⟨⟩⟩, ⟨b

Depends on / 依赖: F.map, Grothendieck, Grothendieck.Hom.mk, Nonempty, StructuredArrow, StructuredArrow.h, StructuredArrow.mk, Zigzag, Zigzag.trans, instances, of_zag, toFunctor, toFunctor.obj, zigzag_isConnected
-/
instance Grothendieck.final_pre [hG : Final G] : (Grothendieck.pre F G).Final := by
  constructor
  rintro ⟨d, f⟩
  let ⟨u, c, g⟩ : Nonempty (StructuredArrow d G) := inferInstance
  let : Nonempty (StructuredArrow ⟨d, f⟩ (pre F G)) :=
    ⟨u, ⟨c, (F.map g).toFunctor.obj f⟩, ⟨(by exact g), (by exact 𝟙 _)⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨⟨⟩⟩, ⟨bi, fi⟩, ⟨gbi, gfi⟩⟩ ⟨⟨⟨⟩⟩, ⟨bj, fj⟩, ⟨gbj, gfj⟩⟩
  dsimp +instances at fj fi gfi gbi gbj gfj
  apply Zigzag.trans (j₂ := StructuredArrow.mk (Y := ⟨bi, ((F.map gbi).toFunctor.obj f)⟩)
      (Grothendieck.Hom.mk gbi (𝟙 _)))
    (.of_zag (.inr ⟨StructuredArrow.homMk (Grothendieck.Hom.mk (by dsimp; exact 𝟙 _)
      (eqToHom (by simp) ≫ gfi)) (by apply Grothendieck.ext <;> simp)⟩))
  refine Zigzag.trans (j₂ := StructuredArrow.mk (Y := ⟨bj, ((F.map gbj).toFunctor.obj f)⟩)
      (Grothendieck.Hom.mk gbj (𝟙 _))) ?_
    (.of_zag (.inl ⟨StructuredArrow.homMk (Grothendieck.Hom.mk (by dsimp; exact 𝟙 _)
      (eqToHom (by simp) ≫ gfj)) (by apply Grothendieck.ext <;> simp)⟩))
  exact zigzag_prefunctor_obj_of_zigzag (Grothendieck.structuredArrowToStructuredArrowPre F G d f)
    (isPreconnected_zigzag (.mk gbi) (.mk gbj))

open Limits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Grothendieck.fiberwiseColimitMapCompEquivalence` / `Grothendieck.fiberwiseColimitMapCompEquivalence` 的定义

English:
definition Grothendieck.fiberwiseColimitMapCompEquivalence
  signature: {C : Type u₁} [Category.{v₁} C]
  body: NatIso.ofComponents
    (fun X =>
      HasColimit.isoOfNatIso ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (ιCompMap α X) H ≪≫ Functor.associator _ _ _) ≪≫
      Final.colimitIso (α.app X).toFunctor (ι G X ⋙ H))
    (fun f => colimit.hom_ext <| fun d => by
      simp only [map, Cat.H

中文:
定义 Grothendieck.fiberwiseColimitMapCompEquivalence
  签名: {C : 类型u₁} [Category.{v₁} C]
  定义体: NatIso.ofComponents
    (fun X =>
      HasColimit.isoOfNatIso ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (ιCompMap α X) H ≪≫ Functor.associator _ _ _) ≪≫
      Final.colimitIso (α.app X).toFunctor (ι G X ⋙ H))
    (fun f => colimit.hom_ext <| fun d => by
      simp only [map, Cat.H

Depends on / 依赖: Cat.Hom, Cat.Hom.comp_toFunctor, Category, Category.assoc, Final.colimitIso, Functor, Functor.associator, Functor.comp_map, HasColimit, HasColimit.isoOfNatIso, Iso.trans_hom, NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app, associator, colimit, colimit.hom_ext, colimitIso, comp_app
-/
def Grothendieck.fiberwiseColimitMapCompEquivalence {C : Type u₁} [Category.{v₁} C]
    {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) [forall X, Final (α.app X).toFunctor]
    (H : Grothendieck G ⥤ Type u₂) : fiberwiseColimit (map α ⋙ H) ≅ fiberwiseColimit H :=
  NatIso.ofComponents
    (fun X =>
      HasColimit.isoOfNatIso ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (ιCompMap α X) H ≪≫ Functor.associator _ _ _) ≪≫
      Final.colimitIso (α.app X).toFunctor (ι G X ⋙ H))
    (fun f => colimit.hom_ext <| fun d => by
      simp only [map, Cat.Hom.comp_toFunctor, comp_obj, ι_obj,
        fiberwiseColimit_map, ιNatTrans, ιCompMap, Iso.trans_hom, Category.assoc, ι_colimMap_assoc,
        NatTrans.comp_app, whiskerRight_app, Functor.comp_map, Cat.Hom₂.eqToHom_toNatTrans,
        eqToHom_app, map_id, Category.comp_id, associator_hom_app, colimit.ι_pre_assoc,
        HasColimit.isoOfNatIso_ι_hom_assoc, Iso.symm_hom, isoWhiskerRight_hom, associator_inv_app,
        NatIso.ofComponents_hom_app, Iso.refl_hom, Final.ι_colimitIso_hom, Category.id_comp,
        Final.ι_colimitIso_hom_assoc, colimit.ι_pre]
      have := Functor.congr_obj congr($(α.naturality f).toFunctor) d
      dsimp at this
      congr
      apply eqToHom_heq_id_dom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Grothendieck.final_map_small` / 引理 `Grothendieck.final_map_small`

English:
lemma Grothendieck.final_map_small
  statement: {C : Type u₁} [SmallCategory C] {F G : C ⥤ Cat.{u₁, u₁}}
  proof: by
  rw [final_iff_isIso_colimit_pre]
  intro H
  let i := (colimitFiberwiseColimitIso _).symm ≪≫
    HasColimit.isoOfNatIso (fiberwiseColimitMapCompEquivalence α H) ≪≫ colimitFiberwiseColimitIso _
  convert! Iso.isIso_hom i
  apply colimit.hom_ext
  intro X
  simp [i, fiberwiseColimitMapCompEquival

中文:
引理 Grothendieck.final_map_small
  结论: {C : 类型u₁} [SmallCategory C] {F G : C ⥤ Cat.{u₁, u₁}}
  证明: by
  rw [final_iff_isIso_colimit_pre]
  intro H
  let i := (colimitFiberwiseColimitIso _).symm ≪≫
    HasColimit.isoOfNatIso (fiberwiseColimitMapCompEquivalence α H) ≪≫ colimitFiberwiseColimitIso _
  convert! Iso.isIso_hom i
  apply colimit.hom_ext
  intro X
  simp [i, fiberwiseColimitMapCompEquival
-/
private lemma Grothendieck.final_map_small {C : Type u₁} [SmallCategory C] {F G : C ⥤ Cat.{u₁, u₁}}
    (α : F ⟶ G) [hα : forall X, Final (α.app X).toFunctor] : Final (map α) := by
  rw [final_iff_isIso_colimit_pre]
  intro H
  let i := (colimitFiberwiseColimitIso _).symm ≪≫
    HasColimit.isoOfNatIso (fiberwiseColimitMapCompEquivalence α H) ≪≫ colimitFiberwiseColimitIso _
  convert! Iso.isIso_hom i
  apply colimit.hom_ext
  intro X
  simp [i, fiberwiseColimitMapCompEquivalence]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Grothendieck.final_map` / 引理 `Grothendieck.final_map`

English:
lemma Grothendieck.final_map
  statement: {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G)
  proof: by
  let sC : C ≌ AsSmall.{max u₁ u₂ v₁ v₂} C := AsSmall.equiv
  let F' : AsSmall C ⥤ Cat := sC.inverse ⋙ F ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let G' : AsSmall C ⥤ Cat := sC.inverse ⋙ G ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let α' : F' ⟶ G' := whiskerLeft _ (whiskerRight α _)
  have : foral

中文:
引理 Grothendieck.final_map
  结论: {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G)
  证明: by
  let sC : C ≌ AsSmall.{max u₁ u₂ v₁ v₂} C := AsSmall.equiv
  let F' : AsSmall C ⥤ Cat := sC.inverse ⋙ F ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let G' : AsSmall C ⥤ Cat := sC.inverse ⋙ G ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let α' : F' ⟶ G' := whiskerLeft _ (whiskerRight α _)
  have : foral

Depends on / 依赖: AsSmall, AsSmall.equiv, AsSmall.equiv.functor, AsSmall.equiv.inverse, Cat.asSmallFunctor, Equivalence, Equivalence.symm_functor, asSmallFunctor, final_map_small, functor, inverse, sC.inverse, symm_functor, toFunctor, whiskerLeft, whiskerRight
-/
lemma Grothendieck.final_map {F G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G)
    [hα : forall X, Final (α.app X).toFunctor] : Final (map α) := by
  let sC : C ≌ AsSmall.{max u₁ u₂ v₁ v₂} C := AsSmall.equiv
  let F' : AsSmall C ⥤ Cat := sC.inverse ⋙ F ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let G' : AsSmall C ⥤ Cat := sC.inverse ⋙ G ⋙ Cat.asSmallFunctor.{max v₁ u₁ v₂ u₂}
  let α' : F' ⟶ G' := whiskerLeft _ (whiskerRight α _)
  have : forall X, Final (α'.app X).toFunctor := fun X =>
    inferInstanceAs (AsSmall.equiv.inverse ⋙ _ ⋙ AsSmall.equiv.functor).Final
  have hα' : (map α').Final := final_map_small _
  dsimp only [α', ← Equivalence.symm_functor] at hα'
  have i := mapWhiskerLeftIsoConjPreMap sC.symm (whiskerRight α Cat.asSmallFunctor)
    ≪≫ isoWhiskerLeft _ (isoWhiskerRight (mapWhiskerRightAsSmallFunctor α) _)
  have := final_of_natIso i
  rwa [← final_iff_equivalence_comp, ← final_iff_comp_equivalence,
    ← final_iff_equivalence_comp, ← final_iff_comp_equivalence] at this

end Grothendieck

section Prod

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {C' : Type u₃} [Category.{v₃} C']
variable {D' : Type u₄} [Category.{v₄} D']
variable (F : C ⥤ D) (G : C' ⥤ D')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Final]
  signature: [G.Final]
  body: fun ⟨d, d'⟩ => isConnected_of_equivalent (StructuredArrow.prodEquivalence d d' F G).symm

中文:
实例 [F.Final]
  签名: [G.Final]
  定义体: fun ⟨d, d'⟩ => isConnected_of_equivalent (StructuredArrow.prodEquivalence d d' F G).symm

Depends on / 依赖: StructuredArrow, StructuredArrow.prodEquivalence, isConnected_of_equivalent, prodEquivalence
-/
instance [F.Final] [G.Final] : (F.prod G).Final where
  out := fun ⟨d, d'⟩ => isConnected_of_equivalent (StructuredArrow.prodEquivalence d d' F G).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Initial]
  signature: [G.Initial]
  body: fun ⟨d, d'⟩ => isConnected_of_equivalent (CostructuredArrow.prodEquivalence F G d d').symm

中文:
实例 [F.Initial]
  签名: [G.Initial]
  定义体: fun ⟨d, d'⟩ => isConnected_of_equivalent (CostructuredArrow.prodEquivalence F G d d').symm

Depends on / 依赖: CostructuredArrow, CostructuredArrow.prodEquivalence, HasPullbacks, HasWeakPullbacksOfHasPullbacks, isConnected_of_equivalent, prodEquivalence
-/
instance [F.Initial] [G.Initial] : (F.prod G).Initial where
  out := fun ⟨d, d'⟩ => isConnected_of_equivalent (CostructuredArrow.prodEquivalence F G d d').symm

end Prod

namespace ObjectProperty

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `initial_ι` / 定理 `initial_ι`

English:
theorem initial_ι
  statement: {C : Type u₁} [Category.{v₁} C] (P : ObjectProperty C)
  proof: .mk fun d => by
  by_cases hd : P d
  · have : Nonempty (CostructuredArrow P.ι d) := ⟨⟨d, hd⟩, ⟨⟨⟩⟩, 𝟙 _⟩
    refine zigzag_isConnected (fun j₁ j₂ => Zigzag.trans
      (j₂ := by exact CostructuredArrow.mk (Y := ⟨d, hd⟩) (𝟙 _)) (.of_hom ?_) (.of_inv ?_))
    · exact CostructuredArrow.homMk (InducedC

中文:
定理 initial_ι
  结论: {C : 类型u₁} [Category.{v₁} C] (P : Object命题erty C)
  证明: .mk fun d => by
  by_cases hd : P d
  · have : Nonempty (CostructuredArrow P.ι d) := ⟨⟨d, hd⟩, ⟨⟨⟩⟩, 𝟙 _⟩
    refine zigzag_isConnected (fun j₁ j₂ => Zigzag.trans
      (j₂ := by exact CostructuredArrow.mk (Y := ⟨d, hd⟩) (𝟙 _)) (.of_hom ?_) (.of_inv ?_))
    · exact CostructuredArrow.homMk (InducedC

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, InducedCategory, InducedCategory.homMk, Nonempty, Zigzag, Zigzag.trans, of_hom, of_inv, zigzag_isConnected
-/
theorem initial_ι {C : Type u₁} [Category.{v₁} C] (P : ObjectProperty C)
    (h : forall d, ¬ P d -> IsConnected (CostructuredArrow P.ι d)) :
P.ι.Initial := .mk fun d => by
  by_cases hd : P d
  · have : Nonempty (CostructuredArrow P.ι d) := ⟨⟨d, hd⟩, ⟨⟨⟩⟩, 𝟙 _⟩
    refine zigzag_isConnected (fun j₁ j₂ => Zigzag.trans
      (j₂ := by exact CostructuredArrow.mk (Y := ⟨d, hd⟩) (𝟙 _)) (.of_hom ?_) (.of_inv ?_))
    · exact CostructuredArrow.homMk (InducedCategory.homMk j₁.hom)
    · exact CostructuredArrow.homMk (InducedCategory.homMk j₂.hom)
  · exact h d hd

end ObjectProperty

section Restriction

variable {J C : Type*} [Category* J] [Category* C] {D : J ⥤ C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Limits.IsLimit.overPost` / `Limits.IsLimit.overPost` 的定义

English:
definition Limits.IsLimit.overPost
  signature: {c : Cone D} (hc : IsLimit c) (j : J)
  body: by
  haveI : Nonempty (Over j) := ⟨Over.mk (𝟙 j)⟩
  letI c'' := Over.liftCone (Over.forget j ⋙ D) (X := D.obj j)
    (Functor.whiskerRight (Over.forgetCocone j).ι D ≫ (Functor.constComp _ _ _).hom)
    (c.whisker (CategoryTheory.Over.forget j)) (c.π.app j) (by cat_disch)
  letI hc'' : IsLimit c'' :=

中文:
定义 Limits.IsLimit.overPost
  签名: {c : Cone D} (hc : IsLimit c) (j : J)
  定义体: by
  haveI : Nonempty (Over j) := ⟨Over.mk (𝟙 j)⟩
  letI c'' := Over.liftCone (Over.forget j ⋙ D) (X := D.obj j)
    (Functor.whiskerRight (Over.forgetCocone j).ι D ≫ (Functor.constComp _ _ _).hom)
    (c.whisker (CategoryTheory.Over.forget j)) (c.π.app j) (by cat_disch)
  letI hc'' : IsLimit c'' :=

Depends on / 依赖: CategoryTheory, CategoryTheory.Over.forget, CategoryTheory.Over.isoMk, D.obj, Functor, Functor.Initial.isLimitWhiskerEquiv, Functor.constComp, Functor.whiskerRight, Initial, IsLimit, IsLimit.equivOfNatIsoOfIso, Iso.refl, NatIso, NatIso.ofComponents, Nonempty, Over.forget, Over.forgetCocone, Over.isLimitLiftCone, Over.liftCone, Over.mk
-/
noncomputable def Limits.IsLimit.overPost {c : Cone D} (hc : IsLimit c) (j : J)
    [(CategoryTheory.Over.forget j).Initial] : IsLimit (c.overPost j) := by
  haveI : Nonempty (Over j) := ⟨Over.mk (𝟙 j)⟩
  letI c'' := Over.liftCone (Over.forget j ⋙ D) (X := D.obj j)
    (Functor.whiskerRight (Over.forgetCocone j).ι D ≫ (Functor.constComp _ _ _).hom)
    (c.whisker (CategoryTheory.Over.forget j)) (c.π.app j) (by cat_disch)
  letI hc'' : IsLimit c'' :=
Over.isLimitLiftCone _ _ _ _ _ (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ hc''
  · exact NatIso.ofComponents (fun k => CategoryTheory.Over.isoMk (Iso.refl _))
  · exact Cone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Limits.IsColimit.underPost` / `Limits.IsColimit.underPost` 的定义

English:
definition Limits.IsColimit.underPost
  signature: {c : Cocone D} (hc : IsColimit c) (j : J)
  body: by
  haveI : Nonempty (Under j) := ⟨CategoryTheory.Under.mk (𝟙 j)⟩
  letI c'' := Under.liftCocone (CategoryTheory.Under.forget j ⋙ D) (X := D.obj j)
    ((Functor.constComp _ _ _).inv ≫ Functor.whiskerRight ((Under.forgetCone j).π) D)
    (c.whisker (CategoryTheory.Under.forget j)) (c.ι.app j) (by c

中文:
定义 Limits.IsColimit.underPost
  签名: {c : Cocone D} (hc : IsColimit c) (j : J)
  定义体: by
  haveI : Nonempty (Under j) := ⟨CategoryTheory.Under.mk (𝟙 j)⟩
  letI c'' := Under.liftCocone (CategoryTheory.Under.forget j ⋙ D) (X := D.obj j)
    ((Functor.constComp _ _ _).inv ≫ Functor.whiskerRight ((Under.forgetCone j).π) D)
    (c.whisker (CategoryTheory.Under.forget j)) (c.ι.app j) (by c

Depends on / 依赖: CategoryTheory, CategoryTheory.Under.forget, CategoryTheory.Under.mk, D.obj, Functor, Functor.Final.isColimitWhiskerEquiv, Functor.constComp, Functor.whiskerRight, IsColimit, IsColimit.equivOfNatIsoOfIso, NatIso, NatIso.ofComponents, Nonempty, Under.forgetCone, Under.isColimitLiftCocone, Under.liftCocone, c.whisker, cat_disch, constComp, equivOfNatIsoOfIso
-/
noncomputable def Limits.IsColimit.underPost {c : Cocone D} (hc : IsColimit c) (j : J)
    [(CategoryTheory.Under.forget j).Final] : IsColimit (c.underPost j) := by
  haveI : Nonempty (Under j) := ⟨CategoryTheory.Under.mk (𝟙 j)⟩
  letI c'' := Under.liftCocone (CategoryTheory.Under.forget j ⋙ D) (X := D.obj j)
    ((Functor.constComp _ _ _).inv ≫ Functor.whiskerRight ((Under.forgetCone j).π) D)
    (c.whisker (CategoryTheory.Under.forget j)) (c.ι.app j) (by cat_disch)
  letI hc'' : IsColimit c'' :=
Under.isColimitLiftCocone _ _ _ _ _ (Functor.Final.isColimitWhiskerEquiv _ _).symm hc
  refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ hc''
  · exact NatIso.ofComponents (fun k => CategoryTheory.Under.isoMk (Iso.refl _))
  · exact Cocone.ext (Iso.refl _)

end Restriction

instance {C₀ C : Type*} [Category* C₀] [Category* C]
    (F : C₀ ⥤ C) (X : C) [F.Initial] :
    (CostructuredArrow.toOver F X).Initial where
  out Y := by
    rw [isConnected_iff_of_equivalence
      (CostructuredArrow.costructuredArrowToOverEquivalence F Y)]
    infer_instance

end CategoryTheory
