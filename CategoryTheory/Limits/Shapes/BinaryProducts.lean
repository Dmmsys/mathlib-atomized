/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Binary (co)products

We define a category `WalkingPair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `HasBinaryProducts` and `HasBinaryCoproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

@[expose] public section

universe v v₁ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

/--
Inductive type `WalkingPair` / 归纳类型 `WalkingPair`

English:
inductive WalkingPair
  parameters: : Type
  constructors (2):
    - left: 
    - right: 

中文:
归纳类型 WalkingPair
  参数: : Type
  构造子 (2 个):
    - left: 
    - right: 
-/
inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited

open WalkingPair

/--
Definition of `WalkingPair.swap` / `WalkingPair.swap` 的定义

English:
definition WalkingPair.swap
  signature: : WalkingPair ≃ WalkingPair where
  body: by cases j <;> rfl
  right_inv j := by cases j <;> rfl

@[simp]

中文:
定义 WalkingPair.swap
  签名: : WalkingPair ≃ WalkingPair where
  定义体: by cases j <;> rfl
  right_inv j := by cases j <;> rfl

@[simp]

Depends on / 依赖: right_inv
-/
def WalkingPair.swap : WalkingPair ≃ WalkingPair where
  toFun
    | left => right
    | right => left
  invFun
    | left => right
    | right => left
  left_inv j := by cases j <;> rfl
  right_inv j := by cases j <;> rfl

@[simp]
/--
theorem `WalkingPair.swap_apply_left` / 定理 `WalkingPair.swap_apply_left`

English:
theorem WalkingPair.swap_apply_left
  statement: WalkingPair.swap left = right
  proof: rfl

@[simp]

中文:
定理 WalkingPair.swap_apply_left
  结论: WalkingPair.swap left = right
  证明: rfl

@[simp]
-/
theorem WalkingPair.swap_apply_left : WalkingPair.swap left = right :=
  rfl

@[simp]
/--
theorem `WalkingPair.swap_apply_right` / 定理 `WalkingPair.swap_apply_right`

English:
theorem WalkingPair.swap_apply_right
  statement: WalkingPair.swap right = left
  proof: rfl

@[simp]

中文:
定理 WalkingPair.swap_apply_right
  结论: WalkingPair.swap right = left
  证明: rfl

@[simp]
-/
theorem WalkingPair.swap_apply_right : WalkingPair.swap right = left :=
  rfl

@[simp]
/--
theorem `WalkingPair.swap_symm_apply_tt` / 定理 `WalkingPair.swap_symm_apply_tt`

English:
theorem WalkingPair.swap_symm_apply_tt
  statement: WalkingPair.swap.symm left = right
  proof: rfl

@[simp]

中文:
定理 WalkingPair.swap_symm_apply_tt
  结论: WalkingPair.swap.symm left = right
  证明: rfl

@[simp]
-/
theorem WalkingPair.swap_symm_apply_tt : WalkingPair.swap.symm left = right :=
  rfl

@[simp]
/--
theorem `WalkingPair.swap_symm_apply_ff` / 定理 `WalkingPair.swap_symm_apply_ff`

English:
theorem WalkingPair.swap_symm_apply_ff
  statement: WalkingPair.swap.symm right = left
  proof: rfl

中文:
定理 WalkingPair.swap_symm_apply_ff
  结论: WalkingPair.swap.symm right = left
  证明: rfl
-/
theorem WalkingPair.swap_symm_apply_ff : WalkingPair.swap.symm right = left :=
  rfl

/--
Definition of `WalkingPair.equivBool` / `WalkingPair.equivBool` 的定义

English:
definition WalkingPair.equivBool
  signature: : WalkingPair ≃ Bool where
  body: Bool.recOn b right left
  left_inv j := by cases j <;> rfl
  right_inv b := by cases b <;> rfl

@[simp]

中文:
定义 WalkingPair.equivBool
  签名: : WalkingPair ≃ 布尔 where
  定义体: Bool.recOn b right left
  left_inv j := by cases j <;> rfl
  right_inv b := by cases b <;> rfl

@[simp]

Depends on / 依赖: Bool.recOn
-/
def WalkingPair.equivBool : WalkingPair ≃ Bool where
  toFun
    | left => true
    | right => false
  -- to match equiv.sum_equiv_sigma_bool
  invFun b := Bool.recOn b right left
  left_inv j := by cases j <;> rfl
  right_inv b := by cases b <;> rfl

@[simp]
/--
theorem `WalkingPair.equivBool_apply_left` / 定理 `WalkingPair.equivBool_apply_left`

English:
theorem WalkingPair.equivBool_apply_left
  statement: WalkingPair.equivBool left = true
  proof: rfl

@[simp]

中文:
定理 WalkingPair.equivBool_apply_left
  结论: WalkingPair.equiv布尔 left = true
  证明: rfl

@[simp]
-/
theorem WalkingPair.equivBool_apply_left : WalkingPair.equivBool left = true :=
  rfl

@[simp]
/--
theorem `WalkingPair.equivBool_apply_right` / 定理 `WalkingPair.equivBool_apply_right`

English:
theorem WalkingPair.equivBool_apply_right
  statement: WalkingPair.equivBool right = false
  proof: rfl

@[simp]

中文:
定理 WalkingPair.equivBool_apply_right
  结论: WalkingPair.equiv布尔 right = false
  证明: rfl

@[simp]

Depends on / 依赖: forget
-/
theorem WalkingPair.equivBool_apply_right : WalkingPair.equivBool right = false :=
  rfl

@[simp]
/--
theorem `WalkingPair.equivBool_symm_apply_true` / 定理 `WalkingPair.equivBool_symm_apply_true`

English:
theorem WalkingPair.equivBool_symm_apply_true
  statement: WalkingPair.equivBool.symm true = left
  proof: rfl

@[simp]

中文:
定理 WalkingPair.equivBool_symm_apply_true
  结论: WalkingPair.equiv布尔.symm true = left
  证明: rfl

@[simp]
-/
theorem WalkingPair.equivBool_symm_apply_true : WalkingPair.equivBool.symm true = left :=
  rfl

@[simp]
/--
theorem `WalkingPair.equivBool_symm_apply_false` / 定理 `WalkingPair.equivBool_symm_apply_false`

English:
theorem WalkingPair.equivBool_symm_apply_false
  statement: WalkingPair.equivBool.symm false = right
  proof: rfl

中文:
定理 WalkingPair.equivBool_symm_apply_false
  结论: WalkingPair.equiv布尔.symm false = right
  证明: rfl
-/
theorem WalkingPair.equivBool_symm_apply_false : WalkingPair.equivBool.symm false = right :=
  rfl

variable {C : Type u}

/--
Definition of `pairFunction` / `pairFunction` 的定义

English:
definition pairFunction
  signature: (X Y : C)
  body: fun j => WalkingPair.casesOn j X Y

@[simp]

中文:
定义 pairFunction
  签名: (X Y : C)
  定义体: fun j => WalkingPair.casesOn j X Y

@[simp]

Depends on / 依赖: WalkingPair, WalkingPair.casesOn, casesOn
-/
def pairFunction (X Y : C) : WalkingPair -> C := fun j => WalkingPair.casesOn j X Y

@[simp]
/--
theorem `pairFunction_left` / 定理 `pairFunction_left`

English:
theorem pairFunction_left
  given: (X Y : C)
  statement: pairFunction X Y left = X
  proof: rfl

@[simp]

中文:
定理 pairFunction_left
  条件: (X Y : C)
  结论: pairFunction X Y left = X
  证明: rfl

@[simp]
-/
theorem pairFunction_left (X Y : C) : pairFunction X Y left = X :=
  rfl

@[simp]
/--
theorem `pairFunction_right` / 定理 `pairFunction_right`

English:
theorem pairFunction_right
  given: (X Y : C)
  statement: pairFunction X Y right = Y
  proof: rfl

中文:
定理 pairFunction_right
  条件: (X Y : C)
  结论: pairFunction X Y right = Y
  证明: rfl
-/
theorem pairFunction_right (X Y : C) : pairFunction X Y right = Y :=
  rfl

variable [Category.{v} C]

/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: (X Y : C)
  body: Discrete.functor fun j => WalkingPair.casesOn j X Y

@[simp]

中文:
定义 pair
  签名: (X Y : C)
  定义体: Discrete.functor fun j => WalkingPair.casesOn j X Y

@[simp]

Depends on / 依赖: Discrete, Discrete.functor, WalkingPair, WalkingPair.casesOn, casesOn, functor
-/
def pair (X Y : C) : Discrete WalkingPair ⥤ C :=
  Discrete.functor fun j => WalkingPair.casesOn j X Y

@[simp]
/--
theorem `pair_obj_left` / 定理 `pair_obj_left`

English:
theorem pair_obj_left
  given: (X Y : C)
  statement: (pair X Y).obj ⟨left⟩ = X
  proof: rfl

@[simp]

中文:
定理 pair_obj_left
  条件: (X Y : C)
  结论: (pair X Y).obj ⟨left⟩ = X
  证明: rfl

@[simp]

Depends on / 依赖: Grp.homMk, toUnit
-/
theorem pair_obj_left (X Y : C) : (pair X Y).obj ⟨left⟩ = X :=
  rfl

@[simp]
/--
theorem `pair_obj_right` / 定理 `pair_obj_right`

English:
theorem pair_obj_right
  given: (X Y : C)
  statement: (pair X Y).obj ⟨right⟩ = Y
  proof: rfl

中文:
定理 pair_obj_right
  条件: (X Y : C)
  结论: (pair X Y).obj ⟨right⟩ = Y
  证明: rfl
-/
theorem pair_obj_right (X Y : C) : (pair X Y).obj ⟨right⟩ = Y :=
  rfl

section

variable {F G : Discrete WalkingPair ⥤ C} (f : F.obj ⟨left⟩ ⟶ G.obj ⟨left⟩)
  (g : F.obj ⟨right⟩ ⟶ G.obj ⟨right⟩)

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/--
Definition of `mapPair` / `mapPair` 的定义

English:
definition mapPair
  signature: : F ⟶ G where
  body: fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by cat_disch

@[simp]

中文:
定义 mapPair
  签名: : F ⟶ G where
  定义体: fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
def mapPair : F ⟶ G where
  app
    | ⟨left⟩ => f
    | ⟨right⟩ => g
  naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by cat_disch

@[simp]
/--
theorem `mapPair_left` / 定理 `mapPair_left`

English:
theorem mapPair_left
  statement: (mapPair f g).app ⟨left⟩ = f
  proof: rfl

@[simp]

中文:
定理 mapPair_left
  结论: (mapPair f g).app ⟨left⟩ = f
  证明: rfl

@[simp]
-/
theorem mapPair_left : (mapPair f g).app ⟨left⟩ = f :=
  rfl

@[simp]
/--
theorem `mapPair_right` / 定理 `mapPair_right`

English:
theorem mapPair_right
  statement: (mapPair f g).app ⟨right⟩ = g
  proof: rfl

中文:
定理 mapPair_right
  结论: (mapPair f g).app ⟨right⟩ = g
  证明: rfl
-/
theorem mapPair_right : (mapPair f g).app ⟨right⟩ = g :=
  rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its
components. -/
@[simps!]
/--
Definition of `mapPairIso` / `mapPairIso` 的定义

English:
definition mapPairIso
  signature: (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩)
  body: NatIso.ofComponents (fun j => match j with
    | ⟨left⟩ => f
    | ⟨right⟩ => g)
    (fun ⟨⟨u⟩⟩ => by cat_disch)

中文:
定义 mapPairIso
  签名: (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩)
  定义体: NatIso.ofComponents (fun j => match j with
    | ⟨left⟩ => f
    | ⟨right⟩ => g)
    (fun ⟨⟨u⟩⟩ => by cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def mapPairIso (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩) : F ≅ G :=
  NatIso.ofComponents (fun j => match j with
    | ⟨left⟩ => f
    | ⟨right⟩ => g)
    (fun ⟨⟨u⟩⟩ => by cat_disch)

end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simps!]
/--
Definition of `diagramIsoPair` / `diagramIsoPair` 的定义

English:
definition diagramIsoPair
  signature: (F : Discrete WalkingPair ⥤ C)
  body: mapPairIso (Iso.refl _) (Iso.refl _)

中文:
定义 diagramIsoPair
  签名: (F : Discrete WalkingPair ⥤ C)
  定义体: mapPairIso (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl, mapPairIso
-/
def diagramIsoPair (F : Discrete WalkingPair ⥤ C) :
    F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
  mapPairIso (Iso.refl _) (Iso.refl _)

section

variable {D : Type u₁} [Category.{v₁} D]

/--
Definition of `pairComp` / `pairComp` 的定义

English:
definition pairComp
  signature: (X Y : C) (F : C ⥤ D)
  body: diagramIsoPair _

中文:
定义 pairComp
  签名: (X Y : C) (F : C ⥤ D)
  定义体: diagramIsoPair _

Depends on / 依赖: diagramIsoPair
-/
def pairComp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
  diagramIsoPair _

end

/--
Definition of `BinaryFan` / `BinaryFan` 的定义

English:
abbreviation BinaryFan
  signature: (X Y : C)
  body: Cone (pair X Y)

中文:
缩写 BinaryFan
  签名: (X Y : C)
  定义体: Cone (pair X Y)
-/
abbrev BinaryFan (X Y : C) :=
  Cone (pair X Y)

/--
Definition of `BinaryFan.fst` / `BinaryFan.fst` 的定义

English:
abbreviation BinaryFan.fst
  signature: {X Y : C} (s : BinaryFan X Y)
  body: s.π.app ⟨WalkingPair.left⟩

中文:
缩写 BinaryFan.fst
  签名: {X Y : C} (s : BinaryFan X Y)
  定义体: s.π.app ⟨WalkingPair.left⟩

Depends on / 依赖: WalkingPair, WalkingPair.left
-/
abbrev BinaryFan.fst {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.left⟩

/--
Definition of `BinaryFan.snd` / `BinaryFan.snd` 的定义

English:
abbreviation BinaryFan.snd
  signature: {X Y : C} (s : BinaryFan X Y)
  body: s.π.app ⟨WalkingPair.right⟩

中文:
缩写 BinaryFan.snd
  签名: {X Y : C} (s : BinaryFan X Y)
  定义体: s.π.app ⟨WalkingPair.right⟩

Depends on / 依赖: WalkingPair, WalkingPair.right
-/
abbrev BinaryFan.snd {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.right⟩

-- Marking this `@[simp]` causes loops since `s.fst` is reducibly defeq to the LHS.
/--
theorem `BinaryFan.π_app_left` / 定理 `BinaryFan.π_app_left`

English:
theorem BinaryFan.π_app_left
  given: {X Y : C} (s : BinaryFan X Y)
  statement: s.π.app ⟨WalkingPair.left⟩ = s.fst
  proof: rfl

中文:
定理 BinaryFan.π_app_left
  条件: {X Y : C} (s : BinaryFan X Y)
  结论: s.π.app ⟨WalkingPair.left⟩ = s.fst
  证明: rfl
-/
theorem BinaryFan.π_app_left {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.left⟩ = s.fst :=
  rfl

-- Marking this `@[simp]` causes loops since `s.snd` is reducibly defeq to the LHS.
/--
theorem `BinaryFan.π_app_right` / 定理 `BinaryFan.π_app_right`

English:
theorem BinaryFan.π_app_right
  given: {X Y : C} (s : BinaryFan X Y)
  statement: s.π.app ⟨WalkingPair.right⟩ = s.snd
  proof: rfl

中文:
定理 BinaryFan.π_app_right
  条件: {X Y : C} (s : BinaryFan X Y)
  结论: s.π.app ⟨WalkingPair.right⟩ = s.snd
  证明: rfl
-/
theorem BinaryFan.π_app_right {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.right⟩ = s.snd :=
  rfl

/--
Definition of `BinaryFan.ext` / `BinaryFan.ext` 的定义

English:
definition BinaryFan.ext
  signature: {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
  body: Cone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]

中文:
定义 BinaryFan.ext
  签名: {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
  定义体: Cone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]

Depends on / 依赖: Cone.ext
-/
def BinaryFan.ext {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) : c ≅ c' :=
  Cone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]
/--
lemma `BinaryFan.ext_hom_hom` / 引理 `BinaryFan.ext_hom_hom`

English:
lemma BinaryFan.ext_hom_hom
  statement: {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
  proof: rfl

中文:
引理 BinaryFan.ext_hom_hom
  结论: {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
  证明: rfl
-/
lemma BinaryFan.ext_hom_hom {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

/--
Definition of `BinaryFan.IsLimit.mk` / `BinaryFan.IsLimit.mk` 的定义

English:
definition BinaryFan.IsLimit.mk
  signature: {X Y : C} (s : BinaryFan X Y)
  body: Limits.IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      · exact hl₁ _ _
      · exact hl₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

中文:
定义 BinaryFan.IsLimit.mk
  签名: {X Y : C} (s : BinaryFan X Y)
  定义体: Limits.IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      · exact hl₁ _ _
      · exact hl₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

Depends on / 依赖: BinaryFan, BinaryFan.fst, BinaryFan.snd, IsLimit, Limits, Limits.IsLimit.mk, WalkingPair, WalkingPair.left, WalkingPair.right
-/
def BinaryFan.IsLimit.mk {X Y : C} (s : BinaryFan X Y)
    (lift : forall {T : C} (_ : T ⟶ X) (_ : T ⟶ Y), T ⟶ s.pt)
    (hl₁ : forall {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.fst = f)
    (hl₂ : forall {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.snd = g)
    (uniq :
      forall {T : C} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ s.pt) (_ : m ≫ s.fst = f) (_ : m ≫ s.snd = g),
        m = lift f g) :
    IsLimit s :=
  Limits.IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      · exact hl₁ _ _
      · exact hl₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

/--
theorem `BinaryFan.IsLimit.hom_ext` / 定理 `BinaryFan.IsLimit.hom_ext`

English:
theorem BinaryFan.IsLimit.hom_ext
  statement: {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.pt}
  proof: h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

中文:
定理 BinaryFan.IsLimit.hom_ext
  结论: {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.pt}
  证明: h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

Depends on / 依赖: Discrete, Discrete.recOn, WalkingPair, WalkingPair.casesOn, casesOn, h.hom_ext, hom_ext
-/
theorem BinaryFan.IsLimit.hom_ext {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.pt}
    (h₁ : f ≫ s.fst = g ≫ s.fst) (h₂ : f ≫ s.snd = g ≫ s.snd) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

/--
Definition of `BinaryCofan` / `BinaryCofan` 的定义

English:
abbreviation BinaryCofan
  signature: (X Y : C)
  body: Cocone (pair X Y)

中文:
缩写 BinaryCofan
  签名: (X Y : C)
  定义体: Cocone (pair X Y)

Depends on / 依赖: Cocone
-/
abbrev BinaryCofan (X Y : C) := Cocone (pair X Y)

/--
Definition of `BinaryCofan.inl` / `BinaryCofan.inl` 的定义

English:
abbreviation BinaryCofan.inl
  signature: {X Y : C} (s : BinaryCofan X Y)
  body: s.ι.app ⟨WalkingPair.left⟩

中文:
缩写 BinaryCofan.inl
  签名: {X Y : C} (s : BinaryCofan X Y)
  定义体: s.ι.app ⟨WalkingPair.left⟩

Depends on / 依赖: WalkingPair, WalkingPair.left
-/
abbrev BinaryCofan.inl {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.left⟩

/--
Definition of `BinaryCofan.inr` / `BinaryCofan.inr` 的定义

English:
abbreviation BinaryCofan.inr
  signature: {X Y : C} (s : BinaryCofan X Y)
  body: s.ι.app ⟨WalkingPair.right⟩

中文:
缩写 BinaryCofan.inr
  签名: {X Y : C} (s : BinaryCofan X Y)
  定义体: s.ι.app ⟨WalkingPair.right⟩

Depends on / 依赖: WalkingPair, WalkingPair.right
-/
abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.right⟩

/--
Definition of `BinaryCofan.ext` / `BinaryCofan.ext` 的定义

English:
definition BinaryCofan.ext
  signature: {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
  body: Cocone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]

中文:
定义 BinaryCofan.ext
  签名: {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
  定义体: Cocone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]

Depends on / 依赖: Cocone, Cocone.ext
-/
def BinaryCofan.ext {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) : c ≅ c' :=
  Cocone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]
/--
lemma `BinaryCofan.ext_hom_hom` / 引理 `BinaryCofan.ext_hom_hom`

English:
lemma BinaryCofan.ext_hom_hom
  statement: {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
  proof: rfl

中文:
引理 BinaryCofan.ext_hom_hom
  结论: {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
  证明: rfl
-/
lemma BinaryCofan.ext_hom_hom {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

-- This cannot be `@[simp]` because `s.inl` is reducibly defeq to the LHS.
/--
theorem `BinaryCofan.ι_app_left` / 定理 `BinaryCofan.ι_app_left`

English:
theorem BinaryCofan.ι_app_left
  given: {X Y : C} (s : BinaryCofan X Y)
  proof: rfl

中文:
定理 BinaryCofan.ι_app_left
  条件: {X Y : C} (s : BinaryCofan X Y)
  证明: rfl
-/
theorem BinaryCofan.ι_app_left {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.left⟩ = s.inl := rfl

-- This cannot be `@[simp]` because `s.inr` is reducibly defeq to the LHS.
/--
theorem `BinaryCofan.ι_app_right` / 定理 `BinaryCofan.ι_app_right`

English:
theorem BinaryCofan.ι_app_right
  given: {X Y : C} (s : BinaryCofan X Y)
  proof: rfl

中文:
定理 BinaryCofan.ι_app_right
  条件: {X Y : C} (s : BinaryCofan X Y)
  证明: rfl
-/
theorem BinaryCofan.ι_app_right {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.right⟩ = s.inr := rfl

/--
Definition of `BinaryCofan.IsColimit.mk` / `BinaryCofan.IsColimit.mk` 的定义

English:
definition BinaryCofan.IsColimit.mk
  signature: {X Y : C} (s : BinaryCofan X Y)
  body: Limits.IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      · exact hd₁ _ _
      · exact hd₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

中文:
定义 BinaryCofan.IsColimit.mk
  签名: {X Y : C} (s : BinaryCofan X Y)
  定义体: Limits.IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      · exact hd₁ _ _
      · exact hd₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

Depends on / 依赖: BinaryCofan, BinaryCofan.inl, BinaryCofan.inr, IsColimit, Limits, Limits.IsColimit.mk, WalkingPair, WalkingPair.left, WalkingPair.right
-/
def BinaryCofan.IsColimit.mk {X Y : C} (s : BinaryCofan X Y)
    (desc : forall {T : C} (_ : X ⟶ T) (_ : Y ⟶ T), s.pt ⟶ T)
    (hd₁ : forall {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inl ≫ desc f g = f)
    (hd₂ : forall {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inr ≫ desc f g = g)
    (uniq :
      forall {T : C} (f : X ⟶ T) (g : Y ⟶ T) (m : s.pt ⟶ T) (_ : s.inl ≫ m = f) (_ : s.inr ≫ m = g),
        m = desc f g) :
    IsColimit s :=
  Limits.IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      · exact hd₁ _ _
      · exact hd₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)

/--
theorem `BinaryCofan.IsColimit.hom_ext` / 定理 `BinaryCofan.IsColimit.hom_ext`

English:
theorem BinaryCofan.IsColimit.hom_ext
  statement: {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s)
  proof: h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

中文:
定理 BinaryCofan.IsColimit.hom_ext
  结论: {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s)
  证明: h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

Depends on / 依赖: Discrete, Discrete.recOn, WalkingPair, WalkingPair.casesOn, casesOn, h.hom_ext, hom_ext
-/
theorem BinaryCofan.IsColimit.hom_ext {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s)
    {f g : s.pt ⟶ W} (h₁ : s.inl ≫ f = s.inl ≫ g) (h₂ : s.inr ≫ f = s.inr ≫ g) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

variable {X Y : C}

section

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- TODO: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

set_option backward.defeqAttrib.useBackward true in
/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
@[simps pt, implicit_reducible]
/--
Definition of `BinaryFan.mk` / `BinaryFan.mk` 的定义

English:
definition BinaryFan.mk
  signature: {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  body: P
  π := { app := fun | { as := j } => match j with | left => π₁ | right => π₂ }

中文:
定义 BinaryFan.mk
  签名: {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  定义体: P
  π := { app := fun | { as := j } => match j with | left => π₁ | right => π₂ }
-/
def BinaryFan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : BinaryFan X Y where
  pt := P
  π := { app := fun | { as := j } => match j with | left => π₁ | right => π₂ }

set_option backward.defeqAttrib.useBackward true in
/-- A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P`. -/
@[simps pt]
/--
Definition of `BinaryCofan.mk` / `BinaryCofan.mk` 的定义

English:
definition BinaryCofan.mk
  signature: {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  body: P
  ι := { app := fun | { as := j } => match j with | left => ι₁ | right => ι₂ }

中文:
定义 BinaryCofan.mk
  签名: {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  定义体: P
  ι := { app := fun | { as := j } => match j with | left => ι₁ | right => ι₂ }
-/
def BinaryCofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : BinaryCofan X Y where
  pt := P
  ι := { app := fun | { as := j } => match j with | left => ι₁ | right => ι₂ }

end

@[simp]
/--
theorem `BinaryFan.mk_fst` / 定理 `BinaryFan.mk_fst`

English:
theorem BinaryFan.mk_fst
  given: {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  statement: (BinaryFan.mk π₁ π₂).fst = π₁
  proof: rfl

@[simp]

中文:
定理 BinaryFan.mk_fst
  条件: {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  结论: (BinaryFan.mk π₁ π₂).fst = π₁
  证明: rfl

@[simp]
-/
theorem BinaryFan.mk_fst {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).fst = π₁ :=
  rfl

@[simp]
/--
theorem `BinaryFan.mk_snd` / 定理 `BinaryFan.mk_snd`

English:
theorem BinaryFan.mk_snd
  given: {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  statement: (BinaryFan.mk π₁ π₂).snd = π₂
  proof: rfl

@[simp]

中文:
定理 BinaryFan.mk_snd
  条件: {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  结论: (BinaryFan.mk π₁ π₂).snd = π₂
  证明: rfl

@[simp]
-/
theorem BinaryFan.mk_snd {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).snd = π₂ :=
  rfl

@[simp]
/--
theorem `BinaryCofan.mk_inl` / 定理 `BinaryCofan.mk_inl`

English:
theorem BinaryCofan.mk_inl
  given: {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  statement: (BinaryCofan.mk ι₁ ι₂).inl = ι₁
  proof: rfl

@[simp]

中文:
定理 BinaryCofan.mk_inl
  条件: {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  结论: (BinaryCofan.mk ι₁ ι₂).inl = ι₁
  证明: rfl

@[simp]
-/
theorem BinaryCofan.mk_inl {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inl = ι₁ :=
  rfl

@[simp]
/--
theorem `BinaryCofan.mk_inr` / 定理 `BinaryCofan.mk_inr`

English:
theorem BinaryCofan.mk_inr
  given: {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  statement: (BinaryCofan.mk ι₁ ι₂).inr = ι₂
  proof: rfl

中文:
定理 BinaryCofan.mk_inr
  条件: {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  结论: (BinaryCofan.mk ι₁ ι₂).inr = ι₂
  证明: rfl
-/
theorem BinaryCofan.mk_inr {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inr = ι₂ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isoBinaryFanMk` / `isoBinaryFanMk` 的定义

English:
definition isoBinaryFanMk
  signature: {X Y : C} (c : BinaryFan X Y)
  body: Cone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

中文:
定义 isoBinaryFanMk
  签名: {X Y : C} (c : BinaryFan X Y)
  定义体: Cone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

Depends on / 依赖: Cone.ext, Iso.refl, repeat
-/
def isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ≅ BinaryFan.mk c.fst c.snd :=
    Cone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isoBinaryCofanMk` / `isoBinaryCofanMk` 的定义

English:
definition isoBinaryCofanMk
  signature: {X Y : C} (c : BinaryCofan X Y)
  body: Cocone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

中文:
定义 isoBinaryCofanMk
  签名: {X Y : C} (c : BinaryCofan X Y)
  定义体: Cocone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl, repeat
-/
def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.inl c.inr :=
    Cocone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

/--
Definition of `BinaryFan.isLimitMk` / `BinaryFan.isLimitMk` 的定义

English:
definition BinaryFan.isLimitMk
  signature: {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (lift : forall s : BinaryFan X Y, s.pt ⟶ W)
  body: { lift := lift
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

中文:
定义 BinaryFan.isLimitMk
  签名: {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (lift : 对任意 s : BinaryFan X Y, s.pt ⟶ W)
  定义体: { lift := lift
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

Depends on / 依赖: WalkingPair, WalkingPair.left, WalkingPair.right, exacts, fac_left, fac_right
-/
def BinaryFan.isLimitMk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (lift : forall s : BinaryFan X Y, s.pt ⟶ W)
    (fac_left : forall s : BinaryFan X Y, lift s ≫ fst = s.fst)
    (fac_right : forall s : BinaryFan X Y, lift s ≫ snd = s.snd)
    (uniq :
      forall (s : BinaryFan X Y) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (BinaryFan.mk fst snd) :=
  { lift := lift
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

/--
Definition of `BinaryCofan.isColimitMk` / `BinaryCofan.isColimitMk` 的定义

English:
definition BinaryCofan.isColimitMk
  signature: {W : C} {inl : X ⟶ W} {inr : Y ⟶ W}
  body: { desc := desc
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

中文:
定义 BinaryCofan.isColimitMk
  签名: {W : C} {inl : X ⟶ W} {inr : Y ⟶ W}
  定义体: { desc := desc
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

Depends on / 依赖: WalkingPair, WalkingPair.left, WalkingPair.right, exacts, fac_left, fac_right
-/
def BinaryCofan.isColimitMk {W : C} {inl : X ⟶ W} {inr : Y ⟶ W}
    (desc : forall s : BinaryCofan X Y, W ⟶ s.pt)
    (fac_left : forall s : BinaryCofan X Y, inl ≫ desc s = s.inl)
    (fac_right : forall s : BinaryCofan X Y, inr ≫ desc s = s.inr)
    (uniq :
      forall (s : BinaryCofan X Y) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (BinaryCofan.mk inl inr) :=
  { desc := desc
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

/--
Definition of `BinaryFan.IsLimit.lift` / `BinaryFan.IsLimit.lift` 的定义

English:
definition BinaryFan.IsLimit.lift
  signature: {W : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) (g : W ⟶ Y)
  body: h.lift (BinaryFan.mk f g)

@[reassoc (attr := simp)]

中文:
定义 BinaryFan.IsLimit.lift
  签名: {W : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) (g : W ⟶ Y)
  定义体: h.lift (BinaryFan.mk f g)

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryFan, BinaryFan.mk, h.lift
-/
def BinaryFan.IsLimit.lift {W : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ s.pt :=
  h.lift (BinaryFan.mk f g)

@[reassoc (attr := simp)]
/--
lemma `BinaryFan.IsLimit.lift_fst` / 引理 `BinaryFan.IsLimit.lift_fst`

English:
lemma BinaryFan.IsLimit.lift_fst
  statement: {W : C} {s : BinaryFan X Y} (h : IsLimit s)
  proof: h.fac (BinaryFan.mk f g) _

@[reassoc (attr := simp)]

中文:
引理 BinaryFan.IsLimit.lift_fst
  结论: {W : C} {s : BinaryFan X Y} (h : IsLimit s)
  证明: h.fac (BinaryFan.mk f g) _

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryFan, BinaryFan.mk, h.fac
-/
lemma BinaryFan.IsLimit.lift_fst {W : C} {s : BinaryFan X Y} (h : IsLimit s)
    (f : W ⟶ X) (g : W ⟶ Y) :
    lift h f g ≫ s.fst = f :=
  h.fac (BinaryFan.mk f g) _

@[reassoc (attr := simp)]
/--
lemma `BinaryFan.IsLimit.lift_snd` / 引理 `BinaryFan.IsLimit.lift_snd`

English:
lemma BinaryFan.IsLimit.lift_snd
  statement: {W : C} {s : BinaryFan X Y} (h : IsLimit s)
  proof: h.fac (BinaryFan.mk f g) _

中文:
引理 BinaryFan.IsLimit.lift_snd
  结论: {W : C} {s : BinaryFan X Y} (h : IsLimit s)
  证明: h.fac (BinaryFan.mk f g) _

Depends on / 依赖: BinaryFan, BinaryFan.mk, h.fac
-/
lemma BinaryFan.IsLimit.lift_snd {W : C} {s : BinaryFan X Y} (h : IsLimit s)
    (f : W ⟶ X) (g : W ⟶ Y) :
    lift h f g ≫ s.snd = g :=
  h.fac (BinaryFan.mk f g) _

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
`g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
-/
@[simps]
/--
Definition of `BinaryFan.IsLimit.lift'` / `BinaryFan.IsLimit.lift'` 的定义

English:
definition BinaryFan.IsLimit.lift'
  signature: {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
  body: ⟨h.lift BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

中文:
定义 BinaryFan.IsLimit.lift'
  签名: {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
  定义体: ⟨h.lift BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

Depends on / 依赖: BinaryFan, BinaryFan.mk, h.fac, h.lift
-/
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
    (g : W ⟶ Y) : { l : W ⟶ s.pt // l ≫ s.fst = f ∧ l ≫ s.snd = g } :=
⟨h.lift BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

/--
Definition of `BinaryCofan.IsColimit.desc` / `BinaryCofan.IsColimit.desc` 的定义

English:
definition BinaryCofan.IsColimit.desc
  signature: {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
  body: h.desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]

中文:
定义 BinaryCofan.IsColimit.desc
  签名: {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
  定义体: h.desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, h.desc
-/
def BinaryCofan.IsColimit.desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.pt ⟶ W :=
  h.desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]
/--
lemma `BinaryCofan.IsColimit.inl_desc` / 引理 `BinaryCofan.IsColimit.inl_desc`

English:
lemma BinaryCofan.IsColimit.inl_desc
  statement: {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
  proof: h.fac (BinaryCofan.mk f g) _

@[reassoc (attr := simp)]

中文:
引理 BinaryCofan.IsColimit.inl_desc
  结论: {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
  证明: h.fac (BinaryCofan.mk f g) _

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, h.fac
-/
lemma BinaryCofan.IsColimit.inl_desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.inl ≫ desc h f g = f :=
  h.fac (BinaryCofan.mk f g) _

@[reassoc (attr := simp)]
/--
lemma `BinaryCofan.IsColimit.inr_desc` / 引理 `BinaryCofan.IsColimit.inr_desc`

English:
lemma BinaryCofan.IsColimit.inr_desc
  statement: {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
  proof: h.fac (BinaryCofan.mk f g) _

中文:
引理 BinaryCofan.IsColimit.inr_desc
  结论: {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
  证明: h.fac (BinaryCofan.mk f g) _

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, h.fac
-/
lemma BinaryCofan.IsColimit.inr_desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.inr ≫ desc h f g = g :=
  h.fac (BinaryCofan.mk f g) _

/-- If `s` is a colimit binary cofan over `X` and `Y`, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
-/
@[simps]
/--
Definition of `BinaryCofan.IsColimit.desc'` / `BinaryCofan.IsColimit.desc'` 的定义

English:
definition BinaryCofan.IsColimit.desc'
  signature: {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
  body: ⟨h.desc BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

中文:
定义 BinaryCofan.IsColimit.desc'
  签名: {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
  定义体: ⟨h.desc BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, h.desc, h.fac
-/
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
    (g : Y ⟶ W) : { l : s.pt ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g } :=
⟨h.desc BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

/--
Definition of `BinaryFan.isLimitFlip` / `BinaryFan.isLimitFlip` 的定义

English:
definition BinaryFan.isLimitFlip
  signature: {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c)
  body: BinaryFan.isLimitMk (fun s => IsLimit.lift hc s.snd s.fst) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryFan.IsLimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.ri

中文:
定义 BinaryFan.isLimitFlip
  签名: {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c)
  定义体: BinaryFan.isLimitMk (fun s => IsLimit.lift hc s.snd s.fst) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryFan.IsLimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.ri

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, BinaryFan.isLimitMk, BinaryFan.mk, IsLimit, IsLimit.lift, WalkingPair, WalkingPair.left, WalkingPair.right, hc.fac, hom_ext, isLimitMk, s.fst, s.snd
-/
def BinaryFan.isLimitFlip {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c) :
    IsLimit (BinaryFan.mk c.snd c.fst) :=
  BinaryFan.isLimitMk (fun s => IsLimit.lift hc s.snd s.fst) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryFan.IsLimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.right⟩).symm)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `BinaryFan.isLimit_iff_isIso_fst` / 定理 `BinaryFan.isLimit_iff_isIso_fst`

English:
theorem BinaryFan.isLimit_iff_isIso_fst
  given: {X Y : C} (h : IsTerminal Y) (c : BinaryFan X Y)
  proof: by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryFan.IsLimit.lift' H (𝟙 X) (h.from X)
    exact
      ⟨⟨l,
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -Category.comp_id] using Category.comp_id _)
            (h.hom_ext _ _),
          hl⟩⟩
  · intro
    exact
      ⟨BinaryFan.

中文:
定理 BinaryFan.isLimit_iff_isIso_fst
  条件: {X Y : C} (h : IsTerminal Y) (c : BinaryFan X Y)
  证明: by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryFan.IsLimit.lift' H (𝟙 X) (h.from X)
    exact
      ⟨⟨l,
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -Category.comp_id] using Category.comp_id _)
            (h.hom_ext _ _),
          hl⟩⟩
  · intro
    exact
      ⟨BinaryFan.

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, BinaryFan.IsLimit.lift, BinaryFan.IsLimit.mk, Category, Category.comp_id, IsLimit, c.fst, comp_id, h.from, h.hom_ext, hom_ext
-/
theorem BinaryFan.isLimit_iff_isIso_fst {X Y : C} (h : IsTerminal Y) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.fst := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryFan.IsLimit.lift' H (𝟙 X) (h.from X)
    exact
      ⟨⟨l,
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -Category.comp_id] using Category.comp_id _)
            (h.hom_ext _ _),
          hl⟩⟩
  · intro
    exact
      ⟨BinaryFan.IsLimit.mk _ (fun f _ => f ≫ inv c.fst) (fun _ _ => by simp)
          (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ => by simp [← e]⟩

/--
theorem `BinaryFan.isLimit_iff_isIso_snd` / 定理 `BinaryFan.isLimit_iff_isIso_snd`

English:
theorem BinaryFan.isLimit_iff_isIso_snd
  given: {X Y : C} (h : IsTerminal X) (c : BinaryFan X Y)
  proof: by
  refine Iff.trans ?_ (BinaryFan.isLimit_iff_isIso_fst h (BinaryFan.mk c.snd c.fst))
  exact
    ⟨fun h => ⟨BinaryFan.isLimitFlip h.some⟩, fun h =>
      ⟨(BinaryFan.isLimitFlip h.some).ofIsoLimit (isoBinaryFanMk c).symm⟩⟩

中文:
定理 BinaryFan.isLimit_iff_isIso_snd
  条件: {X Y : C} (h : IsTerminal X) (c : BinaryFan X Y)
  证明: by
  refine Iff.trans ?_ (BinaryFan.isLimit_iff_isIso_fst h (BinaryFan.mk c.snd c.fst))
  exact
    ⟨fun h => ⟨BinaryFan.isLimitFlip h.some⟩, fun h =>
      ⟨(BinaryFan.isLimitFlip h.some).ofIsoLimit (isoBinaryFanMk c).symm⟩⟩

Depends on / 依赖: BinaryFan, BinaryFan.isLimitFlip, BinaryFan.isLimit_iff_isIso_fst, BinaryFan.mk, Iff.trans, c.fst, c.snd, h.some, isLimitFlip, isLimit_iff_isIso_fst, isoBinaryFanMk, ofIsoLimit
-/
theorem BinaryFan.isLimit_iff_isIso_snd {X Y : C} (h : IsTerminal X) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.snd := by
  refine Iff.trans ?_ (BinaryFan.isLimit_iff_isIso_fst h (BinaryFan.mk c.snd c.fst))
  exact
    ⟨fun h => ⟨BinaryFan.isLimitFlip h.some⟩, fun h =>
      ⟨(BinaryFan.isLimitFlip h.some).ofIsoLimit (isoBinaryFanMk c).symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryFan.isLimitCompLeftIso` / `BinaryFan.isLimitCompLeftIso` 的定义

English:
definition BinaryFan.isLimitCompLeftIso
  signature: {X Y X' : C} (c : BinaryFan X Y) (f : X ⟶ X')
  body: by
  fapply BinaryFan.isLimitMk
  · exact fun s => IsLimit.lift h (s.fst ≫ inv f) s.snd
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryFan.IsLimit.hom_ext h
    · simpa
    · simpa

中文:
定义 BinaryFan.isLimitCompLeftIso
  签名: {X Y X' : C} (c : BinaryFan X Y) (f : X ⟶ X')
  定义体: by
  fapply BinaryFan.isLimitMk
  · exact fun s => IsLimit.lift h (s.fst ≫ inv f) s.snd
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryFan.IsLimit.hom_ext h
    · simpa
    · simpa

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, BinaryFan.isLimitMk, IsLimit, IsLimit.lift, fapply, hom_ext, isLimitMk, s.fst, s.snd
-/
noncomputable def BinaryFan.isLimitCompLeftIso {X Y X' : C} (c : BinaryFan X Y) (f : X ⟶ X')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk (c.fst ≫ f) c.snd) := by
  fapply BinaryFan.isLimitMk
  · exact fun s => IsLimit.lift h (s.fst ≫ inv f) s.snd
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryFan.IsLimit.hom_ext h
    · simpa
    · simpa

/--
Definition of `BinaryFan.isLimitCompRightIso` / `BinaryFan.isLimitCompRightIso` 的定义

English:
definition BinaryFan.isLimitCompRightIso
  signature: {X Y Y' : C} (c : BinaryFan X Y) (f : Y ⟶ Y')
  body: BinaryFan.isLimitFlip BinaryFan.isLimitCompLeftIso _ f (BinaryFan.isLimitFlip h)

中文:
定义 BinaryFan.isLimitCompRightIso
  签名: {X Y Y' : C} (c : BinaryFan X Y) (f : Y ⟶ Y')
  定义体: BinaryFan.isLimitFlip BinaryFan.isLimitCompLeftIso _ f (BinaryFan.isLimitFlip h)

Depends on / 依赖: BinaryFan, BinaryFan.isLimitCompLeftIso, BinaryFan.isLimitFlip, isLimitCompLeftIso, isLimitFlip
-/
noncomputable def BinaryFan.isLimitCompRightIso {X Y Y' : C} (c : BinaryFan X Y) (f : Y ⟶ Y')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk c.fst (c.snd ≫ f)) :=
BinaryFan.isLimitFlip BinaryFan.isLimitCompLeftIso _ f (BinaryFan.isLimitFlip h)

/--
Definition of `BinaryCofan.isColimitFlip` / `BinaryCofan.isColimitFlip` 的定义

English:
definition BinaryCofan.isColimitFlip
  signature: {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c)
  body: BinaryCofan.isColimitMk (fun s => IsColimit.desc hc s.inr s.inl) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryCofan.IsColimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨

中文:
定义 BinaryCofan.isColimitFlip
  签名: {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c)
  定义体: BinaryCofan.isColimitMk (fun s => IsColimit.desc hc s.inr s.inl) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryCofan.IsColimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.hom_ext, BinaryCofan.isColimitMk, BinaryCofan.mk, IsColimit, IsColimit.desc, WalkingPair, WalkingPair.left, WalkingPair.right, hc.fac, hom_ext, isColimitMk, s.inl, s.inr
-/
def BinaryCofan.isColimitFlip {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsColimit (BinaryCofan.mk c.inr c.inl) :=
  BinaryCofan.isColimitMk (fun s => IsColimit.desc hc s.inr s.inl) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryCofan.IsColimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.right⟩).symm)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `BinaryCofan.isColimit_iff_isIso_inl` / 定理 `BinaryCofan.isColimit_iff_isIso_inl`

English:
theorem BinaryCofan.isColimit_iff_isIso_inl
  given: {X Y : C} (h : IsInitial Y) (c : BinaryCofan X Y)
  proof: by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X) (h.to X)
    refine ⟨⟨l, hl, BinaryCofan.IsColimit.hom_ext H (?_) (h.hom_ext _ _)⟩⟩
    rw [Category.comp_id]
    have e : (inl c ≫ l) ≫ inl c = 𝟙 X ≫ inl c := congrArg (· ≫ inl c) hl
    rwa [Category.assoc

中文:
定理 BinaryCofan.isColimit_iff_isIso_inl
  条件: {X Y : C} (h : IsInitial Y) (c : BinaryCofan X Y)
  证明: by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X) (h.to X)
    refine ⟨⟨l, hl, BinaryCofan.IsColimit.hom_ext H (?_) (h.hom_ext _ _)⟩⟩
    rw [Category.comp_id]
    have e : (inl c ≫ l) ≫ inl c = 𝟙 X ≫ inl c := congrArg (· ≫ inl c) hl
    rwa [Category.assoc

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.desc, BinaryCofan.IsColimit.hom_ext, BinaryCofan.IsColimit.mk, Category, Category.assoc, Category.comp_id, Category.id_comp, IsColimit, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc, c.inl, comp_id, eq_inv_comp, h.hom_ext, h.to, hom_ext, hom_inv_id_assoc, id_comp
-/
theorem BinaryCofan.isColimit_iff_isIso_inl {X Y : C} (h : IsInitial Y) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inl := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X) (h.to X)
    refine ⟨⟨l, hl, BinaryCofan.IsColimit.hom_ext H (?_) (h.hom_ext _ _)⟩⟩
    rw [Category.comp_id]
    have e : (inl c ≫ l) ≫ inl c = 𝟙 X ≫ inl c := congrArg (· ≫ inl c) hl
    rwa [Category.assoc, Category.id_comp] at e
  · intro
    exact
      ⟨BinaryCofan.IsColimit.mk _ (fun f _ => inv c.inl ≫ f)
          (fun _ _ => IsIso.hom_inv_id_assoc _ _) (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ =>
          (IsIso.eq_inv_comp _).mpr e⟩

/--
theorem `BinaryCofan.isColimit_iff_isIso_inr` / 定理 `BinaryCofan.isColimit_iff_isIso_inr`

English:
theorem BinaryCofan.isColimit_iff_isIso_inr
  given: {X Y : C} (h : IsInitial X) (c : BinaryCofan X Y)
  proof: by
  refine Iff.trans ?_ (BinaryCofan.isColimit_iff_isIso_inl h (BinaryCofan.mk c.inr c.inl))
  exact
    ⟨fun h => ⟨BinaryCofan.isColimitFlip h.some⟩, fun h =>
      ⟨(BinaryCofan.isColimitFlip h.some).ofIsoColimit (isoBinaryCofanMk c).symm⟩⟩

中文:
定理 BinaryCofan.isColimit_iff_isIso_inr
  条件: {X Y : C} (h : IsInitial X) (c : BinaryCofan X Y)
  证明: by
  refine Iff.trans ?_ (BinaryCofan.isColimit_iff_isIso_inl h (BinaryCofan.mk c.inr c.inl))
  exact
    ⟨fun h => ⟨BinaryCofan.isColimitFlip h.some⟩, fun h =>
      ⟨(BinaryCofan.isColimitFlip h.some).ofIsoColimit (isoBinaryCofanMk c).symm⟩⟩

Depends on / 依赖: BinaryCofan, BinaryCofan.isColimitFlip, BinaryCofan.isColimit_iff_isIso_inl, BinaryCofan.mk, Iff.trans, c.inl, c.inr, h.some, isColimitFlip, isColimit_iff_isIso_inl, isoBinaryCofanMk, ofIsoColimit
-/
theorem BinaryCofan.isColimit_iff_isIso_inr {X Y : C} (h : IsInitial X) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inr := by
  refine Iff.trans ?_ (BinaryCofan.isColimit_iff_isIso_inl h (BinaryCofan.mk c.inr c.inl))
  exact
    ⟨fun h => ⟨BinaryCofan.isColimitFlip h.some⟩, fun h =>
      ⟨(BinaryCofan.isColimitFlip h.some).ofIsoColimit (isoBinaryCofanMk c).symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryCofan.isColimitCompLeftIso` / `BinaryCofan.isColimitCompLeftIso` 的定义

English:
definition BinaryCofan.isColimitCompLeftIso
  signature: {X Y X' : C} (c : BinaryCofan X Y) (f : X' ⟶ X)
  body: by
  fapply BinaryCofan.isColimitMk
  · exact fun s => BinaryCofan.IsColimit.desc h (inv f ≫ s.inl) s.inr
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryCofan.IsColimit.hom_ext h
    · rw [← cancel_epi f]
      simpa using e₁
    · simpa

中文:
定义 BinaryCofan.isColimitCompLeftIso
  签名: {X Y X' : C} (c : BinaryCofan X Y) (f : X' ⟶ X)
  定义体: by
  fapply BinaryCofan.isColimitMk
  · exact fun s => BinaryCofan.IsColimit.desc h (inv f ≫ s.inl) s.inr
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryCofan.IsColimit.hom_ext h
    · rw [← cancel_epi f]
      simpa using e₁
    · simpa

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.desc, BinaryCofan.IsColimit.hom_ext, BinaryCofan.isColimitMk, IsColimit, cancel_epi, fapply, hom_ext, isColimitMk, s.inl, s.inr
-/
noncomputable def BinaryCofan.isColimitCompLeftIso {X Y X' : C} (c : BinaryCofan X Y) (f : X' ⟶ X)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk (f ≫ c.inl) c.inr) := by
  fapply BinaryCofan.isColimitMk
  · exact fun s => BinaryCofan.IsColimit.desc h (inv f ≫ s.inl) s.inr
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryCofan.IsColimit.hom_ext h
    · rw [← cancel_epi f]
      simpa using e₁
    · simpa

/--
Definition of `BinaryCofan.isColimitCompRightIso` / `BinaryCofan.isColimitCompRightIso` 的定义

English:
definition BinaryCofan.isColimitCompRightIso
  signature: {X Y Y' : C} (c : BinaryCofan X Y) (f : Y' ⟶ Y)
  body: BinaryCofan.isColimitFlip BinaryCofan.isColimitCompLeftIso _ f (BinaryCofan.isColimitFlip h)

中文:
定义 BinaryCofan.isColimitCompRightIso
  签名: {X Y Y' : C} (c : BinaryCofan X Y) (f : Y' ⟶ Y)
  定义体: BinaryCofan.isColimitFlip BinaryCofan.isColimitCompLeftIso _ f (BinaryCofan.isColimitFlip h)

Depends on / 依赖: BinaryCofan, BinaryCofan.isColimitCompLeftIso, BinaryCofan.isColimitFlip, isColimitCompLeftIso, isColimitFlip
-/
noncomputable def BinaryCofan.isColimitCompRightIso {X Y Y' : C} (c : BinaryCofan X Y) (f : Y' ⟶ Y)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk c.inl (f ≫ c.inr)) :=
BinaryCofan.isColimitFlip BinaryCofan.isColimitCompLeftIso _ f (BinaryCofan.isColimitFlip h)

/--
Definition of `HasBinaryProduct` / `HasBinaryProduct` 的定义

English:
abbreviation HasBinaryProduct
  signature: (X Y : C)
  body: HasLimit (pair X Y)

中文:
缩写 HasBinaryProduct
  签名: (X Y : C)
  定义体: HasLimit (pair X Y)

Depends on / 依赖: HasLimit
-/
abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)

/--
Definition of `HasBinaryCoproduct` / `HasBinaryCoproduct` 的定义

English:
abbreviation HasBinaryCoproduct
  signature: (X Y : C)
  body: HasColimit (pair X Y)

中文:
缩写 HasBinaryCoproduct
  签名: (X Y : C)
  定义体: HasColimit (pair X Y)

Depends on / 依赖: HasColimit
-/
abbrev HasBinaryCoproduct (X Y : C) :=
  HasColimit (pair X Y)

/--
Definition of `prod` / `prod` 的定义

English:
abbreviation prod
  signature: (X Y : C) [HasBinaryProduct X Y]
  body: limit (pair X Y)

中文:
缩写 prod
  签名: (X Y : C) [HasBinaryProduct X Y]
  定义体: limit (pair X Y)
-/
noncomputable abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)

/--
Definition of `coprod` / `coprod` 的定义

English:
abbreviation coprod
  signature: (X Y : C) [HasBinaryCoproduct X Y]
  body: colimit (pair X Y)

中文:
缩写 coprod
  签名: (X Y : C) [HasBinaryCoproduct X Y]
  定义体: colimit (pair X Y)

Depends on / 依赖: colimit
-/
noncomputable abbrev coprod (X Y : C) [HasBinaryCoproduct X Y] :=
  colimit (pair X Y)

/-- Notation for the product -/
notation:20 X " ⨯ " Y:20 => prod X Y

/-- Notation for the coproduct -/
notation:20 X " ⨿ " Y:20 => coprod X Y

/--
Definition of `prod.fst` / `prod.fst` 的定义

English:
abbreviation prod.fst
  signature: {X Y : C} [HasBinaryProduct X Y]
  body: limit.π (pair X Y) ⟨WalkingPair.left⟩

中文:
缩写 prod.fst
  签名: {X Y : C} [HasBinaryProduct X Y]
  定义体: limit.π (pair X Y) ⟨WalkingPair.left⟩

Depends on / 依赖: WalkingPair, WalkingPair.left
-/
noncomputable abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) ⟨WalkingPair.left⟩

/--
Definition of `prod.snd` / `prod.snd` 的定义

English:
abbreviation prod.snd
  signature: {X Y : C} [HasBinaryProduct X Y]
  body: limit.π (pair X Y) ⟨WalkingPair.right⟩

中文:
缩写 prod.snd
  签名: {X Y : C} [HasBinaryProduct X Y]
  定义体: limit.π (pair X Y) ⟨WalkingPair.right⟩

Depends on / 依赖: WalkingPair, WalkingPair.right
-/
noncomputable abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) ⟨WalkingPair.right⟩

/--
Definition of `coprod.inl` / `coprod.inl` 的定义

English:
abbreviation coprod.inl
  signature: {X Y : C} [HasBinaryCoproduct X Y]
  body: colimit.ι (pair X Y) ⟨WalkingPair.left⟩

中文:
缩写 coprod.inl
  签名: {X Y : C} [HasBinaryCoproduct X Y]
  定义体: colimit.ι (pair X Y) ⟨WalkingPair.left⟩

Depends on / 依赖: WalkingPair, WalkingPair.left, colimit
-/
noncomputable abbrev coprod.inl {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.left⟩

/--
Definition of `coprod.inr` / `coprod.inr` 的定义

English:
abbreviation coprod.inr
  signature: {X Y : C} [HasBinaryCoproduct X Y]
  body: colimit.ι (pair X Y) ⟨WalkingPair.right⟩

中文:
缩写 coprod.inr
  签名: {X Y : C} [HasBinaryCoproduct X Y]
  定义体: colimit.ι (pair X Y) ⟨WalkingPair.right⟩

Depends on / 依赖: WalkingPair, WalkingPair.right, colimit
-/
noncomputable abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.right⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `prodIsProd` / `prodIsProd` 的定义

English:
definition prodIsProd
  signature: (X Y : C) [HasBinaryProduct X Y]
  body: (limit.isLimit _).ofIsoLimit (Cone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · simp [Category.id_comp]
    · simp [Category.id_comp]
  ))

中文:
定义 prodIsProd
  签名: (X Y : C) [HasBinaryProduct X Y]
  定义体: (limit.isLimit _).ofIsoLimit (Cone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · simp [Category.id_comp]
    · simp [Category.id_comp]
  ))

Depends on / 依赖: Category, Category.id_comp, Cone.ext, Iso.refl, id_comp, isLimit, limit.isLimit, ofIsoLimit
-/
noncomputable def prodIsProd (X Y : C) [HasBinaryProduct X Y] :
    IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit (Cone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · simp [Category.id_comp]
    · simp [Category.id_comp]
  ))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `coprodIsCoprod` / `coprodIsCoprod` 的定义

English:
definition coprodIsCoprod
  signature: (X Y : C) [HasBinaryCoproduct X Y]
  body: (colimit.isColimit _).ofIsoColimit (Cocone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.comp_id]
    · dsimp; simp only [Category.comp_id]
  ))

@[ext 1100]

中文:
定义 coprodIsCoprod
  签名: (X Y : C) [HasBinaryCoproduct X Y]
  定义体: (colimit.isColimit _).ofIsoColimit (Cocone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.comp_id]
    · dsimp; simp only [Category.comp_id]
  ))

@[ext 1100]

Depends on / 依赖: Category, Category.comp_id, Cocone, Cocone.ext, Iso.refl, colimit, colimit.isColimit, comp_id, isColimit, ofIsoColimit
-/
noncomputable def coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] :
    IsColimit (BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  (colimit.isColimit _).ofIsoColimit (Cocone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.comp_id]
    · dsimp; simp only [Category.comp_id]
  ))

@[ext 1100]
/--
theorem `prod.hom_ext` / 定理 `prod.hom_ext`

English:
theorem prod.hom_ext
  statement: {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
  proof: BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

@[ext 1100]

中文:
定理 prod.hom_ext
  结论: {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
  证明: BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

@[ext 1100]

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, IsLimit, hom_ext, isLimit, limit.isLimit
-/
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
    (h₁ : f ≫ prod.fst = g ≫ prod.fst) (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

@[ext 1100]
/--
theorem `coprod.hom_ext` / 定理 `coprod.hom_ext`

English:
theorem coprod.hom_ext
  statement: {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W}
  proof: BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂

中文:
定理 coprod.hom_ext
  结论: {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W}
  证明: BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.hom_ext, IsColimit, colimit, colimit.isColimit, hom_ext, isColimit
-/
theorem coprod.hom_ext {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W}
    (h₁ : coprod.inl ≫ f = coprod.inl ≫ g) (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂

/--
Definition of `prod.lift` / `prod.lift` 的定义

English:
abbreviation prod.lift
  signature: {W X Y : C} [HasBinaryProduct X Y]
  body: limit.lift _ (BinaryFan.mk f g)

中文:
缩写 prod.lift
  签名: {W X Y : C} [HasBinaryProduct X Y]
  定义体: limit.lift _ (BinaryFan.mk f g)

Depends on / 依赖: BinaryFan, BinaryFan.mk, limit.lift
-/
noncomputable abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y]
    (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift _ (BinaryFan.mk f g)

/--
Definition of `diag` / `diag` 的定义

English:
abbreviation diag
  signature: (X : C) [HasBinaryProduct X X]
  body: prod.lift (𝟙 _) (𝟙 _)

中文:
缩写 diag
  签名: (X : C) [HasBinaryProduct X X]
  定义体: prod.lift (𝟙 _) (𝟙 _)

Depends on / 依赖: prod.lift
-/
noncomputable abbrev diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X :=
  prod.lift (𝟙 _) (𝟙 _)

/--
Definition of `coprod.desc` / `coprod.desc` 的定义

English:
abbreviation coprod.desc
  signature: {W X Y : C} [HasBinaryCoproduct X Y]
  body: colimit.desc _ (BinaryCofan.mk f g)

中文:
缩写 coprod.desc
  签名: {W X Y : C} [HasBinaryCoproduct X Y]
  定义体: colimit.desc _ (BinaryCofan.mk f g)

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, colimit, colimit.desc
-/
noncomputable abbrev coprod.desc {W X Y : C} [HasBinaryCoproduct X Y]
    (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
  colimit.desc _ (BinaryCofan.mk f g)

/--
Definition of `codiag` / `codiag` 的定义

English:
abbreviation codiag
  signature: (X : C) [HasBinaryCoproduct X X]
  body: coprod.desc (𝟙 _) (𝟙 _)

@[reassoc]

中文:
缩写 codiag
  签名: (X : C) [HasBinaryCoproduct X X]
  定义体: coprod.desc (𝟙 _) (𝟙 _)

@[reassoc]

Depends on / 依赖: coprod, coprod.desc
-/
noncomputable abbrev codiag (X : C) [HasBinaryCoproduct X X] : X ⨿ X ⟶ X :=
  coprod.desc (𝟙 _) (𝟙 _)

@[reassoc]
/--
theorem `prod.lift_fst` / 定理 `prod.lift_fst`

English:
theorem prod.lift_fst
  given: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  proof: limit.lift_π _ _

@[reassoc]

中文:
定理 prod.lift_fst
  条件: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  证明: limit.lift_π _ _

@[reassoc]

Depends on / 依赖: limit.lift_
-/
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.fst = f :=
  limit.lift_π _ _

@[reassoc]
/--
theorem `prod.lift_snd` / 定理 `prod.lift_snd`

English:
theorem prod.lift_snd
  given: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  proof: limit.lift_π _ _

@[reassoc]

中文:
定理 prod.lift_snd
  条件: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  证明: limit.lift_π _ _

@[reassoc]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, limit.lift_
-/
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.snd = g :=
  limit.lift_π _ _

@[reassoc]
/--
theorem `coprod.inl_desc` / 定理 `coprod.inl_desc`

English:
theorem coprod.inl_desc
  given: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  proof: colimit.ι_desc _ _

@[reassoc]

中文:
定理 coprod.inl_desc
  条件: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  证明: colimit.ι_desc _ _

@[reassoc]

Depends on / 依赖: colimit
-/
theorem coprod.inl_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inl ≫ coprod.desc f g = f :=
  colimit.ι_desc _ _

@[reassoc]
/--
theorem `coprod.inr_desc` / 定理 `coprod.inr_desc`

English:
theorem coprod.inr_desc
  given: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  proof: colimit.ι_desc _ _

中文:
定理 coprod.inr_desc
  条件: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  证明: colimit.ι_desc _ _

Depends on / 依赖: IsModHom, cat_disch, colimit, smul_hom
-/
theorem coprod.inr_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inr ≫ coprod.desc f g = g :=
  colimit.ι_desc _ _

/--
Instance `prod.mono_lift_of_mono_left` / 实例 `prod.mono_lift_of_mono_left`

English:
instance prod.mono_lift_of_mono_left
  signature: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  body: mono_of_mono_fac prod.lift_fst _ _

中文:
实例 prod.mono_lift_of_mono_left
  签名: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  定义体: mono_of_mono_fac prod.lift_fst _ _

Depends on / 依赖: lift_fst, mono_of_mono_fac, prod.lift_fst
-/
instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (prod.lift f g) :=
mono_of_mono_fac prod.lift_fst _ _

/--
Instance `prod.mono_lift_of_mono_right` / 实例 `prod.mono_lift_of_mono_right`

English:
instance prod.mono_lift_of_mono_right
  signature: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  body: mono_of_mono_fac prod.lift_snd _ _

中文:
实例 prod.mono_lift_of_mono_right
  签名: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  定义体: mono_of_mono_fac prod.lift_snd _ _

Depends on / 依赖: lift_snd, mono_of_mono_fac, prod.lift_snd
-/
instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (prod.lift f g) :=
mono_of_mono_fac prod.lift_snd _ _

/--
Instance `coprod.epi_desc_of_epi_left` / 实例 `coprod.epi_desc_of_epi_left`

English:
instance coprod.epi_desc_of_epi_left
  signature: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  body: epi_of_epi_fac coprod.inl_desc _ _

中文:
实例 coprod.epi_desc_of_epi_left
  签名: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  定义体: epi_of_epi_fac coprod.inl_desc _ _

Depends on / 依赖: coprod, coprod.inl_desc, epi_of_epi_fac, inl_desc
-/
instance coprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (coprod.desc f g) :=
epi_of_epi_fac coprod.inl_desc _ _

/--
Instance `coprod.epi_desc_of_epi_right` / 实例 `coprod.epi_desc_of_epi_right`

English:
instance coprod.epi_desc_of_epi_right
  signature: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  body: epi_of_epi_fac coprod.inr_desc _ _

中文:
实例 coprod.epi_desc_of_epi_right
  签名: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  定义体: epi_of_epi_fac coprod.inr_desc _ _

Depends on / 依赖: coprod, coprod.inr_desc, epi_of_epi_fac, inr_desc
-/
instance coprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (coprod.desc f g) :=
epi_of_epi_fac coprod.inr_desc _ _

/--
Definition of `prod.lift'` / `prod.lift'` 的定义

English:
definition prod.lift'
  signature: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  body: ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

中文:
定义 prod.lift'
  签名: {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  定义体: ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

Depends on / 依赖: lift_fst, lift_snd, prod.lift, prod.lift_fst, prod.lift_snd
-/
noncomputable def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ X ⨯ Y // l ≫ prod.fst = f ∧ l ≫ prod.snd = g } :=
  ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

/--
Definition of `coprod.desc'` / `coprod.desc'` 的定义

English:
definition coprod.desc'
  signature: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  body: ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

中文:
定义 coprod.desc'
  签名: {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  定义体: ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

Depends on / 依赖: coprod, coprod.desc, coprod.inl_desc, coprod.inr_desc, inl_desc, inr_desc
-/
noncomputable def coprod.desc' {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    { l : X ⨿ Y ⟶ W // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g } :=
  ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

/--
Definition of `prod.map` / `prod.map` 的定义

English:
definition prod.map
  signature: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z]
  body: limMap (mapPair f g)

中文:
定义 prod.map
  签名: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z]
  定义体: limMap (mapPair f g)

Depends on / 依赖: limMap, mapPair
-/
noncomputable def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
  limMap (mapPair f g)

/--
Definition of `coprod.map` / `coprod.map` 的定义

English:
definition coprod.map
  signature: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z]
  body: colimMap (mapPair f g)

noncomputable section ProdLemmas

中文:
定义 coprod.map
  签名: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z]
  定义体: colimMap (mapPair f g)

noncomputable section ProdLemmas

Depends on / 依赖: colimMap, mapPair
-/
noncomputable def coprod.map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
  colimMap (mapPair f g)

noncomputable section ProdLemmas

set_option backward.isDefEq.respectTransparency false in
-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.
@[reassoc, simp]
/--
theorem `prod.comp_lift` / 定理 `prod.comp_lift`

English:
theorem prod.comp_lift
  given: {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y)
  proof: by ext <;> simp

中文:
定理 prod.comp_lift
  条件: {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y)
  证明: by ext <;> simp
-/
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ prod.lift g h = prod.lift (f ≫ g) (f ≫ h) := by ext <;> simp

/--
theorem `prod.comp_diag` / 定理 `prod.comp_diag`

English:
theorem prod.comp_diag
  given: {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y)
  proof: by simp

@[reassoc (attr := simp)]

中文:
定理 prod.comp_diag
  条件: {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y)
  证明: by simp

@[reassoc (attr := simp)]
-/
theorem prod.comp_diag {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y) :
    f ≫ diag Y = prod.lift f f := by simp

@[reassoc (attr := simp)]
/--
theorem `prod.map_fst` / 定理 `prod.map_fst`

English:
theorem prod.map_fst
  statement: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
  proof: limMap_π _ _

@[reassoc (attr := simp)]

中文:
定理 prod.map_fst
  结论: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
  证明: limMap_π _ _

@[reassoc (attr := simp)]
-/
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.fst = prod.fst ≫ f :=
  limMap_π _ _

@[reassoc (attr := simp)]
/--
theorem `prod.map_snd` / 定理 `prod.map_snd`

English:
theorem prod.map_snd
  statement: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
  proof: limMap_π _ _

@[simp]

中文:
定理 prod.map_snd
  结论: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
  证明: limMap_π _ _

@[simp]
-/
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.snd = prod.snd ≫ g :=
  limMap_π _ _

@[simp]
/--
theorem `prod.map_id_id` / 定理 `prod.map_id_id`

English:
theorem prod.map_id_id
  given: {X Y : C} [HasBinaryProduct X Y]
  statement: prod.map (𝟙 X) (𝟙 Y) = 𝟙 _
  proof: by
  ext <;> simp

中文:
定理 prod.map_id_id
  条件: {X Y : C} [HasBinaryProduct X Y]
  结论: prod.map (𝟙 X) (𝟙 Y) = 𝟙 _
  证明: by
  ext <;> simp
-/
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `prod.lift_fst_snd` / 定理 `prod.lift_fst_snd`

English:
theorem prod.lift_fst_snd
  given: {X Y : C} [HasBinaryProduct X Y]
  proof: by ext <;> simp

中文:
定理 prod.lift_fst_snd
  条件: {X Y : C} [HasBinaryProduct X Y]
  证明: by ext <;> simp
-/
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] :
    prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `prod.lift_map` / 定理 `prod.lift_map`

English:
theorem prod.lift_map
  statement: {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
  proof: by ext <;> simp

@[simp]

中文:
定理 prod.lift_map
  结论: {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
  证明: by ext <;> simp

@[simp]
-/
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
    (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
/--
theorem `prod.lift_fst_comp_snd_comp` / 定理 `prod.lift_fst_comp_snd_comp`

English:
theorem prod.lift_fst_comp_snd_comp
  statement: {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
  proof: by
  rw [← prod.lift_map]
  simp

中文:
定理 prod.lift_fst_comp_snd_comp
  结论: {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
  证明: by
  rw [← prod.lift_map]
  simp

Depends on / 依赖: lift_map, prod.lift_map
-/
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
    (g : W ⟶ X) (g' : Y ⟶ Z) : prod.lift (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by
  rw [← prod.lift_map]
  simp

-- We take the right-hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (e.g. `id_comp`), while `map_fst` and `map_snd` can still work just
-- as well.
@[reassoc (attr := simp)]
/--
theorem `prod.map_map` / 定理 `prod.map_map`

English:
theorem prod.map_map
  statement: {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
  proof: by ext <;> simp

中文:
定理 prod.map_map
  结论: {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
  证明: by ext <;> simp
-/
theorem prod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
    [HasBinaryProduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) := by ext <;> simp

-- TODO: is it necessary to weaken the assumption here?
@[reassoc]
/--
theorem `prod.map_swap` / 定理 `prod.map_swap`

English:
theorem prod.map_swap
  statement: {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
  proof: by simp

@[reassoc]

中文:
定理 prod.map_swap
  结论: {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
  证明: by simp

@[reassoc]
-/
theorem prod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasLimitsOfShape (Discrete WalkingPair) C] :
    prod.map (𝟙 X) f ≫ prod.map g (𝟙 B) = prod.map g (𝟙 A) ≫ prod.map (𝟙 Y) f := by simp

@[reassoc]
/--
theorem `prod.map_comp_id` / 定理 `prod.map_comp_id`

English:
theorem prod.map_comp_id
  statement: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W]
  proof: by simp

@[reassoc]

中文:
定理 prod.map_comp_id
  结论: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W]
  证明: by simp

@[reassoc]
-/
theorem prod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W]
    [HasBinaryProduct Z W] [HasBinaryProduct Y W] :
    prod.map (f ≫ g) (𝟙 W) = prod.map f (𝟙 W) ≫ prod.map g (𝟙 W) := by simp

@[reassoc]
/--
theorem `prod.map_id_comp` / 定理 `prod.map_id_comp`

English:
theorem prod.map_id_comp
  statement: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X]
  proof: by simp

中文:
定理 prod.map_id_comp
  结论: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X]
  证明: by simp
-/
theorem prod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X]
    [HasBinaryProduct W Y] [HasBinaryProduct W Z] :
    prod.map (𝟙 W) (f ≫ g) = prod.map (𝟙 W) f ≫ prod.map (𝟙 W) g := by simp

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : X ≅ Z` induces an isomorphism `prod.mapIso f g : W ⨯ X ≅ Y ⨯ Z`. -/
@[simps]
/--
Definition of `prod.mapIso` / `prod.mapIso` 的定义

English:
definition prod.mapIso
  signature: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
  body: prod.map f.hom g.hom
  inv := prod.map f.inv g.inv

中文:
定义 prod.mapIso
  签名: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
  定义体: prod.map f.hom g.hom
  inv := prod.map f.inv g.inv

Depends on / 依赖: f.hom, g.hom, prod.map
-/
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨯ X ≅ Y ⨯ Z where
  hom := prod.map f.hom g.hom
  inv := prod.map f.inv g.inv

/--
Instance `isIso_prod` / 实例 `isIso_prod`

English:
instance isIso_prod
  signature: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
  body: (prod.mapIso (asIso f) (asIso g)).isIso_hom

中文:
实例 isIso_prod
  签名: {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
  定义体: (prod.mapIso (asIso f) (asIso g)).isIso_hom

Depends on / 依赖: isIso_hom, mapIso, prod.mapIso
-/
instance isIso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (prod.map f g) :=
  (prod.mapIso (asIso f) (asIso g)).isIso_hom

/--
Instance `prod.map_mono` / 实例 `prod.map_mono`

English:
instance prod.map_mono
  signature: {C : Type*} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
  body: ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ prod.fst) h
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ prod.snd) h⟩

@[reassoc]

中文:
实例 prod.map_mono
  签名: {C : 类型} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
  定义体: ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ prod.fst) h
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ prod.snd) h⟩

@[reassoc]

Depends on / 依赖: cancel_mono, congr_arg, prod.fst, prod.snd
-/
instance prod.map_mono {C : Type*} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ prod.fst) h
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ prod.snd) h⟩

@[reassoc]
/--
theorem `prod.diag_map` / 定理 `prod.diag_map`

English:
theorem prod.diag_map
  given: {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y]
  proof: by simp

@[reassoc]

中文:
定理 prod.diag_map
  条件: {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y]
  证明: by simp

@[reassoc]
-/
theorem prod.diag_map {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y] :
    diag X ≫ prod.map f f = f ≫ diag Y := by simp

@[reassoc]
/--
theorem `prod.diag_map_fst_snd` / 定理 `prod.diag_map_fst_snd`

English:
theorem prod.diag_map_fst_snd
  given: {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)]
  proof: by simp

@[reassoc]

中文:
定理 prod.diag_map_fst_snd
  条件: {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)]
  证明: by simp

@[reassoc]
-/
theorem prod.diag_map_fst_snd {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)] :
    diag (X ⨯ Y) ≫ prod.map prod.fst prod.snd = 𝟙 (X ⨯ Y) := by simp

@[reassoc]
/--
theorem `prod.diag_map_fst_snd_comp` / 定理 `prod.diag_map_fst_snd_comp`

English:
theorem prod.diag_map_fst_snd_comp
  statement: [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
  proof: by simp

中文:
定理 prod.diag_map_fst_snd_comp
  结论: [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
  证明: by simp
-/
theorem prod.diag_map_fst_snd_comp [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    diag (X ⨯ X') ≫ prod.map (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by simp

set_option backward.isDefEq.respectTransparency false in
instance {X : C} [HasBinaryProduct X X] : IsSplitMono (diag X) :=
  IsSplitMono.mk' { retraction := prod.fst }

end ProdLemmas

noncomputable section CoprodLemmas

set_option backward.isDefEq.respectTransparency false in
@[reassoc, simp]
/--
theorem `coprod.desc_comp` / 定理 `coprod.desc_comp`

English:
theorem coprod.desc_comp
  statement: {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
  proof: by
  ext <;> simp

中文:
定理 coprod.desc_comp
  结论: {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
  证明: by
  ext <;> simp
-/
theorem coprod.desc_comp {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
    (h : Y ⟶ V) : coprod.desc g h ≫ f = coprod.desc (g ≫ f) (h ≫ f) := by
  ext <;> simp

/--
theorem `coprod.diag_comp` / 定理 `coprod.diag_comp`

English:
theorem coprod.diag_comp
  given: {X Y : C} [HasBinaryCoproduct X X] (f : X ⟶ Y)
  proof: by simp

@[reassoc (attr := simp)]

中文:
定理 coprod.diag_comp
  条件: {X Y : C} [HasBinaryCoproduct X X] (f : X ⟶ Y)
  证明: by simp

@[reassoc (attr := simp)]
-/
theorem coprod.diag_comp {X Y : C} [HasBinaryCoproduct X X] (f : X ⟶ Y) :
    codiag X ≫ f = coprod.desc f f := by simp

@[reassoc (attr := simp)]
/--
theorem `coprod.inl_map` / 定理 `coprod.inl_map`

English:
theorem coprod.inl_map
  statement: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
  proof: ι_colimMap _ _

@[reassoc (attr := simp)]

中文:
定理 coprod.inl_map
  结论: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
  证明: ι_colimMap _ _

@[reassoc (attr := simp)]
-/
theorem coprod.inl_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inl ≫ coprod.map f g = f ≫ coprod.inl :=
  ι_colimMap _ _

@[reassoc (attr := simp)]
/--
theorem `coprod.inr_map` / 定理 `coprod.inr_map`

English:
theorem coprod.inr_map
  statement: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
  proof: ι_colimMap _ _

@[simp]

中文:
定理 coprod.inr_map
  结论: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
  证明: ι_colimMap _ _

@[simp]
-/
theorem coprod.inr_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inr ≫ coprod.map f g = g ≫ coprod.inr :=
  ι_colimMap _ _

@[simp]
/--
theorem `coprod.map_id_id` / 定理 `coprod.map_id_id`

English:
theorem coprod.map_id_id
  given: {X Y : C} [HasBinaryCoproduct X Y]
  statement: coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _
  proof: by
  ext <;> simp

中文:
定理 coprod.map_id_id
  条件: {X Y : C} [HasBinaryCoproduct X Y]
  结论: coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _
  证明: by
  ext <;> simp

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, mul_hom
-/
theorem coprod.map_id_id {X Y : C} [HasBinaryCoproduct X Y] : coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `coprod.desc_inl_inr` / 定理 `coprod.desc_inl_inr`

English:
theorem coprod.desc_inl_inr
  given: {X Y : C} [HasBinaryCoproduct X Y]
  proof: by ext <;> simp

中文:
定理 coprod.desc_inl_inr
  条件: {X Y : C} [HasBinaryCoproduct X Y]
  证明: by ext <;> simp
-/
theorem coprod.desc_inl_inr {X Y : C} [HasBinaryCoproduct X Y] :
    coprod.desc coprod.inl coprod.inr = 𝟙 (X ⨿ Y) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
/--
theorem `coprod.map_desc` / 定理 `coprod.map_desc`

English:
theorem coprod.map_desc
  statement: {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V]
  proof: by
  ext <;> simp

@[simp]

中文:
定理 coprod.map_desc
  结论: {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V]
  证明: by
  ext <;> simp

@[simp]
-/
theorem coprod.map_desc {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V]
    (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
    coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) := by
  ext <;> simp

@[simp]
/--
theorem `coprod.desc_comp_inl_comp_inr` / 定理 `coprod.desc_comp_inl_comp_inr`

English:
theorem coprod.desc_comp_inl_comp_inr
  statement: {W X Y Z : C} [HasBinaryCoproduct W Y]
  proof: by
  rw [← coprod.map_desc]; simp

中文:
定理 coprod.desc_comp_inl_comp_inr
  结论: {W X Y Z : C} [HasBinaryCoproduct W Y]
  证明: by
  rw [← coprod.map_desc]; simp

Depends on / 依赖: coprod, coprod.map_desc, map_desc
-/
theorem coprod.desc_comp_inl_comp_inr {W X Y Z : C} [HasBinaryCoproduct W Y]
    [HasBinaryCoproduct X Z] (g : W ⟶ X) (g' : Y ⟶ Z) :
    coprod.desc (g ≫ coprod.inl) (g' ≫ coprod.inr) = coprod.map g g' := by
  rw [← coprod.map_desc]; simp

-- We take the right-hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (e.g. `id_comp`), while `inl_map` and `inr_map` can still work just
-- as well.
@[reassoc (attr := simp)]
/--
theorem `coprod.map_map` / 定理 `coprod.map_map`

English:
theorem coprod.map_map
  statement: {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
  proof: by
  ext <;> simp

中文:
定理 coprod.map_map
  结论: {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
  证明: by
  ext <;> simp
-/
theorem coprod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
    [HasBinaryCoproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) := by
  ext <;> simp

-- I don't think it's a good idea to make any of the following three simp lemmas.
@[reassoc]
/--
theorem `coprod.map_swap` / 定理 `coprod.map_swap`

English:
theorem coprod.map_swap
  statement: {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
  proof: by simp

@[reassoc]

中文:
定理 coprod.map_swap
  结论: {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
  证明: by simp

@[reassoc]
-/
theorem coprod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasColimitsOfShape (Discrete WalkingPair) C] :
    coprod.map (𝟙 X) f ≫ coprod.map g (𝟙 B) = coprod.map g (𝟙 A) ≫ coprod.map (𝟙 Y) f := by simp

@[reassoc]
/--
theorem `coprod.map_comp_id` / 定理 `coprod.map_comp_id`

English:
theorem coprod.map_comp_id
  statement: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct Z W]
  proof: by simp

@[reassoc]

中文:
定理 coprod.map_comp_id
  结论: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct Z W]
  证明: by simp

@[reassoc]
-/
theorem coprod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct Z W]
    [HasBinaryCoproduct Y W] [HasBinaryCoproduct X W] :
    coprod.map (f ≫ g) (𝟙 W) = coprod.map f (𝟙 W) ≫ coprod.map g (𝟙 W) := by simp

@[reassoc]
/--
theorem `coprod.map_id_comp` / 定理 `coprod.map_id_comp`

English:
theorem coprod.map_id_comp
  statement: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct W X]
  proof: by simp

中文:
定理 coprod.map_id_comp
  结论: {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct W X]
  证明: by simp
-/
theorem coprod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct W X]
    [HasBinaryCoproduct W Y] [HasBinaryCoproduct W Z] :
    coprod.map (𝟙 W) (f ≫ g) = coprod.map (𝟙 W) f ≫ coprod.map (𝟙 W) g := by simp

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : W ≅ Z` induces an isomorphism `coprod.mapIso f g : W ⨿ X ≅ Y ⨿ Z`. -/
@[simps]
/--
Definition of `coprod.mapIso` / `coprod.mapIso` 的定义

English:
definition coprod.mapIso
  signature: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y)
  body: coprod.map f.hom g.hom
  inv := coprod.map f.inv g.inv

中文:
定义 coprod.mapIso
  签名: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y)
  定义体: coprod.map f.hom g.hom
  inv := coprod.map f.inv g.inv

Depends on / 依赖: coprod, coprod.map, f.hom, g.hom
-/
def coprod.mapIso {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨿ X ≅ Y ⨿ Z where
  hom := coprod.map f.hom g.hom
  inv := coprod.map f.inv g.inv

/--
Instance `isIso_coprod` / 实例 `isIso_coprod`

English:
instance isIso_coprod
  signature: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
  body: (coprod.mapIso (asIso f) (asIso g)).isIso_hom

中文:
实例 isIso_coprod
  签名: {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
  定义体: (coprod.mapIso (asIso f) (asIso g)).isIso_hom

Depends on / 依赖: coprod, coprod.mapIso, isIso_hom, mapIso
-/
instance isIso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (coprod.map f g) :=
  (coprod.mapIso (asIso f) (asIso g)).isIso_hom

/--
Instance `coprod.map_epi` / 实例 `coprod.map_epi`

English:
instance coprod.map_epi
  signature: {C : Type*} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
  body: ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩

@[reassoc]

中文:
实例 coprod.map_epi
  签名: {C : 类型} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
  定义体: ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩

@[reassoc]

Depends on / 依赖: cancel_epi, congr_arg, coprod, coprod.inl, coprod.inr
-/
instance coprod.map_epi {C : Type*} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] : Epi (coprod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩

@[reassoc]
/--
theorem `coprod.map_codiag` / 定理 `coprod.map_codiag`

English:
theorem coprod.map_codiag
  given: {X Y : C} (f : X ⟶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y]
  proof: by simp

@[reassoc]

中文:
定理 coprod.map_codiag
  条件: {X Y : C} (f : X ⟶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y]
  证明: by simp

@[reassoc]
-/
theorem coprod.map_codiag {X Y : C} (f : X ⟶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y] :
    coprod.map f f ≫ codiag Y = codiag X ≫ f := by simp

@[reassoc]
/--
theorem `coprod.map_inl_inr_codiag` / 定理 `coprod.map_inl_inr_codiag`

English:
theorem coprod.map_inl_inr_codiag
  statement: {X Y : C} [HasBinaryCoproduct X Y]
  proof: by simp

@[reassoc]

中文:
定理 coprod.map_inl_inr_codiag
  结论: {X Y : C} [HasBinaryCoproduct X Y]
  证明: by simp

@[reassoc]
-/
theorem coprod.map_inl_inr_codiag {X Y : C} [HasBinaryCoproduct X Y]
    [HasBinaryCoproduct (X ⨿ Y) (X ⨿ Y)] :
    coprod.map coprod.inl coprod.inr ≫ codiag (X ⨿ Y) = 𝟙 (X ⨿ Y) := by simp

@[reassoc]
/--
theorem `coprod.map_comp_inl_inr_codiag` / 定理 `coprod.map_comp_inl_inr_codiag`

English:
theorem coprod.map_comp_inl_inr_codiag
  statement: [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
  proof: by simp

中文:
定理 coprod.map_comp_inl_inr_codiag
  结论: [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
  证明: by simp
-/
theorem coprod.map_comp_inl_inr_codiag [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    coprod.map (g ≫ coprod.inl) (g' ≫ coprod.inr) ≫ codiag (Y ⨿ Y') = coprod.map g g' := by simp

end CoprodLemmas

variable (C)

/-- A category `HasBinaryProducts` if it has all limits of shape `Discrete WalkingPair`,
i.e. if it has a product for every pair of objects. -/
@[stacks 001T]
/--
Definition of `HasBinaryProducts` / `HasBinaryProducts` 的定义

English:
abbreviation HasBinaryProducts
  body: HasLimitsOfShape (Discrete WalkingPair) C

中文:
缩写 HasBinaryProducts
  定义体: HasLimitsOfShape (Discrete WalkingPair) C

Depends on / 依赖: Discrete, HasLimitsOfShape, WalkingPair
-/
abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C

/-- A category `HasBinaryCoproducts` if it has all colimit of shape `Discrete WalkingPair`,
i.e. if it has a coproduct for every pair of objects. -/
@[stacks 04AP]
/--
Definition of `HasBinaryCoproducts` / `HasBinaryCoproducts` 的定义

English:
abbreviation HasBinaryCoproducts
  body: HasColimitsOfShape (Discrete WalkingPair) C

中文:
缩写 HasBinaryCoproducts
  定义体: HasColimitsOfShape (Discrete WalkingPair) C

Depends on / 依赖: Discrete, HasColimitsOfShape, WalkingPair
-/
abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C

/--
theorem `hasBinaryProducts_of_hasLimit_pair` / 定理 `hasBinaryProducts_of_hasLimit_pair`

English:
theorem hasBinaryProducts_of_hasLimit_pair
  given: [forall {X Y : C}, HasLimit (pair X Y)]
  proof: { has_limit := fun F => hasLimit_of_iso (diagramIsoPair F).symm }

中文:
定理 hasBinaryProducts_of_hasLimit_pair
  条件: [对任意 {X Y : C}, HasLimit (pair X Y)]
  证明: { has_limit := fun F => hasLimit_of_iso (diagramIsoPair F).symm }

Depends on / 依赖: diagramIsoPair, fun_, hasLimit_of_iso, has_limit
-/
theorem hasBinaryProducts_of_hasLimit_pair [forall {X Y : C}, HasLimit (pair X Y)] :
    HasBinaryProducts C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoPair F).symm }

/--
theorem `hasBinaryCoproducts_of_hasColimit_pair` / 定理 `hasBinaryCoproducts_of_hasColimit_pair`

English:
theorem hasBinaryCoproducts_of_hasColimit_pair
  given: [forall {X Y : C}, HasColimit (pair X Y)]
  proof: { has_colimit := fun F => hasColimit_of_iso (diagramIsoPair F) }

noncomputable section

中文:
定理 hasBinaryCoproducts_of_hasColimit_pair
  条件: [对任意 {X Y : C}, HasColimit (pair X Y)]
  证明: { has_colimit := fun F => hasColimit_of_iso (diagramIsoPair F) }

noncomputable section

Depends on / 依赖: Category, Category.assoc, diagramIsoPair, hasColimit_of_iso, has_colimit, mul_def, mul_hom, one_def, one_hom, slice_lhs, slice_rhs, tensorHom_comp_tensorHom, tensorObj, tensorObj.mul_def, tensorObj.one_def
-/
theorem hasBinaryCoproducts_of_hasColimit_pair [forall {X Y : C}, HasColimit (pair X Y)] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoPair F) }

noncomputable section

variable {C}

set_option backward.isDefEq.respectTransparency false in
/-- The braiding isomorphism which swaps a binary product. -/
@[simps]
/--
Definition of `prod.braiding` / `prod.braiding` 的定义

English:
definition prod.braiding
  signature: (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P]
  body: prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

中文:
定义 prod.braiding
  签名: (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P]
  定义体: prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

Depends on / 依赖: IsMonHom, mul_hom, one_hom, prod.fst, prod.lift, prod.snd
-/
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P ⨯ Q ≅ Q ⨯ P where
  hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/--
theorem `braid_natural` / 定理 `braid_natural`

English:
theorem braid_natural
  given: [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W)
  proof: by simp

@[reassoc]

中文:
定理 braid_natural
  条件: [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W)
  证明: by simp

@[reassoc]

Depends on / 依赖: IsMonHom, mul_hom, one_hom
-/
theorem braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g f := by simp

@[reassoc]
/--
theorem `prod.symmetry'` / 定理 `prod.symmetry'`

English:
theorem prod.symmetry'
  given: (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P]
  proof: (prod.braiding _ _).hom_inv_id

中文:
定理 prod.symmetry'
  条件: (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P]
  证明: (prod.braiding _ _).hom_inv_id

Depends on / 依赖: braiding, hom_inv_id, prod.braiding
-/
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
  (prod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
/--
theorem `prod.symmetry` / 定理 `prod.symmetry`

English:
theorem prod.symmetry
  given: (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P]
  proof: (prod.braiding _ _).hom_inv_id

中文:
定理 prod.symmetry
  条件: (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P]
  证明: (prod.braiding _ _).hom_inv_id

Depends on / 依赖: braiding, hom_inv_id, prod.braiding
-/
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
  (prod.braiding _ _).hom_inv_id

set_option backward.isDefEq.respectTransparency false in
/-- The associator isomorphism for binary products. -/
@[simps]
/--
Definition of `prod.associator` / `prod.associator` 的定义

English:
definition prod.associator
  signature: [HasBinaryProducts C] (P Q R : C)
  body: prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)

中文:
定义 prod.associator
  签名: [HasBinaryProducts C] (P Q R : C)
  定义体: prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)

Depends on / 依赖: prod.fst, prod.lift, prod.snd
-/
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ Q ⨯ R where
  hom := prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `prod.pentagon` / 定理 `prod.pentagon`

English:
theorem prod.pentagon
  given: [HasBinaryProducts C] (W X Y Z : C)
  proof: by
  simp

@[reassoc]

中文:
定理 prod.pentagon
  条件: [HasBinaryProducts C] (W X Y Z : C)
  证明: by
  simp

@[reassoc]
-/
theorem prod.pentagon [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (prod.associator W X Y).hom (𝟙 Z) ≫
        (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) (prod.associator X Y Z).hom =
      (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y ⨯ Z)).hom := by
  simp

@[reassoc]
/--
theorem `prod.associator_naturality` / 定理 `prod.associator_naturality`

English:
theorem prod.associator_naturality
  statement: [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁)
  proof: by
  simp

中文:
定理 prod.associator_naturality
  结论: [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁)
  证明: by
  simp

Depends on / 依赖: IsMonHom, cat_disch, mul_f, one_f
-/
theorem prod.associator_naturality [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
      (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) := by
  simp

variable [HasTerminal C]

set_option backward.isDefEq.respectTransparency false in
/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps]
/--
Definition of `prod.leftUnitor` / `prod.leftUnitor` 的定义

English:
definition prod.leftUnitor
  signature: (P : C) [HasBinaryProduct (⊤_ C) P]
  body: prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

中文:
定义 prod.leftUnitor
  签名: (P : C) [HasBinaryProduct (⊤_ C) P]
  定义体: prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

Depends on / 依赖: prod.snd
-/
def prod.leftUnitor (P : C) [HasBinaryProduct (⊤_ C) P] : (⊤_ C) ⨯ P ≅ P where
  hom := prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps]
/--
Definition of `prod.rightUnitor` / `prod.rightUnitor` 的定义

English:
definition prod.rightUnitor
  signature: (P : C) [HasBinaryProduct P (⊤_ C)]
  body: prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[reassoc]

中文:
定义 prod.rightUnitor
  签名: (P : C) [HasBinaryProduct P (⊤_ C)]
  定义体: prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[reassoc]

Depends on / 依赖: prod.fst
-/
def prod.rightUnitor (P : C) [HasBinaryProduct P (⊤_ C)] : P ⨯ ⊤_ C ≅ P where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[reassoc]
/--
theorem `prod.leftUnitor_hom_naturality` / 定理 `prod.leftUnitor_hom_naturality`

English:
theorem prod.leftUnitor_hom_naturality
  given: [HasBinaryProducts C] (f : X ⟶ Y)
  proof: prod.map_snd _ _

@[reassoc]

中文:
定理 prod.leftUnitor_hom_naturality
  条件: [HasBinaryProducts C] (f : X ⟶ Y)
  证明: prod.map_snd _ _

@[reassoc]

Depends on / 依赖: map_snd, prod.map_snd
-/
theorem prod.leftUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map (𝟙 _) f ≫ (prod.leftUnitor Y).hom = (prod.leftUnitor X).hom ≫ f :=
  prod.map_snd _ _

@[reassoc]
/--
theorem `prod.leftUnitor_inv_naturality` / 定理 `prod.leftUnitor_inv_naturality`

English:
theorem prod.leftUnitor_inv_naturality
  given: [HasBinaryProducts C] (f : X ⟶ Y)
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [prod.leftUnitor_hom_naturality]

@[reassoc]

中文:
定理 prod.leftUnitor_inv_naturality
  条件: [HasBinaryProducts C] (f : X ⟶ Y)
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [prod.leftUnitor_hom_naturality]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, Iso.inv_comp_eq, eq_comp_inv, inv_comp_eq, leftUnitor_hom_naturality, prod.leftUnitor_hom_naturality
-/
theorem prod.leftUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.leftUnitor Y).inv := by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [prod.leftUnitor_hom_naturality]

@[reassoc]
/--
theorem `prod.rightUnitor_hom_naturality` / 定理 `prod.rightUnitor_hom_naturality`

English:
theorem prod.rightUnitor_hom_naturality
  given: [HasBinaryProducts C] (f : X ⟶ Y)
  proof: prod.map_fst _ _

@[reassoc]

中文:
定理 prod.rightUnitor_hom_naturality
  条件: [HasBinaryProducts C] (f : X ⟶ Y)
  证明: prod.map_fst _ _

@[reassoc]

Depends on / 依赖: map_fst, prod.map_fst
-/
theorem prod.rightUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map f (𝟙 _) ≫ (prod.rightUnitor Y).hom = (prod.rightUnitor X).hom ≫ f :=
  prod.map_fst _ _

@[reassoc]
/--
theorem `prod_rightUnitor_inv_naturality` / 定理 `prod_rightUnitor_inv_naturality`

English:
theorem prod_rightUnitor_inv_naturality
  given: [HasBinaryProducts C] (f : X ⟶ Y)
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [prod.rightUnitor_hom_naturality]

中文:
定理 prod_rightUnitor_inv_naturality
  条件: [HasBinaryProducts C] (f : X ⟶ Y)
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [prod.rightUnitor_hom_naturality]

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, Iso.inv_comp_eq, eq_comp_inv, f.isMonHom_hom, inv_comp_eq, isMonHom_hom, prod.rightUnitor_hom_naturality, rightUnitor_hom_naturality
-/
theorem prod_rightUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv := by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [prod.rightUnitor_hom_naturality]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `prod.triangle` / 定理 `prod.triangle`

English:
theorem prod.triangle
  given: [HasBinaryProducts C] (X Y : C)
  proof: by
  ext <;> simp

中文:
定理 prod.triangle
  条件: [HasBinaryProducts C] (X Y : C)
  证明: by
  ext <;> simp

Depends on / 依赖: Hom.ext
-/
theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) (prod.leftUnitor Y).hom =
      prod.map (prod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section

variable {C}
variable [HasBinaryCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps]
/--
Definition of `coprod.braiding` / `coprod.braiding` 的定义

English:
definition coprod.braiding
  signature: (P Q : C)
  body: coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]

中文:
定义 coprod.braiding
  签名: (P Q : C)
  定义体: coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]

Depends on / 依赖: coprod, coprod.desc, coprod.inl, coprod.inr
-/
def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P where
  hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]
/--
theorem `coprod.symmetry'` / 定理 `coprod.symmetry'`

English:
theorem coprod.symmetry'
  given: (P Q : C)
  proof: (coprod.braiding _ _).hom_inv_id

中文:
定理 coprod.symmetry'
  条件: (P Q : C)
  证明: (coprod.braiding _ _).hom_inv_id

Depends on / 依赖: braiding, coprod, coprod.braiding, hom_inv_id
-/
theorem coprod.symmetry' (P Q : C) :
    coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
  (coprod.braiding _ _).hom_inv_id

/--
theorem `coprod.symmetry` / 定理 `coprod.symmetry`

English:
theorem coprod.symmetry
  given: (P Q : C)
  statement: (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _
  proof: coprod.symmetry' _ _

中文:
定理 coprod.symmetry
  条件: (P Q : C)
  结论: (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _
  证明: coprod.symmetry' _ _

Depends on / 依赖: coprod, coprod.symmetry, symmetry
-/
theorem coprod.symmetry (P Q : C) : (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
  coprod.symmetry' _ _

set_option backward.isDefEq.respectTransparency false in
/-- The associator isomorphism for binary coproducts. -/
@[simps]
/--
Definition of `coprod.associator` / `coprod.associator` 的定义

English:
definition coprod.associator
  signature: (P Q R : C)
  body: coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)

中文:
定义 coprod.associator
  签名: (P Q R : C)
  定义体: coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)

Depends on / 依赖: coprod, coprod.desc, coprod.inl, coprod.inr
-/
def coprod.associator (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ Q ⨿ R where
  hom := coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coprod.pentagon` / 定理 `coprod.pentagon`

English:
theorem coprod.pentagon
  given: (W X Y Z : C)
  proof: by
  simp

中文:
定理 coprod.pentagon
  条件: (W X Y Z : C)
  证明: by
  simp
-/
theorem coprod.pentagon (W X Y Z : C) :
    coprod.map (coprod.associator W X Y).hom (𝟙 Z) ≫
        (coprod.associator W (X ⨿ Y) Z).hom ≫ coprod.map (𝟙 W) (coprod.associator X Y Z).hom =
      (coprod.associator (W ⨿ X) Y Z).hom ≫ (coprod.associator W X (Y ⨿ Z)).hom := by
  simp

/--
theorem `coprod.associator_naturality` / 定理 `coprod.associator_naturality`

English:
theorem coprod.associator_naturality
  statement: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  proof: by
  simp

中文:
定理 coprod.associator_naturality
  结论: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  证明: by
  simp
-/
theorem coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
      (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) := by
  simp

variable [HasInitial C]

set_option backward.isDefEq.respectTransparency false in
/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
/--
Definition of `coprod.leftUnitor` / `coprod.leftUnitor` 的定义

English:
definition coprod.leftUnitor
  signature: (P : C)
  body: coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

中文:
定义 coprod.leftUnitor
  签名: (P : C)
  定义体: coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

Depends on / 依赖: coprod, coprod.desc, forget, initial, initial.to
-/
def coprod.leftUnitor (P : C) : (⊥_ C) ⨿ P ≅ P where
  hom := coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

/--
theorem `coprod.leftUnitor_naturality` / 定理 `coprod.leftUnitor_naturality`

English:
theorem coprod.leftUnitor_naturality
  given: (f : X ⟶ Y)
  proof: by
  simp

中文:
定理 coprod.leftUnitor_naturality
  条件: (f : X ⟶ Y)
  证明: by
  simp
-/
theorem coprod.leftUnitor_naturality (f : X ⟶ Y) :
    coprod.map (𝟙 _) f ≫ (coprod.leftUnitor Y).hom = (coprod.leftUnitor X).hom ≫ f := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
/--
Definition of `coprod.rightUnitor` / `coprod.rightUnitor` 的定义

English:
definition coprod.rightUnitor
  signature: (P : C)
  body: coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

中文:
定义 coprod.rightUnitor
  签名: (P : C)
  定义体: coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

Depends on / 依赖: coprod, coprod.desc, initial, initial.to
-/
def coprod.rightUnitor (P : C) : P ⨿ ⊥_ C ≅ P where
  hom := coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

/--
theorem `coprod.rightUnitor_naturality` / 定理 `coprod.rightUnitor_naturality`

English:
theorem coprod.rightUnitor_naturality
  given: (f : X ⟶ Y)
  proof: by
  simp

中文:
定理 coprod.rightUnitor_naturality
  条件: (f : X ⟶ Y)
  证明: by
  simp
-/
theorem coprod.rightUnitor_naturality (f : X ⟶ Y) :
    coprod.map f (𝟙 _) ≫ (coprod.rightUnitor Y).hom = (coprod.rightUnitor X).hom ≫ f := by
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coprod.triangle` / 定理 `coprod.triangle`

English:
theorem coprod.triangle
  given: (X Y : C)
  proof: by
  ext <;> simp

中文:
定理 coprod.triangle
  条件: (X Y : C)
  证明: by
  ext <;> simp
-/
theorem coprod.triangle (X Y : C) :
    (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) (coprod.leftUnitor Y).hom =
      coprod.map (coprod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section ProdFunctor

variable {C} [HasBinaryProducts C]

/-- The binary product functor. -/
@[simps]
/--
Definition of `prod.functor` / `prod.functor` 的定义

English:
definition prod.functor
  signature: : C ⥤ C ⥤ C where
  body: { obj := fun Y => X ⨯ Y
      map := fun {_ _} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }

中文:
定义 prod.functor
  签名: : C ⥤ C ⥤ C where
  定义体: { obj := fun Y => X ⨯ Y
      map := fun {_ _} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }

Depends on / 依赖: prod.map
-/
def prod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨯ Y
      map := fun {_ _} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `prod.functorLeftComp` / `prod.functorLeftComp` 的定义

English:
definition prod.functorLeftComp
  signature: (X Y : C)
  body: NatIso.ofComponents (prod.associator _ _)

中文:
定义 prod.functorLeftComp
  签名: (X Y : C)
  定义体: NatIso.ofComponents (prod.associator _ _)

Depends on / 依赖: NatIso, NatIso.ofComponents, associator, ofComponents, prod.associator
-/
def prod.functorLeftComp (X Y : C) :
    prod.functor.obj (X ⨯ Y) ≅ prod.functor.obj Y ⋙ prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)

end ProdFunctor

noncomputable section CoprodFunctor

variable {C} [HasBinaryCoproducts C]

/-- The binary coproduct functor. -/
@[simps]
/--
Definition of `coprod.functor` / `coprod.functor` 的定义

English:
definition coprod.functor
  signature: : C ⥤ C ⥤ C where
  body: { obj := fun Y => X ⨿ Y
      map := fun {_ _} => coprod.map (𝟙 X) }
  map f := { app := fun T => coprod.map f (𝟙 T) }

中文:
定义 coprod.functor
  签名: : C ⥤ C ⥤ C where
  定义体: { obj := fun Y => X ⨿ Y
      map := fun {_ _} => coprod.map (𝟙 X) }
  map f := { app := fun T => coprod.map f (𝟙 T) }

Depends on / 依赖: coprod, coprod.map
-/
def coprod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨿ Y
      map := fun {_ _} => coprod.map (𝟙 X) }
  map f := { app := fun T => coprod.map f (𝟙 T) }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `coprod.functorLeftComp` / `coprod.functorLeftComp` 的定义

English:
definition coprod.functorLeftComp
  signature: (X Y : C)
  body: NatIso.ofComponents (coprod.associator _ _)

中文:
定义 coprod.functorLeftComp
  签名: (X Y : C)
  定义体: NatIso.ofComponents (coprod.associator _ _)

Depends on / 依赖: NatIso, NatIso.ofComponents, associator, coprod, coprod.associator, ofComponents
-/
def coprod.functorLeftComp (X Y : C) :
    coprod.functor.obj (X ⨿ Y) ≅ coprod.functor.obj Y ⋙ coprod.functor.obj X :=
  NatIso.ofComponents (coprod.associator _ _)

end CoprodFunctor

section

variable {C} {D : Type*} [Category* D] {F : C ⥤ D}

variable (F) in
/--
Definition of `BinaryFan.map` / `BinaryFan.map` 的定义

English:
abbreviation BinaryFan.map
  signature: {X Y : C} (s : BinaryFan X Y)
  body: mk (F.map s.fst) (F.map s.snd)

@[simp]

中文:
缩写 BinaryFan.map
  签名: {X Y : C} (s : BinaryFan X Y)
  定义体: mk (F.map s.fst) (F.map s.snd)

@[simp]

Depends on / 依赖: F.map, s.fst, s.snd
-/
abbrev BinaryFan.map {X Y : C} (s : BinaryFan X Y) : BinaryFan (F.obj X) (F.obj Y) :=
  mk (F.map s.fst) (F.map s.snd)

@[simp]
/--
lemma `BinaryFan.map_fst` / 引理 `BinaryFan.map_fst`

English:
lemma BinaryFan.map_fst
  given: {X Y : C} (s : BinaryFan X Y)
  statement: (s.map F).fst = F.map s.fst
  proof: rfl

@[simp]

中文:
引理 BinaryFan.map_fst
  条件: {X Y : C} (s : BinaryFan X Y)
  结论: (s.map F).fst = F.map s.fst
  证明: rfl

@[simp]
-/
lemma BinaryFan.map_fst {X Y : C} (s : BinaryFan X Y) : (s.map F).fst = F.map s.fst := rfl

@[simp]
/--
lemma `BinaryFan.map_snd` / 引理 `BinaryFan.map_snd`

English:
lemma BinaryFan.map_snd
  given: {X Y : C} (s : BinaryFan X Y)
  statement: (s.map F).snd = F.map s.snd
  proof: rfl

中文:
引理 BinaryFan.map_snd
  条件: {X Y : C} (s : BinaryFan X Y)
  结论: (s.map F).snd = F.map s.snd
  证明: rfl
-/
lemma BinaryFan.map_snd {X Y : C} (s : BinaryFan X Y) : (s.map F).snd = F.map s.snd := rfl

variable (F) in
/--
Definition of `BinaryCofan.map` / `BinaryCofan.map` 的定义

English:
abbreviation BinaryCofan.map
  signature: {X Y : C} (s : BinaryCofan X Y)
  body: mk (F.map s.inl) (F.map s.inr)

@[simp]

中文:
缩写 BinaryCofan.map
  签名: {X Y : C} (s : BinaryCofan X Y)
  定义体: mk (F.map s.inl) (F.map s.inr)

@[simp]

Depends on / 依赖: F.map, s.inl, s.inr
-/
abbrev BinaryCofan.map {X Y : C} (s : BinaryCofan X Y) : BinaryCofan (F.obj X) (F.obj Y) :=
  mk (F.map s.inl) (F.map s.inr)

@[simp]
/--
lemma `BinaryCofan.map_inl` / 引理 `BinaryCofan.map_inl`

English:
lemma BinaryCofan.map_inl
  given: {X Y : C} (s : BinaryCofan X Y)
  statement: (s.map F).inl = F.map s.inl
  proof: rfl

@[simp]

中文:
引理 BinaryCofan.map_inl
  条件: {X Y : C} (s : BinaryCofan X Y)
  结论: (s.map F).inl = F.map s.inl
  证明: rfl

@[simp]
-/
lemma BinaryCofan.map_inl {X Y : C} (s : BinaryCofan X Y) : (s.map F).inl = F.map s.inl := rfl

@[simp]
/--
lemma `BinaryCofan.map_inr` / 引理 `BinaryCofan.map_inr`

English:
lemma BinaryCofan.map_inr
  given: {X Y : C} (s : BinaryCofan X Y)
  statement: (s.map F).inr = F.map s.inr
  proof: rfl

中文:
引理 BinaryCofan.map_inr
  条件: {X Y : C} (s : BinaryCofan X Y)
  结论: (s.map F).inr = F.map s.inr
  证明: rfl
-/
lemma BinaryCofan.map_inr {X Y : C} (s : BinaryCofan X Y) : (s.map F).inr = F.map s.inr := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `BinaryFan.isLimitMapConeEquiv` / `BinaryFan.isLimitMapConeEquiv` 的定义

English:
definition BinaryFan.isLimitMapConeEquiv
  signature: {X Y : C} {s : BinaryFan X Y}
  body: IsLimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ ext (Iso.refl _)
    (by simp [fst]) (by simp [snd])

中文:
定义 BinaryFan.isLimitMapConeEquiv
  签名: {X Y : C} {s : BinaryFan X Y}
  定义体: IsLimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ ext (Iso.refl _)
    (by simp [fst]) (by simp [snd])

Depends on / 依赖: IsLimit, IsLimit.equivOfNatIsoOfIso, Iso.refl, diagramIsoPair, equivOfNatIsoOfIso
-/
def BinaryFan.isLimitMapConeEquiv {X Y : C} {s : BinaryFan X Y} :
    IsLimit (F.mapCone s) ≃ IsLimit (s.map F) :=
IsLimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ ext (Iso.refl _)
    (by simp [fst]) (by simp [snd])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `BinaryCofan.isColimitMapConeEquiv` / `BinaryCofan.isColimitMapConeEquiv` 的定义

English:
definition BinaryCofan.isColimitMapConeEquiv
  signature: {X Y : C} {s : BinaryCofan X Y}
  body: IsColimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ ext (Iso.refl _)
    (by simp [inl]) (by simp [inr])

中文:
定义 BinaryCofan.isColimitMapConeEquiv
  签名: {X Y : C} {s : BinaryCofan X Y}
  定义体: IsColimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ ext (Iso.refl _)
    (by simp [inl]) (by simp [inr])

Depends on / 依赖: IsColimit, IsColimit.equivOfNatIsoOfIso, Iso.refl, diagramIsoPair, equivOfNatIsoOfIso
-/
def BinaryCofan.isColimitMapConeEquiv {X Y : C} {s : BinaryCofan X Y} :
    IsColimit (F.mapCocone s) ≃ IsColimit (s.map F) :=
IsColimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ ext (Iso.refl _)
    (by simp [inl]) (by simp [inr])

end

noncomputable section ProdComparison

universe w w' u₃

variable {C} {D : Type u₂} [Category.{w} D] {E : Type u₃} [Category.{w'} E]
variable (F : C ⥤ D) (G : D ⥤ E) {A A' B B' : C}
variable [HasBinaryProduct A B] [HasBinaryProduct A' B']
variable [HasBinaryProduct (F.obj A) (F.obj B)]
variable [HasBinaryProduct (F.obj A') (F.obj B')]
variable [HasBinaryProduct (G.obj (F.obj A)) (G.obj (F.obj B))]
variable [HasBinaryProduct ((F ⋙ G).obj A) ((F ⋙ G).obj B)]

/--
Definition of `prodComparison` / `prodComparison` 的定义

English:
definition prodComparison
  signature: (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
  body: prod.lift (F.map prod.fst) (F.map prod.snd)

中文:
定义 prodComparison
  签名: (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
  定义体: prod.lift (F.map prod.fst) (F.map prod.snd)

Depends on / 依赖: F.map, prod.fst, prod.lift, prod.snd
-/
def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
    [HasBinaryProduct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

variable (A B)

@[reassoc (attr := simp)]
/--
theorem `prodComparison_fst` / 定理 `prodComparison_fst`

English:
theorem prodComparison_fst
  statement: prodComparison F A B ≫ prod.fst = F.map prod.fst
  proof: prod.lift_fst _ _

@[reassoc (attr := simp)]

中文:
定理 prodComparison_fst
  结论: prodComparison F A B ≫ prod.fst = F.map prod.fst
  证明: prod.lift_fst _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst, prod.lift_fst
-/
theorem prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
/--
theorem `prodComparison_snd` / 定理 `prodComparison_snd`

English:
theorem prodComparison_snd
  statement: prodComparison F A B ≫ prod.snd = F.map prod.snd
  proof: prod.lift_snd _ _

中文:
定理 prodComparison_snd
  结论: prodComparison F A B ≫ prod.snd = F.map prod.snd
  证明: prod.lift_snd _ _

Depends on / 依赖: lift_snd, prod.lift_snd
-/
theorem prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

variable {A B}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
/--
theorem `prodComparison_natural` / 定理 `prodComparison_natural`

English:
theorem prodComparison_natural
  given: (f : A ⟶ A') (g : B ⟶ B')
  proof: by
  rw [prodComparison]; rw [prodComparison]; rw [prod.lift_map]; rw [← F.map_comp]; rw [← F.map_comp]; rw [prod.comp_lift]; rw [←
    F.map_comp]; rw [prod.map_fst]; rw [← F.map_comp]; rw [prod.map_snd]

中文:
定理 prodComparison_natural
  条件: (f : A ⟶ A') (g : B ⟶ B')
  证明: by
  rw [prodComparison]; rw [prodComparison]; rw [prod.lift_map]; rw [← F.map_comp]; rw [← F.map_comp]; rw [prod.comp_lift]; rw [←
    F.map_comp]; rw [prod.map_fst]; rw [← F.map_comp]; rw [prod.map_snd]

Depends on / 依赖: F.map_comp, comp_lift, lift_map, map_comp, map_fst, map_snd, prod.comp_lift, prod.lift_map, prod.map_fst, prod.map_snd, prodComparison
-/
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prodComparison]; rw [prodComparison]; rw [prod.lift_map]; rw [← F.map_comp]; rw [← F.map_comp]; rw [prod.comp_lift]; rw [←
    F.map_comp]; rw [prod.map_fst]; rw [← F.map_comp]; rw [prod.map_snd]

variable {F}

/-- Naturality of the `prodComparison` morphism in a natural transformation. -/
@[reassoc]
/--
theorem `prodComparison_natural_of_natTrans` / 定理 `prodComparison_natural_of_natTrans`

English:
theorem prodComparison_natural_of_natTrans
  statement: {H : C ⥤ D} [HasBinaryProduct (H.obj A) (H.obj B)]
  proof: by
  rw [prodComparison]; rw [prodComparison]; rw [prod.lift_map]; rw [prod.comp_lift]; rw [α.naturality]; rw [α.naturality]

中文:
定理 prodComparison_natural_of_natTrans
  结论: {H : C ⥤ D} [HasBinaryProduct (H.obj A) (H.obj B)]
  证明: by
  rw [prodComparison]; rw [prodComparison]; rw [prod.lift_map]; rw [prod.comp_lift]; rw [α.naturality]; rw [α.naturality]

Depends on / 依赖: comp_lift, lift_map, naturality, prod.comp_lift, prod.lift_map, prodComparison
-/
theorem prodComparison_natural_of_natTrans {H : C ⥤ D} [HasBinaryProduct (H.obj A) (H.obj B)]
    (α : F ⟶ H) :
    α.app (prod A B) ≫ prodComparison H A B =
      prodComparison F A B ≫ prod.map (α.app A) (α.app B) := by
  rw [prodComparison]; rw [prodComparison]; rw [prod.lift_map]; rw [prod.comp_lift]; rw [α.naturality]; rw [α.naturality]

variable (F)

set_option backward.defeqAttrib.useBackward true in
/-- The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prodComparison`.
-/
@[simps]
/--
Definition of `prodComparisonNatTrans` / `prodComparisonNatTrans` 的定义

English:
definition prodComparisonNatTrans
  signature: [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C)
  body: prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[reassoc]

中文:
定义 prodComparisonNatTrans
  签名: [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C)
  定义体: prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[reassoc]

Depends on / 依赖: Mon.mk, MonObj, otimes, prodComparison
-/
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app B := prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[reassoc]
/--
theorem `inv_prodComparison_map_fst` / 定理 `inv_prodComparison_map_fst`

English:
theorem inv_prodComparison_map_fst
  given: [IsIso (prodComparison F A B)]
  proof: by simp [IsIso.inv_comp_eq]

@[reassoc]

中文:
定理 inv_prodComparison_map_fst
  条件: [IsIso (prodComparison F A B)]
  证明: by simp [IsIso.inv_comp_eq]

@[reassoc]

Depends on / 依赖: IsIso.inv_comp_eq, inv_comp_eq
-/
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = prod.fst := by simp [IsIso.inv_comp_eq]

@[reassoc]
/--
theorem `inv_prodComparison_map_snd` / 定理 `inv_prodComparison_map_snd`

English:
theorem inv_prodComparison_map_snd
  given: [IsIso (prodComparison F A B)]
  proof: by simp [IsIso.inv_comp_eq]

中文:
定理 inv_prodComparison_map_snd
  条件: [IsIso (prodComparison F A B)]
  证明: by simp [IsIso.inv_comp_eq]

Depends on / 依赖: IsIso.inv_comp_eq, inv_comp_eq
-/
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = prod.snd := by simp [IsIso.inv_comp_eq]

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
/--
theorem `prodComparison_inv_natural` / 定理 `prodComparison_inv_natural`

English:
theorem prodComparison_inv_natural
  statement: (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
  proof: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural]

中文:
定理 prodComparison_inv_natural
  结论: (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
  证明: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural]

Depends on / 依赖: Category, Category.assoc, IsIso.eq_comp_inv, IsIso.inv_comp_eq, eq_comp_inv, inv_comp_eq, prodComparison_natural
-/
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) =
      prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
/--
Definition of `prodComparisonNatIso` / `prodComparisonNatIso` 的定义

English:
definition prodComparisonNatIso
  signature: [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
  body: by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

中文:
定义 prodComparisonNatIso
  签名: [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
  定义体: by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app, prodComparisonNatTrans
-/
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
    [forall B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) := by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `prodComparison_comp` / 定理 `prodComparison_comp`

English:
theorem prodComparison_comp
  proof: by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

中文:
定理 prodComparison_comp
  证明: by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

Depends on / 依赖: G.map_comp, map_comp, prodComparison
-/
theorem prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

end ProdComparison

noncomputable section CoprodComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]
variable (F : C ⥤ D) {A A' B B' : C}
variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']
variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

/--
Definition of `coprodComparison` / `coprodComparison` 的定义

English:
definition coprodComparison
  signature: (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
  body: coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[reassoc (attr := simp)]

中文:
定义 coprodComparison
  签名: (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
  定义体: coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, coprod, coprod.desc, coprod.inl, coprod.inr
-/
def coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
    [HasBinaryCoproduct (F.obj A) (F.obj B)] : F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[reassoc (attr := simp)]
/--
theorem `coprodComparison_inl` / 定理 `coprodComparison_inl`

English:
theorem coprodComparison_inl
  statement: coprod.inl ≫ coprodComparison F A B = F.map coprod.inl
  proof: coprod.inl_desc _ _

@[reassoc (attr := simp)]

中文:
定理 coprodComparison_inl
  结论: coprod.inl ≫ coprodComparison F A B = F.map coprod.inl
  证明: coprod.inl_desc _ _

@[reassoc (attr := simp)]

Depends on / 依赖: coprod, coprod.inl_desc, inl_desc, mul_braiding, one_braiding
-/
theorem coprodComparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _

@[reassoc (attr := simp)]
/--
theorem `coprodComparison_inr` / 定理 `coprodComparison_inr`

English:
theorem coprodComparison_inr
  statement: coprod.inr ≫ coprodComparison F A B = F.map coprod.inr
  proof: coprod.inr_desc _ _

中文:
定理 coprodComparison_inr
  结论: coprod.inr ≫ coprodComparison F A B = F.map coprod.inr
  证明: coprod.inr_desc _ _

Depends on / 依赖: coprod, coprod.inr_desc, inr_desc
-/
theorem coprodComparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _

/-- Naturality of the `coprodComparison` morphism in both arguments. -/
@[reassoc]
/--
theorem `coprodComparison_natural` / 定理 `coprodComparison_natural`

English:
theorem coprodComparison_natural
  given: (f : A ⟶ A') (g : B ⟶ B')
  proof: by
  rw [coprodComparison]; rw [coprodComparison]; rw [coprod.map_desc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [coprod.desc_comp]; rw [← F.map_comp]; rw [coprod.inl_map]; rw [← F.map_comp]; rw [coprod.inr_map]

中文:
定理 coprodComparison_natural
  条件: (f : A ⟶ A') (g : B ⟶ B')
  证明: by
  rw [coprodComparison]; rw [coprodComparison]; rw [coprod.map_desc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [coprod.desc_comp]; rw [← F.map_comp]; rw [coprod.inl_map]; rw [← F.map_comp]; rw [coprod.inr_map]

Depends on / 依赖: F.map_comp, coprod, coprod.desc_comp, coprod.inl_map, coprod.inr_map, coprod.map_desc, coprodComparison, desc_comp, inl_map, inr_map, map_comp, map_desc
-/
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (coprod.map f g) =
      coprod.map (F.map f) (F.map g) ≫ coprodComparison F A' B' := by
  rw [coprodComparison]; rw [coprodComparison]; rw [coprod.map_desc]; rw [← F.map_comp]; rw [← F.map_comp]; rw [coprod.desc_comp]; rw [← F.map_comp]; rw [coprod.inl_map]; rw [← F.map_comp]; rw [coprod.inr_map]

set_option backward.defeqAttrib.useBackward true in
/-- The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components are given by
`coprodComparison`.
-/
@[simps]
/--
Definition of `coprodComparisonNatTrans` / `coprodComparisonNatTrans` 的定义

English:
definition coprodComparisonNatTrans
  signature: [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C)
  body: coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]

@[reassoc]

中文:
定义 coprodComparisonNatTrans
  签名: [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C)
  定义体: coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]

@[reassoc]

Depends on / 依赖: coprodComparison
-/
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C) :
    F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F where
  app B := coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]

@[reassoc]
/--
theorem `map_inl_inv_coprodComparison` / 定理 `map_inl_inv_coprodComparison`

English:
theorem map_inl_inv_coprodComparison
  given: [IsIso (coprodComparison F A B)]
  proof: by simp

@[reassoc]

中文:
定理 map_inl_inv_coprodComparison
  条件: [IsIso (coprodComparison F A B)]
  证明: by simp

@[reassoc]
-/
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ≫ inv (coprodComparison F A B) = coprod.inl := by simp

@[reassoc]
/--
theorem `map_inr_inv_coprodComparison` / 定理 `map_inr_inv_coprodComparison`

English:
theorem map_inr_inv_coprodComparison
  given: [IsIso (coprodComparison F A B)]
  proof: by simp

中文:
定理 map_inr_inv_coprodComparison
  条件: [IsIso (coprodComparison F A B)]
  证明: by simp
-/
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ≫ inv (coprodComparison F A B) = coprod.inr := by simp

/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
/--
theorem `coprodComparison_inv_natural` / 定理 `coprodComparison_inv_natural`

English:
theorem coprodComparison_inv_natural
  statement: (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
  proof: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [coprodComparison_natural]

中文:
定理 coprodComparison_inv_natural
  结论: (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
  证明: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [coprodComparison_natural]

Depends on / 依赖: Category, Category.assoc, IsIso.eq_comp_inv, IsIso.inv_comp_eq, coprodComparison_natural, eq_comp_inv, inv_comp_eq
-/
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [coprodComparison_natural]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
/--
Definition of `coprodComparisonNatIso` / `coprodComparisonNatIso` 的定义

English:
definition coprodComparisonNatIso
  signature: [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
  body: { @asIso _ _ _ _ _ (NatIso.isIso_of_isIso_app ..) with hom := coprodComparisonNatTrans F A }

中文:
定义 coprodComparisonNatIso
  签名: [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
  定义体: { @asIso _ _ _ _ _ (NatIso.isIso_of_isIso_app ..) with hom := coprodComparisonNatTrans F A }

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, coprodComparisonNatTrans, isIso_of_isIso_app
-/
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [forall B, IsIso (coprodComparison F A B)] :
    F ⋙ coprod.functor.obj (F.obj A) ≅ coprod.functor.obj A ⋙ F :=
  { @asIso _ _ _ _ _ (NatIso.isIso_of_isIso_app ..) with hom := coprodComparisonNatTrans F A }

end CoprodComparison

end CategoryTheory.Limits

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `Over.coprod`. -/
@[simps]
/--
Definition of `Over.coprodObj` / `Over.coprodObj` 的定义

English:
definition Over.coprodObj
  signature: [HasBinaryCoproducts C] {A : C}
  body: fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }

中文:
定义 Over.coprodObj
  签名: [HasBinaryCoproducts C] {A : C}
  定义体: fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }

Depends on / 依赖: Over.homMk, Over.mk, coprod, coprod.desc, coprod.map, f.hom, g.hom, k.left
-/
noncomputable def Over.coprodObj [HasBinaryCoproducts C] {A : C} :
    Over A -> Over A ⥤ Over A :=
  fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A category with binary coproducts has a functorial `sup` operation on over categories. -/
@[simps]
/--
Definition of `Over.coprod` / `Over.coprod` 的定义

English:
definition Over.coprod
  signature: [HasBinaryCoproducts C] {A : C}
  body: Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, Category.id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        simp }
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

中文:
定义 Over.coprod
  签名: [HasBinaryCoproducts C] {A : C}
  定义体: Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, Category.id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        simp }
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

Depends on / 依赖: Over.coprodObj, coprodObj
-/
noncomputable def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ⥤ Over A ⥤ Over A where
  obj f := Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, Category.id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        simp }
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

end CategoryTheory

namespace CategoryTheory.Limits
open Opposite

variable {C : Type u} [Category.{v} C] {X Y Z P : C}

section opposite

/--
Definition of `BinaryFan.op` / `BinaryFan.op` 的定义

English:
abbreviation BinaryFan.op
  signature: (c : BinaryFan X Y)
  body: .mk c.fst.op c.snd.op

中文:
缩写 BinaryFan.op
  签名: (c : BinaryFan X Y)
  定义体: .mk c.fst.op c.snd.op
-/
protected abbrev BinaryFan.op (c : BinaryFan X Y) : BinaryCofan (op X) (op Y) :=
  .mk c.fst.op c.snd.op

/--
Definition of `BinaryCofan.op` / `BinaryCofan.op` 的定义

English:
abbreviation BinaryCofan.op
  signature: (c : BinaryCofan X Y)
  body: .mk c.inl.op c.inr.op

中文:
缩写 BinaryCofan.op
  签名: (c : BinaryCofan X Y)
  定义体: .mk c.inl.op c.inr.op
-/
protected abbrev BinaryCofan.op (c : BinaryCofan X Y) : BinaryFan (op X) (op Y) :=
  .mk c.inl.op c.inr.op

/--
Definition of `BinaryFan.unop` / `BinaryFan.unop` 的定义

English:
abbreviation BinaryFan.unop
  signature: (c : BinaryFan (op X) (op Y))
  body: .mk c.fst.unop c.snd.unop

中文:
缩写 BinaryFan.unop
  签名: (c : BinaryFan (op X) (op Y))
  定义体: .mk c.fst.unop c.snd.unop
-/
protected abbrev BinaryFan.unop (c : BinaryFan (op X) (op Y)) : BinaryCofan X Y :=
  .mk c.fst.unop c.snd.unop

/--
Definition of `BinaryCofan.unop` / `BinaryCofan.unop` 的定义

English:
abbreviation BinaryCofan.unop
  signature: (c : BinaryCofan (op X) (op Y))
  body: .mk c.inl.unop c.inr.unop

中文:
缩写 BinaryCofan.unop
  签名: (c : BinaryCofan (op X) (op Y))
  定义体: .mk c.inl.unop c.inr.unop
-/
protected abbrev BinaryCofan.unop (c : BinaryCofan (op X) (op Y)) : BinaryFan X Y :=
  .mk c.inl.unop c.inr.unop

/--
lemma `BinaryFan.op_mk` / 引理 `BinaryFan.op_mk`

English:
lemma BinaryFan.op_mk
  given: (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  proof: rfl

中文:
引理 BinaryFan.op_mk
  条件: (π₁ : P ⟶ X) (π₂ : P ⟶ Y)
  证明: rfl
-/
@[simp] lemma BinaryFan.op_mk (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
    BinaryFan.op (mk π₁ π₂) = .mk π₁.op π₂.op := rfl

/--
lemma `BinaryFan.unop_mk` / 引理 `BinaryFan.unop_mk`

English:
lemma BinaryFan.unop_mk
  given: (π₁ : op P ⟶ op X) (π₂ : op P ⟶ op Y)
  proof: rfl

中文:
引理 BinaryFan.unop_mk
  条件: (π₁ : op P ⟶ op X) (π₂ : op P ⟶ op Y)
  证明: rfl
-/
@[simp] lemma BinaryFan.unop_mk (π₁ : op P ⟶ op X) (π₂ : op P ⟶ op Y) :
    BinaryFan.unop (mk π₁ π₂) = .mk π₁.unop π₂.unop := rfl

/--
lemma `BinaryCofan.op_mk` / 引理 `BinaryCofan.op_mk`

English:
lemma BinaryCofan.op_mk
  given: (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  proof: rfl

中文:
引理 BinaryCofan.op_mk
  条件: (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P)
  证明: rfl
-/
@[simp] lemma BinaryCofan.op_mk (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
    BinaryCofan.op (mk ι₁ ι₂) = .mk ι₁.op ι₂.op := rfl

/--
lemma `BinaryCofan.unop_mk` / 引理 `BinaryCofan.unop_mk`

English:
lemma BinaryCofan.unop_mk
  given: (ι₁ : op X ⟶ op P) (ι₂ : op Y ⟶ op P)
  proof: rfl

中文:
引理 BinaryCofan.unop_mk
  条件: (ι₁ : op X ⟶ op P) (ι₂ : op Y ⟶ op P)
  证明: rfl
-/
@[simp] lemma BinaryCofan.unop_mk (ι₁ : op X ⟶ op P) (ι₂ : op Y ⟶ op P) :
    BinaryCofan.unop (mk ι₁ ι₂) = .mk ι₁.unop ι₂.unop := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryFan.IsLimit.op` / `BinaryFan.IsLimit.op` 的定义

English:
definition BinaryFan.IsLimit.op
  signature: {c : BinaryFan X Y} (hc : IsLimit c)
  body: BinaryCofan.isColimitMk (fun s => (hc.lift s.unop).op)
    (fun _ => Quiver.Hom.unop_inj (by simp)) (fun _ => Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.unop_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

中文:
定义 BinaryFan.IsLimit.op
  签名: {c : BinaryFan X Y} (hc : IsLimit c)
  定义体: BinaryCofan.isColimitMk (fun s => (hc.lift s.unop).op)
    (fun _ => Quiver.Hom.unop_inj (by simp)) (fun _ => Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.unop_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))
-/
protected def BinaryFan.IsLimit.op {c : BinaryFan X Y} (hc : IsLimit c) : IsColimit c.op :=
  BinaryCofan.isColimitMk (fun s => (hc.lift s.unop).op)
    (fun _ => Quiver.Hom.unop_inj (by simp)) (fun _ => Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.unop_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryCofan.IsColimit.op` / `BinaryCofan.IsColimit.op` 的定义

English:
definition BinaryCofan.IsColimit.op
  signature: {c : BinaryCofan X Y} (hc : IsColimit c)
  body: BinaryFan.isLimitMk (fun s => (hc.desc s.unop).op)
    (fun _ => Quiver.Hom.unop_inj (by simp)) (fun _ => Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.unop_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

中文:
定义 BinaryCofan.IsColimit.op
  签名: {c : BinaryCofan X Y} (hc : IsColimit c)
  定义体: BinaryFan.isLimitMk (fun s => (hc.desc s.unop).op)
    (fun _ => Quiver.Hom.unop_inj (by simp)) (fun _ => Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.unop_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))
-/
protected def BinaryCofan.IsColimit.op {c : BinaryCofan X Y} (hc : IsColimit c) : IsLimit c.op :=
  BinaryFan.isLimitMk (fun s => (hc.desc s.unop).op)
    (fun _ => Quiver.Hom.unop_inj (by simp)) (fun _ => Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.unop_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryFan.IsLimit.unop` / `BinaryFan.IsLimit.unop` 的定义

English:
definition BinaryFan.IsLimit.unop
  signature: {c : BinaryFan (op X) (op Y)} (hc : IsLimit c)
  body: BinaryCofan.isColimitMk (fun s => (hc.lift s.op).unop)
    (fun _ => Quiver.Hom.op_inj (by simp)) (fun _ => Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.op_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

中文:
定义 BinaryFan.IsLimit.unop
  签名: {c : BinaryFan (op X) (op Y)} (hc : IsLimit c)
  定义体: BinaryCofan.isColimitMk (fun s => (hc.lift s.op).unop)
    (fun _ => Quiver.Hom.op_inj (by simp)) (fun _ => Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.op_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))
-/
protected def BinaryFan.IsLimit.unop {c : BinaryFan (op X) (op Y)} (hc : IsLimit c) :
    IsColimit c.unop :=
  BinaryCofan.isColimitMk (fun s => (hc.lift s.op).unop)
    (fun _ => Quiver.Hom.op_inj (by simp)) (fun _ => Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.op_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryCofan.IsColimit.unop` / `BinaryCofan.IsColimit.unop` 的定义

English:
definition BinaryCofan.IsColimit.unop
  signature: {c : BinaryCofan (op X) (op Y)} (hc : IsColimit c)
  body: BinaryFan.isLimitMk (fun s => (hc.desc s.op).unop)
    (fun _ => Quiver.Hom.op_inj (by simp)) (fun _ => Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.op_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

中文:
定义 BinaryCofan.IsColimit.unop
  签名: {c : BinaryCofan (op X) (op Y)} (hc : IsColimit c)
  定义体: BinaryFan.isLimitMk (fun s => (hc.desc s.op).unop)
    (fun _ => Quiver.Hom.op_inj (by simp)) (fun _ => Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.op_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))
-/
protected def BinaryCofan.IsColimit.unop {c : BinaryCofan (op X) (op Y)} (hc : IsColimit c) :
    IsLimit c.unop :=
  BinaryFan.isLimitMk (fun s => (hc.desc s.op).unop)
    (fun _ => Quiver.Hom.op_inj (by simp)) (fun _ => Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ => Quiver.Hom.op_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

end opposite

section swap
variable {s : BinaryFan X Y} {t : BinaryFan Y X}

/--
Definition of `BinaryFan.swap` / `BinaryFan.swap` 的定义

English:
definition BinaryFan.swap
  signature: (s : BinaryFan X Y)
  body: .mk s.snd s.fst

中文:
定义 BinaryFan.swap
  签名: (s : BinaryFan X Y)
  定义体: .mk s.snd s.fst

Depends on / 依赖: s.fst, s.snd
-/
def BinaryFan.swap (s : BinaryFan X Y) : BinaryFan Y X := .mk s.snd s.fst

/--
lemma `BinaryFan.swap_fst` / 引理 `BinaryFan.swap_fst`

English:
lemma BinaryFan.swap_fst
  given: (s : BinaryFan X Y)
  statement: s.swap.fst = s.snd
  proof: rfl

中文:
引理 BinaryFan.swap_fst
  条件: (s : BinaryFan X Y)
  结论: s.swap.fst = s.snd
  证明: rfl
-/
@[simp] lemma BinaryFan.swap_fst (s : BinaryFan X Y) : s.swap.fst = s.snd := rfl
/--
lemma `BinaryFan.swap_snd` / 引理 `BinaryFan.swap_snd`

English:
lemma BinaryFan.swap_snd
  given: (s : BinaryFan X Y)
  statement: s.swap.snd = s.fst
  proof: rfl

中文:
引理 BinaryFan.swap_snd
  条件: (s : BinaryFan X Y)
  结论: s.swap.snd = s.fst
  证明: rfl
-/
@[simp] lemma BinaryFan.swap_snd (s : BinaryFan X Y) : s.swap.snd = s.fst := rfl

set_option backward.isDefEq.respectTransparency false in
/-- If a binary fan `s` over `X Y` is a limit cone, then `s.swap` is a limit cone over `Y X`. -/
@[simps]
/--
Definition of `IsLimit.binaryFanSwap` / `IsLimit.binaryFanSwap` 的定义

English:
definition IsLimit.binaryFanSwap
  signature: (I : IsLimit s)
  body: I.lift (BinaryFan.swap t)
  fac t := by rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := I.uniq (BinaryFan.swap t) m
    rw [h]
    rintro ⟨j⟩
    specialize w ⟨WalkingPair.swap j⟩
    cases j <;> exact w

中文:
定义 IsLimit.binaryFanSwap
  签名: (I : IsLimit s)
  定义体: I.lift (BinaryFan.swap t)
  fac t := by rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := I.uniq (BinaryFan.swap t) m
    rw [h]
    rintro ⟨j⟩
    specialize w ⟨WalkingPair.swap j⟩
    cases j <;> exact w

Depends on / 依赖: BinaryFan, BinaryFan.swap, I.lift
-/
def IsLimit.binaryFanSwap (I : IsLimit s) : IsLimit s.swap where
  lift t := I.lift (BinaryFan.swap t)
  fac t := by rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := I.uniq (BinaryFan.swap t) m
    rw [h]
    rintro ⟨j⟩
    specialize w ⟨WalkingPair.swap j⟩
    cases j <;> exact w

/--
lemma `HasBinaryProduct.swap` / 引理 `HasBinaryProduct.swap`

English:
lemma HasBinaryProduct.swap
  given: (X Y : C) [HasBinaryProduct X Y]
  statement: HasBinaryProduct Y X
  proof: .mk ⟨BinaryFan.swap (limit.cone (pair X Y)), (limit.isLimit (pair X Y)).binaryFanSwap⟩

中文:
引理 HasBinaryProduct.swap
  条件: (X Y : C) [HasBinaryProduct X Y]
  结论: HasBinaryProduct Y X
  证明: .mk ⟨BinaryFan.swap (limit.cone (pair X Y)), (limit.isLimit (pair X Y)).binaryFanSwap⟩

Depends on / 依赖: BinaryFan, BinaryFan.swap, binaryFanSwap, isLimit, limit.cone, limit.isLimit
-/
lemma HasBinaryProduct.swap (X Y : C) [HasBinaryProduct X Y] : HasBinaryProduct Y X :=
  .mk ⟨BinaryFan.swap (limit.cone (pair X Y)), (limit.isLimit (pair X Y)).binaryFanSwap⟩

end swap

section braiding
variable {X Y : C} {s : BinaryFan X Y} (P : IsLimit s) {t : BinaryFan Y X} (Q : IsLimit t)

/--
Definition of `BinaryFan.braiding` / `BinaryFan.braiding` 的定义

English:
definition BinaryFan.braiding
  signature: (P : IsLimit s) (Q : IsLimit t)
  body: P.conePointUniqueUpToIso Q.binaryFanSwap

@[reassoc (attr := simp)]

中文:
定义 BinaryFan.braiding
  签名: (P : IsLimit s) (Q : IsLimit t)
  定义体: P.conePointUniqueUpToIso Q.binaryFanSwap

@[reassoc (attr := simp)]

Depends on / 依赖: P.conePointUniqueUpToIso, Q.binaryFanSwap, binaryFanSwap, conePointUniqueUpToIso
-/
def BinaryFan.braiding (P : IsLimit s) (Q : IsLimit t) : s.pt ≅ t.pt :=
  P.conePointUniqueUpToIso Q.binaryFanSwap

@[reassoc (attr := simp)]
/--
lemma `BinaryFan.braiding_hom_fst` / 引理 `BinaryFan.braiding_hom_fst`

English:
lemma BinaryFan.braiding_hom_fst
  statement: (braiding P Q).hom ≫ t.fst = s.snd
  proof: P.conePointUniqueUpToIso_hom_comp _ ⟨.right⟩

@[reassoc (attr := simp)]

中文:
引理 BinaryFan.braiding_hom_fst
  结论: (braiding P Q).hom ≫ t.fst = s.snd
  证明: P.conePointUniqueUpToIso_hom_comp _ ⟨.right⟩

@[reassoc (attr := simp)]

Depends on / 依赖: P.conePointUniqueUpToIso_hom_comp, conePointUniqueUpToIso_hom_comp
-/
lemma BinaryFan.braiding_hom_fst : (braiding P Q).hom ≫ t.fst = s.snd :=
  P.conePointUniqueUpToIso_hom_comp _ ⟨.right⟩

@[reassoc (attr := simp)]
/--
lemma `BinaryFan.braiding_hom_snd` / 引理 `BinaryFan.braiding_hom_snd`

English:
lemma BinaryFan.braiding_hom_snd
  statement: (braiding P Q).hom ≫ t.snd = s.fst
  proof: P.conePointUniqueUpToIso_hom_comp _ ⟨.left⟩

@[reassoc (attr := simp)]

中文:
引理 BinaryFan.braiding_hom_snd
  结论: (braiding P Q).hom ≫ t.snd = s.fst
  证明: P.conePointUniqueUpToIso_hom_comp _ ⟨.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: P.conePointUniqueUpToIso_hom_comp, conePointUniqueUpToIso_hom_comp
-/
lemma BinaryFan.braiding_hom_snd : (braiding P Q).hom ≫ t.snd = s.fst :=
  P.conePointUniqueUpToIso_hom_comp _ ⟨.left⟩

@[reassoc (attr := simp)]
/--
lemma `BinaryFan.braiding_inv_fst` / 引理 `BinaryFan.braiding_inv_fst`

English:
lemma BinaryFan.braiding_inv_fst
  statement: (braiding P Q).inv ≫ s.fst = t.snd
  proof: P.conePointUniqueUpToIso_inv_comp _ ⟨.left⟩

@[reassoc (attr := simp)]

中文:
引理 BinaryFan.braiding_inv_fst
  结论: (braiding P Q).inv ≫ s.fst = t.snd
  证明: P.conePointUniqueUpToIso_inv_comp _ ⟨.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: P.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
lemma BinaryFan.braiding_inv_fst : (braiding P Q).inv ≫ s.fst = t.snd :=
  P.conePointUniqueUpToIso_inv_comp _ ⟨.left⟩

@[reassoc (attr := simp)]
/--
lemma `BinaryFan.braiding_inv_snd` / 引理 `BinaryFan.braiding_inv_snd`

English:
lemma BinaryFan.braiding_inv_snd
  statement: (braiding P Q).inv ≫ s.snd = t.fst
  proof: P.conePointUniqueUpToIso_inv_comp _ ⟨.right⟩

中文:
引理 BinaryFan.braiding_inv_snd
  结论: (braiding P Q).inv ≫ s.snd = t.fst
  证明: P.conePointUniqueUpToIso_inv_comp _ ⟨.right⟩

Depends on / 依赖: P.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
lemma BinaryFan.braiding_inv_snd : (braiding P Q).inv ≫ s.snd = t.fst :=
  P.conePointUniqueUpToIso_inv_comp _ ⟨.right⟩

end braiding

section assoc
variable {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z}

/--
Definition of `BinaryFan.assoc` / `BinaryFan.assoc` 的定义

English:
definition BinaryFan.assoc
  signature: (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z)
  body: mk (s.fst ≫ sXY.fst) (Q.lift (mk (s.fst ≫ sXY.snd) s.snd))

@[simp]

中文:
定义 BinaryFan.assoc
  签名: (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z)
  定义体: mk (s.fst ≫ sXY.fst) (Q.lift (mk (s.fst ≫ sXY.snd) s.snd))

@[simp]

Depends on / 依赖: Q.lift, s.fst, s.snd, sXY.fst, sXY.snd
-/
def BinaryFan.assoc (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) : BinaryFan X sYZ.pt :=
  mk (s.fst ≫ sXY.fst) (Q.lift (mk (s.fst ≫ sXY.snd) s.snd))

@[simp]
/--
lemma `BinaryFan.assoc_fst` / 引理 `BinaryFan.assoc_fst`

English:
lemma BinaryFan.assoc_fst
  given: (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z)
  proof: rfl

@[simp]

中文:
引理 BinaryFan.assoc_fst
  条件: (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z)
  证明: rfl

@[simp]
-/
lemma BinaryFan.assoc_fst (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (assoc Q s).fst = s.fst ≫ sXY.fst := rfl

@[simp]
/--
lemma `BinaryFan.assoc_snd` / 引理 `BinaryFan.assoc_snd`

English:
lemma BinaryFan.assoc_snd
  given: (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z)
  proof: rfl

中文:
引理 BinaryFan.assoc_snd
  条件: (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z)
  证明: rfl
-/
lemma BinaryFan.assoc_snd (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (assoc Q s).snd = Q.lift (mk (s.fst ≫ sXY.snd) s.snd) := rfl

/--
Definition of `BinaryFan.assocInv` / `BinaryFan.assocInv` 的定义

English:
definition BinaryFan.assocInv
  signature: (P : IsLimit sXY) (s : BinaryFan X sYZ.pt)
  body: BinaryFan.mk (IsLimit.lift P s.fst (s.snd ≫ sYZ.fst)) (s.snd ≫ sYZ.snd)

@[simp]

中文:
定义 BinaryFan.assocInv
  签名: (P : IsLimit sXY) (s : BinaryFan X sYZ.pt)
  定义体: BinaryFan.mk (IsLimit.lift P s.fst (s.snd ≫ sYZ.fst)) (s.snd ≫ sYZ.snd)

@[simp]

Depends on / 依赖: BinaryFan, BinaryFan.mk, IsLimit, IsLimit.lift, s.fst, s.snd, sYZ.fst, sYZ.snd
-/
def BinaryFan.assocInv (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) : BinaryFan sXY.pt Z :=
  BinaryFan.mk (IsLimit.lift P s.fst (s.snd ≫ sYZ.fst)) (s.snd ≫ sYZ.snd)

@[simp]
/--
lemma `BinaryFan.assocInv_fst` / 引理 `BinaryFan.assocInv_fst`

English:
lemma BinaryFan.assocInv_fst
  given: (P : IsLimit sXY) (s : BinaryFan X sYZ.pt)
  proof: rfl

@[simp]

中文:
引理 BinaryFan.assocInv_fst
  条件: (P : IsLimit sXY) (s : BinaryFan X sYZ.pt)
  证明: rfl

@[simp]
-/
lemma BinaryFan.assocInv_fst (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).fst = IsLimit.lift P s.fst (s.snd ≫ sYZ.fst) := rfl

@[simp]
/--
lemma `BinaryFan.assocInv_snd` / 引理 `BinaryFan.assocInv_snd`

English:
lemma BinaryFan.assocInv_snd
  given: (P : IsLimit sXY) (s : BinaryFan X sYZ.pt)
  proof: rfl

中文:
引理 BinaryFan.assocInv_snd
  条件: (P : IsLimit sXY) (s : BinaryFan X sYZ.pt)
  证明: rfl
-/
lemma BinaryFan.assocInv_snd (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).snd = s.snd ≫ sYZ.snd := rfl

set_option backward.isDefEq.respectTransparency false in
/-- If all the binary fans involved a limit cones, `BinaryFan.assoc` produces another limit cone. -/
@[simps]
/--
Definition of `IsLimit.assoc` / `IsLimit.assoc` 的定义

English:
definition IsLimit.assoc
  signature: (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
  body: R.lift (BinaryFan.assocInv P t)
  fac t := by
    rintro ⟨⟨⟩⟩
    · simp
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (BinaryFan.assocInv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
      · simpa using w ⟨.left⟩
      · replace w 

中文:
定义 IsLimit.assoc
  签名: (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
  定义体: R.lift (BinaryFan.assocInv P t)
  fac t := by
    rintro ⟨⟨⟩⟩
    · simp
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (BinaryFan.assocInv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
      · simpa using w ⟨.left⟩
      · replace w 
-/
protected def IsLimit.assoc (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
    (R : IsLimit s) : IsLimit (BinaryFan.assoc Q s) where
  lift t := R.lift (BinaryFan.assocInv P t)
  fac t := by
    rintro ⟨⟨⟩⟩
    · simp
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (BinaryFan.assocInv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
      · simpa using w ⟨.left⟩
      · replace w : m ≫ BinaryFan.IsLimit.lift Q (s.fst ≫ sXY.snd) s.snd = t.π.app ⟨.right⟩ := by
          simpa using! w ⟨.right⟩
        simp [← w]
    · replace w : m ≫ BinaryFan.IsLimit.lift Q (s.fst ≫ sXY.snd) s.snd = t.π.app ⟨.right⟩ := by
        simpa using! w ⟨.right⟩
      simp [← w]

/--
Definition of `BinaryFan.associator` / `BinaryFan.associator` 的定义

English:
abbreviation BinaryFan.associator
  signature: (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
  body: (P.assoc Q R).conePointUniqueUpToIso S

中文:
缩写 BinaryFan.associator
  签名: (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
  定义体: (P.assoc Q R).conePointUniqueUpToIso S

Depends on / 依赖: P.assoc, conePointUniqueUpToIso
-/
abbrev BinaryFan.associator (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
    (R : IsLimit s) {t : BinaryFan X sYZ.pt} (S : IsLimit t) : s.pt ≅ t.pt :=
  (P.assoc Q R).conePointUniqueUpToIso S

/--
Definition of `BinaryFan.associatorOfLimitCone` / `BinaryFan.associatorOfLimitCone` 的定义

English:
abbreviation BinaryFan.associatorOfLimitCone
  signature: (L : forall X Y : C, LimitCone (pair X Y)) (X Y Z : C)
  body: associator (L X Y).isLimit (L Y Z).isLimit (L (L X Y).cone.pt Z).isLimit
    (L X (L Y Z).cone.pt).isLimit

中文:
缩写 BinaryFan.associatorOfLimitCone
  签名: (L : 对任意 X Y : C, LimitCone (pair X Y)) (X Y Z : C)
  定义体: associator (L X Y).isLimit (L Y Z).isLimit (L (L X Y).cone.pt Z).isLimit
    (L X (L Y Z).cone.pt).isLimit

Depends on / 依赖: associator, cone.pt, isLimit
-/
abbrev BinaryFan.associatorOfLimitCone (L : forall X Y : C, LimitCone (pair X Y)) (X Y Z : C) :
    (L (L X Y).cone.pt Z).cone.pt ≅ (L X (L Y Z).cone.pt).cone.pt :=
  associator (L X Y).isLimit (L Y Z).isLimit (L (L X Y).cone.pt Z).isLimit
    (L X (L Y Z).cone.pt).isLimit

end assoc

section unitor

set_option backward.isDefEq.respectTransparency false in
/-- Construct a left unitor from specified limit cones. -/
@[simps]
/--
Definition of `BinaryFan.leftUnitor` / `BinaryFan.leftUnitor` 的定义

English:
definition BinaryFan.leftUnitor
  signature: {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
  body: t.snd
inv := Q.lift BinaryFan.mk (P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩) (𝟙 _)
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
    · simp

中文:
定义 BinaryFan.leftUnitor
  签名: {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
  定义体: t.snd
inv := Q.lift BinaryFan.mk (P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩) (𝟙 _)
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
    · simp

Depends on / 依赖: t.snd
-/
def BinaryFan.leftUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan s.pt X} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.snd
inv := Q.lift BinaryFan.mk (P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩) (𝟙 _)
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
    · simp

set_option backward.isDefEq.respectTransparency false in
/-- Construct a right unitor from specified limit cones. -/
@[simps]
/--
Definition of `BinaryFan.rightUnitor` / `BinaryFan.rightUnitor` 的定义

English:
definition BinaryFan.rightUnitor
  signature: {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
  body: t.fst
inv := Q.lift BinaryFan.mk (𝟙 _) P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩

中文:
定义 BinaryFan.rightUnitor
  签名: {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
  定义体: t.fst
inv := Q.lift BinaryFan.mk (𝟙 _) P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩

Depends on / 依赖: t.fst
-/
def BinaryFan.rightUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan X s.pt} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.fst
inv := Q.lift BinaryFan.mk (𝟙 _) P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩

end unitor
end CategoryTheory.Limits
set_option linter.style.longFile 1700
