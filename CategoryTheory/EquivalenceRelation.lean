/-
Copyright (c) 2026 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Equivalence relations

We define internal equivalence relations (sometimes called congruences) in any category `C`, as a
structure on pairs of parallel morphisms `p₁, p₂ : R ⟶ X` .
We also define effective and universally effective equivalence relations.

We prove that equivalence relations on types provide internal equivalence relation structures in the
category of types.
In general, kernel pairs in any category are internal equivalence relations.

## References

* <https://ncatlab.org/nlab/show/congruence>

-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
variable {R X : C} {p₁ p₂ : R ⟶ X}

/--
Definition of `JointlyMono₂` / `JointlyMono₂` 的定义

English:
class JointlyMono₂
  parameters: {R X₁ X₂ : C} (p₁ : R ⟶ X₁) (p₂ : R ⟶ X₂)
  axioms and operations (1):
    - right_cancellation : forall ⦃Y : C⦄ (f g : Y ⟶ R), f ≫ p₁ = g ≫ p₁ -> f ≫ p₂ = g ≫ p₂ -> f = g

中文:
类 JointlyMono₂
  参数: {R X₁ X₂ : C} (p₁ : R ⟶ X₁) (p₂ : R ⟶ X₂)
  公理与运算 (1 个):
    - right_cancellation : 对任意 ⦃Y : C⦄ (f g : Y ⟶ R), f ≫ p₁ = g ≫ p₁ -> f ≫ p₂ = g ≫ p₂ -> f = g
-/
class JointlyMono₂ {R X₁ X₂ : C} (p₁ : R ⟶ X₁) (p₂ : R ⟶ X₂) : Prop where
  right_cancellation : forall ⦃Y : C⦄ (f g : Y ⟶ R), f ≫ p₁ = g ≫ p₁ -> f ≫ p₂ = g ≫ p₂ -> f = g

/--
Definition of `ReflexiveRelation` / `ReflexiveRelation` 的定义

English:
structure ReflexiveRelation
  parameters: {R X : C} (p₁ p₂ : R ⟶ X)
  extends: JointlyMono₂ p₁ p₂
  axioms and operations (3):
    - r : X ⟶ R
    - reflexivity₁ : r ≫ p₁ = 𝟙 _  [default: by cat_disch]
    - reflexivity₂ : r ≫ p₂ = 𝟙 _  [default: by cat_disch]

中文:
结构 ReflexiveRelation
  参数: {R X : C} (p₁ p₂ : R ⟶ X)
  继承: JointlyMono₂ p₁ p₂
  公理与运算 (3 个):
    - r : X ⟶ R
    - reflexivity₁ : r ≫ p₁ = 𝟙 _  [默认: by cat_disch]
    - reflexivity₂ : r ≫ p₂ = 𝟙 _  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure ReflexiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `r` is the morphism witnessing reflexivity -/
  r : X ⟶ R
  reflexivity₁ : r ≫ p₁ = 𝟙 _ := by cat_disch
  reflexivity₂ : r ≫ p₂ = 𝟙 _ := by cat_disch

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  ReflexiveRelation.reflexivity₁ ReflexiveRelation.reflexivity₂

/--
Definition of `SymmetricRelation` / `SymmetricRelation` 的定义

English:
structure SymmetricRelation
  parameters: {R X : C} (p₁ p₂ : R ⟶ X)
  extends: JointlyMono₂ p₁ p₂
  axioms and operations (3):
    - s : R ⟶ R
    - symmetry₁ : s ≫ p₁ = p₂  [default: by cat_disch]
    - symmetry₂ : s ≫ p₂ = p₁  [default: by cat_disch]

中文:
结构 SymmetricRelation
  参数: {R X : C} (p₁ p₂ : R ⟶ X)
  继承: JointlyMono₂ p₁ p₂
  公理与运算 (3 个):
    - s : R ⟶ R
    - symmetry₁ : s ≫ p₁ = p₂  [默认: by cat_disch]
    - symmetry₂ : s ≫ p₂ = p₁  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure SymmetricRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `s` is the morphism witnessing symmetry -/
  s : R ⟶ R
  symmetry₁ : s ≫ p₁ = p₂ := by cat_disch
  symmetry₂ : s ≫ p₂ = p₁ := by cat_disch

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  SymmetricRelation.symmetry₁ SymmetricRelation.symmetry₂

/--
Definition of `TransitiveRelation` / `TransitiveRelation` 的定义

English:
structure TransitiveRelation
  parameters: {R X : C} (p₁ p₂ : R ⟶ X)
  extends: JointlyMono₂ p₁ p₂
  axioms and operations (5):
    - c : PullbackCone p₂ p₁
    - isLimit : IsLimit c
    - t : c.pt ⟶ R
    - transitivity₁ : t ≫ p₁ = c.fst ≫ p₁  [default: by cat_disch]
    - transitivity₂ : t ≫ p₂ = c.snd ≫ p₂  [default: by cat_disch]

中文:
结构 TransitiveRelation
  参数: {R X : C} (p₁ p₂ : R ⟶ X)
  继承: JointlyMono₂ p₁ p₂
  公理与运算 (5 个):
    - c : PullbackCone p₂ p₁
    - isLimit : 是极限 c
    - t : c.pt ⟶ R
    - transitivity₁ : t ≫ p₁ = c.fst ≫ p₁  [默认: by cat_disch]
    - transitivity₂ : t ≫ p₂ = c.snd ≫ p₂  [默认: by cat_disch]

Depends on / 依赖: c.snd, cat_disch
-/
structure TransitiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `c` is a pullback cone for `p₁` and `p₂` -/
  c : PullbackCone p₂ p₁
  /-- `c` is limiting -/
  isLimit : IsLimit c
  /-- `t` is the morphism witnessing transitivity -/
  t : c.pt ⟶ R
  transitivity₁ : t ≫ p₁ = c.fst ≫ p₁ := by cat_disch
  transitivity₂ : t ≫ p₂ = c.snd ≫ p₂ := by cat_disch

initialize_simps_projections TransitiveRelation (-isLimit)

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  TransitiveRelation.transitivity₁ TransitiveRelation.transitivity₂

/--
Definition of `EquivalenceRelation` / `EquivalenceRelation` 的定义

English:
structure EquivalenceRelation
  parameters: {R X : C} (p₁ p₂ : R ⟶ X)
  extends: ReflexiveRelation p₁ p₂, 
  (no additional axioms)

中文:
结构 EquivalenceRelation
  参数: {R X : C} (p₁ p₂ : R ⟶ X)
  继承: ReflexiveRelation p₁ p₂, 
  (无附加公理)
-/
structure EquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) extends ReflexiveRelation p₁ p₂,
  SymmetricRelation p₁ p₂, TransitiveRelation p₁ p₂

/-- Reinterpret an equivalence relation as a reflexive relation. -/
add_decl_doc EquivalenceRelation.toReflexiveRelation

/-- Reinterpret an equivalence relation as a symmetric relation. -/
add_decl_doc EquivalenceRelation.toSymmetricRelation

/-- Reinterpret an equivalence relation as a transitive relation. -/
add_decl_doc EquivalenceRelation.toTransitiveRelation

/--
Definition of `IsEquivalenceRelation` / `IsEquivalenceRelation` 的定义

English:
class IsEquivalenceRelation
  parameters: {R X : C} (p₁ p₂ : R ⟶ X)
  axioms and operations (1):
    - nonempty_equivalenceRelation : Nonempty (EquivalenceRelation p₁ p₂)

中文:
类 是EquivalenceRelation
  参数: {R X : C} (p₁ p₂ : R ⟶ X)
  公理与运算 (1 个):
    - nonempty_equivalenceRelation : 非空 (EquivalenceRelation p₁ p₂)
-/
class IsEquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) : Prop where
  nonempty_equivalenceRelation : Nonempty (EquivalenceRelation p₁ p₂)

/--
lemma `EquivalenceRelation.isEquivalenceRelation` / 引理 `EquivalenceRelation.isEquivalenceRelation`

English:
lemma EquivalenceRelation.isEquivalenceRelation
  given: (h : EquivalenceRelation p₁ p₂)
  proof: ⟨h⟩

中文:
引理 EquivalenceRelation.isEquivalenceRelation
  条件: (h : EquivalenceRelation p₁ p₂)
  证明: ⟨h⟩
-/
lemma EquivalenceRelation.isEquivalenceRelation (h : EquivalenceRelation p₁ p₂) :
    IsEquivalenceRelation p₁ p₂ where
  nonempty_equivalenceRelation := ⟨h⟩

/--
Definition of `IsKernelPair.equivalenceRelation` / `IsKernelPair.equivalenceRelation` 的定义

English:
definition IsKernelPair.equivalenceRelation
  signature: {X Y : C} (f : X ⟶ Y) {R : C} (p₁ p₂ : R ⟶ X)
  body: h.hom_ext h₁ h₂
  r := h.lift (𝟙 _) (𝟙 _) (by simp)
  s := h.lift p₂ p₁ h.w.symm
  c := t
  isLimit := ht
  t := h.lift (t.fst ≫ p₁) (t.snd ≫ p₂) (by simp [reassoc_of% t.condition, h.w])

中文:
定义 IsKernelPair.equivalenceRelation
  签名: {X Y : C} (f : X ⟶ Y) {R : C} (p₁ p₂ : R ⟶ X)
  定义体: h.hom_ext h₁ h₂
  r := h.lift (𝟙 _) (𝟙 _) (by simp)
  s := h.lift p₂ p₁ h.w.symm
  c := t
  isLimit := ht
  t := h.lift (t.fst ≫ p₁) (t.snd ≫ p₂) (by simp [reassoc_of% t.condition, h.w])

Depends on / 依赖: h.hom_ext, hom_ext
-/
noncomputable def IsKernelPair.equivalenceRelation {X Y : C} (f : X ⟶ Y) {R : C} (p₁ p₂ : R ⟶ X)
    {t : PullbackCone p₂ p₁} (ht : IsLimit t) (h : IsKernelPair f p₁ p₂) :
    EquivalenceRelation p₁ p₂ where
  right_cancellation A a b h₁ h₂ := h.hom_ext h₁ h₂
  r := h.lift (𝟙 _) (𝟙 _) (by simp)
  s := h.lift p₂ p₁ h.w.symm
  c := t
  isLimit := ht
  t := h.lift (t.fst ≫ p₁) (t.snd ≫ p₂) (by simp [reassoc_of% t.condition, h.w])

/--
Definition of `ReflexiveRelation.map` / `ReflexiveRelation.map` 的定义

English:
definition ReflexiveRelation.map
  signature: (e : ReflexiveRelation p₁ p₂) (F : C ⥤ D)
  body: F.map e.r
  reflexivity₁ := by simp [← F.map_comp]
  reflexivity₂ := by simp [← F.map_comp]

中文:
定义 ReflexiveRelation.map
  签名: (e : ReflexiveRelation p₁ p₂) (F : C ⥤ D)
  定义体: F.map e.r
  reflexivity₁ := by simp [← F.map_comp]
  reflexivity₂ := by simp [← F.map_comp]

Depends on / 依赖: F.map
-/
def ReflexiveRelation.map (e : ReflexiveRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] :
    ReflexiveRelation (F.map p₁) (F.map p₂) where
  r := F.map e.r
  reflexivity₁ := by simp [← F.map_comp]
  reflexivity₂ := by simp [← F.map_comp]

/--
Definition of `SymmetricRelation.map` / `SymmetricRelation.map` 的定义

English:
definition SymmetricRelation.map
  signature: (e : SymmetricRelation p₁ p₂) (F : C ⥤ D)
  body: F.map e.s
  symmetry₁ := by simp [← F.map_comp]
  symmetry₂ := by simp [← F.map_comp]

中文:
定义 SymmetricRelation.map
  签名: (e : SymmetricRelation p₁ p₂) (F : C ⥤ D)
  定义体: F.map e.s
  symmetry₁ := by simp [← F.map_comp]
  symmetry₂ := by simp [← F.map_comp]

Depends on / 依赖: F.map
-/
def SymmetricRelation.map (e : SymmetricRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] :
    SymmetricRelation (F.map p₁) (F.map p₂) where
  s := F.map e.s
  symmetry₁ := by simp [← F.map_comp]
  symmetry₂ := by simp [← F.map_comp]

/--
Definition of `TransitiveRelation.map` / `TransitiveRelation.map` 的定义

English:
definition TransitiveRelation.map
  signature: (e : TransitiveRelation p₁ p₂) (F : C ⥤ D)
  body: F.map e.t
  c := e.c.map F
  isLimit := isLimitPullbackConeMapOfIsLimit F e.c.condition (.ofIsoLimit e.isLimit e.c.eta)
  transitivity₁ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₁)).trans (F.map_comp _ _))
  transitivity₂ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₂)).trans (F.map_comp _ _))

中文:
定义 TransitiveRelation.map
  签名: (e : TransitiveRelation p₁ p₂) (F : C ⥤ D)
  定义体: F.map e.t
  c := e.c.map F
  isLimit := isLimitPullbackConeMapOfIsLimit F e.c.condition (.ofIsoLimit e.isLimit e.c.eta)
  transitivity₁ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₁)).trans (F.map_comp _ _))
  transitivity₂ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₂)).trans (F.map_comp _ _))

Depends on / 依赖: F.map
-/
noncomputable def TransitiveRelation.map (e : TransitiveRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] [PreservesLimitsOfShape WalkingCospan F] :
    TransitiveRelation (F.map p₁) (F.map p₂) where
  t := F.map e.t
  c := e.c.map F
  isLimit := isLimitPullbackConeMapOfIsLimit F e.c.condition (.ofIsoLimit e.isLimit e.c.eta)
  transitivity₁ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₁)).trans (F.map_comp _ _))
  transitivity₂ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₂)).trans (F.map_comp _ _))

end CategoryTheory

namespace TypeCat

open CategoryTheory Limits

variable {X : Type w} (φ : X -> X -> Prop)

/--
Definition of `ROfRel` / `ROfRel` 的定义

English:
abbreviation ROfRel
  body: Subtype φ.uncurry

中文:
缩写 ROfRel
  定义体: Subtype φ.uncurry

Depends on / 依赖: Subtype, uncurry
-/
abbrev ROfRel := Subtype φ.uncurry

/--
Definition of `p₁OfRel` / `p₁OfRel` 的定义

English:
abbreviation p₁OfRel
  signature: : ROfRel φ ⟶ X
  body: ↾(Prod.fst ∘ Subtype.val)

中文:
缩写 p₁OfRel
  签名: : ROfRel φ ⟶ X
  定义体: ↾(Prod.fst ∘ Subtype.val)

Depends on / 依赖: Prod.fst, Subtype, Subtype.val
-/
abbrev p₁OfRel : ROfRel φ ⟶ X := ↾(Prod.fst ∘ Subtype.val)

/--
Definition of `p₂OfRel` / `p₂OfRel` 的定义

English:
abbreviation p₂OfRel
  signature: : ROfRel φ ⟶ X
  body: ↾(Prod.snd ∘ Subtype.val)

中文:
缩写 p₂OfRel
  签名: : ROfRel φ ⟶ X
  定义体: ↾(Prod.snd ∘ Subtype.val)

Depends on / 依赖: Prod.snd, Subtype, Subtype.val
-/
abbrev p₂OfRel : ROfRel φ ⟶ X := ↾(Prod.snd ∘ Subtype.val)

/--
lemma `jointlyMono₂` / 引理 `jointlyMono₂`

English:
lemma jointlyMono₂
  proof: by
    ext y
    · exact congr($h₁ y)
    · exact congr($h₂ y)

中文:
引理 jointlyMono₂
  证明: by
    ext y
    · exact congr($h₁ y)
    · exact congr($h₂ y)
-/
lemma jointlyMono₂ :
    JointlyMono₂ (p₁OfRel φ) (p₂OfRel φ) where
  right_cancellation Y f g h₁ h₂ := by
    ext y
    · exact congr($h₁ y)
    · exact congr($h₂ y)

/--
Definition of `ReflexiveRelation.ofRefl` / `ReflexiveRelation.ofRefl` 的定义

English:
definition ReflexiveRelation.ofRefl
  signature: {X : Type w} {φ : X -> X -> Prop} (hφ : Std.Refl φ)
  body: jointlyMono₂ φ
  r := (↾(fun x => ⟨⟨x, x⟩, hφ.refl x⟩))

中文:
定义 ReflexiveRelation.ofRefl
  签名: {X : 类型 w} {φ : X -> X -> 命题} (hφ : Std.Refl φ)
  定义体: jointlyMono₂ φ
  r := (↾(fun x => ⟨⟨x, x⟩, hφ.refl x⟩))
-/
def ReflexiveRelation.ofRefl {X : Type w} {φ : X -> X -> Prop} (hφ : Std.Refl φ) :
    ReflexiveRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  r := (↾(fun x => ⟨⟨x, x⟩, hφ.refl x⟩))

/--
Definition of `SymmetricRelation.ofSymmetric` / `SymmetricRelation.ofSymmetric` 的定义

English:
definition SymmetricRelation.ofSymmetric
  signature: {X : Type w} {φ : X -> X -> Prop} [Std.Symm φ]
  body: jointlyMono₂ φ
  s := ↾(fun ⟨⟨x₁, x₂⟩, h⟩ => ⟨⟨x₂, x₁⟩, symm h⟩)

中文:
定义 SymmetricRelation.ofSymmetric
  签名: {X : 类型 w} {φ : X -> X -> 命题} [Std.Symm φ]
  定义体: jointlyMono₂ φ
  s := ↾(fun ⟨⟨x₁, x₂⟩, h⟩ => ⟨⟨x₂, x₁⟩, symm h⟩)
-/
def SymmetricRelation.ofSymmetric {X : Type w} {φ : X -> X -> Prop} [Std.Symm φ] :
    SymmetricRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  s := ↾(fun ⟨⟨x₁, x₂⟩, h⟩ => ⟨⟨x₂, x₁⟩, symm h⟩)

/--
Definition of `TransitiveRelation.ofIsTrans` / `TransitiveRelation.ofIsTrans` 的定义

English:
definition TransitiveRelation.ofIsTrans
  signature: {X : Type w} {φ : X -> X -> Prop} (hφ : IsTrans _ φ)
  body: jointlyMono₂ φ
  c := Types.pullbackCone _ _
  isLimit := (Types.pullbackLimitCone _ _).isLimit
  t := ↾(fun ⟨⟨⟨⟨x₁, _⟩, h⟩, ⟨⟨_, x₂'⟩, h'⟩⟩, h₁₂⟩ => by
    dsimp at h₁₂
    rw [← h₁₂] at h'
    refine ⟨⟨x₁, x₂'⟩, hφ.trans _ _ _ h h'⟩)

中文:
定义 TransitiveRelation.ofIsTrans
  签名: {X : 类型 w} {φ : X -> X -> 命题} (hφ : 是Trans _ φ)
  定义体: jointlyMono₂ φ
  c := Types.pullbackCone _ _
  isLimit := (Types.pullbackLimitCone _ _).isLimit
  t := ↾(fun ⟨⟨⟨⟨x₁, _⟩, h⟩, ⟨⟨_, x₂'⟩, h'⟩⟩, h₁₂⟩ => by
    dsimp at h₁₂
    rw [← h₁₂] at h'
    refine ⟨⟨x₁, x₂'⟩, hφ.trans _ _ _ h h'⟩)
-/
def TransitiveRelation.ofIsTrans {X : Type w} {φ : X -> X -> Prop} (hφ : IsTrans _ φ) :
    TransitiveRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  c := Types.pullbackCone _ _
  isLimit := (Types.pullbackLimitCone _ _).isLimit
  t := ↾(fun ⟨⟨⟨⟨x₁, _⟩, h⟩, ⟨⟨_, x₂'⟩, h'⟩⟩, h₁₂⟩ => by
    dsimp at h₁₂
    rw [← h₁₂] at h'
    refine ⟨⟨x₁, x₂'⟩, hφ.trans _ _ _ h h'⟩)

/--
Definition of `EquivalenceRelation.ofEquivalence` / `EquivalenceRelation.ofEquivalence` 的定义

English:
definition EquivalenceRelation.ofEquivalence
  signature: {X : Type w} {φ : X -> X -> Prop} (hφ : Equivalence φ)
  body: ReflexiveRelation.ofRefl hφ.stdRefl
  __ := let := hφ.stdSymm; SymmetricRelation.ofSymmetric
  __ := TransitiveRelation.ofIsTrans hφ.isTrans

中文:
定义 EquivalenceRelation.ofEquivalence
  签名: {X : 类型 w} {φ : X -> X -> 命题} (hφ : 等价 φ)
  定义体: ReflexiveRelation.ofRefl hφ.stdRefl
  __ := let := hφ.stdSymm; SymmetricRelation.ofSymmetric
  __ := TransitiveRelation.ofIsTrans hφ.isTrans

Depends on / 依赖: ReflexiveRelation, ReflexiveRelation.ofRefl, ofRefl, stdRefl
-/
def EquivalenceRelation.ofEquivalence {X : Type w} {φ : X -> X -> Prop} (hφ : Equivalence φ) :
    EquivalenceRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := ReflexiveRelation.ofRefl hφ.stdRefl
  __ := let := hφ.stdSymm; SymmetricRelation.ofSymmetric
  __ := TransitiveRelation.ofIsTrans hφ.isTrans

variable {R : Type w} (p₁ p₂ : R ⟶ X)

/--
Definition of `Rel.ofPair` / `Rel.ofPair` 的定义

English:
abbreviation Rel.ofPair
  body: fun x₁ x₂ => exists r : R, p₁ r = x₁ ∧ p₂ r = x₂

中文:
缩写 关系.ofPair
  定义体: fun x₁ x₂ => exists r : R, p₁ r = x₁ ∧ p₂ r = x₂
-/
abbrev Rel.ofPair := fun x₁ x₂ => exists r : R, p₁ r = x₁ ∧ p₂ r = x₂

variable {p₁ p₂}

/--
lemma `refl_of_reflexiveRelation` / 引理 `refl_of_reflexiveRelation`

English:
lemma refl_of_reflexiveRelation
  given: (e : ReflexiveRelation p₁ p₂)
  proof: ⟨e.r x, congr($e.reflexivity₁ x), by simp⟩

中文:
引理 refl_of_reflexiveRelation
  条件: (e : ReflexiveRelation p₁ p₂)
  证明: ⟨e.r x, congr($e.reflexivity₁ x), by simp⟩

Depends on / 依赖: e.reflexivity
-/
lemma refl_of_reflexiveRelation (e : ReflexiveRelation p₁ p₂) :
    Std.Refl (Rel.ofPair p₁ p₂) where
  refl x := ⟨e.r x, congr($e.reflexivity₁ x), by simp⟩

/--
lemma `symm_of_symmetricRelation` / 引理 `symm_of_symmetricRelation`

English:
lemma symm_of_symmetricRelation
  given: (e : SymmetricRelation p₁ p₂)
  statement: Std.Symm (Rel.ofPair p₁ p₂) where
  proof: fun ⟨r, hr₁, hr₂⟩ => ⟨e.s r, by simpa, by simpa⟩

@[deprecated (since := "2026-06-10")]
alias symmetric_of_symmetricRelation := symm_of_symmetricRelation

中文:
引理 symm_of_symmetricRelation
  条件: (e : SymmetricRelation p₁ p₂)
  结论: Std.Symm (关系.ofPair p₁ p₂) where
  证明: fun ⟨r, hr₁, hr₂⟩ => ⟨e.s r, by simpa, by simpa⟩

@[deprecated (since := "2026-06-10")]
alias symmetric_of_symmetricRelation := symm_of_symmetricRelation
-/
lemma symm_of_symmetricRelation (e : SymmetricRelation p₁ p₂) : Std.Symm (Rel.ofPair p₁ p₂) where
  symm x₁ x₂ := fun ⟨r, hr₁, hr₂⟩ => ⟨e.s r, by simpa, by simpa⟩

@[deprecated (since := "2026-06-10")]
alias symmetric_of_symmetricRelation := symm_of_symmetricRelation

/--
lemma `isTrans_of_transitiveRelation` / 引理 `isTrans_of_transitiveRelation`

English:
lemma isTrans_of_transitiveRelation
  given: (e : TransitiveRelation p₁ p₂)
  proof: by
    refine fun ⟨r, ⟨hr₁, hr₂⟩⟩ ⟨r', ⟨hr₁', hr₂'⟩⟩ =>
      ⟨e.t ((PullbackCone.IsLimit.equivPullbackObj e.isLimit).symm ⟨(r, r'), hr₂.trans hr₁'.symm⟩),
        ⟨?_, ?_⟩⟩
    all_goals simpa

中文:
引理 isTrans_of_transitiveRelation
  条件: (e : TransitiveRelation p₁ p₂)
  证明: by
    refine fun ⟨r, ⟨hr₁, hr₂⟩⟩ ⟨r', ⟨hr₁', hr₂'⟩⟩ =>
      ⟨e.t ((PullbackCone.IsLimit.equivPullbackObj e.isLimit).symm ⟨(r, r'), hr₂.trans hr₁'.symm⟩),
        ⟨?_, ?_⟩⟩
    all_goals simpa

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.equivPullbackObj, all_goals, e.isLimit, equivPullbackObj, isLimit
-/
lemma isTrans_of_transitiveRelation (e : TransitiveRelation p₁ p₂) :
    IsTrans _ (Rel.ofPair p₁ p₂) where
  trans x₁ x₂ x₃ := by
    refine fun ⟨r, ⟨hr₁, hr₂⟩⟩ ⟨r', ⟨hr₁', hr₂'⟩⟩ =>
      ⟨e.t ((PullbackCone.IsLimit.equivPullbackObj e.isLimit).symm ⟨(r, r'), hr₂.trans hr₁'.symm⟩),
        ⟨?_, ?_⟩⟩
    all_goals simpa

/--
lemma `equivalence_of_equivalenceRelation` / 引理 `equivalence_of_equivalenceRelation`

English:
lemma equivalence_of_equivalenceRelation
  given: (e : EquivalenceRelation p₁ p₂)
  proof: (refl_of_reflexiveRelation e.toReflexiveRelation).refl
.symm _ _ symm := symm_of_symmetricRelation e.toSymmetricRelation
  trans := (isTrans_of_transitiveRelation e.toTransitiveRelation).trans _ _ _

中文:
引理 equivalence_of_equivalenceRelation
  条件: (e : EquivalenceRelation p₁ p₂)
  证明: (refl_of_reflexiveRelation e.toReflexiveRelation).refl
.symm _ _ symm := symm_of_symmetricRelation e.toSymmetricRelation
  trans := (isTrans_of_transitiveRelation e.toTransitiveRelation).trans _ _ _

Depends on / 依赖: e.toReflexiveRelation, refl_of_reflexiveRelation, toReflexiveRelation
-/
lemma equivalence_of_equivalenceRelation (e : EquivalenceRelation p₁ p₂) :
    Equivalence (Rel.ofPair p₁ p₂) where
  refl := (refl_of_reflexiveRelation e.toReflexiveRelation).refl
.symm _ _ symm := symm_of_symmetricRelation e.toSymmetricRelation
  trans := (isTrans_of_transitiveRelation e.toTransitiveRelation).trans _ _ _

end TypeCat

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]
variable {R A : C} (p₁ p₂ : R ⟶ A)

section Effective

/--
Definition of `EffectiveEquivalenceRelation` / `EffectiveEquivalenceRelation` 的定义

English:
structure EffectiveEquivalenceRelation
  parameters: {R A : C} (p₁ p₂ : R ⟶ A)
  extends: EquivalenceRelation p₁ p₂
  axioms and operations (4):
    - B : C
    - π : A ⟶ B
    - isKernelPair : IsKernelPair π p₁ p₂
    - isPushout : IsPushout p₁ p₂ π π

中文:
结构 EffectiveEquivalenceRelation
  参数: {R A : C} (p₁ p₂ : R ⟶ A)
  继承: EquivalenceRelation p₁ p₂
  公理与运算 (4 个):
    - B : C
    - π : A ⟶ B
    - isKernelPair : IsKernelPair π p₁ p₂
    - isPushout : 是推出 p₁ p₂ π π
-/
structure EffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) extends EquivalenceRelation p₁ p₂
    where
  /-- `B` is the "quotient" of the relation -/
  B : C
  /-- `π` is the "quotient map" of the relation -/
  π : A ⟶ B
  isKernelPair : IsKernelPair π p₁ p₂
  isPushout : IsPushout p₁ p₂ π π

/--
Definition of `IsEffectiveEquivalenceRelation` / `IsEffectiveEquivalenceRelation` 的定义

English:
class IsEffectiveEquivalenceRelation
  parameters: {R A : C} (p₁ p₂ : R ⟶ A)
  axioms and operations (1):
    - nonempty_effectiveEquivalenceRelation : Nonempty (EffectiveEquivalenceRelation p₁ p₂)

中文:
类 是EffectiveEquivalenceRelation
  参数: {R A : C} (p₁ p₂ : R ⟶ A)
  公理与运算 (1 个):
    - nonempty_effectiveEquivalenceRelation : 非空 (EffectiveEquivalenceRelation p₁ p₂)
-/
class IsEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) : Prop where
  nonempty_effectiveEquivalenceRelation : Nonempty (EffectiveEquivalenceRelation p₁ p₂)

/--
Definition of `EffectiveEquivalenceRelation.isCoequalizer` / `EffectiveEquivalenceRelation.isCoequalizer` 的定义

English:
definition EffectiveEquivalenceRelation.isCoequalizer
  signature: {R A : C} (p₁ p₂ : R ⟶ A)
  body: e.isPushout.isLimitFork

中文:
定义 EffectiveEquivalenceRelation.isCoequalizer
  签名: {R A : C} (p₁ p₂ : R ⟶ A)
  定义体: e.isPushout.isLimitFork

Depends on / 依赖: e.isPushout.isLimitFork, isLimitFork, isPushout
-/
noncomputable def EffectiveEquivalenceRelation.isCoequalizer {R A : C} (p₁ p₂ : R ⟶ A)
    (e : EffectiveEquivalenceRelation p₁ p₂) :
    IsColimit (Cofork.ofπ e.π e.isPushout.w) :=
  e.isPushout.isLimitFork

instance (e : EffectiveEquivalenceRelation p₁ p₂) :
    IsRegularEpi e.π where
  regularEpi := ⟨Cofork.IsColimit.regularEpi e.isCoequalizer⟩

/--
Definition of `UniversallyEffectiveEquivalenceRelation` / `UniversallyEffectiveEquivalenceRelation` 的定义

English:
structure UniversallyEffectiveEquivalenceRelation
  parameters: {R A : C} (p₁ p₂ : R ⟶ A)
  extends: EffectiveEquivalenceRelation p₁ p₂
  axioms and operations (1):
    - universally_effectiveEpi_π : MorphismProperty.universally (fun _ _ f => EffectiveEpi f) toEffectiveEquivalenceRelation.π

中文:
结构 UniversallyEffectiveEquivalenceRelation
  参数: {R A : C} (p₁ p₂ : R ⟶ A)
  继承: EffectiveEquivalenceRelation p₁ p₂
  公理与运算 (1 个):
    - universally_effectiveEpi_π : MorphismProperty.universally (fun _ _ f => 有效满态射 f) toEffectiveEquivalenceRelation.π
-/
structure UniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A)
    extends EffectiveEquivalenceRelation p₁ p₂ where
  universally_effectiveEpi_π : MorphismProperty.universally (fun _ _ f => EffectiveEpi f)
    toEffectiveEquivalenceRelation.π

/--
Definition of `IsUniversallyEffectiveEquivalenceRelation` / `IsUniversallyEffectiveEquivalenceRelation` 的定义

English:
class IsUniversallyEffectiveEquivalenceRelation
  parameters: {R A : C} (p₁ p₂ : R ⟶ A)
  axioms and operations (1):
    - nonempty_universallyEffectiveEquivalenceRelation : Nonempty (UniversallyEffectiveEquivalenceRelation p₁ p₂)

中文:
类 是UniversallyEffectiveEquivalenceRelation
  参数: {R A : C} (p₁ p₂ : R ⟶ A)
  公理与运算 (1 个):
    - nonempty_universallyEffectiveEquivalenceRelation : 非空 (UniversallyEffectiveEquivalenceRelation p₁ p₂)
-/
class IsUniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) : Prop where
  nonempty_universallyEffectiveEquivalenceRelation :
    Nonempty (UniversallyEffectiveEquivalenceRelation p₁ p₂)

variable (C) in
/--
Definition of `IsUniversallyEffectiveEquivalenceRelationCategory` / `IsUniversallyEffectiveEquivalenceRelationCategory` 的定义

English:
class IsUniversallyEffectiveEquivalenceRelationCategory
  parameters: where
  axioms and operations (1):
    - isUniversallyEffectiveEquivalenceRelation((p₁ p₂ : R ⟶ A) [IsEquivalenceRelation p₁ p₂]) : IsUniversallyEffectiveEquivalenceRelation p₁ p₂

中文:
类 是UniversallyEffectiveEquivalenceRelation范畴
  参数: where
  公理与运算 (1 个):
    - isUniversallyEffectiveEquivalenceRelation((p₁ p₂ : R ⟶ A) [是EquivalenceRelation p₁ p₂]) : 是UniversallyEffectiveEquivalenceRelation p₁ p₂
-/
class IsUniversallyEffectiveEquivalenceRelationCategory where
  isUniversallyEffectiveEquivalenceRelation (p₁ p₂ : R ⟶ A) [IsEquivalenceRelation p₁ p₂] :
    IsUniversallyEffectiveEquivalenceRelation p₁ p₂

end Effective

end CategoryTheory
