/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.CategoryTheory.Groupoid

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/

@[expose] public section


/--
Definition of `HomRel` / `HomRel` 的定义

English:
definition HomRel
  signature: (C) [Quiver C]
  body: forall ⦃X Y : C⦄, (X ⟶ Y) -> (X ⟶ Y) -> Prop
deriving Inhabited

中文:
定义 HomRel
  签名: (C) [箭图 C]
  定义体: forall ⦃X Y : C⦄, (X ⟶ Y) -> (X ⟶ Y) -> Prop
deriving Inhabited
-/
def HomRel (C) [Quiver C] :=
  forall ⦃X Y : C⦄, (X ⟶ Y) -> (X ⟶ Y) -> Prop
deriving Inhabited

namespace CategoryTheory

open CategoryTheory.Functor

section

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/--
Definition of `Functor.homRel` / `Functor.homRel` 的定义

English:
definition Functor.homRel
  signature: : HomRel C
  body: fun _ _ f g => F.map f = F.map g

@[simp]

中文:
定义 函子.homRel
  签名: : HomRel C
  定义体: fun _ _ f g => F.map f = F.map g

@[simp]

Depends on / 依赖: F.map
-/
def Functor.homRel : HomRel C :=
  fun _ _ f g => F.map f = F.map g

@[simp]
/--
lemma `Functor.homRel_iff` / 引理 `Functor.homRel_iff`

English:
lemma Functor.homRel_iff
  given: {X Y : C} (f g : X ⟶ Y)
  proof: Iff.rfl

中文:
引理 函子.homRel_iff
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma Functor.homRel_iff {X Y : C} (f g : X ⟶ Y) :
    F.homRel f g ↔ F.map f = F.map g := Iff.rfl

end

variable {C : Type*} [Category* C] (r : HomRel C)

namespace HomRel

/--
Definition of `IsStableUnderPrecomp` / `IsStableUnderPrecomp` 的定义

English:
class IsStableUnderPrecomp
  parameters: : Prop where
  axioms and operations (1):
    - comp_left({X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z}) : r g g' -> r (f ≫ g) (f ≫ g')

中文:
类 是StableUnderPrecomp
  参数: : 命题 where
  公理与运算 (1 个):
    - comp_left({X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z}) : r g g' -> r (f ≫ g) (f ≫ g')
-/
class IsStableUnderPrecomp : Prop where
  comp_left {X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z} : r g g' -> r (f ≫ g) (f ≫ g')

/--
Definition of `IsStableUnderPostcomp` / `IsStableUnderPostcomp` 的定义

English:
class IsStableUnderPostcomp
  parameters: : Prop where
  axioms and operations (1):
    - comp_right({X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z)) : r f f' -> r (f ≫ g) (f' ≫ g)

中文:
类 是StableUnderPostcomp
  参数: : 命题 where
  公理与运算 (1 个):
    - comp_right({X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z)) : r f f' -> r (f ≫ g) (f' ≫ g)
-/
class IsStableUnderPostcomp : Prop where
  comp_right {X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z) : r f f' -> r (f ≫ g) (f' ≫ g)

export IsStableUnderPrecomp (comp_left)
export IsStableUnderPostcomp (comp_right)

/--
Inductive type `CompClosure` / 归纳类型 `CompClosure`

English:
inductive CompClosure
  parameters: (r : HomRel C)
  constructors (1):
    - intro: {s t : C} (a b : C) (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) : CompClosure r (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)

中文:
归纳类型 余mpClosure
  参数: (r : HomRel C)
  构造子 (1 个):
    - intro: {s t : C} (a b : C) (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) : 余mpClosure r (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)
-/
inductive CompClosure (r : HomRel C) : HomRel C
  | intro {s t : C} (a b : C) (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) :
    CompClosure r (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)

variable {r} in
/--
theorem `CompClosure.of` / 定理 `CompClosure.of`

English:
theorem CompClosure.of
  given: {a b : C} {m₁ m₂ : a ⟶ b} (h : r m₁ m₂)
  statement: CompClosure r m₁ m₂
  proof: by
  simpa using CompClosure.intro _ _ (𝟙 _) m₁ m₂ (𝟙 _) h

中文:
定理 余mpClosure.of
  条件: {a b : C} {m₁ m₂ : a ⟶ b} (h : r m₁ m₂)
  结论: 余mpClosure r m₁ m₂
  证明: by
  simpa using CompClosure.intro _ _ (𝟙 _) m₁ m₂ (𝟙 _) h

Depends on / 依赖: CompClosure, CompClosure.intro
-/
theorem CompClosure.of {a b : C} {m₁ m₂ : a ⟶ b} (h : r m₁ m₂) : CompClosure r m₁ m₂ := by
  simpa using CompClosure.intro _ _ (𝟙 _) m₁ m₂ (𝟙 _) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderPrecomp (CompClosure r)
  body: by
    rintro a b e f _ _ ⟨c, d, g, h₁, h₂, i, h⟩
    simpa using CompClosure.intro _ _ (f ≫ g) _ _ i h

中文:
实例 :
  签名: 是StableUnderPrecomp (余mpClosure r)
  定义体: by
    rintro a b e f _ _ ⟨c, d, g, h₁, h₂, i, h⟩
    simpa using CompClosure.intro _ _ (f ≫ g) _ _ i h

Depends on / 依赖: CompClosure, CompClosure.intro, IsBasis, M.IsBasis, aesop_mat
-/
instance : IsStableUnderPrecomp (CompClosure r) where
  comp_left := by
    rintro a b e f _ _ ⟨c, d, g, h₁, h₂, i, h⟩
    simpa using CompClosure.intro _ _ (f ≫ g) _ _ i h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderPostcomp (CompClosure r)
  body: by
    rintro a d e _ _ g ⟨b, c, f, g₁, g₂, i, h⟩
    simpa using CompClosure.intro _ _ f _ _ (i ≫ g) h

中文:
实例 :
  签名: 是StableUnderPostcomp (余mpClosure r)
  定义体: by
    rintro a d e _ _ g ⟨b, c, f, g₁, g₂, i, h⟩
    simpa using CompClosure.intro _ _ f _ _ (i ≫ g) h

Depends on / 依赖: CompClosure, CompClosure.intro
-/
instance : IsStableUnderPostcomp (CompClosure r) where
  comp_right := by
    rintro a d e _ _ g ⟨b, c, f, g₁, g₂, i, h⟩
    simpa using CompClosure.intro _ _ f _ _ (i ≫ g) h

section

variable [IsStableUnderPrecomp r] [IsStableUnderPostcomp r]

/--
lemma `compClosure_iff_self` / 引理 `compClosure_iff_self`

English:
lemma compClosure_iff_self
  given: {X Y : C} (f g : X ⟶ Y)
  proof: by
  refine ⟨?_, CompClosure.of⟩
  rintro ⟨_, _, _, _, _, _, h⟩
  exact HomRel.comp_left _ (HomRel.comp_right _ h)

@[simp]

中文:
引理 compClosure_iff_self
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: by
  refine ⟨?_, CompClosure.of⟩
  rintro ⟨_, _, _, _, _, _, h⟩
  exact HomRel.comp_left _ (HomRel.comp_right _ h)

@[simp]

Depends on / 依赖: CompClosure, CompClosure.of, HomRel, HomRel.comp_left, HomRel.comp_right, comp_left, comp_right
-/
lemma compClosure_iff_self {X Y : C} (f g : X ⟶ Y) :
    CompClosure r f g ↔ r f g := by
  refine ⟨?_, CompClosure.of⟩
  rintro ⟨_, _, _, _, _, _, h⟩
  exact HomRel.comp_left _ (HomRel.comp_right _ h)

@[simp]
/--
theorem `compClosure_eq_self` / 定理 `compClosure_eq_self`

English:
theorem compClosure_eq_self
  proof: by
  dsimp [HomRel]
  ext
  simp only [compClosure_iff_self]

中文:
定理 compClosure_eq_self
  证明: by
  dsimp [HomRel]
  ext
  simp only [compClosure_iff_self]

Depends on / 依赖: HomRel, compClosure_iff_self
-/
theorem compClosure_eq_self :
    CompClosure r = r := by
  dsimp [HomRel]
  ext
  simp only [compClosure_iff_self]

end

end HomRel

/--
Definition of `Congruence` / `Congruence` 的定义

English:
class Congruence
  parameters: : Prop
  extends: HomRel.IsStableUnderPrecomp r, HomRel.IsStableUnderPostcomp r
  axioms and operations (1):
    - equivalence : forall {X Y}, _root_.Equivalence (@r X Y)

中文:
类 余ngruence
  参数: : 命题
  继承: HomRel.是StableUnderPrecomp r, HomRel.是StableUnderPostcomp r
  公理与运算 (1 个):
    - equivalence : 对任意 {X Y}, _root_.等价 (@r X Y)
-/
class Congruence : Prop
    extends HomRel.IsStableUnderPrecomp r, HomRel.IsStableUnderPostcomp r where
  /-- `r` is an equivalence on every hom-set. -/
  equivalence : forall {X Y}, _root_.Equivalence (@r X Y)

/--
Instance `Functor.congruence_homRel` / 实例 `Functor.congruence_homRel`

English:
instance Functor.congruence_homRel
  signature: {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  body: { refl := fun _ => rfl
      symm := by aesop
      trans := by aesop }
  comp_left := by aesop
  comp_right := by aesop

中文:
实例 函子.congruence_homRel
  签名: {C D : 类型} [范畴* C] [范畴* D] (F : C ⥤ D)
  定义体: { refl := fun _ => rfl
      symm := by aesop
      trans := by aesop }
  comp_left := by aesop
  comp_right := by aesop

Depends on / 依赖: comp_left, comp_right
-/
instance Functor.congruence_homRel {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) :
    Congruence F.homRel where
  equivalence :=
    { refl := fun _ => rfl
      symm := by aesop
      trans := by aesop }
  comp_left := by aesop
  comp_right := by aesop

/-- A type synonym for `C`, thought of as the objects of the quotient category. -/
@[ext]
/--
Definition of `Quotient` / `Quotient` 的定义

English:
structure Quotient
  parameters: (r : HomRel C)
  axioms and operations (1):
    - as : C

中文:
结构 商
  参数: (r : HomRel C)
  公理与运算 (1 个):
    - as : C
-/
structure Quotient (r : HomRel C) where
  /-- The object of `C`. -/
  as : C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (Quotient r)
  body: ⟨{ as := default }⟩

中文:
实例 [可居
  签名: C] : 可居 (商 r)
  定义体: ⟨{ as := default }⟩
-/
instance [Inhabited C] : Inhabited (Quotient r) :=
  ⟨{ as := default }⟩

namespace Quotient

/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: (s t : Quotient r)
  body: Quot @HomRel.CompClosure C _ r s.as t.as

中文:
定义 态射
  签名: (s t : 商 r)
  定义体: Quot @HomRel.CompClosure C _ r s.as t.as

Depends on / 依赖: CompClosure, HomRel, HomRel.CompClosure, s.as, t.as
-/
def Hom (s t : Quotient r) : Type _ :=
Quot @HomRel.CompClosure C _ r s.as t.as

instance (a : Quotient r) : Inhabited (Hom r a a) :=
  ⟨Quot.mk _ (𝟙 a.as)⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: ⦃a b c
  body: fun hf hg =>
  Quot.liftOn hf
    (fun f =>
      Quot.liftOn hg (fun g => Quot.mk _ (f ≫ g)) fun _ _ h =>
        Quot.sound (HomRel.comp_left f h))
    fun _ _ h => Quot.inductionOn hg fun _ => Quot.sound (HomRel.comp_right _ h)

@[simp]

中文:
定义 comp
  签名: ⦃a b c
  定义体: fun hf hg =>
  Quot.liftOn hf
    (fun f =>
      Quot.liftOn hg (fun g => Quot.mk _ (f ≫ g)) fun _ _ h =>
        Quot.sound (HomRel.comp_left f h))
    fun _ _ h => Quot.inductionOn hg fun _ => Quot.sound (HomRel.comp_right _ h)

@[simp]
-/
def comp ⦃a b c : Quotient r⦄ : Hom r a b -> Hom r b c -> Hom r a c := fun hf hg =>
  Quot.liftOn hf
    (fun f =>
      Quot.liftOn hg (fun g => Quot.mk _ (f ≫ g)) fun _ _ h =>
        Quot.sound (HomRel.comp_left f h))
    fun _ _ h => Quot.inductionOn hg fun _ => Quot.sound (HomRel.comp_right _ h)

@[simp]
/--
theorem `comp_mk` / 定理 `comp_mk`

English:
theorem comp_mk
  given: {a b c : Quotient r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as)
  proof: rfl

中文:
定理 comp_mk
  条件: {a b c : 商 r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as)
  证明: rfl

Depends on / 依赖: IsBasis, M.IsBasis, _iff_isBasis_inter_ground, aesop_mat, inter_eq_self_of_subset_left, isBasis
-/
theorem comp_mk {a b c : Quotient r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    comp r (Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (f ≫ g) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (Quotient r) where
  body: Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := @comp _ _ r
comp_id f := Quot.inductionOn f by simp
id_comp f := Quot.inductionOn f by simp
assoc f g h := Quot.inductionOn f Quot.inductionOn g Quot.inductionOn h by simp

中文:
实例 category
  签名: : 范畴 (商 r) where
  定义体: Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := @comp _ _ r
comp_id f := Quot.inductionOn f by simp
id_comp f := Quot.inductionOn f by simp
assoc f g h := Quot.inductionOn f Quot.inductionOn g Quot.inductionOn h by simp
-/
instance category : Category (Quotient r) where
  Hom := Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := @comp _ _ r
comp_id f := Quot.inductionOn f by simp
id_comp f := Quot.inductionOn f by simp
assoc f g h := Quot.inductionOn f Quot.inductionOn g Quot.inductionOn h by simp

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: {C : Type _} [Category* C] (r : HomRel C)
  body: x.1
  invFun x := ⟨x⟩

noncomputable section

中文:
定义 equiv
  签名: {C : 类型 _} [范畴* C] (r : HomRel C)
  定义体: x.1
  invFun x := ⟨x⟩

noncomputable section

Depends on / 依赖: _iff_isBasis_inter_ground, _iff_isBasis_inter_ground.mp, isBasis
-/
def equiv {C : Type _} [Category* C] (r : HomRel C) : Quotient r ≃ C where
  toFun x := x.1
  invFun x := ⟨x⟩

noncomputable section

variable {G : Type*} [Groupoid G] (r : HomRel G)

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: {X Y : Quotient r} (f : X ⟶ Y)
  body: Quot.liftOn f (fun f' => Quot.mk _ (Groupoid.inv f')) (fun _ _ con => by
    obtain ⟨_, _, a, f, g, b, hfg⟩ := con
    simpa using! (Quot.sound (HomRel.CompClosure.intro _ _
      (inv b ≫ inv g) _ _ (inv f ≫ inv a) hfg)).symm)

@[simp]

中文:
定义 inv
  签名: {X Y : 商 r} (f : X ⟶ Y)
  定义体: Quot.liftOn f (fun f' => Quot.mk _ (Groupoid.inv f')) (fun _ _ con => by
    obtain ⟨_, _, a, f, g, b, hfg⟩ := con
    simpa using! (Quot.sound (HomRel.CompClosure.intro _ _
      (inv b ≫ inv g) _ _ (inv f ≫ inv a) hfg)).symm)

@[simp]

Depends on / 依赖: antisymm, hIJ.antisymm
-/
protected def inv {X Y : Quotient r} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun f' => Quot.mk _ (Groupoid.inv f')) (fun _ _ con => by
    obtain ⟨_, _, a, f, g, b, hfg⟩ := con
    simpa using! (Quot.sound (HomRel.CompClosure.intro _ _
      (inv b ≫ inv g) _ _ (inv f ≫ inv a) hfg)).symm)

@[simp]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  given: {X Y : Quotient r} (f : X.as ⟶ Y.as)
  proof: rfl

中文:
定理 inv_mk
  条件: {X Y : 商 r} (f : X.as ⟶ Y.as)
  证明: rfl

Depends on / 依赖: Eq.symm, eq_of_subset_indep, hI.eq_of_subset_indep, hI.subset, insert_eq_self, insert_subset, subset, subset_insert
-/
theorem inv_mk {X Y : Quotient r} (f : X.as ⟶ Y.as) :
    Quotient.inv r (Quot.mk _ f) = Quot.mk _ (Groupoid.inv f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `groupoid` / 实例 `groupoid`

English:
instance groupoid
  signature: : Groupoid (Quotient r) where
  body: Quotient.inv r f
inv_comp f := Quot.inductionOn f by simp [CategoryStruct.comp, CategoryStruct.id]
comp_inv f := Quot.inductionOn f by simp [CategoryStruct.comp, CategoryStruct.id]

中文:
实例 groupoid
  签名: : 群胚 (商 r) where
  定义体: Quotient.inv r f
inv_comp f := Quot.inductionOn f by simp [CategoryStruct.comp, CategoryStruct.id]
comp_inv f := Quot.inductionOn f by simp [CategoryStruct.comp, CategoryStruct.id]

Depends on / 依赖: Quotient, Quotient.inv
-/
instance groupoid : Groupoid (Quotient r) where
  inv f := Quotient.inv r f
inv_comp f := Quot.inductionOn f by simp [CategoryStruct.comp, CategoryStruct.id]
comp_inv f := Quot.inductionOn f by simp [CategoryStruct.comp, CategoryStruct.id]

end

/-- The functor from a category to its quotient. -/
@[implicit_reducible]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : C ⥤ Quotient r where
  body: { as := a }
  map f := Quot.mk _ f

中文:
定义 functor
  签名: : C ⥤ 商 r where
  定义体: { as := a }
  map f := Quot.mk _ f
-/
def functor : C ⥤ Quotient r where
  obj a := { as := a }
  map f := Quot.mk _ f

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `full_functor` / 实例 `full_functor`

English:
instance full_functor
  signature: : (functor r).Full where
  body: ⟨Quot.out f, by simp [functor]⟩

中文:
实例 full_functor
  签名: : (functor r).满 where
  定义体: ⟨Quot.out f, by simp [functor]⟩

Depends on / 依赖: Quot.out, functor
-/
instance full_functor : (functor r).Full where
  map_surjective f := ⟨Quot.out f, by simp [functor]⟩

/--
Instance `essSurj_functor` / 实例 `essSurj_functor`

English:
instance essSurj_functor
  signature: : (functor r).EssSurj where
  body: ⟨Y.as, ⟨eqToIso rfl⟩⟩

中文:
实例 essSurj_functor
  签名: : (functor r).本质满射 where
  定义体: ⟨Y.as, ⟨eqToIso rfl⟩⟩

Depends on / 依赖: Y.as, eqToIso
-/
instance essSurj_functor : (functor r).EssSurj where
  mem_essImage Y := ⟨Y.as, ⟨eqToIso rfl⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: C] : Unique (Quotient r) where
  body: by ext; subsingleton

中文:
实例 [唯一
  签名: C] : 唯一 (商 r) where
  定义体: by ext; subsingleton

Depends on / 依赖: subsingleton
-/
instance [Unique C] : Unique (Quotient r) where
  uniq a := by ext; subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: (x y : C), Subsingleton (x ⟶ y)] (x y
  body: (full_functor r).map_surjective.subsingleton

中文:
实例 [对任意
  签名: (x y : C), 子单例 (x ⟶ y)] (x y
  定义体: (full_functor r).map_surjective.subsingleton

Depends on / 依赖: full_functor, map_surjective, map_surjective.subsingleton, subsingleton
-/
instance [forall (x y : C), Subsingleton (x ⟶ y)] (x y : Quotient r) :
    Subsingleton (x ⟶ y) := (full_functor r).map_surjective.subsingleton

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {P : forall {a b : Quotient r}, (a ⟶ b) -> Prop}
  proof: by
  rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
  exact h f

中文:
定理 induction
  结论: {P : 对任意 {a b : 商 r}, (a ⟶ b) -> 命题}
  证明: by
  rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
  exact h f
-/
protected theorem induction {P : forall {a b : Quotient r}, (a ⟶ b) -> Prop}
    (h : forall {x y : C} (f : x ⟶ y), P ((functor r).map f)) :
    forall {a b : Quotient r} (f : a ⟶ b), P f := by
  rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
  exact h f

/--
theorem `sound` / 定理 `sound`

English:
theorem sound
  given: {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂)
  proof: by
  simpa using! Quot.sound (HomRel.CompClosure.intro _ _ (𝟙 a) f₁ f₂ (𝟙 b) h)

中文:
定理 sound
  条件: {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂)
  证明: by
  simpa using! Quot.sound (HomRel.CompClosure.intro _ _ (𝟙 a) f₁ f₂ (𝟙 b) h)

Depends on / 依赖: hI.isBasis_inter_ground.mem_of_insert_indep, hIe.subset_ground, isBasis_inter_ground, mem_insert, mem_of_insert_indep, subset_ground
-/
protected theorem sound {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂) :
    (functor r).map f₁ = (functor r).map f₂ := by
  simpa using! Quot.sound (HomRel.CompClosure.intro _ _ (𝟙 a) f₁ f₂ (𝟙 b) h)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `functor_map_eq_iff` / 定理 `functor_map_eq_iff`

English:
theorem functor_map_eq_iff
  given: [h : Congruence r] {X Y : C} (f f' : X ⟶ Y)
  proof: by
  dsimp [functor]
  rw [Equivalence.quot_mk_eq_iff]; rw [HomRel.compClosure_eq_self r]
  simpa only [HomRel.compClosure_eq_self r] using h.equivalence

中文:
定理 functor_map_eq_iff
  条件: [h : 余ngruence r] {X Y : C} (f f' : X ⟶ Y)
  证明: by
  dsimp [functor]
  rw [Equivalence.quot_mk_eq_iff]; rw [HomRel.compClosure_eq_self r]
  simpa only [HomRel.compClosure_eq_self r] using h.equivalence

Depends on / 依赖: Equivalence, Equivalence.quot_mk_eq_iff, HomRel, HomRel.compClosure_eq_self, compClosure_eq_self, equivalence, functor, h.equivalence, quot_mk_eq_iff
-/
theorem functor_map_eq_iff [h : Congruence r] {X Y : C} (f f' : X ⟶ Y) :
    (functor r).map f = (functor r).map f' ↔ r f f' := by
  dsimp [functor]
  rw [Equivalence.quot_mk_eq_iff]; rw [HomRel.compClosure_eq_self r]
  simpa only [HomRel.compClosure_eq_self r] using h.equivalence

/--
theorem `functor_homRel_eq_compClosure_eqvGen` / 定理 `functor_homRel_eq_compClosure_eqvGen`

English:
theorem functor_homRel_eq_compClosure_eqvGen
  given: {X Y : C} (f g : X ⟶ Y)
  proof: Quot.eq

中文:
定理 functor_homRel_eq_compClosure_eqvGen
  条件: {X Y : C} (f g : X ⟶ Y)
  证明: Quot.eq

Depends on / 依赖: Quot.eq
-/
theorem functor_homRel_eq_compClosure_eqvGen {X Y : C} (f g : X ⟶ Y) :
    (functor r).homRel f g ↔ Relation.EqvGen (@HomRel.CompClosure C _ r X Y) f g :=
  Quot.eq

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `compClosure.congruence` / 定理 `compClosure.congruence`

English:
theorem compClosure.congruence
  proof: by
  convert! (inferInstance : Congruence (functor r).homRel)
  ext
  rw [functor_homRel_eq_compClosure_eqvGen]

中文:
定理 compClosure.congruence
  证明: by
  convert! (inferInstance : Congruence (functor r).homRel)
  ext
  rw [functor_homRel_eq_compClosure_eqvGen]

Depends on / 依赖: Congruence, convert, functor, functor_homRel_eq_compClosure_eqvGen, homRel
-/
theorem compClosure.congruence :
    Congruence fun X Y => Relation.EqvGen (@HomRel.CompClosure C _ r X Y) := by
  convert! (inferInstance : Congruence (functor r).homRel)
  ext
  rw [functor_homRel_eq_compClosure_eqvGen]

variable {D : Type _} [Category* D] (F : C ⥤ D)

/-- The induced functor on the quotient category. -/
@[implicit_reducible]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (H : forall (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ -> F.map f₁ = F.map f₂)
  body: F.obj a.as
  map hf :=
    Quot.liftOn hf (fun f => F.map f)
      (by
        rintro _ _ ⟨_, _, _, _, _, _, h⟩
        simp [H _ _ _ _ h])
  map_id a := F.map_id a.as
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    exact F.map_comp f g

中文:
定义 lift
  签名: (H : 对任意 (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ -> F.map f₁ = F.map f₂)
  定义体: F.obj a.as
  map hf :=
    Quot.liftOn hf (fun f => F.map f)
      (by
        rintro _ _ ⟨_, _, _, _, _, _, h⟩
        simp [H _ _ _ _ h])
  map_id a := F.map_id a.as
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    exact F.map_comp f g

Depends on / 依赖: F.obj, a.as
-/
def lift (H : forall (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ -> F.map f₁ = F.map f₂) : Quotient r ⥤ D where
  obj a := F.obj a.as
  map hf :=
    Quot.liftOn hf (fun f => F.map f)
      (by
        rintro _ _ ⟨_, _, _, _, _, _, h⟩
        simp [H _ _ _ _ h])
  map_id a := F.map_id a.as
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    exact F.map_comp f g

variable (H : forall (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ -> F.map f₁ = F.map f₂)

/--
theorem `lift_spec` / 定理 `lift_spec`

English:
theorem lift_spec
  statement: functor r ⋙ lift r F H = F
  proof: by
  tauto

中文:
定理 lift_spec
  结论: functor r ⋙ lift r F H = F
  证明: by
  tauto
-/
theorem lift_spec : functor r ⋙ lift r F H = F := by
  tauto

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F)
  statement: Φ = lift r F H
  proof: by
  subst_vars
  fapply Functor.hext
  · rintro X
    dsimp [lift, Functor]
    congr
  · rintro _ _ f
    dsimp [lift, Functor]
    refine Quot.inductionOn f fun _ => ?_
    simp only [heq_eq_eq]
    congr

中文:
定理 lift_unique
  条件: (Φ : 商 r ⥤ D) (hΦ : functor r ⋙ Φ = F)
  结论: Φ = lift r F H
  证明: by
  subst_vars
  fapply Functor.hext
  · rintro X
    dsimp [lift, Functor]
    congr
  · rintro _ _ f
    dsimp [lift, Functor]
    refine Quot.inductionOn f fun _ => ?_
    simp only [heq_eq_eq]
    congr

Depends on / 依赖: Functor, Functor.hext, Quot.inductionOn, fapply, heq_eq_eq, inductionOn
-/
theorem lift_unique (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F) : Φ = lift r F H := by
  subst_vars
  fapply Functor.hext
  · rintro X
    dsimp [lift, Functor]
    congr
  · rintro _ _ f
    dsimp [lift, Functor]
    refine Quot.inductionOn f fun _ => ?_
    simp only [heq_eq_eq]
    congr

/--
lemma `lift_unique'` / 引理 `lift_unique'`

English:
lemma lift_unique'
  given: (F₁ F₂ : Quotient r ⥤ D) (h : functor r ⋙ F₁ = functor r ⋙ F₂)
  proof: by
  rw [lift_unique r (functor r ⋙ F₂) _ F₂ rfl]; swap
  · rintro X Y f g h
    dsimp
    rw [Quotient.sound r h]
  apply lift_unique
  rw [h]

中文:
引理 lift_unique'
  条件: (F₁ F₂ : 商 r ⥤ D) (h : functor r ⋙ F₁ = functor r ⋙ F₂)
  证明: by
  rw [lift_unique r (functor r ⋙ F₂) _ F₂ rfl]; swap
  · rintro X Y f g h
    dsimp
    rw [Quotient.sound r h]
  apply lift_unique
  rw [h]

Depends on / 依赖: Quotient, Quotient.sound, functor, lift_unique
-/
lemma lift_unique' (F₁ F₂ : Quotient r ⥤ D) (h : functor r ⋙ F₁ = functor r ⋙ F₂) :
    F₁ = F₂ := by
  rw [lift_unique r (functor r ⋙ F₂) _ F₂ rfl]; swap
  · rintro X Y f g h
    dsimp
    rw [Quotient.sound r h]
  apply lift_unique
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift.isLift` / `lift.isLift` 的定义

English:
definition lift.isLift
  signature: : functor r ⋙ lift r F H ≅ F
  body: NatIso.ofComponents fun _ => Iso.refl _

@[simp]

中文:
定义 lift.isLift
  签名: : functor r ⋙ lift r F H ≅ F
  定义体: NatIso.ofComponents fun _ => Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def lift.isLift : functor r ⋙ lift r F H ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
/--
theorem `lift.isLift_hom` / 定理 `lift.isLift_hom`

English:
theorem lift.isLift_hom
  given: (X : C)
  statement: (lift.isLift r F H).hom.app X = 𝟙 (F.obj X)
  proof: rfl

@[simp]

中文:
定理 lift.isLift_hom
  条件: (X : C)
  结论: (lift.isLift r F H).hom.app X = 𝟙 (F.obj X)
  证明: rfl

@[simp]
-/
theorem lift.isLift_hom (X : C) : (lift.isLift r F H).hom.app X = 𝟙 (F.obj X) :=
  rfl

@[simp]
/--
theorem `lift.isLift_inv` / 定理 `lift.isLift_inv`

English:
theorem lift.isLift_inv
  given: (X : C)
  statement: (lift.isLift r F H).inv.app X = 𝟙 (F.obj X)
  proof: rfl

中文:
定理 lift.isLift_inv
  条件: (X : C)
  结论: (lift.isLift r F H).inv.app X = 𝟙 (F.obj X)
  证明: rfl
-/
theorem lift.isLift_inv (X : C) : (lift.isLift r F H).inv.app X = 𝟙 (F.obj X) :=
  rfl

/--
theorem `lift_obj_functor_obj` / 定理 `lift_obj_functor_obj`

English:
theorem lift_obj_functor_obj
  given: (X : C)
  proof: rfl

中文:
定理 lift_obj_functor_obj
  条件: (X : C)
  证明: rfl
-/
theorem lift_obj_functor_obj (X : C) :
    (lift r F H).obj ((functor r).obj X) = F.obj X := rfl

/--
theorem `lift_map_functor_map` / 定理 `lift_map_functor_map`

English:
theorem lift_map_functor_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 lift_map_functor_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
theorem lift_map_functor_map {X Y : C} (f : X ⟶ Y) :
    (lift r F H).map ((functor r).map f) = F.map f :=
  rfl

variable {r}

/--
lemma `natTrans_ext` / 引理 `natTrans_ext`

English:
lemma natTrans_ext
  statement: {F G : Quotient r ⥤ D} (τ₁ τ₂ : F ⟶ G)
  proof: NatTrans.ext (by ext1 ⟨X⟩; exact NatTrans.congr_app h X)

中文:
引理 natTrans_ext
  结论: {F G : 商 r ⥤ D} (τ₁ τ₂ : F ⟶ G)
  证明: NatTrans.ext (by ext1 ⟨X⟩; exact NatTrans.congr_app h X)

Depends on / 依赖: NatTrans, NatTrans.congr_app, NatTrans.ext, congr_app
-/
lemma natTrans_ext {F G : Quotient r ⥤ D} (τ₁ τ₂ : F ⟶ G)
    (h : whiskerLeft (Quotient.functor r) τ₁ = whiskerLeft (Quotient.functor r) τ₂) : τ₁ = τ₂ :=
  NatTrans.ext (by ext1 ⟨X⟩; exact NatTrans.congr_app h X)

variable (r)

/--
Definition of `natTransLift` / `natTransLift` 的定义

English:
definition natTransLift
  signature: {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G)
  body: fun ⟨X⟩ => τ.app X
  naturality := fun ⟨X⟩ ⟨Y⟩ => by
    rintro ⟨f⟩
    exact τ.naturality f

@[simp]

中文:
定义 natTransLift
  签名: {F G : 商 r ⥤ D} (τ : 商.functor r ⋙ F ⟶ 商.functor r ⋙ G)
  定义体: fun ⟨X⟩ => τ.app X
  naturality := fun ⟨X⟩ ⟨Y⟩ => by
    rintro ⟨f⟩
    exact τ.naturality f

@[simp]
-/
def natTransLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) :
    F ⟶ G where
  app := fun ⟨X⟩ => τ.app X
  naturality := fun ⟨X⟩ ⟨Y⟩ => by
    rintro ⟨f⟩
    exact τ.naturality f

@[simp]
/--
lemma `natTransLift_app` / 引理 `natTransLift_app`

English:
lemma natTransLift_app
  statement: (F G : Quotient r ⥤ D)
  proof: rfl

@[reassoc]

中文:
引理 natTransLift_app
  结论: (F G : 商 r ⥤ D)
  证明: rfl

@[reassoc]
-/
lemma natTransLift_app (F G : Quotient r ⥤ D)
    (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) (X : C) :
    (natTransLift r τ).app ((Quotient.functor r).obj X) = τ.app X := rfl

@[reassoc]
/--
lemma `comp_natTransLift` / 引理 `comp_natTransLift`

English:
lemma comp_natTransLift
  statement: {F G H : Quotient r ⥤ D}
  proof: by cat_disch

@[simp]

中文:
引理 comp_natTransLift
  结论: {F G H : 商 r ⥤ D}
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma comp_natTransLift {F G H : Quotient r ⥤ D}
    (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G)
    (τ' : Quotient.functor r ⋙ G ⟶ Quotient.functor r ⋙ H) :
    natTransLift r τ ≫ natTransLift r τ' = natTransLift r (τ ≫ τ') := by cat_disch

@[simp]
/--
lemma `natTransLift_id` / 引理 `natTransLift_id`

English:
lemma natTransLift_id
  given: (F : Quotient r ⥤ D)
  proof: by cat_disch

中文:
引理 natTransLift_id
  条件: (F : 商 r ⥤ D)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma natTransLift_id (F : Quotient r ⥤ D) :
    natTransLift r (𝟙 (Quotient.functor r ⋙ F)) = 𝟙 _ := by cat_disch

/-- In order to define a natural isomorphism `F ≅ G` with `F G : Quotient r ⥤ D`, it suffices
to do so after precomposing with `Quotient.functor r`. -/
@[simps]
/--
Definition of `natIsoLift` / `natIsoLift` 的定义

English:
definition natIsoLift
  signature: {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ≅ Quotient.functor r ⋙ G)
  body: natTransLift _ τ.hom
  inv := natTransLift _ τ.inv
  hom_inv_id := by rw [comp_natTransLift, τ.hom_inv_id, natTransLift_id]
  inv_hom_id := by rw [comp_natTransLift, τ.inv_hom_id, natTransLift_id]

中文:
定义 natIsoLift
  签名: {F G : 商 r ⥤ D} (τ : 商.functor r ⋙ F ≅ 商.functor r ⋙ G)
  定义体: natTransLift _ τ.hom
  inv := natTransLift _ τ.inv
  hom_inv_id := by rw [comp_natTransLift, τ.hom_inv_id, natTransLift_id]
  inv_hom_id := by rw [comp_natTransLift, τ.inv_hom_id, natTransLift_id]

Depends on / 依赖: natTransLift
-/
def natIsoLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ≅ Quotient.functor r ⋙ G) :
    F ≅ G where
  hom := natTransLift _ τ.hom
  inv := natTransLift _ τ.inv
  hom_inv_id := by rw [comp_natTransLift, τ.hom_inv_id, natTransLift_id]
  inv_hom_id := by rw [comp_natTransLift, τ.inv_hom_id, natTransLift_id]

variable (D)

/--
Instance `full_whiskeringLeft_functor` / 实例 `full_whiskeringLeft_functor`

English:
instance full_whiskeringLeft_functor
  signature: :
  body: ⟨natTransLift r f, by cat_disch⟩

中文:
实例 full_whiskeringLeft_functor
  签名: :
  定义体: ⟨natTransLift r f, by cat_disch⟩

Depends on / 依赖: cat_disch, natTransLift
-/
instance full_whiskeringLeft_functor :
    ((whiskeringLeft C _ D).obj (functor r)).Full where
  map_surjective f := ⟨natTransLift r f, by cat_disch⟩

/--
Instance `faithful_whiskeringLeft_functor` / 实例 `faithful_whiskeringLeft_functor`

English:
instance faithful_whiskeringLeft_functor
  signature: :
  body: ⟨by apply natTrans_ext⟩

中文:
实例 faithful_whiskeringLeft_functor
  签名: :
  定义体: ⟨by apply natTrans_ext⟩

Depends on / 依赖: natTrans_ext
-/
instance faithful_whiskeringLeft_functor :
    ((whiskeringLeft C _ D).obj (functor r)).Faithful := ⟨by apply natTrans_ext⟩

end Quotient

namespace Functor

variable {D : Type*} [Category* D] (L : C ⥤ D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.Full]
  signature: : (Quotient.lift L.homRel L (by simp)).Full where
  body: by
    rintro ⟨X⟩ ⟨Y⟩ (f : L.obj X ⟶ L.obj Y)
    obtain ⟨f, rfl⟩ := L.map_surjective f
    exact ⟨(Quotient.functor _).map f, rfl⟩

中文:
实例 [L.满]
  签名: : (商.lift L.homRel L (by simp)).满 where
  定义体: by
    rintro ⟨X⟩ ⟨Y⟩ (f : L.obj X ⟶ L.obj Y)
    obtain ⟨f, rfl⟩ := L.map_surjective f
    exact ⟨(Quotient.functor _).map f, rfl⟩

Depends on / 依赖: L.map_surjective, L.obj, Quotient, Quotient.functor, functor, map_surjective
-/
instance [L.Full] : (Quotient.lift L.homRel L (by simp)).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ (f : L.obj X ⟶ L.obj Y)
    obtain ⟨f, rfl⟩ := L.map_surjective f
    exact ⟨(Quotient.functor _).map f, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Quotient.lift L.homRel L (by simp)).Faithful
  body: by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ h
    exact Quotient.sound _ h

中文:
实例 :
  签名: (商.lift L.homRel L (by simp)).忠实
  定义体: by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ h
    exact Quotient.sound _ h

Depends on / 依赖: Quotient, Quotient.sound
-/
instance : (Quotient.lift L.homRel L (by simp)).Faithful where
  map_injective := by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ h
    exact Quotient.sound _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.EssSurj]
  signature: : (Quotient.lift L.homRel L (by simp)).EssSurj where
  body: ⟨(Quotient.functor _).obj (L.objPreimage X), ⟨L.objObjPreimageIso X⟩⟩

中文:
实例 [L.本质满射]
  签名: : (商.lift L.homRel L (by simp)).本质满射 where
  定义体: ⟨(Quotient.functor _).obj (L.objPreimage X), ⟨L.objObjPreimageIso X⟩⟩

Depends on / 依赖: L.objObjPreimageIso, L.objPreimage, Quotient, Quotient.functor, functor, objObjPreimageIso, objPreimage
-/
instance [L.EssSurj] : (Quotient.lift L.homRel L (by simp)).EssSurj where
  mem_essImage X :=
    ⟨(Quotient.functor _).obj (L.objPreimage X), ⟨L.objObjPreimageIso X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.Full]
  signature: [L.EssSurj]

中文:
实例 [L.满]
  签名: [L.本质满射]
-/
instance [L.Full] [L.EssSurj] : (Quotient.lift L.homRel L (by simp)).IsEquivalence where

end Functor

end CategoryTheory
