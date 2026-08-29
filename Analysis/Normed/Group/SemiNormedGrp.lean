/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The category of seminormed groups

We define `SemiNormedGrp`, the category of seminormed groups and normed group homs between
them, as well as `SemiNormedGrp₁`, the subcategory of norm non-increasing morphisms.
-/

@[expose] public section


noncomputable section

universe u

open CategoryTheory

/--
Definition of `SemiNormedGrp` / `SemiNormedGrp` 的定义

English:
structure SemiNormedGrp
  parameters: : Type (u + 1) where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [str : SeminormedAddCommGroup carrier]

中文:
结构 SemiNormedGrp
  参数: : 类型 (u + 1) where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [str : SeminormedAddComm群 carrier]
-/
structure SemiNormedGrp : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp.str

namespace SemiNormedGrp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort SemiNormedGrp Type*
  body: X.carrier

中文:
实例 :
  签名: CoeSort SemiNormedGrp 类型
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort SemiNormedGrp Type* where
  coe X := X.carrier

/-- The type of morphisms in `SemiNormedGrp` -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : SemiNormedGrp.{u})
  axioms and operations (1):
    - hom' : NormedAddGroupHom M N

中文:
结构 态射
  参数: (M N : SemiNormedGrp.{u})
  公理与运算 (1 个):
    - hom' : 赋范加群态射 M N
-/
structure Hom (M N : SemiNormedGrp.{u}) where
  /-- The underlying `NormedAddGroupHom`. -/
  hom' : NormedAddGroupHom M N

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} SemiNormedGrp
  body: Hom X Y
  id X := ⟨NormedAddGroupHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 大范畴.{u} SemiNormedGrp
  定义体: Hom X Y
  id X := ⟨NormedAddGroupHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : LargeCategory.{u} SemiNormedGrp where
  Hom X Y := Hom X Y
  id X := ⟨NormedAddGroupHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory SemiNormedGrp (NormedAddGroupHom · ·)
  body: f.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: 余ncrete范畴 SemiNormedGrp (赋范加群态射 · ·)
  定义体: f.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: f.hom
-/
instance : ConcreteCategory SemiNormedGrp (NormedAddGroupHom · ·) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {M N : SemiNormedGrp.{u}} (f : Hom M N)
  body: ConcreteCategory.hom (C := SemiNormedGrp) f

中文:
缩写 态射.hom
  签名: {M N : SemiNormedGrp.{u}} (f : 态射 M N)
  定义体: ConcreteCategory.hom (C := SemiNormedGrp) f
-/
abbrev Hom.hom {M N : SemiNormedGrp.{u}} (f : Hom M N) :=
  ConcreteCategory.hom (C := SemiNormedGrp) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  body: ConcreteCategory.ofHom (C := SemiNormedGrp) f

中文:
缩写 ofHom
  签名: {M N : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  定义体: ConcreteCategory.ofHom (C := SemiNormedGrp) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, SemiNormedGrp
-/
abbrev ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) : of M ⟶ of N :=
  ConcreteCategory.ofHom (C := SemiNormedGrp) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (M N : SemiNormedGrp.{u}) (f : Hom M N)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (M N : SemiNormedGrp.{u}) (f : 态射 M N)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (M N : SemiNormedGrp.{u}) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : forall (x : M), f₁ x = f₂ x)
  statement: f₁ = f₂
  proof: ConcreteCategory.ext_apply h

@[simp]

中文:
引理 ext
  条件: {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : 对任意 (x : M), f₁ x = f₂ x)
  结论: f₁ = f₂
  证明: ConcreteCategory.ext_apply h

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext_apply, ext_apply
-/
lemma ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : forall (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {M : SemiNormedGrp}
  statement: (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M
  proof: rfl

中文:
引理 hom_id
  条件: {M : SemiNormedGrp}
  结论: (𝟙 M : M ⟶ M).hom = 赋范加群态射.id M
  证明: rfl
-/
lemma hom_id {M : SemiNormedGrp} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (M : SemiNormedGrp) (r : M)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (M : SemiNormedGrp) (r : M)
  证明: by simp

@[simp]
-/
lemma id_apply (M : SemiNormedGrp) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O)
  proof: rfl

中文:
引理 hom_comp
  条件: {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O)
  证明: rfl
-/
lemma hom_comp {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M)
  证明: by simp

@[ext]
-/
lemma comp_apply {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : SemiNormedGrp} {f g : M ⟶ N} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {M N : SemiNormedGrp} {f g : M ⟶ N} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {M N : SemiNormedGrp} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  statement: {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  结论: {M N : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  证明: rfl

@[simp]
-/
lemma hom_ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {M N : SemiNormedGrp} (f : M ⟶ N)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {M N : SemiNormedGrp} (f : M ⟶ N)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {M N : SemiNormedGrp} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {M : Type u} [SeminormedAddCommGroup M]
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {M : 类型u} [SeminormedAddComm群 M]
  证明: rfl

@[simp]
-/
lemma ofHom_id {M : Type u} [SeminormedAddCommGroup M] :
    ofHom (NormedAddGroupHom.id M) = 𝟙 (of M) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {M N O : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  证明: rfl
-/
lemma ofHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {M N : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  证明: rfl
-/
lemma ofHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (r : M) : ofHom f r = f r := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {M N : SemiNormedGrp} (e : M ≅ N) (r : M)
  statement: e.inv (e.hom r) = r
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {M N : SemiNormedGrp} (e : M ≅ N) (r : M)
  结论: e.inv (e.hom r) = r
  证明: by
  simp
-/
lemma inv_hom_apply {M N : SemiNormedGrp} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {M N : SemiNormedGrp} (e : M ≅ N) (s : N)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {M N : SemiNormedGrp} (e : M ≅ N) (s : N)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {M N : SemiNormedGrp} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (V : Type u) [SeminormedAddCommGroup V]
  statement: (SemiNormedGrp.of V : Type u) = V
  proof: rfl

中文:
定理 coe_of
  条件: (V : 类型u) [SeminormedAddComm群 V]
  结论: (SemiNormedGrp.of V : 类型u) = V
  证明: rfl
-/
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp.of V : Type u) = V :=
  rfl

/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: (V : SemiNormedGrp)
  statement: (𝟙 V : V -> V) = id
  proof: rfl

中文:
定理 coe_id
  条件: (V : SemiNormedGrp)
  结论: (𝟙 V : V -> V) = id
  证明: rfl
-/
theorem coe_id (V : SemiNormedGrp) : (𝟙 V : V -> V) = id :=
  rfl

/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

中文:
定理 coe_comp
  条件: {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl
-/
theorem coe_comp {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M -> K) = g ∘ f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited SemiNormedGrp
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 SemiNormedGrp
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited SemiNormedGrp :=
  ⟨of PUnit⟩

instance {M N : SemiNormedGrp} : Zero (M ⟶ N) where
  zero := ofHom 0

@[simp]
/--
theorem `hom_zero` / 定理 `hom_zero`

English:
theorem hom_zero
  given: {V W : SemiNormedGrp}
  statement: (0 : V ⟶ W).hom = 0
  proof: rfl

中文:
定理 hom_zero
  条件: {V W : SemiNormedGrp}
  结论: (0 : V ⟶ W).hom = 0
  证明: rfl
-/
theorem hom_zero {V W : SemiNormedGrp} : (0 : V ⟶ W).hom = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: {V W : SemiNormedGrp} (x : V)
  statement: (0 : V ⟶ W) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: {V W : SemiNormedGrp} (x : V)
  结论: (0 : V ⟶ W) x = 0
  证明: rfl
-/
theorem zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp

中文:
实例 :
  签名: Limits.有ZeroMorphisms.{u, u + 1} SemiNormedGrp
-/
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp where

/--
theorem `isZero_of_subsingleton` / 定理 `isZero_of_subsingleton`

English:
theorem isZero_of_subsingleton
  given: (V : SemiNormedGrp) [Subsingleton V]
  statement: Limits.IsZero V
  proof: by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

中文:
定理 isZero_of_subsingleton
  条件: (V : SemiNormedGrp) [子单例 V]
  结论: Limits.是零 V
  证明: by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

Depends on / 依赖: Subsingleton, Subsingleton.elim, map_zero
-/
theorem isZero_of_subsingleton (V : SemiNormedGrp) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

/--
Instance `hasZeroObject` / 实例 `hasZeroObject`

English:
instance hasZeroObject
  signature: : Limits.HasZeroObject SemiNormedGrp.{u}
  body: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

中文:
实例 hasZeroObject
  签名: : Limits.有ZeroObject SemiNormedGrp.{u}
  定义体: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

Depends on / 依赖: isZero_of_subsingleton
-/
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

/--
theorem `iso_isometry_of_normNoninc` / 定理 `iso_isometry_of_normNoninc`

English:
theorem iso_isometry_of_normNoninc
  statement: {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.hom.NormNoninc)
  proof: by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ <= ‖i.hom v‖ := h2 _

中文:
定理 iso_isometry_of_normNoninc
  结论: {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.hom.NormNoninc)
  证明: by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ <= ‖i.hom v‖ := h2 _

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, Iso.hom_inv_id, comp_apply, hom_inv_id, i.hom, i.inv, id_apply, isometry_of_norm, le_antisymm
-/
theorem iso_isometry_of_normNoninc {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.hom.NormNoninc)
    (h2 : i.inv.hom.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ <= ‖i.hom v‖ := h2 _

/--
Instance `Hom.add` / 实例 `Hom.add`

English:
instance Hom.add
  signature: {M N : SemiNormedGrp}
  body: ofHom (f.hom + g.hom)

@[simp]

中文:
实例 态射.add
  签名: {M N : SemiNormedGrp}
  定义体: ofHom (f.hom + g.hom)

@[simp]

Depends on / 依赖: f.hom, g.hom
-/
instance Hom.add {M N : SemiNormedGrp} : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

@[simp]
/--
theorem `hom_add` / 定理 `hom_add`

English:
theorem hom_add
  given: {V W : SemiNormedGrp} (f g : V ⟶ W)
  statement: (f + g).hom = f.hom + g.hom
  proof: rfl

中文:
定理 hom_add
  条件: {V W : SemiNormedGrp} (f g : V ⟶ W)
  结论: (f + g).hom = f.hom + g.hom
  证明: rfl
-/
theorem hom_add {V W : SemiNormedGrp} (f g : V ⟶ W) : (f + g).hom = f.hom + g.hom :=
  rfl

/--
Instance `Hom.neg` / 实例 `Hom.neg`

English:
instance Hom.neg
  signature: {M N : SemiNormedGrp}
  body: ofHom (- f.hom)

@[simp]

中文:
实例 态射.neg
  签名: {M N : SemiNormedGrp}
  定义体: ofHom (- f.hom)

@[simp]

Depends on / 依赖: f.hom
-/
instance Hom.neg {M N : SemiNormedGrp} : Neg (M ⟶ N) where
  neg f := ofHom (- f.hom)

@[simp]
/--
theorem `hom_neg` / 定理 `hom_neg`

English:
theorem hom_neg
  given: {V W : SemiNormedGrp} (f : V ⟶ W)
  statement: (-f).hom = -f.hom
  proof: rfl

中文:
定理 hom_neg
  条件: {V W : SemiNormedGrp} (f : V ⟶ W)
  结论: (-f).hom = -f.hom
  证明: rfl
-/
theorem hom_neg {V W : SemiNormedGrp} (f : V ⟶ W) : (-f).hom = -f.hom :=
  rfl

/--
Instance `Hom.sub` / 实例 `Hom.sub`

English:
instance Hom.sub
  signature: {M N : SemiNormedGrp}
  body: ofHom (f.hom - g.hom)

@[simp]

中文:
实例 态射.sub
  签名: {M N : SemiNormedGrp}
  定义体: ofHom (f.hom - g.hom)

@[simp]

Depends on / 依赖: f.hom, g.hom
-/
instance Hom.sub {M N : SemiNormedGrp} : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

@[simp]
/--
theorem `hom_sub` / 定理 `hom_sub`

English:
theorem hom_sub
  given: {V W : SemiNormedGrp} (f g : V ⟶ W)
  statement: (f - g).hom = f.hom - g.hom
  proof: rfl

中文:
定理 hom_sub
  条件: {V W : SemiNormedGrp} (f g : V ⟶ W)
  结论: (f - g).hom = f.hom - g.hom
  证明: rfl
-/
theorem hom_sub {V W : SemiNormedGrp} (f g : V ⟶ W) : (f - g).hom = f.hom - g.hom :=
  rfl

/--
Instance `Hom.nsmul` / 实例 `Hom.nsmul`

English:
instance Hom.nsmul
  signature: {M N : SemiNormedGrp}
  body: ofHom (n • f.hom)

@[simp]

中文:
实例 态射.nsmul
  签名: {M N : SemiNormedGrp}
  定义体: ofHom (n • f.hom)

@[simp]

Depends on / 依赖: f.hom
-/
instance Hom.nsmul {M N : SemiNormedGrp} : SMul Nat (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp]
/--
theorem `hom_nsum` / 定理 `hom_nsum`

English:
theorem hom_nsum
  given: {V W : SemiNormedGrp} (n : Nat) (f : V ⟶ W)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
定理 hom_nsum
  条件: {V W : SemiNormedGrp} (n : 自然数) (f : V ⟶ W)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
theorem hom_nsum {V W : SemiNormedGrp} (n : Nat) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl

/--
Instance `Hom.zsmul` / 实例 `Hom.zsmul`

English:
instance Hom.zsmul
  signature: {M N : SemiNormedGrp}
  body: ofHom (n • f.hom)

@[simp]

中文:
实例 态射.zsmul
  签名: {M N : SemiNormedGrp}
  定义体: ofHom (n • f.hom)

@[simp]

Depends on / 依赖: f.hom
-/
instance Hom.zsmul {M N : SemiNormedGrp} : SMul Int (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

@[simp]
/--
theorem `hom_zsum` / 定理 `hom_zsum`

English:
theorem hom_zsum
  given: {V W : SemiNormedGrp} (n : Int) (f : V ⟶ W)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
定理 hom_zsum
  条件: {V W : SemiNormedGrp} (n : 整数) (f : V ⟶ W)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
theorem hom_zsum {V W : SemiNormedGrp} (n : Int) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl

/--
Instance `Hom.addCommGroup` / 实例 `Hom.addCommGroup`

English:
instance Hom.addCommGroup
  signature: {V W : SemiNormedGrp}
  body: Function.Injective.addCommGroup _ ConcreteCategory.hom_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 态射.addCommGroup
  签名: {V W : SemiNormedGrp}
  定义体: Function.Injective.addCommGroup _ ConcreteCategory.hom_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_injective, Function, Function.Injective.addCommGroup, Injective, addCommGroup, hom_injective
-/
instance Hom.addCommGroup {V W : SemiNormedGrp} : AddCommGroup (V ⟶ W) :=
  Function.Injective.addCommGroup _ ConcreteCategory.hom_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end SemiNormedGrp

/--
Definition of `SemiNormedGrp₁` / `SemiNormedGrp₁` 的定义

English:
structure SemiNormedGrp₁
  parameters: : Type (u + 1) where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [str : SeminormedAddCommGroup carrier]

中文:
结构 SemiNormedGrp₁
  参数: : 类型 (u + 1) where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [str : SeminormedAddComm群 carrier]
-/
structure SemiNormedGrp₁ : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp₁` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp₁.str

namespace SemiNormedGrp₁

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort SemiNormedGrp₁ Type*
  body: X.carrier

中文:
实例 :
  签名: CoeSort SemiNormedGrp₁ 类型
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort SemiNormedGrp₁ Type* where
  coe X := X.carrier

/-- The type of morphisms in `SemiNormedGrp₁` -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (M N : SemiNormedGrp₁.{u})
  axioms and operations (2):
    - hom' : NormedAddGroupHom M N
    - normNoninc : hom'.NormNoninc

中文:
结构 态射
  参数: (M N : SemiNormedGrp₁.{u})
  公理与运算 (2 个):
    - hom' : 赋范加群态射 M N
    - normNoninc : hom'.NormNoninc
-/
structure Hom (M N : SemiNormedGrp₁.{u}) where
  /-- The underlying `NormedAddGroupHom`. -/
  hom' : NormedAddGroupHom M N
  normNoninc : hom'.NormNoninc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} SemiNormedGrp₁
  body: Hom
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {_ _ _} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

中文:
实例 :
  签名: 大范畴.{u} SemiNormedGrp₁
  定义体: Hom
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {_ _ _} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩
-/
instance : LargeCategory.{u} SemiNormedGrp₁ where
  Hom := Hom
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {_ _ _} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: (X Y : SemiNormedGrp₁)
  body: f.1.toFun
  coe_injective _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)

中文:
实例 instFunLike
  签名: (X Y : SemiNormedGrp₁)
  定义体: f.1.toFun
  coe_injective _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)
-/
instance instFunLike (X Y : SemiNormedGrp₁) :
    FunLike { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  coe f := f.1.toFun
  coe_injective _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory SemiNormedGrp₁
  body: ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

中文:
实例 :
  签名: 余ncrete范畴 SemiNormedGrp₁
  定义体: ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩
-/
instance : ConcreteCategory SemiNormedGrp₁
    fun X Y => { f : NormedAddGroupHom X Y // f.NormNoninc } where
  hom f := ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

instance (X Y : SemiNormedGrp₁) :
    AddMonoidHomClass { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  map_add f := map_add f.1
  map_zero f := map_zero f.1

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {M N : SemiNormedGrp₁.{u}} (f : Hom M N)
  body: ConcreteCategory.hom (C := SemiNormedGrp₁) f

中文:
缩写 态射.hom
  签名: {M N : SemiNormedGrp₁.{u}} (f : 态射 M N)
  定义体: ConcreteCategory.hom (C := SemiNormedGrp₁) f
-/
abbrev Hom.hom {M N : SemiNormedGrp₁.{u}} (f : Hom M N) :=
  ConcreteCategory.hom (C := SemiNormedGrp₁) f

/--
Definition of `mkHom` / `mkHom` 的定义

English:
abbreviation mkHom
  signature: {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  body: ConcreteCategory.ofHom ⟨f, i⟩

中文:
缩写 mkHom
  签名: {M N : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  定义体: ConcreteCategory.ofHom ⟨f, i⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) :
    SemiNormedGrp₁.of M ⟶ SemiNormedGrp₁.of N :=
  ConcreteCategory.ofHom ⟨f, i⟩

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (M N : SemiNormedGrp₁.{u}) (f : Hom M N)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (M N : SemiNormedGrp₁.{u}) (f : 态射 M N)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (M N : SemiNormedGrp₁.{u}) (f : Hom M N) : NormedAddGroupHom M N :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

instance (X Y : SemiNormedGrp₁) : CoeFun (X ⟶ Y) (fun _ => X -> Y) where
  coe f := f.hom.1

/--
theorem `mkHom_apply` / 定理 `mkHom_apply`

English:
theorem mkHom_apply
  statement: {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  proof: rfl

中文:
定理 mkHom_apply
  结论: {M N : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  证明: rfl
-/
theorem mkHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : forall (x : M), f₁ x = f₂ x)
  statement: f₁ = f₂
  proof: ConcreteCategory.ext_apply h

@[simp]

中文:
引理 ext
  条件: {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : 对任意 (x : M), f₁ x = f₂ x)
  结论: f₁ = f₂
  证明: ConcreteCategory.ext_apply h

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext_apply, ext_apply
-/
lemma ext {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : forall (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {M : SemiNormedGrp₁}
  statement: (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M
  proof: rfl

中文:
引理 hom_id
  条件: {M : SemiNormedGrp₁}
  结论: (𝟙 M : M ⟶ M).hom = 赋范加群态射.id M
  证明: rfl
-/
lemma hom_id {M : SemiNormedGrp₁} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (M : SemiNormedGrp₁) (r : M)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (M : SemiNormedGrp₁) (r : M)
  证明: by simp

@[simp]
-/
lemma id_apply (M : SemiNormedGrp₁) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O)
  proof: rfl

中文:
引理 hom_comp
  条件: {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O)
  证明: rfl
-/
lemma hom_comp {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom.1 = g.hom.1.comp f.hom.1 := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M)
  证明: by simp

@[ext]
-/
lemma comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext (congr_arg Subtype.val hf)

@[simp]

中文:
引理 hom_ext
  条件: {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext (congr_arg Subtype.val hf)

@[simp]

Depends on / 依赖: Hom.ext, Subtype, Subtype.val, congr_arg
-/
lemma hom_ext {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext (congr_arg Subtype.val hf)

@[simp]
/--
lemma `hom_mkHom` / 引理 `hom_mkHom`

English:
lemma hom_mkHom
  statement: {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  proof: rfl

@[simp]

中文:
引理 hom_mkHom
  结论: {M N : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  证明: rfl

@[simp]
-/
lemma hom_mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : f.NormNoninc) : (mkHom f hf).hom = f := rfl

@[simp]
/--
lemma `mkHom_hom` / 引理 `mkHom_hom`

English:
lemma mkHom_hom
  given: {M N : SemiNormedGrp₁} (f : M ⟶ N)
  proof: rfl

@[simp]

中文:
引理 mkHom_hom
  条件: {M N : SemiNormedGrp₁} (f : M ⟶ N)
  证明: rfl

@[simp]
-/
lemma mkHom_hom {M N : SemiNormedGrp₁} (f : M ⟶ N) :
    mkHom (Hom.hom f) f.normNoninc = f := rfl

@[simp]
/--
lemma `mkHom_id` / 引理 `mkHom_id`

English:
lemma mkHom_id
  given: {M : Type u} [SeminormedAddCommGroup M]
  proof: rfl

@[simp]

中文:
引理 mkHom_id
  条件: {M : 类型u} [SeminormedAddComm群 M]
  证明: rfl

@[simp]
-/
lemma mkHom_id {M : Type u} [SeminormedAddCommGroup M] :
    mkHom (NormedAddGroupHom.id M) NormedAddGroupHom.NormNoninc.id = 𝟙 (of M) := rfl

@[simp]
/--
lemma `mkHom_comp` / 引理 `mkHom_comp`

English:
lemma mkHom_comp
  statement: {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  proof: rfl

@[simp]

中文:
引理 mkHom_comp
  结论: {M N O : 类型u} [SeminormedAddComm群 M] [SeminormedAddComm群 N]
  证明: rfl

@[simp]
-/
lemma mkHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O)
    (hf : f.NormNoninc) (hg : g.NormNoninc) (hgf : (g.comp f).NormNoninc) :
    mkHom (g.comp f) hgf = mkHom f hf ≫ mkHom g hg :=
  rfl

@[simp]
/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {M N : SemiNormedGrp₁} (e : M ≅ N) (r : M)
  statement: e.inv (e.hom r) = r
  proof: by
  rw [← comp_apply]
  simp

@[simp]

中文:
引理 inv_hom_apply
  条件: {M N : SemiNormedGrp₁} (e : M ≅ N) (r : M)
  结论: e.inv (e.hom r) = r
  证明: by
  rw [← comp_apply]
  simp

@[simp]

Depends on / 依赖: comp_apply
-/
lemma inv_hom_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  rw [← comp_apply]
  simp

@[simp]
/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {M N : SemiNormedGrp₁} (e : M ≅ N) (s : N)
  statement: e.hom (e.inv s) = s
  proof: by
  rw [← comp_apply]
  simp

中文:
引理 hom_inv_apply
  条件: {M N : SemiNormedGrp₁} (e : M ≅ N) (s : N)
  结论: e.hom (e.inv s) = s
  证明: by
  rw [← comp_apply]
  simp

Depends on / 依赖: comp_apply
-/
lemma hom_inv_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp

instance (M : SemiNormedGrp₁) : SeminormedAddCommGroup M :=
  M.str

/-- Promote an isomorphism in `SemiNormedGrp` to an isomorphism in `SemiNormedGrp₁`. -/
@[simps]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.hom.NormNoninc) (i' : f.inv.hom.NormNoninc)
  body: mkHom f.hom.hom i
  inv := mkHom f.inv.hom i'

中文:
定义 mkIso
  签名: {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.hom.NormNoninc) (i' : f.inv.hom.NormNoninc)
  定义体: mkHom f.hom.hom i
  inv := mkHom f.inv.hom i'

Depends on / 依赖: f.hom.hom
-/
def mkIso {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.hom.NormNoninc) (i' : f.inv.hom.NormNoninc) :
    SemiNormedGrp₁.of M ≅ SemiNormedGrp₁.of N where
  hom := mkHom f.hom.hom i
  inv := mkHom f.inv.hom i'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ SemiNormedGrp₁ SemiNormedGrp
  body: { obj := fun X => SemiNormedGrp.of X
      map := fun f => SemiNormedGrp.ofHom f.1 }

中文:
实例 :
  签名: 有Forget₂ SemiNormedGrp₁ SemiNormedGrp
  定义体: { obj := fun X => SemiNormedGrp.of X
      map := fun f => SemiNormedGrp.ofHom f.1 }

Depends on / 依赖: SemiNormedGrp, SemiNormedGrp.of, SemiNormedGrp.ofHom
-/
instance : HasForget₂ SemiNormedGrp₁ SemiNormedGrp where
  forget₂ :=
    { obj := fun X => SemiNormedGrp.of X
      map := fun f => SemiNormedGrp.ofHom f.1 }

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (V : Type u) [SeminormedAddCommGroup V]
  statement: (SemiNormedGrp₁.of V : Type u) = V
  proof: rfl

中文:
定理 coe_of
  条件: (V : 类型u) [SeminormedAddComm群 V]
  结论: (SemiNormedGrp₁.of V : 类型u) = V
  证明: rfl
-/
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp₁.of V : Type u) = V :=
  rfl

/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: (V : SemiNormedGrp₁)
  statement: ⇑(𝟙 V) = id
  proof: rfl

中文:
定理 coe_id
  条件: (V : SemiNormedGrp₁)
  结论: ⇑(𝟙 V) = id
  证明: rfl
-/
theorem coe_id (V : SemiNormedGrp₁) : ⇑(𝟙 V) = id :=
  rfl

/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

中文:
定理 coe_comp
  条件: {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl
-/
theorem coe_comp {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M -> K) = g ∘ f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited SemiNormedGrp₁
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 SemiNormedGrp₁
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited SemiNormedGrp₁ :=
  ⟨of PUnit⟩

instance (X Y : SemiNormedGrp₁) : Zero (X ⟶ Y) where
  zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: {V W : SemiNormedGrp₁} (x : V)
  statement: (0 : V ⟶ W) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: {V W : SemiNormedGrp₁} (x : V)
  结论: (0 : V ⟶ W) x = 0
  证明: rfl
-/
theorem zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp₁

中文:
实例 :
  签名: Limits.有ZeroMorphisms.{u, u + 1} SemiNormedGrp₁
-/
instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp₁ where

/--
theorem `isZero_of_subsingleton` / 定理 `isZero_of_subsingleton`

English:
theorem isZero_of_subsingleton
  given: (V : SemiNormedGrp₁) [Subsingleton V]
  statement: Limits.IsZero V
  proof: by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

中文:
定理 isZero_of_subsingleton
  条件: (V : SemiNormedGrp₁) [子单例 V]
  结论: Limits.是零 V
  证明: by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

Depends on / 依赖: Subsingleton, Subsingleton.elim, map_zero
-/
theorem isZero_of_subsingleton (V : SemiNormedGrp₁) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

/--
Instance `hasZeroObject` / 实例 `hasZeroObject`

English:
instance hasZeroObject
  signature: : Limits.HasZeroObject SemiNormedGrp₁.{u}
  body: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

中文:
实例 hasZeroObject
  签名: : Limits.有ZeroObject SemiNormedGrp₁.{u}
  定义体: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

Depends on / 依赖: isZero_of_subsingleton
-/
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

/--
theorem `iso_isometry` / 定理 `iso_isometry`

English:
theorem iso_isometry
  given: {V W : SemiNormedGrp₁} (i : V ≅ W)
  statement: Isometry i.hom
  proof: by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V ->+ W)
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ <= ‖i.hom v‖ := i.inv.2 _

中文:
定理 iso_isometry
  条件: {V W : SemiNormedGrp₁} (i : V ≅ W)
  结论: 等距 i.hom
  证明: by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V ->+ W)
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ <= ‖i.hom v‖ := i.inv.2 _

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, Iso.hom_inv_id, Isometry, comp_apply, hom_inv_id, i.hom, i.inv, id_apply, isometry_of_norm, le_antisymm, map_add, map_zero
-/
theorem iso_isometry {V W : SemiNormedGrp₁} (i : V ≅ W) : Isometry i.hom := by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V ->+ W)
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ <= ‖i.hom v‖ := i.inv.2 _

end SemiNormedGrp₁
