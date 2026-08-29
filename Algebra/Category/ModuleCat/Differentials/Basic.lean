/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# The differentials of a morphism in the category of commutative rings

In this file, given a morphism `f : A ⟶ B` in the category `CommRingCat`,
and `M : ModuleCat B`, we define the type `M.Derivation f` of
derivations with values in `M` relative to `f`.
We also construct the module of differentials
`CommRingCat.KaehlerDifferential f : ModuleCat B` and the corresponding derivation.

-/

@[expose] public section

universe v u

open CategoryTheory

attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid

namespace ModuleCat

variable {A B : CommRingCat.{u}} (M : ModuleCat.{v} B) (f : A ⟶ B)

/--
Definition of `Derivation` / `Derivation` 的定义

English:
definition Derivation
  signature: : Type _
  body: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation A B M

中文:
定义 导子
  签名: : 类型 _
  定义体: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation A B M

Depends on / 依赖: Derivation, Module, Module.compHom, _root_, _root_.Derivation, compHom, f.hom, f.hom.toAlgebra, toAlgebra
-/
def Derivation : Type _ :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation A B M

namespace Derivation

variable {M f}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (d : B -> M) (d_add : forall (b b' : B), d (b + b') = d b + d b' := by simp)
  body: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  { toFun := d
    map_add' := d_add
    map_smul' := fun a b => by
      dsimp
      rw [RingHom.smul_toAlgebra]; rw [d_mul]; rw [d_map]; rw [smul_zero]; rw [add_zero]
      rfl
    map_one_eq_zero' := by
      dsimp
      rw [← f.hom.map_one]; rw [d_map]
    leibniz' := d_mul }

中文:
定义 mk
  签名: (d : B -> M) (d_add : 对任意 (b b' : B), d (b + b') = d b + d b' := by simp)
  定义体: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  { toFun := d
    map_add' := d_add
    map_smul' := fun a b => by
      dsimp
      rw [RingHom.smul_toAlgebra]; rw [d_mul]; rw [d_map]; rw [smul_zero]; rw [add_zero]
      rfl
    map_one_eq_zero' := by
      dsimp
      rw [← f.hom.map_one]; rw [d_map]
    leibniz' := d_mul }

Depends on / 依赖: Derivation, M.Derivation, Module, Module.compHom, RingHom, RingHom.smul_toAlgebra, add_zero, compHom, d_add, d_map, d_mul, f.hom, f.hom.map_one, f.hom.toAlgebra, leibniz, map_add, map_one, map_one_eq_zero, map_smul, smul_toAlgebra
-/
def mk (d : B -> M) (d_add : forall (b b' : B), d (b + b') = d b + d b' := by simp)
    (d_mul : forall (b b' : B), d (b * b') = b • d b' + b' • d b := by simp)
    (d_map : forall (a : A), d (f a) = 0 := by simp) :
    M.Derivation f :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  { toFun := d
    map_add' := d_add
    map_smul' := fun a b => by
      dsimp
      rw [RingHom.smul_toAlgebra]; rw [d_mul]; rw [d_map]; rw [smul_zero]; rw [add_zero]
      rfl
    map_one_eq_zero' := by
      dsimp
      rw [← f.hom.map_one]; rw [d_map]
    leibniz' := d_mul }

variable (D : M.Derivation f)

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: (b : B)
  body: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation.toLinearMap D b

@[simp]

中文:
定义 d
  签名: (b : B)
  定义体: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation.toLinearMap D b

@[simp]

Depends on / 依赖: Derivation, Module, Module.compHom, _root_, _root_.Derivation.toLinearMap, compHom, f.hom, f.hom.toAlgebra, toAlgebra, toLinearMap
-/
def d (b : B) : M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation.toLinearMap D b

@[simp]
/--
lemma `d_add` / 引理 `d_add`

English:
lemma d_add
  given: (b b' : B)
  statement: D.d (b + b') = D.d b + D.d b'
  proof: by simp [d]

中文:
引理 d_add
  条件: (b b' : B)
  结论: D.d (b + b') = D.d b + D.d b'
  证明: by simp [d]
-/
lemma d_add (b b' : B) : D.d (b + b') = D.d b + D.d b' := by simp [d]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `d_mul` / 引理 `d_mul`

English:
lemma d_mul
  given: (b b' : B)
  statement: D.d (b * b') = b • D.d b' + b' • D.d b
  proof: by simp [d]

@[simp]

中文:
引理 d_mul
  条件: (b b' : B)
  结论: D.d (b * b') = b • D.d b' + b' • D.d b
  证明: by simp [d]

@[simp]
-/
lemma d_mul (b b' : B) : D.d (b * b') = b • D.d b' + b' • D.d b := by simp [d]

@[simp]
/--
lemma `d_map` / 引理 `d_map`

English:
lemma d_map
  given: (a : A)
  statement: D.d (f a) = 0
  proof: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  D.map_algebraMap a

中文:
引理 d_map
  条件: (a : A)
  结论: D.d (f a) = 0
  证明: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  D.map_algebraMap a

Depends on / 依赖: D.map_algebraMap, Module, Module.compHom, compHom, f.hom, f.hom.toAlgebra, map_algebraMap, toAlgebra
-/
lemma d_map (a : A) : D.d (f a) = 0 :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  D.map_algebraMap a

end Derivation

end ModuleCat

namespace CommRingCat

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')

variable (f) in
/--
Definition of `KaehlerDifferential` / `KaehlerDifferential` 的定义

English:
definition KaehlerDifferential
  signature: : ModuleCat.{u} B
  body: letI := f.hom.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)

中文:
定义 KaehlerDifferential
  签名: : 模范畴.{u} B
  定义体: letI := f.hom.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)

Depends on / 依赖: KaehlerDifferential, ModuleCat, ModuleCat.of, _root_, _root_.KaehlerDifferential, f.hom.toAlgebra, toAlgebra
-/
noncomputable def KaehlerDifferential : ModuleCat.{u} B :=
  letI := f.hom.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)

namespace KaehlerDifferential

set_option backward.isDefEq.respectTransparency false in
variable (f) in
/--
Definition of `D` / `D` 的定义

English:
definition D
  signature: : (KaehlerDifferential f).Derivation f
  body: letI := f.hom.toAlgebra
  ModuleCat.Derivation.mk
    (fun b => _root_.KaehlerDifferential.D A B b) (by simp) (by simp)
      (_root_.KaehlerDifferential.D A B).map_algebraMap

中文:
定义 D
  签名: : (KaehlerDifferential f).导子 f
  定义体: letI := f.hom.toAlgebra
  ModuleCat.Derivation.mk
    (fun b => _root_.KaehlerDifferential.D A B b) (by simp) (by simp)
      (_root_.KaehlerDifferential.D A B).map_algebraMap

Depends on / 依赖: Derivation, KaehlerDifferential, ModuleCat, ModuleCat.Derivation.mk, _root_, _root_.KaehlerDifferential.D, f.hom.toAlgebra, map_algebraMap, toAlgebra
-/
noncomputable def D : (KaehlerDifferential f).Derivation f :=
  letI := f.hom.toAlgebra
  ModuleCat.Derivation.mk
    (fun b => _root_.KaehlerDifferential.D A B b) (by simp) (by simp)
      (_root_.KaehlerDifferential.D A B).map_algebraMap

/--
Definition of `d` / `d` 的定义

English:
abbreviation d
  signature: (b : B)
  body: (D f).d b

中文:
缩写 d
  签名: (b : B)
  定义体: (D f).d b
-/
noncomputable abbrev d (b : B) : KaehlerDifferential f := (D f).d b

set_option backward.isDefEq.respectTransparency false in
@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
  proof: by
  rw [← sub_eq_zero]
  have : ⊤ <= LinearMap.ker (α - β).hom := by
    rw [← KaehlerDifferential.span_range_derivation]; rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe]; rw [LinearMap.mem_ker]; rw [ModuleCat.hom_sub]; rw [LinearMap.sub_apply]; rw [sub_eq_zero]
    apply h
  rw [top_le_iff]; rw [LinearMap.ker_eq_top] at this
  ext : 1
  exact this

中文:
引理 ext
  结论: {M : 模范畴 B} {α β : KaehlerDifferential f ⟶ M}
  证明: by
  rw [← sub_eq_zero]
  have : ⊤ <= LinearMap.ker (α - β).hom := by
    rw [← KaehlerDifferential.span_range_derivation]; rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe]; rw [LinearMap.mem_ker]; rw [ModuleCat.hom_sub]; rw [LinearMap.sub_apply]; rw [sub_eq_zero]
    apply h
  rw [top_le_iff]; rw [LinearMap.ker_eq_top] at this
  ext : 1
  exact this

Depends on / 依赖: KaehlerDifferential, KaehlerDifferential.span_range_derivation, LinearMap, LinearMap.ker, LinearMap.ker_eq_top, LinearMap.mem_ker, LinearMap.sub_apply, ModuleCat, ModuleCat.hom_sub, SetLike, SetLike.mem_coe, Submodule, Submodule.span_le, hom_sub, ker_eq_top, mem_coe, mem_ker, span_le, span_range_derivation, sub_apply
-/
lemma ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
    (h : forall (b : B), α (d b) = β (d b)) : α = β := by
  rw [← sub_eq_zero]
  have : ⊤ <= LinearMap.ker (α - β).hom := by
    rw [← KaehlerDifferential.span_range_derivation]; rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe]; rw [LinearMap.mem_ker]; rw [ModuleCat.hom_sub]; rw [LinearMap.sub_apply]; rw [sub_eq_zero]
    apply h
  rw [top_le_iff]; rw [LinearMap.ker_eq_top] at this
  ext : 1
  exact this

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: :
  body: letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := g'.hom.toAlgebra
  letI := (g ≫ f').hom.toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f'))
  { toFun := fun x => _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }

@[simp]

中文:
定义 map
  签名: :
  定义体: letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := g'.hom.toAlgebra
  letI := (g ≫ f').hom.toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f'))
  { toFun := fun x => _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }

@[simp]

Depends on / 依赖: Hom.hom, IsScalarTower, IsScalarTower.of_algebraMap_eq, f.hom.toAlgebra, g.hom.toAlgebra, hom.toAlgebra, of_algebraMap_eq, toAlgebra
-/
noncomputable def map :
    KaehlerDifferential f ⟶
      (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f') :=
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := g'.hom.toAlgebra
  letI := (g ≫ f').hom.toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f'))
  { toFun := fun x => _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }

@[simp]
/--
lemma `map_d` / 引理 `map_d`

English:
lemma map_d
  given: (b : B)
  statement: map fac (d b) = d (g' b)
  proof: by
  algebraize [f.hom, f'.hom, g.hom, g'.hom, f'.hom.comp g.hom]
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  exact _root_.KaehlerDifferential.map_D A A' B B' b

中文:
引理 map_d
  条件: (b : B)
  结论: map fac (d b) = d (g' b)
  证明: by
  algebraize [f.hom, f'.hom, g.hom, g'.hom, f'.hom.comp g.hom]
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  exact _root_.KaehlerDifferential.map_D A A' B B' b

Depends on / 依赖: Hom.hom, IsScalarTower, IsScalarTower.of_algebraMap_eq, KaehlerDifferential, _root_, _root_.KaehlerDifferential.map_D, algebraize, f.hom, g.hom, hom.comp, map_D, of_algebraMap_eq
-/
lemma map_d (b : B) : map fac (d b) = d (g' b) := by
  algebraize [f.hom, f'.hom, g.hom, g'.hom, f'.hom.comp g.hom]
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  exact _root_.KaehlerDifferential.map_D A A' B B' b

end KaehlerDifferential

end CommRingCat

namespace ModuleCat.Derivation

variable {A B : CommRingCat.{u}} {f : A ⟶ B}
  {M : ModuleCat.{u} B} (D : M.Derivation f)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: : CommRingCat.KaehlerDifferential f ⟶ M
  body: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  ofHom D.liftKaehlerDifferential

中文:
定义 desc
  签名: : 交换环范畴.KaehlerDifferential f ⟶ M
  定义体: letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  ofHom D.liftKaehlerDifferential

Depends on / 依赖: D.liftKaehlerDifferential, Module, Module.compHom, compHom, f.hom, f.hom.toAlgebra, liftKaehlerDifferential, toAlgebra
-/
noncomputable def desc : CommRingCat.KaehlerDifferential f ⟶ M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  ofHom D.liftKaehlerDifferential

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `desc_d` / 引理 `desc_d`

English:
lemma desc_d
  given: (b : B)
  statement: D.desc (CommRingCat.KaehlerDifferential.d b) = D.d b
  proof: by
  let := f.hom.toAlgebra
  let := Module.compHom M f.hom
  apply D.liftKaehlerDifferential_comp_D

中文:
引理 desc_d
  条件: (b : B)
  结论: D.desc (交换环范畴.KaehlerDifferential.d b) = D.d b
  证明: by
  let := f.hom.toAlgebra
  let := Module.compHom M f.hom
  apply D.liftKaehlerDifferential_comp_D

Depends on / 依赖: D.liftKaehlerDifferential_comp_D, Module, Module.compHom, compHom, f.hom, f.hom.toAlgebra, liftKaehlerDifferential_comp_D, toAlgebra
-/
lemma desc_d (b : B) : D.desc (CommRingCat.KaehlerDifferential.d b) = D.d b := by
  let := f.hom.toAlgebra
  let := Module.compHom M f.hom
  apply D.liftKaehlerDifferential_comp_D

end ModuleCat.Derivation
