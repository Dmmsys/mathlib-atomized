/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The exterior powers as functors on the category of modules

In this file, given `M : ModuleCat R` and `n : ℕ`, we define `M.exteriorPower n : ModuleCat R`,
and this extends to a functor `ModuleCat.exteriorPower.functor : ModuleCat R ⥤ ModuleCat R`.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/--
Definition of `exteriorPower` / `exteriorPower` 的定义

English:
definition exteriorPower
  signature: (M : ModuleCat.{v} R) (n : Nat)
  body: ModuleCat.of R (⋀[R]^n M)

中文:
定义 exteriorPower
  签名: (M : ModuleCat.{v} R) (n : 自然数)
  定义体: ModuleCat.of R (⋀[R]^n M)

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
def exteriorPower (M : ModuleCat.{v} R) (n : Nat) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n M)

-- this could be an abbrev, but using a def eases automation
/--
Definition of `AlternatingMap` / `AlternatingMap` 的定义

English:
definition AlternatingMap
  signature: (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : Nat)
  body: _root_.AlternatingMap R M N (Fin n)

中文:
定义 AlternatingMap
  签名: (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : 自然数)
  定义体: _root_.AlternatingMap R M N (Fin n)

Depends on / 依赖: AlternatingMap, _root_, _root_.AlternatingMap
-/
def AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : Nat) :=
  _root_.AlternatingMap R M N (Fin n)

instance (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : Nat) :
    FunLike (M.AlternatingMap N n) (Fin n -> M) N :=
  inferInstanceAs (FunLike (M [⋀^(Fin n)]->ₗ[R] N) (Fin n -> M) N)

namespace AlternatingMap

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : Nat}

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {φ φ' : M.AlternatingMap N n} (h : forall (x : Fin n -> M), φ x = φ' x)
  proof: _root_.AlternatingMap.ext h

中文:
引理 ext
  条件: {φ φ' : M.AlternatingMap N n} (h : 对任意 (x : Fin n -> M), φ x = φ' x)
  证明: _root_.AlternatingMap.ext h

Depends on / 依赖: AlternatingMap, _root_, _root_.AlternatingMap.ext
-/
lemma ext {φ φ' : M.AlternatingMap N n} (h : forall (x : Fin n -> M), φ x = φ' x) :
    φ = φ' :=
  _root_.AlternatingMap.ext h

variable (φ : M.AlternatingMap N n) {N' : ModuleCat.{max u v} R} (g : N ⟶ N')

/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: : M.AlternatingMap N' n
  body: g.hom.compAlternatingMap φ

@[simp]

中文:
定义 postcomp
  签名: : M.AlternatingMap N' n
  定义体: g.hom.compAlternatingMap φ

@[simp]

Depends on / 依赖: compAlternatingMap, g.hom.compAlternatingMap
-/
def postcomp : M.AlternatingMap N' n :=
  g.hom.compAlternatingMap φ

@[simp]
/--
lemma `postcomp_apply` / 引理 `postcomp_apply`

English:
lemma postcomp_apply
  given: (x : Fin n -> M)
  proof: rfl

中文:
引理 postcomp_apply
  条件: (x : Fin n -> M)
  证明: rfl
-/
lemma postcomp_apply (x : Fin n -> M) :
    φ.postcomp g x = g (φ x) := rfl

end AlternatingMap

namespace exteriorPower

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {M : ModuleCat.{v} R} {n : Nat}
  body: exteriorPower.ιMulti _ _

@[ext]

中文:
定义 mk
  签名: {M : ModuleCat.{v} R} {n : 自然数}
  定义体: exteriorPower.ιMulti _ _

@[ext]

Depends on / 依赖: exteriorPower
-/
def mk {M : ModuleCat.{v} R} {n : Nat} :
    M.AlternatingMap (M.exteriorPower n) n :=
  exteriorPower.ιMulti _ _

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : Nat}
  proof: by
  ext : 1
  exact exteriorPower.linearMap_ext h

中文:
引理 hom_ext
  结论: {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : 自然数}
  证明: by
  ext : 1
  exact exteriorPower.linearMap_ext h

Depends on / 依赖: exteriorPower, exteriorPower.linearMap_ext, linearMap_ext
-/
lemma hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : Nat}
    {f g : M.exteriorPower n ⟶ N}
    (h : mk.postcomp f = mk.postcomp g) : f = g := by
  ext : 1
  exact exteriorPower.linearMap_ext h

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: {M : ModuleCat.{v} R} {n : Nat} {N : ModuleCat.{max u v} R}
  body: ofHom (exteriorPower.alternatingMapLinearEquiv φ)

@[simp]

中文:
定义 desc
  签名: {M : ModuleCat.{v} R} {n : 自然数} {N : ModuleCat.{max u v} R}
  定义体: ofHom (exteriorPower.alternatingMapLinearEquiv φ)

@[simp]

Depends on / 依赖: alternatingMapLinearEquiv, exteriorPower, exteriorPower.alternatingMapLinearEquiv
-/
noncomputable def desc {M : ModuleCat.{v} R} {n : Nat} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) : M.exteriorPower n ⟶ N :=
  ofHom (exteriorPower.alternatingMapLinearEquiv φ)

@[simp]
/--
lemma `desc_mk` / 引理 `desc_mk`

English:
lemma desc_mk
  statement: {M : ModuleCat.{v} R} {n : Nat} {N : ModuleCat.{max u v} R}
  proof: by
  apply exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

中文:
引理 desc_mk
  结论: {M : ModuleCat.{v} R} {n : 自然数} {N : ModuleCat.{max u v} R}
  证明: by
  apply exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

Depends on / 依赖: exteriorPower, exteriorPower.alternatingMapLinearEquiv_apply_
-/
lemma desc_mk {M : ModuleCat.{v} R} {n : Nat} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) (x : Fin n -> M) :
    desc φ (mk x) = φ x := by
  apply exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : Nat)
  body: ofHom (_root_.exteriorPower.map n f.hom)

@[simp]

中文:
定义 map
  签名: {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : 自然数)
  定义体: ofHom (_root_.exteriorPower.map n f.hom)

@[simp]

Depends on / 依赖: _root_, _root_.exteriorPower.map, exteriorPower, f.hom
-/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : Nat) :
    M.exteriorPower n ⟶ N.exteriorPower n :=
  ofHom (_root_.exteriorPower.map n f.hom)

@[simp]
/--
lemma `map_mk` / 引理 `map_mk`

English:
lemma map_mk
  given: {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : Nat} (x : Fin n -> M)
  proof: by
  apply exteriorPower.map_apply_ιMulti

中文:
引理 map_mk
  条件: {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : 自然数} (x : Fin n -> M)
  证明: by
  apply exteriorPower.map_apply_ιMulti

Depends on / 依赖: exteriorPower, exteriorPower.map_apply_
-/
lemma map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : Nat} (x : Fin n -> M) :
    map f n (mk x) = mk (f ∘ x) := by
  apply exteriorPower.map_apply_ιMulti

variable (R) in
/-- The functor `ModuleCat R ⥤ ModuleCat R` which sends a module to its
`n`th exterior power. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: (n : Nat)
  body: M.exteriorPower n
  map f := map f n

中文:
定义 functor
  签名: (n : 自然数)
  定义体: M.exteriorPower n
  map f := map f n

Depends on / 依赖: M.exteriorPower, exteriorPower
-/
noncomputable def functor (n : Nat) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.exteriorPower n
  map f := map f n

/--
Definition of `iso₀` / `iso₀` 的定义

English:
definition iso₀
  signature: (M : ModuleCat.{u} R)
  body: (exteriorPower.zeroEquiv R M).toModuleIso

@[simp]

中文:
定义 iso₀
  签名: (M : ModuleCat.{u} R)
  定义体: (exteriorPower.zeroEquiv R M).toModuleIso

@[simp]

Depends on / 依赖: exteriorPower, exteriorPower.zeroEquiv, toModuleIso, zeroEquiv
-/
noncomputable def iso₀ (M : ModuleCat.{u} R) : M.exteriorPower 0 ≅ ModuleCat.of R R :=
  (exteriorPower.zeroEquiv R M).toModuleIso

@[simp]
/--
lemma `iso₀_hom_apply` / 引理 `iso₀_hom_apply`

English:
lemma iso₀_hom_apply
  given: {M : ModuleCat.{u} R} (f : Fin 0 -> M)
  proof: exteriorPower.zeroEquiv_ιMulti _

@[reassoc (attr := simp)]

中文:
引理 iso₀_hom_apply
  条件: {M : ModuleCat.{u} R} (f : Fin 0 -> M)
  证明: exteriorPower.zeroEquiv_ιMulti _

@[reassoc (attr := simp)]

Depends on / 依赖: exteriorPower, exteriorPower.zeroEquiv_
-/
lemma iso₀_hom_apply {M : ModuleCat.{u} R} (f : Fin 0 -> M) :
    (iso₀ M).hom (mk f) = 1 :=
  exteriorPower.zeroEquiv_ιMulti _

@[reassoc (attr := simp)]
/--
lemma `iso₀_hom_naturality` / 引理 `iso₀_hom_naturality`

English:
lemma iso₀_hom_naturality
  given: {M N : ModuleCat.{u} R} (f : M ⟶ N)
  proof: ModuleCat.hom_ext (exteriorPower.zeroEquiv_naturality f.hom)

中文:
引理 iso₀_hom_naturality
  条件: {M N : ModuleCat.{u} R} (f : M ⟶ N)
  证明: ModuleCat.hom_ext (exteriorPower.zeroEquiv_naturality f.hom)

Depends on / 依赖: ModuleCat, ModuleCat.hom_ext, exteriorPower, exteriorPower.zeroEquiv_naturality, f.hom, hom_ext, zeroEquiv_naturality
-/
lemma iso₀_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 0 ≫ (iso₀ N).hom = (iso₀ M).hom :=
  ModuleCat.hom_ext (exteriorPower.zeroEquiv_naturality f.hom)

/--
Definition of `iso₁` / `iso₁` 的定义

English:
definition iso₁
  signature: (M : ModuleCat.{u} R)
  body: (exteriorPower.oneEquiv R M).toModuleIso

@[simp]

中文:
定义 iso₁
  签名: (M : ModuleCat.{u} R)
  定义体: (exteriorPower.oneEquiv R M).toModuleIso

@[simp]

Depends on / 依赖: exteriorPower, exteriorPower.oneEquiv, oneEquiv, toModuleIso
-/
noncomputable def iso₁ (M : ModuleCat.{u} R) : M.exteriorPower 1 ≅ M :=
  (exteriorPower.oneEquiv R M).toModuleIso

@[simp]
/--
lemma `iso₁_hom_apply` / 引理 `iso₁_hom_apply`

English:
lemma iso₁_hom_apply
  given: {M : ModuleCat.{u} R} (f : Fin 1 -> M)
  proof: exteriorPower.oneEquiv_ιMulti _

@[reassoc (attr := simp)]

中文:
引理 iso₁_hom_apply
  条件: {M : ModuleCat.{u} R} (f : Fin 1 -> M)
  证明: exteriorPower.oneEquiv_ιMulti _

@[reassoc (attr := simp)]

Depends on / 依赖: exteriorPower, exteriorPower.oneEquiv_
-/
lemma iso₁_hom_apply {M : ModuleCat.{u} R} (f : Fin 1 -> M) :
    (iso₁ M).hom (mk f) = f 0 :=
  exteriorPower.oneEquiv_ιMulti _

@[reassoc (attr := simp)]
/--
lemma `iso₁_hom_naturality` / 引理 `iso₁_hom_naturality`

English:
lemma iso₁_hom_naturality
  given: {M N : ModuleCat.{u} R} (f : M ⟶ N)
  proof: ModuleCat.hom_ext (exteriorPower.oneEquiv_naturality f.hom)

中文:
引理 iso₁_hom_naturality
  条件: {M N : ModuleCat.{u} R} (f : M ⟶ N)
  证明: ModuleCat.hom_ext (exteriorPower.oneEquiv_naturality f.hom)

Depends on / 依赖: ModuleCat, ModuleCat.hom_ext, exteriorPower, exteriorPower.oneEquiv_naturality, f.hom, hom_ext, oneEquiv_naturality
-/
lemma iso₁_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    map f 1 ≫ (iso₁ N).hom = (iso₁ M).hom ≫ f :=
  ModuleCat.hom_ext (exteriorPower.oneEquiv_naturality f.hom)

variable (R)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `natIso₀` / `natIso₀` 的定义

English:
definition natIso₀
  signature: : functor.{u} R 0 ≅ (Functor.const _).obj (ModuleCat.of R R)
  body: NatIso.ofComponents iso₀

中文:
定义 natIso₀
  签名: : functor.{u} R 0 ≅ (Functor.const _).obj (ModuleCat.of R R)
  定义体: NatIso.ofComponents iso₀

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def natIso₀ : functor.{u} R 0 ≅ (Functor.const _).obj (ModuleCat.of R R) :=
  NatIso.ofComponents iso₀

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `natIso₁` / `natIso₁` 的定义

English:
definition natIso₁
  signature: : functor.{u} R 1 ≅ 𝟭 _
  body: NatIso.ofComponents iso₁

中文:
定义 natIso₁
  签名: : functor.{u} R 1 ≅ 𝟭 _
  定义体: NatIso.ofComponents iso₁

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def natIso₁ : functor.{u} R 1 ≅ 𝟭 _ :=
  NatIso.ofComponents iso₁

end exteriorPower

end ModuleCat
