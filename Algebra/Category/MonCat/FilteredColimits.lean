/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Algebra.Category.MonCat.Basic

/-!
# The forgetful functor from (commutative) (additive) monoids preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ MonCat`.
We then construct a monoid structure on the colimit of `F ⋙ forget MonCat` (in `Type`), thereby
showing that the forgetful functor `forget MonCat` preserves filtered colimits. Similarly for
`AddMonCat`, `CommMonCat` and `AddCommMonCat`.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max -> max' -- avoid name collision with `_root_.max`.

namespace MonCat.FilteredColimits

section

-- Porting note: mathlib 3 used `parameters` here, mainly so we can have the abbreviations `M` and
-- `M.mk` below, without passing around `F` all the time.
variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

/-- The colimit of `F ⋙ forget MonCat` in the category of types.
In the following, we will construct a monoid structure on `M`.
-/
@[to_additive
      /-- The colimit of `F ⋙ forget AddMon` in the category of types.
      In the following, we will construct an additive monoid structure on `M`. -/]
/--
Definition of `M` / `M` 的定义

English:
abbreviation M
  body: (F ⋙ forget MonCat).ColimitType

中文:
缩写 M
  定义体: (F ⋙ forget MonCat).ColimitType

Depends on / 依赖: ColimitType, MonCat, forget
-/
abbrev M := (F ⋙ forget MonCat).ColimitType

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive /-- The canonical projection into the colimit, as a quotient type. -/]
/--
Definition of `M.mk` / `M.mk` 的定义

English:
abbreviation M.mk
  signature: : (Σ j, F.obj j) -> M.{v, u} F
  body: fun x => (F ⋙ forget MonCat).ιColimitType x.1 x.2

@[to_additive]

中文:
缩写 M.mk
  签名: : (Σ j, F.obj j) -> M.{v, u} F
  定义体: fun x => (F ⋙ forget MonCat).ιColimitType x.1 x.2

@[to_additive]
-/
noncomputable abbrev M.mk : (Σ j, F.obj j) -> M.{v, u} F :=
  fun x => (F ⋙ forget MonCat).ιColimitType x.1 x.2

@[to_additive]
/--
lemma `M.mk_surjective` / 引理 `M.mk_surjective`

English:
lemma M.mk_surjective
  given: (m : M.{v, u} F)
  proof: (F ⋙ forget MonCat).ιColimitType_jointly_surjective m

@[to_additive]

中文:
引理 M.mk_surjective
  条件: (m : M.{v, u} F)
  证明: (F ⋙ forget MonCat).ιColimitType_jointly_surjective m

@[to_additive]
-/
lemma M.mk_surjective (m : M.{v, u} F) :
    exists (j : J) (x : F.obj j), M.mk F ⟨j, x⟩ = m :=
  (F ⋙ forget MonCat).ιColimitType_jointly_surjective m

@[to_additive]
/--
theorem `M.mk_eq` / 定理 `M.mk_eq`

English:
theorem M.mk_eq
  statement: (x y : Σ j, F.obj j)
  proof: Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget MonCat) x y h)

@[to_additive]

中文:
定理 M.mk_eq
  结论: (x y : Σ j, F.obj j)
  证明: Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget MonCat) x y h)

@[to_additive]
-/
theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : exists (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    M.mk.{v, u} F x = M.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget MonCat) x y h)

@[to_additive]
/--
lemma `M.map_mk` / 引理 `M.map_mk`

English:
lemma M.map_mk
  given: {j k : J} (f : j ⟶ k) (x : F.obj j)
  proof: M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

中文:
引理 M.map_mk
  条件: {j k : J} (f : j ⟶ k) (x : F.obj j)
  证明: M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

Depends on / 依赖: M.mk_eq, mk_eq
-/
lemma M.map_mk {j k : J} (f : j ⟶ k) (x : F.obj j) :
    M.mk F ⟨k, F.map f x⟩ = M.mk F ⟨j, x⟩ :=
  M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

variable [IsFiltered J]

/-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to define the
"one" in the colimit as the equivalence class of `⟨j₀, 1 : F.obj j₀⟩`.
-/
@[to_additive
  /-- As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to
  define the "zero" in the colimit as the equivalence class of `⟨j₀, 0 : F.obj j₀⟩`. -/]
/--
Instance `colimitOne` / 实例 `colimitOne`

English:
instance colimitOne
  signature: : One (M.{v, u} F) where
  body: M.mk F ⟨IsFiltered.nonempty.some,1⟩

中文:
实例 colimitOne
  签名: : One (M.{v, u} F) where
  定义体: M.mk F ⟨IsFiltered.nonempty.some,1⟩

Depends on / 依赖: IsFiltered, IsFiltered.nonempty.some, M.mk, nonempty
-/
noncomputable instance colimitOne : One (M.{v, u} F) where
  one := M.mk F ⟨IsFiltered.nonempty.some,1⟩

/-- The definition of the "one" in the colimit is independent of the chosen object of `J`.
In particular, this lemma allows us to "unfold" the definition of `colimit_one` at a custom chosen
object `j`.
-/
@[to_additive
      /-- The definition of the "zero" in the colimit is independent of the chosen object
      of `J`. In particular, this lemma allows us to "unfold" the definition of `colimit_zero` at
      a custom chosen object `j`. -/]
/--
theorem `colimit_one_eq` / 定理 `colimit_one_eq`

English:
theorem colimit_one_eq
  given: (j : J)
  statement: (1 : M.{v, u} F) = M.mk F ⟨j, 1⟩
  proof: by
  apply M.mk_eq
  refine ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, ?_⟩
  simp

中文:
定理 colimit_one_eq
  条件: (j : J)
  结论: (1 : M.{v, u} F) = M.mk F ⟨j, 1⟩
  证明: by
  apply M.mk_eq
  refine ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, ?_⟩
  simp

Depends on / 依赖: IsFiltered, IsFiltered.leftToMax, IsFiltered.rightToMax, M.mk_eq, leftToMax, mk_eq, rightToMax
-/
theorem colimit_one_eq (j : J) : (1 : M.{v, u} F) = M.mk F ⟨j, 1⟩ := by
  apply M.mk_eq
  refine ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, ?_⟩
  simp

/-- The "unlifted" version of multiplication in the colimit. To multiply two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `IsFiltered.max`)
and multiply them there.
-/
@[to_additive
      /-- The "unlifted" version of addition in the colimit. To add two dependent pairs
      `⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂`
      (given by `IsFiltered.max`) and add them there. -/]
/--
Definition of `colimitMulAux` / `colimitMulAux` 的定义

English:
definition colimitMulAux
  signature: (x y : Σ j, F.obj j)
  body: M.mk F ⟨IsFiltered.max x.fst y.fst, F.map (IsFiltered.leftToMax x.1 y.1) x.2 *
    F.map (IsFiltered.rightToMax x.1 y.1) y.2⟩

中文:
定义 colimitMulAux
  签名: (x y : Σ j, F.obj j)
  定义体: M.mk F ⟨IsFiltered.max x.fst y.fst, F.map (IsFiltered.leftToMax x.1 y.1) x.2 *
    F.map (IsFiltered.rightToMax x.1 y.1) y.2⟩

Depends on / 依赖: F.map, IsFiltered, IsFiltered.leftToMax, IsFiltered.max, IsFiltered.rightToMax, M.mk, leftToMax, rightToMax, x.fst, y.fst
-/
noncomputable def colimitMulAux (x y : Σ j, F.obj j) : M.{v, u} F :=
  M.mk F ⟨IsFiltered.max x.fst y.fst, F.map (IsFiltered.leftToMax x.1 y.1) x.2 *
    F.map (IsFiltered.rightToMax x.1 y.1) y.2⟩

/-- Multiplication in the colimit is well-defined in the left argument. -/
@[to_additive /-- Addition in the colimit is well-defined in the left argument. -/]
/--
theorem `colimitMulAux_eq_of_rel_left` / 定理 `colimitMulAux_eq_of_rel_left`

English:
theorem colimitMulAux_eq_of_rel_left
  statement: {x x' y : Σ j, F.obj j}
  proof: by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  replace hfg : F.map f x = F.map g x' := by simpa
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃

中文:
定理 colimitMulAux_eq_of_rel_left
  结论: {x x' y : Σ j, F.obj j}
  证明: by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  replace hfg : F.map f x = F.map g x' := by simpa
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.map, F.map_comp, IsFiltered, IsFiltered.leftToMax, IsFiltered.rightToMax, IsFiltered.tulip, M.mk_eq, comp_apply, leftToMax, map_comp, map_mul, mk_eq, replace, rightToMax, simp_rw
-/
theorem colimitMulAux_eq_of_rel_left {x x' y : Σ j, F.obj j}
    (hxx' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) x x') :
    colimitMulAux.{v, u} F x y = colimitMulAux.{v, u} F x' y := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  replace hfg : F.map f x = F.map g x' := by simpa
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃ j₂) (IsFiltered.leftToMax j₃ j₂) f g
  apply M.mk_eq
  use s, α, γ
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

set_option backward.defeqAttrib.useBackward true in
/-- Multiplication in the colimit is well-defined in the right argument. -/
@[to_additive /-- Addition in the colimit is well-defined in the right argument. -/]
/--
theorem `colimitMulAux_eq_of_rel_right` / 定理 `colimitMulAux_eq_of_rel_right`

English:
theorem colimitMulAux_eq_of_rel_right
  statement: {x y y' : Σ j, F.obj j}
  proof: by
  obtain ⟨j₁, y⟩ := y; obtain ⟨j₂, x⟩ := x; obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (Is

中文:
定理 colimitMulAux_eq_of_rel_right
  结论: {x y y' : Σ j, F.obj j}
  证明: by
  obtain ⟨j₁, y⟩ := y; obtain ⟨j₂, x⟩ := x; obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (Is

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, F.map_comp, Functor, Functor.comp_map, Functor.comp_obj, IsFiltered, IsFiltered.leftToMax, IsFiltered.rightToMax, IsFiltered.tulip, M.mk_eq, TypeCat, TypeCat.Fun.coe_mk, coe_mk, comp_apply, comp_map, comp_obj, hom_ofHom, leftToMax, map_comp
-/
theorem colimitMulAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) y y') :
    colimitMulAux.{v, u} F x y = colimitMulAux.{v, u} F x y' := by
  obtain ⟨j₁, y⟩ := y; obtain ⟨j₂, x⟩ := x; obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply M.mk_eq
  use s, α, γ
  simp_rw [map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    comp_apply, hfg]

/-- Multiplication in the colimit. See also `colimitMulAux`. -/
@[to_additive /-- Addition in the colimit. See also `colimitAddAux`. -/]
/--
Instance `colimitMul` / 实例 `colimitMul`

English:
instance colimitMul
  signature: : Mul (M.{v, u} F)
  body: { mul := fun x y => by
    refine Quot.lift₂ (colimitMulAux F) ?_ ?_ x y
    · intro x y y' h
      apply colimitMulAux_eq_of_rel_right
      apply Types.FilteredColimit.rel_of_colimitTypeRel
      exact h
    · intro x x' y h
      apply colimitMulAux_eq_of_rel_left
      apply Types.FilteredColimi

中文:
实例 colimitMul
  签名: : Mul (M.{v, u} F)
  定义体: { mul := fun x y => by
    refine Quot.lift₂ (colimitMulAux F) ?_ ?_ x y
    · intro x y y' h
      apply colimitMulAux_eq_of_rel_right
      apply Types.FilteredColimit.rel_of_colimitTypeRel
      exact h
    · intro x x' y h
      apply colimitMulAux_eq_of_rel_left
      apply Types.FilteredColimi

Depends on / 依赖: FilteredColimit, Quot.lift, Types.FilteredColimit.rel_of_colimitTypeRel, colimitMulAux, colimitMulAux_eq_of_rel_left, colimitMulAux_eq_of_rel_right, rel_of_colimitTypeRel
-/
noncomputable instance colimitMul : Mul (M.{v, u} F) :=
{ mul := fun x y => by
    refine Quot.lift₂ (colimitMulAux F) ?_ ?_ x y
    · intro x y y' h
      apply colimitMulAux_eq_of_rel_right
      apply Types.FilteredColimit.rel_of_colimitTypeRel
      exact h
    · intro x x' y h
      apply colimitMulAux_eq_of_rel_left
      apply Types.FilteredColimit.rel_of_colimitTypeRel
      exact h }

/-- Multiplication in the colimit is independent of the chosen "maximum" in the filtered category.
In particular, this lemma allows us to "unfold" the definition of the multiplication of `x` and `y`,
using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`.
-/
@[to_additive
      /-- Addition in the colimit is independent of the chosen "maximum" in the filtered
      category. In particular, this lemma allows us to "unfold" the definition of the addition of
      `x` and `y`, using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`. -/]
/--
theorem `colimit_mul_mk_eq` / 定理 `colimit_mul_mk_eq`

English:
theorem colimit_mul_mk_eq
  given: (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k)
  proof: by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  refine M.mk_eq F _ _ ?_
  use s, α, β
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

@[to_additive]

中文:
定理 colimit_mul_mk_eq
  条件: (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k)
  证明: by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  refine M.mk_eq F _ _ ?_
  use s, α, β
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

@[to_additive]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.map_comp, IsFiltered, IsFiltered.bowtie, IsFiltered.leftToMax, IsFiltered.rightToMax, M.mk_eq, bowtie, comp_apply, leftToMax, map_comp, map_mul, mk_eq, rightToMax, simp_rw
-/
theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk.{v, u} F x * M.mk F y = M.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  refine M.mk_eq F _ _ ?_
  use s, α, β
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

@[to_additive]
/--
lemma `colimit_mul_mk_eq'` / 引理 `colimit_mul_mk_eq'`

English:
lemma colimit_mul_mk_eq'
  given: {j : J} (x y : F.obj j)
  proof: by
  simpa using! colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

@[to_additive]

中文:
引理 colimit_mul_mk_eq'
  条件: {j : J} (x y : F.obj j)
  证明: by
  simpa using! colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

@[to_additive]

Depends on / 依赖: colimit_mul_mk_eq
-/
lemma colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    M.mk.{v, u} F ⟨j, x⟩ * M.mk.{v, u} F ⟨j, y⟩ = M.mk.{v, u} F ⟨j, x * y⟩ := by
  simpa using! colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

@[to_additive]
/--
Instance `colimitMulOneClass` / 实例 `colimitMulOneClass`

English:
instance colimitMulOneClass
  signature: : MulOneClass (M.{v, u} F)
  body: { colimitOne F,
    colimitMul F with
    one_mul := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j]; rw [colimit_mul_mk_eq']; rw [one_mul]
    mul_one := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j]; rw [colimit_mul_mk_e

中文:
实例 colimitMulOneClass
  签名: : MulOneClass (M.{v, u} F)
  定义体: { colimitOne F,
    colimitMul F with
    one_mul := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j]; rw [colimit_mul_mk_eq']; rw [one_mul]
    mul_one := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j]; rw [colimit_mul_mk_e

Depends on / 依赖: colimitMul, colimitOne, colimit_mul_mk_eq, colimit_one_eq, mk_surjective, mul_one, one_mul, x.mk_surjective
-/
noncomputable instance colimitMulOneClass : MulOneClass (M.{v, u} F) :=
  { colimitOne F,
    colimitMul F with
    one_mul := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j]; rw [colimit_mul_mk_eq']; rw [one_mul]
    mul_one := fun x => by
      obtain ⟨j, x, rfl⟩ := x.mk_surjective
      rw [colimit_one_eq F j]; rw [colimit_mul_mk_eq']; rw [mul_one] }

@[to_additive]
/--
Instance `colimitMonoid` / 实例 `colimitMonoid`

English:
instance colimitMonoid
  signature: : Monoid (M.{v, u} F)
  body: { colimitMulOneClass F with
    mul_assoc := fun x y z => by
      obtain ⟨j₁, x₁, rfl⟩ := x.mk_surjective
      obtain ⟨j₂, y₂, rfl⟩ := y.mk_surjective
      obtain ⟨j₃, z₃, rfl⟩ := z.mk_surjective
      obtain ⟨j, f₁, f₂, f₃, x, y, z, h₁, h₂, h₃⟩ :
          exists (j : J) (f₁ : j₁ ⟶ j) (f₂ : j₂ ⟶

中文:
实例 colimitMonoid
  签名: : Monoid (M.{v, u} F)
  定义体: { colimitMulOneClass F with
    mul_assoc := fun x y z => by
      obtain ⟨j₁, x₁, rfl⟩ := x.mk_surjective
      obtain ⟨j₂, y₂, rfl⟩ := y.mk_surjective
      obtain ⟨j₃, z₃, rfl⟩ := z.mk_surjective
      obtain ⟨j, f₁, f₂, f₃, x, y, z, h₁, h₂, h₃⟩ :
          exists (j : J) (f₁ : j₁ ⟶ j) (f₂ : j₂ ⟶

Depends on / 依赖: F.map, F.obj, IsFiltered, IsFiltered.firstToMax, IsFiltered.max, IsFiltered.secondToMax, IsFiltered.thirdToMax, colimitMulOneClass, mk_surjective, mul_assoc, x.mk_surjective, y.mk_surjective, z.mk_surjective
-/
noncomputable instance colimitMonoid : Monoid (M.{v, u} F) :=
  { colimitMulOneClass F with
    mul_assoc := fun x y z => by
      obtain ⟨j₁, x₁, rfl⟩ := x.mk_surjective
      obtain ⟨j₂, y₂, rfl⟩ := y.mk_surjective
      obtain ⟨j₃, z₃, rfl⟩ := z.mk_surjective
      obtain ⟨j, f₁, f₂, f₃, x, y, z, h₁, h₂, h₃⟩ :
          exists (j : J) (f₁ : j₁ ⟶ j) (f₂ : j₂ ⟶ j) (f₃ : j₃ ⟶ j) (x y z : F.obj j),
          F.map f₁ x₁ = x ∧ F.map f₂ y₂ = y ∧ F.map f₃ z₃ = z :=
        ⟨IsFiltered.max₃ j₁ j₂ j₃, IsFiltered.firstToMax₃ _ _ _,
          IsFiltered.secondToMax₃ _ _ _, IsFiltered.thirdToMax₃ _ _ _,
          _, _, _, rfl, rfl, rfl⟩
      simp only [← M.map_mk F f₁, ← M.map_mk F f₂, ← M.map_mk F f₃, h₁, h₂, h₃,
        colimit_mul_mk_eq', mul_assoc] }

/-- The bundled monoid giving the filtered colimit of a diagram. -/
@[to_additive
  /-- The bundled additive monoid giving the filtered colimit of a diagram. -/]
/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : MonCat.{max v u}
  body: MonCat.of (M.{v, u} F)

中文:
定义 colimit
  签名: : MonCat.{max v u}
  定义体: MonCat.of (M.{v, u} F)

Depends on / 依赖: MonCat, MonCat.of
-/
noncomputable def colimit : MonCat.{max v u} :=
  MonCat.of (M.{v, u} F)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
@[to_additive
      /-- The additive monoid homomorphism from a given additive monoid in the diagram to the
      colimit additive monoid. -/]
/--
Definition of `coconeMorphism` / `coconeMorphism` 的定义

English:
definition coconeMorphism
  signature: (j : J)
  body: ofHom
  { toFun := (Types.TypeMax.colimitCocone.{v, max v u, v} (F ⋙ forget MonCat)).ι.app j
    map_one' := (colimit_one_eq F j).symm
    map_mul' x y := by symm; apply colimit_mul_mk_eq' }

@[to_additive (attr := simp)]

中文:
定义 coconeMorphism
  签名: (j : J)
  定义体: ofHom
  { toFun := (Types.TypeMax.colimitCocone.{v, max v u, v} (F ⋙ forget MonCat)).ι.app j
    map_one' := (colimit_one_eq F j).symm
    map_mul' x y := by symm; apply colimit_mul_mk_eq' }

@[to_additive (attr := simp)]

Depends on / 依赖: MonCat, TypeMax, Types.TypeMax.colimitCocone, colimitCocone, colimit_mul_mk_eq, colimit_one_eq, forget, map_mul, map_one
-/
noncomputable def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
  { toFun := (Types.TypeMax.colimitCocone.{v, max v u, v} (F ⋙ forget MonCat)).ι.app j
    map_one' := (colimit_one_eq F j).symm
    map_mul' x y := by symm; apply colimit_mul_mk_eq' }

@[to_additive (attr := simp)]
/--
theorem `cocone_naturality` / 定理 `cocone_naturality`

English:
theorem cocone_naturality
  given: {j j' : J} (f : j ⟶ j')
  proof: MonCat.ext fun x =>
    ConcreteCategory.congr_hom ((Types.TypeMax.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x

中文:
定理 cocone_naturality
  条件: {j j' : J} (f : j ⟶ j')
  证明: MonCat.ext fun x =>
    ConcreteCategory.congr_hom ((Types.TypeMax.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, MonCat, MonCat.ext, TypeMax, Types.TypeMax.colimitCocone, colimitCocone, congr_hom, forget, naturality
-/
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism.{v, u} F j' = coconeMorphism F j :=
  MonCat.ext fun x =>
    ConcreteCategory.congr_hom ((Types.TypeMax.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x

set_option backward.defeqAttrib.useBackward true in
/-- The cocone over the proposed colimit monoid. -/
@[to_additive /-- The cocone over the proposed colimit additive monoid. -/]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι := { app := coconeMorphism F }

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι := { app := coconeMorphism F }

Depends on / 依赖: colimit
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι := { app := coconeMorphism F }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a cocone `t` of `F`, the induced monoid homomorphism from the colimit to the cocone point.
As a function, this is simply given by the induced map of the corresponding cocone in `Type`.
The only thing left to see is that it is a monoid homomorphism.
-/
@[to_additive
      /-- Given a cocone `t` of `F`, the induced additive monoid homomorphism from the colimit
      to the cocone point. As a function, this is simply given by the induced map of the
      corresponding cocone in `Type`. The only thing left to see is that it is an additive monoid
      homomorphism. -/]
/--
Definition of `colimitDesc` / `colimitDesc` 的定义

English:
definition colimitDesc
  signature: (t : Cocone F)
  body: ofHom
  { toFun := (F ⋙ forget MonCat).descColimitType
        ((F ⋙ forget MonCat).coconeTypesEquiv.symm ((forget MonCat).mapCocone t))
    map_one' := by
      simp [colimit_one_eq F IsFiltered.nonempty.some]
    map_mul' x y := by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rf

中文:
定义 colimitDesc
  签名: (t : Cocone F)
  定义体: ofHom
  { toFun := (F ⋙ forget MonCat).descColimitType
        ((F ⋙ forget MonCat).coconeTypesEquiv.symm ((forget MonCat).mapCocone t))
    map_one' := by
      simp [colimit_one_eq F IsFiltered.nonempty.some]
    map_mul' x y := by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rf

Depends on / 依赖: IsFiltered, IsFiltered.leftToMax, IsFiltered.nonempty.some, IsFiltered.rightToMax, MonCat, backward, backward.isDefEq.respectTransparency, coconeTypesEquiv, coconeTypesEquiv.symm, colimit_mul_mk_eq, colimit_one_eq, descColimitType, forget, isDefEq, leftToMax, mapCocone, map_mul, map_one, mk_surjective, nonempty
-/
noncomputable def colimitDesc (t : Cocone F) : colimit.{v, u} F ⟶ t.pt :=
  ofHom
  { toFun := (F ⋙ forget MonCat).descColimitType
        ((F ⋙ forget MonCat).coconeTypesEquiv.symm ((forget MonCat).mapCocone t))
    map_one' := by
      simp [colimit_one_eq F IsFiltered.nonempty.some]
    map_mul' x y := by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rfl⟩ := y.mk_surjective
      rw [colimit_mul_mk_eq F ⟨i]; rw [x⟩ ⟨j]; rw [y⟩ (max' i j) (IsFiltered.leftToMax i j)
        (IsFiltered.rightToMax i j)]
      dsimp
      set_option backward.isDefEq.respectTransparency true in
      rw [map_mul]; rw [t.w_apply]; rw [t.w_apply] }

/-- The proposed colimit cocone is a colimit in `MonCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddMonCat`. -/]
/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit (colimitCocone.{v, u} F) where
  body: colimitDesc.{v, u} F
  fac t j := rfl
  uniq t m h := MonCat.ext fun y => by
    obtain ⟨j, y, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y
    exact ConcreteCategory.congr_hom (h j) y

@[to_additive]

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit (colimitCocone.{v, u} F) where
  定义体: colimitDesc.{v, u} F
  fac t j := rfl
  uniq t m h := MonCat.ext fun y => by
    obtain ⟨j, y, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y
    exact ConcreteCategory.congr_hom (h j) y

@[to_additive]

Depends on / 依赖: colimitDesc
-/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc := colimitDesc.{v, u} F
  fac t j := rfl
  uniq t m h := MonCat.ext fun y => by
    obtain ⟨j, y, rfl⟩ := Functor.ιColimitType_jointly_surjective _ y
    exact ConcreteCategory.congr_hom (h j) y

@[to_additive]
/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: :
  body: ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget MonCat.{u}))⟩

中文:
实例 forget_preservesFilteredColimits
  签名: :
  定义体: ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget MonCat.{u}))⟩

Depends on / 依赖: MonCat, TypeMax, Types.TypeMax.colimitCoconeIsColimit, colimitCoconeIsColimit, forget, preservesColimit_of_preserves_colimit_cocone
-/
instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget MonCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget MonCat.{u}))⟩
end

end MonCat.FilteredColimits

namespace CommMonCat.FilteredColimits

open MonCat.FilteredColimits (colimit_mul_mk_eq)

section

-- We use parameters here, mainly so we can have the abbreviation `M` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommMonCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommMonCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a _commutative_ monoid.
-/
@[to_additive
      /-- The colimit of `F ⋙ forget₂ AddCommMonCat AddMonCat` in the category `AddMonCat`. In the
      following, we will show that this has the structure of a _commutative_ additive monoid. -/]
/--
Definition of `M` / `M` 的定义

English:
abbreviation M
  signature: : MonCat.{max v u}
  body: MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommMonCat MonCat.{max v u})

中文:
缩写 M
  签名: : MonCat.{max v u}
  定义体: MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommMonCat MonCat.{max v u})

Depends on / 依赖: CommMonCat, FilteredColimits, MonCat, MonCat.FilteredColimits.colimit, colimit
-/
noncomputable abbrev M : MonCat.{max v u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommMonCat MonCat.{max v u})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
Instance `colimitCommMonoid` / 实例 `colimitCommMonoid`

English:
instance colimitCommMonoid
  signature: : CommMonoid.{max v u} (M.{v, u} F)
  body: { (M.{v, u} F) with
    mul_comm := fun x y => by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rfl⟩ := y.mk_surjective
      let k := max' i j
      let f := IsFiltered.leftToMax i j
      let g := IsFiltered.rightToMax i j
      rw [colimit_mul_mk_eq.{v]; rw [u} (F ⋙ forget₂ Comm

中文:
实例 colimitCommMonoid
  签名: : CommMonoid.{max v u} (M.{v, u} F)
  定义体: { (M.{v, u} F) with
    mul_comm := fun x y => by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rfl⟩ := y.mk_surjective
      let k := max' i j
      let f := IsFiltered.leftToMax i j
      let g := IsFiltered.rightToMax i j
      rw [colimit_mul_mk_eq.{v]; rw [u} (F ⋙ forget₂ Comm

Depends on / 依赖: CommMonCat, IsFiltered, IsFiltered.leftToMax, IsFiltered.rightToMax, MonCat, colimit_mul_mk_eq, leftToMax, mk_surjective, mul_comm, rightToMax, x.mk_surjective, y.mk_surjective
-/
noncomputable instance colimitCommMonoid : CommMonoid.{max v u} (M.{v, u} F) :=
  { (M.{v, u} F) with
    mul_comm := fun x y => by
      obtain ⟨i, x, rfl⟩ := x.mk_surjective
      obtain ⟨j, y, rfl⟩ := y.mk_surjective
      let k := max' i j
      let f := IsFiltered.leftToMax i j
      let g := IsFiltered.rightToMax i j
      rw [colimit_mul_mk_eq.{v]; rw [u} (F ⋙ forget₂ CommMonCat MonCat) ⟨i]; rw [x⟩ ⟨j]; rw [y⟩ k f g]; rw [colimit_mul_mk_eq.{v]; rw [u} (F ⋙ forget₂ CommMonCat MonCat) ⟨j]; rw [y⟩ ⟨i]; rw [x⟩ k g f]
      dsimp
      rw [mul_comm] }

/-- The bundled commutative monoid giving the filtered colimit of a diagram. -/
@[to_additive
/-- The bundled additive commutative monoid giving the filtered colimit of a diagram. -/]
/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : CommMonCat.{max v u}
  body: CommMonCat.of (M.{v, u} F)

中文:
定义 colimit
  签名: : CommMonCat.{max v u}
  定义体: CommMonCat.of (M.{v, u} F)

Depends on / 依赖: CommMonCat, CommMonCat.of
-/
noncomputable def colimit : CommMonCat.{max v u} :=
  CommMonCat.of (M.{v, u} F)

/-- The cocone over the proposed colimit commutative monoid. -/
@[to_additive /-- The cocone over the proposed colimit additive commutative monoid. -/]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι.app j := ofHom ((MonCat.FilteredColimits.colimitCocone.{v, u}
    (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι.app j).hom
ι.naturality _ _ f := hom_ext congr_arg (MonCat.Hom.hom)
    ((MonCat.FilteredColimits.colimitCocone.{v, u}
      (F ⋙ forget₂ CommMonCat MonCat.{max v u})).

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι.app j := ofHom ((MonCat.FilteredColimits.colimitCocone.{v, u}
    (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι.app j).hom
ι.naturality _ _ f := hom_ext congr_arg (MonCat.Hom.hom)
    ((MonCat.FilteredColimits.colimitCocone.{v, u}
      (F ⋙ forget₂ CommMonCat MonCat.{max v u})).

Depends on / 依赖: colimit
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app j := ofHom ((MonCat.FilteredColimits.colimitCocone.{v, u}
    (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι.app j).hom
ι.naturality _ _ f := hom_ext congr_arg (MonCat.Hom.hom)
    ((MonCat.FilteredColimits.colimitCocone.{v, u}
      (F ⋙ forget₂ CommMonCat MonCat.{max v u})).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `CommMonCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddCommMonCat`. -/]
/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit (colimitCocone.{v, u} F)
  body: isColimitOfReflects (forget₂ CommMonCat MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))

@[to_additive forget₂AddMonPreservesFilteredColimits]

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit (colimitCocone.{v, u} F)
  定义体: isColimitOfReflects (forget₂ CommMonCat MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))

@[to_additive forget₂AddMonPreservesFilteredColimits]

Depends on / 依赖: CommMonCat, FilteredColimits, MonCat, MonCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, isColimitOfReflects
-/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ CommMonCat MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))

@[to_additive forget₂AddMonPreservesFilteredColimits]
/--
Instance `forget₂Mon_preservesFilteredColimits` / 实例 `forget₂Mon_preservesFilteredColimits`

English:
instance forget₂Mon_preservesFilteredColimits
  signature: :
  body: ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMonCat MonCat.{u}))⟩

@[to_additive]

中文:
实例 forget₂Mon_preservesFilteredColimits
  签名: :
  定义体: ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMonCat MonCat.{u}))⟩

@[to_additive]

Depends on / 依赖: CommMonCat, FilteredColimits, MonCat, MonCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommMonCat MonCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
      (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommMonCat MonCat.{u}))⟩

@[to_additive]
/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: :
  body: Limits.comp_preservesFilteredColimits (forget₂ CommMonCat MonCat) (forget MonCat)

中文:
实例 forget_preservesFilteredColimits
  签名: :
  定义体: Limits.comp_preservesFilteredColimits (forget₂ CommMonCat MonCat) (forget MonCat)

Depends on / 依赖: CommMonCat, Limits, Limits.comp_preservesFilteredColimits, MonCat, comp_preservesFilteredColimits, forget
-/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommMonCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommMonCat MonCat) (forget MonCat)

end

end CommMonCat.FilteredColimits
