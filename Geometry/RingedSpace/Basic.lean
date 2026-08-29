/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Ringed spaces

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRingCat`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance <https://stacks.math.columbia.edu/tag/01HZ>.

-/

@[expose] public section

universe v u

open CategoryTheory

open TopologicalSpace

open Opposite

open TopCat

open TopCat.Presheaf

namespace AlgebraicGeometry

-- The universes appear together in the type, but separately in the value.
set_option linter.checkUnivs false in
/--
Definition of `RingedSpace` / `RingedSpace` 的定义

English:
abbreviation RingedSpace
  signature: : Type max (u + 1) (v + 1)
  body: SheafedSpace.{v + 1, v, u} CommRingCat.{v}

中文:
缩写 RingedSpace
  签名: : 类型 最大值 (u + 1) (v + 1)
  定义体: SheafedSpace.{v + 1, v, u} CommRingCat.{v}

Depends on / 依赖: CommRingCat, SheafedSpace
-/
abbrev RingedSpace : Type max (u + 1) (v + 1) :=
  SheafedSpace.{v + 1, v, u} CommRingCat.{v}

namespace RingedSpace

open SheafedSpace

@[simp]
/--
lemma `res_zero` / 引理 `res_zero`

English:
lemma res_zero
  statement: {X : RingedSpace.{u}} {U V : TopologicalSpace.Opens X}
  proof: map_zero _

中文:
引理 res_zero
  结论: {X : RingedSpace.{u}} {U V : 拓扑空间.Opens X}
  证明: map_zero _

Depends on / 依赖: map_zero
-/
lemma res_zero {X : RingedSpace.{u}} {U V : TopologicalSpace.Opens X}
    (hUV : U <= V) : (0 : X.presheaf.obj (op V)) |_ U = (0 : X.presheaf.obj (op U)) :=
  map_zero _

variable (X : RingedSpace)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort RingedSpace Type*
  body: X.carrier

中文:
实例 :
  签名: CoeSort RingedSpace 类型
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort RingedSpace Type* where
  coe X := X.carrier

/--
lemma `exists_res_eq_zero_of_germ_eq_zero` / 引理 `exists_res_eq_zero_of_germ_eq_zero`

English:
lemma exists_res_eq_zero_of_germ_eq_zero
  statement: (U : Opens X) (f : X.presheaf.obj (op U)) (x : U)
  proof: by
  have h1 : X.presheaf.germ U x.val x.property f = X.presheaf.germ U x.val x.property 0 := by simpa
  obtain ⟨V, hv, i, _, (hv4 : (X.presheaf.map i.op) f = (X.presheaf.map _) 0)⟩ :=
    TopCat.Presheaf.germ_eq X.presheaf x.1 x.2 x.2 f 0 h1
  use V, i, hv
  simpa using hv4

中文:
引理 存在_res_eq_zero_of_germ_eq_zero
  结论: (U : Opens X) (f : X.presheaf.obj (op U)) (x : U)
  证明: by
  have h1 : X.presheaf.germ U x.val x.property f = X.presheaf.germ U x.val x.property 0 := by simpa
  obtain ⟨V, hv, i, _, (hv4 : (X.presheaf.map i.op) f = (X.presheaf.map _) 0)⟩ :=
    TopCat.Presheaf.germ_eq X.presheaf x.1 x.2 x.2 f 0 h1
  use V, i, hv
  simpa using hv4

Depends on / 依赖: Presheaf, TopCat, TopCat.Presheaf.germ_eq, X.presheaf, X.presheaf.germ, X.presheaf.map, germ_eq, i.op, presheaf, property, x.property, x.val
-/
lemma exists_res_eq_zero_of_germ_eq_zero (U : Opens X) (f : X.presheaf.obj (op U)) (x : U)
    (h : X.presheaf.germ U x.val x.property f = 0) :
    exists (V : Opens X) (i : V ⟶ U) (_ : x.1 in V), X.presheaf.map i.op f = 0 := by
  have h1 : X.presheaf.germ U x.val x.property f = X.presheaf.germ U x.val x.property 0 := by simpa
  obtain ⟨V, hv, i, _, (hv4 : (X.presheaf.map i.op) f = (X.presheaf.map _) 0)⟩ :=
    TopCat.Presheaf.germ_eq X.presheaf x.1 x.2 x.2 f 0 h1
  use V, i, hv
  simpa using hv4

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isUnit_res_of_isUnit_germ` / 定理 `isUnit_res_of_isUnit_germ`

English:
theorem isUnit_res_of_isUnit_germ
  statement: (U : Opens X) (f : X.presheaf.obj (op U)) (x : X) (hx : x in U)
  proof: by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.exists_germ_eq g'
  let W := U ⊓ V
  have hxW : x in W := ⟨hx, hxV⟩
  replace heq : (X.presheaf.germ _ x hxW) ((X.presheaf.map (U.infLELeft V).op) f *
      (X.presheaf.map (U.infLERight V).op) g) = (X.presheaf.germ 

中文:
定理 isUnit_res_of_isUnit_germ
  结论: (U : Opens X) (f : X.presheaf.obj (op U)) (x : X) (hx : x in U)
  证明: by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.exists_germ_eq g'
  let W := U ⊓ V
  have hxW : x in W := ⟨hx, hxV⟩
  replace heq : (X.presheaf.germ _ x hxW) ((X.presheaf.map (U.infLELeft V).op) f *
      (X.presheaf.map (U.infLERight V).op) g) = (X.presheaf.germ 

Depends on / 依赖: Opens.infLELeft, Opens.infLERight, U.infLELeft, U.infLERight, X.presheaf.exists_germ_eq, X.presheaf.germ, X.presheaf.germ_eq, X.presheaf.germ_res_apply, X.presheaf.map, exists_germ_eq, exists_right_inv, germ_eq, germ_res_apply, h.exists_right_inv, infLELeft, infLERight, map_mul, map_one, presheaf, replace
-/
theorem isUnit_res_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U)) (x : X) (hx : x in U)
    (h : IsUnit (X.presheaf.germ U x hx f)) :
    exists (V : Opens X) (i : V ⟶ U) (_ : x in V), IsUnit (X.presheaf.map i.op f) := by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.exists_germ_eq g'
  let W := U ⊓ V
  have hxW : x in W := ⟨hx, hxV⟩
  replace heq : (X.presheaf.germ _ x hxW) ((X.presheaf.map (U.infLELeft V).op) f *
      (X.presheaf.map (U.infLERight V).op) g) = (X.presheaf.germ _ x hxW) 1 := by
    rwa [map_mul, map_one, X.presheaf.germ_res_apply (Opens.infLELeft U V) x hxW f,
      X.presheaf.germ_res_apply (Opens.infLERight U V) x hxW g]
  obtain ⟨W', hxW', i₁, i₂, heq'⟩ := X.presheaf.germ_eq x hxW hxW _ _ heq
  use W', i₁ ≫ Opens.infLELeft U V, hxW'
  simp only [map_mul, map_one] at heq'
  simpa using .of_mul_eq_one _ heq'

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isUnit_of_isUnit_germ` / 定理 `isUnit_of_isUnit_germ`

English:
theorem isUnit_of_isUnit_germ
  statement: (U : Opens X) (f : X.presheaf.obj (op U))
  proof: by
  -- We pick a cover of `U` by open sets `V x`, such that `f` is a unit on each `V x`.
  choose V iVU m h_unit using fun x : U => X.isUnit_res_of_isUnit_germ U f x x.2 (h x.1 x.2)
  have hcover : U <= iSup V := by
    intro x hxU
    simp only [Opens.mem_iSup]
    tauto
  -- Let `g x` denote the 

中文:
定理 isUnit_of_isUnit_germ
  结论: (U : Opens X) (f : X.presheaf.obj (op U))
  证明: by
  -- We pick a cover of `U` by open sets `V x`, such that `f` is a unit on each `V x`.
  choose V iVU m h_unit using fun x : U => X.isUnit_res_of_isUnit_germ U f x x.2 (h x.1 x.2)
  have hcover : U <= iSup V := by
    intro x hxU
    simp only [Opens.mem_iSup]
    tauto
  -- Let `g x` denote the 
-/
theorem isUnit_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U))
    (h : forall (x) (hx : x in U), IsUnit (X.presheaf.germ U x hx f)) : IsUnit f := by
  -- We pick a cover of `U` by open sets `V x`, such that `f` is a unit on each `V x`.
  choose V iVU m h_unit using fun x : U => X.isUnit_res_of_isUnit_germ U f x x.2 (h x.1 x.2)
  have hcover : U <= iSup V := by
    intro x hxU
    simp only [Opens.mem_iSup]
    tauto
  -- Let `g x` denote the inverse of `f` in `U x`.
  choose g hg using fun x : U => IsUnit.exists_right_inv (h_unit x)
  have ic : IsCompatible (sheaf X).obj V g := by
    intro x y
    apply section_ext X.sheaf (V x ⊓ V y)
    rintro z ⟨hzVx, hzVy⟩
    rw [germ_res_apply]; rw [germ_res_apply]
    apply (h z ((iVU x).le hzVx)).mul_right_inj.mp
    rw [← germ_res_apply X.presheaf (iVU x) z hzVx f]
    -- Porting note: change was not necessary in Lean3
    change X.presheaf.germ _ z hzVx _ * (X.presheaf.germ _ z hzVx _) =
      X.presheaf.germ _ z hzVx _ * X.presheaf.germ _ z hzVy (g y)
    rw [← map_mul]; rw [hg x]; rw [germ_res_apply X.presheaf _ _ _ f]; rw [← germ_res_apply X.presheaf (iVU y) z hzVy f]; rw [← map_mul]; rw [(hg y)]; rw [map_one]; rw [map_one]
  -- We claim that these local inverses glue together to a global inverse of `f`.
  obtain ⟨gl, gl_spec, -⟩ :
    -- We need to rephrase the result from `ConcreteCategory` to `CommRingCat`.
    exists gl : X.presheaf.obj (op U), (forall i, ((sheaf X).obj.map (iVU i).op) gl = g i) ∧ _ :=
    X.sheaf.existsUnique_gluing' V U iVU hcover g ic
refine .of_mul_eq_one gl X.sheaf.eq_of_locally_eq' V U iVU hcover _ _ fun i => ?_
  -- We need to rephrase the goal from `ConcreteCategory` to `CommRingCat`.
  change ((sheaf X).obj.map (iVU i).op).hom (f * gl) = ((sheaf X).obj.map (iVU i).op) 1
  rw [map_one]; rw [map_mul]; rw [gl_spec]
  exact hg i

/--
Definition of `basicOpen` / `basicOpen` 的定义

English:
definition basicOpen
  signature: {U : Opens X} (f : X.presheaf.obj (op U))
  body: { x : X | exists (hx : x in U), IsUnit (X.presheaf.germ U x hx f) }
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxU, hx⟩
    obtain ⟨V, i, hxV, hf⟩ := X.isUnit_res_of_isUnit_germ U f x hxU hx
    use V.1
    refine ⟨?_, V.2, hxV⟩
    intro y hy
    use i.le hy
    convert! Rin

中文:
定义 basicOpen
  签名: {U : Opens X} (f : X.presheaf.obj (op U))
  定义体: { x : X | exists (hx : x in U), IsUnit (X.presheaf.germ U x hx f) }
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxU, hx⟩
    obtain ⟨V, i, hxV, hf⟩ := X.isUnit_res_of_isUnit_germ U f x hxU hx
    use V.1
    refine ⟨?_, V.2, hxV⟩
    intro y hy
    use i.le hy
    convert! Rin

Depends on / 依赖: IsUnit, X.presheaf.germ, presheaf
-/
def basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) : Opens X where
  carrier := { x : X | exists (hx : x in U), IsUnit (X.presheaf.germ U x hx f) }
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxU, hx⟩
    obtain ⟨V, i, hxV, hf⟩ := X.isUnit_res_of_isUnit_germ U f x hxU hx
    use V.1
    refine ⟨?_, V.2, hxV⟩
    intro y hy
    use i.le hy
    convert! RingHom.isUnit_map (X.presheaf.germ _ y hy).hom hf
    exact (X.presheaf.germ_res_apply i y hy f).symm

/--
theorem `mem_basicOpen` / 定理 `mem_basicOpen`

English:
theorem mem_basicOpen
  given: {U : Opens X} (f : X.presheaf.obj (op U)) (x : X) (hx : x in U)
  proof: ⟨Exists.choose_spec, (⟨hx, ·⟩)⟩

中文:
定理 mem_basicOpen
  条件: {U : Opens X} (f : X.presheaf.obj (op U)) (x : X) (hx : x in U)
  证明: ⟨Exists.choose_spec, (⟨hx, ·⟩)⟩

Depends on / 依赖: Exists, Exists.choose_spec, choose_spec
-/
theorem mem_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) :
    x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f) :=
  ⟨Exists.choose_spec, (⟨hx, ·⟩)⟩

/-- A variant of `mem_basicOpen` with bundled `x : U`. -/
@[simp]
/--
theorem `mem_basicOpen'` / 定理 `mem_basicOpen'`

English:
theorem mem_basicOpen'
  given: {U : Opens X} (f : X.presheaf.obj (op U)) (x : U)
  proof: mem_basicOpen X f x.1 x.2

@[simp]

中文:
定理 mem_basicOpen'
  条件: {U : Opens X} (f : X.presheaf.obj (op U)) (x : U)
  证明: mem_basicOpen X f x.1 x.2

@[simp]

Depends on / 依赖: mem_basicOpen
-/
theorem mem_basicOpen' {U : Opens X} (f : X.presheaf.obj (op U)) (x : U) :
    ↑x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x.1 x.2 f) :=
  mem_basicOpen X f x.1 x.2

@[simp]
/--
theorem `mem_top_basicOpen` / 定理 `mem_top_basicOpen`

English:
theorem mem_top_basicOpen
  given: (f : X.presheaf.obj (op ⊤)) (x : X)
  proof: mem_basicOpen X f x .intro

中文:
定理 mem_top_basicOpen
  条件: (f : X.presheaf.obj (op ⊤)) (x : X)
  证明: mem_basicOpen X f x .intro

Depends on / 依赖: mem_basicOpen
-/
theorem mem_top_basicOpen (f : X.presheaf.obj (op ⊤)) (x : X) :
    x in X.basicOpen f ↔ IsUnit (X.presheaf.Γgerm x f) :=
  mem_basicOpen X f x .intro

/--
theorem `basicOpen_le` / 定理 `basicOpen_le`

English:
theorem basicOpen_le
  given: {U : Opens X} (f : X.presheaf.obj (op U))
  statement: X.basicOpen f <= U
  proof: by
  rintro x ⟨h, _⟩; exact h

中文:
定理 basicOpen_le
  条件: {U : Opens X} (f : X.presheaf.obj (op U))
  结论: X.basicOpen f <= U
  证明: by
  rintro x ⟨h, _⟩; exact h
-/
theorem basicOpen_le {U : Opens X} (f : X.presheaf.obj (op U)) : X.basicOpen f <= U := by
  rintro x ⟨h, _⟩; exact h

/--
theorem `isUnit_res_basicOpen` / 定理 `isUnit_res_basicOpen`

English:
theorem isUnit_res_basicOpen
  given: {U : Opens X} (f : X.presheaf.obj (op U))
  proof: by
  apply isUnit_of_isUnit_germ
  rintro x ⟨hxU, hx⟩
  convert! hx
  exact X.presheaf.germ_res_apply _ _ _ _

@[simp]

中文:
定理 isUnit_res_basicOpen
  条件: {U : Opens X} (f : X.presheaf.obj (op U))
  证明: by
  apply isUnit_of_isUnit_germ
  rintro x ⟨hxU, hx⟩
  convert! hx
  exact X.presheaf.germ_res_apply _ _ _ _

@[simp]

Depends on / 依赖: X.presheaf.germ_res_apply, convert, germ_res_apply, isUnit_of_isUnit_germ, presheaf
-/
theorem isUnit_res_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) :
    IsUnit (X.presheaf.map (@homOfLE (Opens X) _ _ _ (X.basicOpen_le f)).op f) := by
  apply isUnit_of_isUnit_germ
  rintro x ⟨hxU, hx⟩
  convert! hx
  exact X.presheaf.germ_res_apply _ _ _ _

@[simp]
/--
theorem `basicOpen_res` / 定理 `basicOpen_res`

English:
theorem basicOpen_res
  given: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U)
  proof: by
  ext x; constructor
  · rintro ⟨hxV, hx⟩
    rw [germ_res_apply' X.presheaf] at hx
    exact ⟨hxV, i.unop.le hxV, hx⟩
  · rintro ⟨hxV, _, hx⟩
    refine ⟨hxV, ?_⟩
    rw [germ_res_apply' X.presheaf]
    exact hx

中文:
定理 basicOpen_res
  条件: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U)
  证明: by
  ext x; constructor
  · rintro ⟨hxV, hx⟩
    rw [germ_res_apply' X.presheaf] at hx
    exact ⟨hxV, i.unop.le hxV, hx⟩
  · rintro ⟨hxV, _, hx⟩
    refine ⟨hxV, ?_⟩
    rw [germ_res_apply' X.presheaf]
    exact hx

Depends on / 依赖: X.presheaf, germ_res_apply, i.unop.le, presheaf
-/
theorem basicOpen_res {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = unop V ⊓ @basicOpen X (unop U) f := by
  ext x; constructor
  · rintro ⟨hxV, hx⟩
    rw [germ_res_apply' X.presheaf] at hx
    exact ⟨hxV, i.unop.le hxV, hx⟩
  · rintro ⟨hxV, _, hx⟩
    refine ⟨hxV, ?_⟩
    rw [germ_res_apply' X.presheaf]
    exact hx

/-- High priority: This should fire before `basicOpen_res`. -/
@[simp (high)]
/--
theorem `basicOpen_res_eq` / 定理 `basicOpen_res_eq`

English:
theorem basicOpen_res_eq
  given: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.presheaf.obj U)
  proof: by
  apply le_antisymm
  · rw [X.basicOpen_res i f]; exact inf_le_right
  · have := X.basicOpen_res (inv i) (X.presheaf.map i f)
    rw [← CommRingCat.comp_apply]; rw [← X.presheaf.map_comp]; rw [IsIso.hom_inv_id]; rw [X.presheaf.map_id]; rw [CommRingCat.id_apply] at this
    rw [this]
    exact inf

中文:
定理 basicOpen_res_eq
  条件: {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [是同构 i] (f : X.presheaf.obj U)
  证明: by
  apply le_antisymm
  · rw [X.basicOpen_res i f]; exact inf_le_right
  · have := X.basicOpen_res (inv i) (X.presheaf.map i f)
    rw [← CommRingCat.comp_apply]; rw [← X.presheaf.map_comp]; rw [IsIso.hom_inv_id]; rw [X.presheaf.map_id]; rw [CommRingCat.id_apply] at this
    rw [this]
    exact inf

Depends on / 依赖: CommRingCat, CommRingCat.comp_apply, CommRingCat.id_apply, IsIso.hom_inv_id, X.basicOpen_res, X.presheaf.map, X.presheaf.map_comp, X.presheaf.map_id, basicOpen_res, comp_apply, hom_inv_id, id_apply, inf_le_right, le_antisymm, map_comp, map_id, presheaf
-/
theorem basicOpen_res_eq {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = @RingedSpace.basicOpen X (unop U) f := by
  apply le_antisymm
  · rw [X.basicOpen_res i f]; exact inf_le_right
  · have := X.basicOpen_res (inv i) (X.presheaf.map i f)
    rw [← CommRingCat.comp_apply]; rw [← X.presheaf.map_comp]; rw [IsIso.hom_inv_id]; rw [X.presheaf.map_id]; rw [CommRingCat.id_apply] at this
    rw [this]
    exact inf_le_right

@[simp]
/--
theorem `basicOpen_mul` / 定理 `basicOpen_mul`

English:
theorem basicOpen_mul
  given: {U : Opens X} (f g : X.presheaf.obj (op U))
  proof: by
  ext x
  by_cases hx : x in U
  · simp [mem_basicOpen (hx := hx)]
  · simp [mt (basicOpen_le X _ ·) hx]

@[simp]

中文:
定理 basicOpen_mul
  条件: {U : Opens X} (f g : X.presheaf.obj (op U))
  证明: by
  ext x
  by_cases hx : x in U
  · simp [mem_basicOpen (hx := hx)]
  · simp [mt (basicOpen_le X _ ·) hx]

@[simp]

Depends on / 依赖: basicOpen_le, mem_basicOpen
-/
theorem basicOpen_mul {U : Opens X} (f g : X.presheaf.obj (op U)) :
    X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g := by
  ext x
  by_cases hx : x in U
  · simp [mem_basicOpen (hx := hx)]
  · simp [mt (basicOpen_le X _ ·) hx]

@[simp]
/--
lemma `basicOpen_pow` / 引理 `basicOpen_pow`

English:
lemma basicOpen_pow
  given: {U : Opens X} (f : X.presheaf.obj (op U)) (n : Nat) (h : 0 < n)
  proof: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  induction k with
  | zero => simp
  | succ n hn => rw [pow_add]; simp_all

中文:
引理 basicOpen_pow
  条件: {U : Opens X} (f : X.presheaf.obj (op U)) (n : 自然数) (h : 0 < n)
  证明: by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  induction k with
  | zero => simp
  | succ n hn => rw [pow_add]; simp_all

Depends on / 依赖: Nat.exists_eq_add_of_le, exists_eq_add_of_le, pow_add
-/
lemma basicOpen_pow {U : Opens X} (f : X.presheaf.obj (op U)) (n : Nat) (h : 0 < n) :
    X.basicOpen (f ^ n) = X.basicOpen f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  induction k with
  | zero => simp
  | succ n hn => rw [pow_add]; simp_all

/--
theorem `basicOpen_of_isUnit` / 定理 `basicOpen_of_isUnit`

English:
theorem basicOpen_of_isUnit
  given: {U : Opens X} {f : X.presheaf.obj (op U)} (hf : IsUnit f)
  proof: by
  apply le_antisymm
  · exact X.basicOpen_le f
  intro x hx
  rw [X.mem_basicOpen f x hx]
  exact RingHom.isUnit_map _ hf

中文:
定理 basicOpen_of_isUnit
  条件: {U : Opens X} {f : X.presheaf.obj (op U)} (hf : 是单位 f)
  证明: by
  apply le_antisymm
  · exact X.basicOpen_le f
  intro x hx
  rw [X.mem_basicOpen f x hx]
  exact RingHom.isUnit_map _ hf

Depends on / 依赖: RingHom, RingHom.isUnit_map, X.basicOpen_le, X.mem_basicOpen, basicOpen_le, isUnit_map, le_antisymm, mem_basicOpen
-/
theorem basicOpen_of_isUnit {U : Opens X} {f : X.presheaf.obj (op U)} (hf : IsUnit f) :
    X.basicOpen f = U := by
  apply le_antisymm
  · exact X.basicOpen_le f
  intro x hx
  rw [X.mem_basicOpen f x hx]
  exact RingHom.isUnit_map _ hf

/--
Definition of `zeroLocus` / `zeroLocus` 的定义

English:
definition zeroLocus
  signature: {U : Opens X} (s : Set (X.presheaf.obj (op U)))
  body: ⋂ f in s, (X.basicOpen f)ᶜ

中文:
定义 zeroLocus
  签名: {U : Opens X} (s : 集合 (X.presheaf.obj (op U)))
  定义体: ⋂ f in s, (X.basicOpen f)ᶜ

Depends on / 依赖: X.basicOpen, basicOpen
-/
def zeroLocus {U : Opens X} (s : Set (X.presheaf.obj (op U))) : Set X :=
  ⋂ f in s, (X.basicOpen f)ᶜ

/--
lemma `zeroLocus_isClosed` / 引理 `zeroLocus_isClosed`

English:
lemma zeroLocus_isClosed
  given: {U : Opens X} (s : Set (X.presheaf.obj (op U)))
  proof: by
  apply isClosed_biInter
  intro i _
  simp only [isClosed_compl_iff]
  exact Opens.isOpen (X.basicOpen i)

中文:
引理 zeroLocus_isClosed
  条件: {U : Opens X} (s : 集合 (X.presheaf.obj (op U)))
  证明: by
  apply isClosed_biInter
  intro i _
  simp only [isClosed_compl_iff]
  exact Opens.isOpen (X.basicOpen i)

Depends on / 依赖: Opens.isOpen, X.basicOpen, basicOpen, isClosed_biInter, isClosed_compl_iff, isOpen
-/
lemma zeroLocus_isClosed {U : Opens X} (s : Set (X.presheaf.obj (op U))) :
    IsClosed (X.zeroLocus s) := by
  apply isClosed_biInter
  intro i _
  simp only [isClosed_compl_iff]
  exact Opens.isOpen (X.basicOpen i)

/--
lemma `zeroLocus_singleton` / 引理 `zeroLocus_singleton`

English:
lemma zeroLocus_singleton
  given: {U : Opens X} (f : X.presheaf.obj (op U))
  proof: by
  simp [zeroLocus]

@[simp]

中文:
引理 zeroLocus_singleton
  条件: {U : Opens X} (f : X.presheaf.obj (op U))
  证明: by
  simp [zeroLocus]

@[simp]

Depends on / 依赖: zeroLocus
-/
lemma zeroLocus_singleton {U : Opens X} (f : X.presheaf.obj (op U)) :
    X.zeroLocus {f} = (X.basicOpen f).carrierᶜ := by
  simp [zeroLocus]

@[simp]
/--
lemma `zeroLocus_empty_eq_univ` / 引理 `zeroLocus_empty_eq_univ`

English:
lemma zeroLocus_empty_eq_univ
  given: {U : Opens X}
  proof: by
  simp [zeroLocus]

@[simp]

中文:
引理 zeroLocus_empty_eq_univ
  条件: {U : Opens X}
  证明: by
  simp [zeroLocus]

@[simp]

Depends on / 依赖: zeroLocus
-/
lemma zeroLocus_empty_eq_univ {U : Opens X} :
    X.zeroLocus (∅ : Set (X.presheaf.obj (op U))) = Set.univ := by
  simp [zeroLocus]

@[simp]
/--
lemma `mem_zeroLocus_iff` / 引理 `mem_zeroLocus_iff`

English:
lemma mem_zeroLocus_iff
  given: {U : Opens X} (s : Set (X.presheaf.obj (op U))) (x : X)
  proof: by
  simp [zeroLocus]

中文:
引理 mem_zeroLocus_iff
  条件: {U : Opens X} (s : 集合 (X.presheaf.obj (op U))) (x : X)
  证明: by
  simp [zeroLocus]

Depends on / 依赖: zeroLocus
-/
lemma mem_zeroLocus_iff {U : Opens X} (s : Set (X.presheaf.obj (op U))) (x : X) :
    x in X.zeroLocus s ↔ forall f in s, x ∉ X.basicOpen f := by
  simp [zeroLocus]

end RingedSpace

end AlgebraicGeometry
