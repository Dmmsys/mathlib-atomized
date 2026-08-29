/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SuppressCompilation

/-!
# Composable arrows

If `C` is a category, the type of `n`-simplices in the nerve of `C` identifies
to the type of functors `Fin (n + 1) ⥤ C`, which can be thought of as families of `n` composable
arrows in `C`. In this file, we introduce and study this category `ComposableArrows C n`
of `n` composable arrows in `C`.

If `F : ComposableArrows C n`, we define `F.left` as the leftmost object, `F.right` as the
rightmost object, and `F.hom : F.left ⟶ F.right` is the canonical map.

The most significant definition in this file is the constructor
`F.precomp f : ComposableArrows C (n + 1)` for `F : ComposableArrows C n` and `f : X ⟶ F.left`:
"it shifts `F` towards the right and inserts `f` on the left". This `precomp` has
good definitional properties.

In the namespace `CategoryTheory.ComposableArrows`, we provide constructors
like `mk₁ f`, `mk₂ f g`, `mk₃ f g h` for `ComposableArrows C n` for small `n`.

TODO (@joelriou):
* construct some elements in `ComposableArrows m (Fin (n + 1))` for small `n`
  the precomposition with which shall induce functors
  `ComposableArrows C n ⥤ ComposableArrows C m` which correspond to simplicial operations
  (specifically faces) with good definitional properties (this might be necessary for
  up to `n = 7` in order to formalize spectral sequences following Verdier)

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

/-!
New `simprocs` that run even in `dsimp` have caused breakages in this file.

(e.g. `dsimp` can now simplify `2 + 3` to `5`)

For now, we just turn off the offending simprocs in this file.

*However*, hopefully it is possible to refactor the material here so that no disabling of
simprocs is needed.

See issue https://github.com/leanprover-community/mathlib4/issues/27382.
-/
attribute [-simp] Fin.reduceFinMk

namespace CategoryTheory

open Category

variable (C : Type*) [Category* C]

/--
Definition of `ComposableArrows` / `ComposableArrows` 的定义

English:
abbreviation ComposableArrows
  signature: (n : Nat)
  body: Fin (n + 1) ⥤ C

中文:
缩写 ComposableArrows
  签名: (n : 自然数)
  定义体: Fin (n + 1) ⥤ C
-/
abbrev ComposableArrows (n : Nat) := Fin (n + 1) ⥤ C

namespace ComposableArrows

variable {C} {n m : Nat}
variable (F G : ComposableArrows C n)

-- We do not yet replace `omega` with `lia` here, as it is measurably slower.
/-- A wrapper for `omega` which prefaces it with some quick and useful attempts -/
macro "valid" : tactic =>
  `(tactic| first | assumption | apply zero_le | apply le_rfl | transitivity <;> assumption | omega)

/-- The `i`th object (with `i : ℕ` such that `i ≤ n`) of `F : ComposableArrows C n`. -/
@[simp]
/--
Definition of `obj'` / `obj'` 的定义

English:
abbreviation obj'
  signature: (i : Nat) (hi : i <= n := by valid)
  body: F.obj ⟨i, by lia⟩

中文:
缩写 obj'
  签名: (i : 自然数) (hi : i <= n := by valid)
  定义体: F.obj ⟨i, by lia⟩

Depends on / 依赖: F.obj
-/
abbrev obj' (i : Nat) (hi : i <= n := by valid) : C := F.obj ⟨i, by lia⟩

/-- The map `F.obj' i ⟶ F.obj' j` when `F : ComposableArrows C n`, and `i` and `j`
are natural numbers such that `i ≤ j ≤ n`. -/
@[simp]
/--
Definition of `map'` / `map'` 的定义

English:
abbreviation map'
  signature: (i j : Nat) (hij : i <= j := by valid) (hjn : j <= n := by valid)
  body: F.map (homOfLE (by simp only [Fin.mk_le_mk]; valid))

中文:
缩写 map'
  签名: (i j : 自然数) (hij : i <= j := by valid) (hjn : j <= n := by valid)
  定义体: F.map (homOfLE (by simp only [Fin.mk_le_mk]; valid))

Depends on / 依赖: F.map, F.obj, Fin.mk_le_mk, homOfLE, mk_le_mk
-/
abbrev map' (i j : Nat) (hij : i <= j := by valid) (hjn : j <= n := by valid) :
    F.obj ⟨i, by lia⟩ ⟶ F.obj ⟨j, by lia⟩ :=
  F.map (homOfLE (by simp only [Fin.mk_le_mk]; valid))

/--
lemma `map'_self` / 引理 `map'_self`

English:
lemma map'_self
  given: (i : Nat) (hi : i <= n := by valid)
  statement: F.map' i i = 𝟙 _
  proof: F.map_id _

中文:
引理 map'_self
  条件: (i : 自然数) (hi : i <= n := by valid)
  结论: F.map' i i = 𝟙 _
  证明: F.map_id _
-/
lemma map'_self (i : Nat) (hi : i <= n := by valid) : F.map' i i = 𝟙 _ := F.map_id _

/--
lemma `map'_comp` / 引理 `map'_comp`

English:
lemma map'_comp
  statement: (i j k : Nat) (hij : i <= j := by valid)
  proof: F.map_comp _ _

中文:
引理 map'_comp
  结论: (i j k : 自然数) (hij : i <= j := by valid)
  证明: F.map_comp _ _
-/
lemma map'_comp (i j k : Nat) (hij : i <= j := by valid)
    (hjk : j <= k := by valid) (hk : k <= n := by valid) :
    F.map' i k = F.map' i j ≫ F.map' j k :=
  F.map_comp _ _

/--
Definition of `left` / `left` 的定义

English:
abbreviation left
  body: obj' F 0

中文:
缩写 left
  定义体: obj' F 0

Depends on / 依赖: P.hI
-/
abbrev left := obj' F 0

/--
Definition of `right` / `right` 的定义

English:
abbreviation right
  body: obj' F n

中文:
缩写 right
  定义体: obj' F n
-/
abbrev right := obj' F n

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: : F.left ⟶ F.right
  body: map' F 0 n

中文:
缩写 hom
  签名: : F.left ⟶ F.right
  定义体: map' F 0 n
-/
abbrev hom : F.left ⟶ F.right := map' F 0 n

variable {F G}

/-- The map `F.obj' i ⟶ G.obj' i` induced on `i`th objects by a morphism `F ⟶ G`
in `ComposableArrows C n` when `i` is a natural number such that `i ≤ n`. -/
@[simp]
/--
Definition of `app'` / `app'` 的定义

English:
abbreviation app'
  signature: (φ : F ⟶ G) (i : Nat) (hi : i <= n := by valid)
  body: φ.app _

@[reassoc]

中文:
缩写 app'
  签名: (φ : F ⟶ G) (i : 自然数) (hi : i <= n := by valid)
  定义体: φ.app _

@[reassoc]

Depends on / 依赖: F.obj, G.obj
-/
abbrev app' (φ : F ⟶ G) (i : Nat) (hi : i <= n := by valid) :
    F.obj' i ⟶ G.obj' i := φ.app _

@[reassoc]
/--
lemma `naturality'` / 引理 `naturality'`

English:
lemma naturality'
  statement: (φ : F ⟶ G) (i j : Nat) (hij : i <= j := by valid)
  proof: φ.naturality _

中文:
引理 naturality'
  结论: (φ : F ⟶ G) (i j : 自然数) (hij : i <= j := by valid)
  证明: φ.naturality _

Depends on / 依赖: F.map, G.map, naturality
-/
lemma naturality' (φ : F ⟶ G) (i j : Nat) (hij : i <= j := by valid)
    (hj : j <= n := by valid) :
    F.map' i j ≫ app' φ j = app' φ i ≫ G.map' i j :=
  φ.naturality _

/-- Constructor for `ComposableArrows C 0`. -/
@[simps!]
/--
Definition of `mk₀` / `mk₀` 的定义

English:
definition mk₀
  signature: (X : C)
  body: (Functor.const (Fin 1)).obj X

中文:
定义 mk₀
  签名: (X : C)
  定义体: (Functor.const (Fin 1)).obj X

Depends on / 依赖: Functor, Functor.const
-/
def mk₀ (X : C) : ComposableArrows C 0 := (Functor.const (Fin 1)).obj X

namespace Mk₁

variable (X₀ X₁ : C)

/-- The map which sends `0 : Fin 2` to `X₀` and `1` to `X₁`. -/
@[simp]
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: : Fin 2 -> C

中文:
定义 obj
  签名: : 有限集 2 -> C
-/
def obj : Fin 2 -> C
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩ => X₁

variable {X₀ X₁}
variable (f : X₀ ⟶ X₁)

/-- The obvious map `obj X₀ X₁ i ⟶ obj X₀ X₁ j` whenever `i j : Fin 2` satisfy `i ≤ j`. -/
@[simp]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : forall (i j : Fin 2) (_ : i <= j), obj X₀ X₁ i ⟶ obj X₀ X₁ j

中文:
定义 map
  签名: : 对任意 (i j : 有限集 2) (_ : i <= j), obj X₀ X₁ i ⟶ obj X₀ X₁ j
-/
def map : forall (i j : Fin 2) (_ : i <= j), obj X₀ X₁ i ⟶ obj X₀ X₁ j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (i : Fin 2)
  statement: map f i i (by simp) = 𝟙 _
  proof: match i with
    | 0 => rfl
    | 1 => rfl

中文:
引理 map_id
  条件: (i : 有限集 2)
  结论: map f i i (by simp) = 𝟙 _
  证明: match i with
    | 0 => rfl
    | 1 => rfl
-/
lemma map_id (i : Fin 2) : map f i i (by simp) = 𝟙 _ :=
  match i with
    | 0 => rfl
    | 1 => rfl

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {i j k : Fin 2} (hij : i <= j) (hjk : j <= k)
  proof: by
  obtain rfl | rfl : i = j ∨ j = k := by lia
  · rw [map_id, id_comp]
  · rw [map_id, comp_id]

中文:
引理 map_comp
  条件: {i j k : 有限集 2} (hij : i <= j) (hjk : j <= k)
  证明: by
  obtain rfl | rfl : i = j ∨ j = k := by lia
  · rw [map_id, id_comp]
  · rw [map_id, comp_id]

Depends on / 依赖: comp_id, id_comp, map_id
-/
lemma map_comp {i j k : Fin 2} (hij : i <= j) (hjk : j <= k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk := by
  obtain rfl | rfl : i = j ∨ j = k := by lia
  · rw [map_id, id_comp]
  · rw [map_id, comp_id]

end Mk₁

/-- Constructor for `ComposableArrows C 1`. -/
@[simps]
/--
Definition of `mk₁` / `mk₁` 的定义

English:
definition mk₁
  signature: {X₀ X₁ : C} (f : X₀ ⟶ X₁)
  body: Mk₁.obj X₀ X₁
  map g := Mk₁.map f _ _ (leOfHom g)
  map_id := Mk₁.map_id f
  map_comp g g' := Mk₁.map_comp f (leOfHom g) (leOfHom g')

中文:
定义 mk₁
  签名: {X₀ X₁ : C} (f : X₀ ⟶ X₁)
  定义体: Mk₁.obj X₀ X₁
  map g := Mk₁.map f _ _ (leOfHom g)
  map_id := Mk₁.map_id f
  map_comp g g' := Mk₁.map_comp f (leOfHom g) (leOfHom g')
-/
def mk₁ {X₀ X₁ : C} (f : X₀ ⟶ X₁) : ComposableArrows C 1 where
  obj := Mk₁.obj X₀ X₁
  map g := Mk₁.map f _ _ (leOfHom g)
  map_id := Mk₁.map_id f
  map_comp g g' := Mk₁.map_comp f (leOfHom g) (leOfHom g')

/-- Constructor for morphisms `F ⟶ G` in `ComposableArrows C n` which takes as inputs
a family of morphisms `F.obj i ⟶ G.obj i` and the naturality condition only for the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i)
  body: app
  naturality := by
    suffices forall (k i j : Nat) (hj : i + k = j) (hj' : j <= n),
        F.map' i j ≫ app _ = app _ ≫ G.map' i j by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hij' := leOfHom hij
      simp only [Fin.mk_le_mk] at hij'
      obtain ⟨k, hk⟩ := Nat.le.dest hij'
      exact thi

中文:
定义 homMk
  签名: {F G : ComposableArrows C n} (app : 对任意 i, F.obj i ⟶ G.obj i)
  定义体: app
  naturality := by
    suffices forall (k i j : Nat) (hj : i + k = j) (hj' : j <= n),
        F.map' i j ≫ app _ = app _ ≫ G.map' i j by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hij' := leOfHom hij
      simp only [Fin.mk_le_mk] at hij'
      obtain ⟨k, hk⟩ := Nat.le.dest hij'
      exact thi
-/
def homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i)
    (w : forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)) :
    F ⟶ G where
  app := app
  naturality := by
    suffices forall (k i j : Nat) (hj : i + k = j) (hj' : j <= n),
        F.map' i j ≫ app _ = app _ ≫ G.map' i j by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hij' := leOfHom hij
      simp only [Fin.mk_le_mk] at hij'
      obtain ⟨k, hk⟩ := Nat.le.dest hij'
      exact this k i j hk (by valid)
    intro k
    induction k with intro i j hj hj'
    | zero =>
      simp only [add_zero] at hj
      obtain rfl := hj
      rw [F.map'_self i]; rw [G.map'_self i]; rw [id_comp]; rw [comp_id]
    | succ k hk =>
      rw [← add_assoc] at hj
      subst hj
      rw [F.map'_comp i (i + k) (i + k + 1)]; rw [G.map'_comp i (i + k) (i + k + 1)]; rw [assoc]; rw [w (i + k) (by valid)]; rw [reassoc_of% (hk i (i + k) rfl (by valid))]

/-- Constructor for isomorphisms `F ≅ G` in `ComposableArrows C n` which takes as inputs
a family of isomorphisms `F.obj i ≅ G.obj i` and the naturality condition only for the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i)
  body: homMk (fun i => (app i).hom) w
  inv := homMk (fun i => (app i).inv) (fun i hi => by
    rw [← cancel_epi ((app _).hom)]; rw [← reassoc_of% (w i hi)]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc])

中文:
定义 isoMk
  签名: {F G : ComposableArrows C n} (app : 对任意 i, F.obj i ≅ G.obj i)
  定义体: homMk (fun i => (app i).hom) w
  inv := homMk (fun i => (app i).inv) (fun i hi => by
    rw [← cancel_epi ((app _).hom)]; rw [← reassoc_of% (w i hi)]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc])
-/
def isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i)
    (w : forall (i : Nat) (hi : i < n),
      F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)) :
    F ≅ G where
  hom := homMk (fun i => (app i).hom) w
  inv := homMk (fun i => (app i).inv) (fun i hi => by
    rw [← cancel_epi ((app _).hom)]; rw [← reassoc_of% (w i hi)]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc])

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i)
  proof: Functor.ext_of_iso
    (isoMk (fun i => eqToIso (h i)) (fun i hi => by simp [w i hi])) h

中文:
引理 ext
  结论: {F G : ComposableArrows C n} (h : 对任意 i, F.obj i = G.obj i)
  证明: Functor.ext_of_iso
    (isoMk (fun i => eqToIso (h i)) (fun i hi => by simp [w i hi])) h

Depends on / 依赖: Functor, Functor.ext_of_iso, eqToIso, ext_of_iso
-/
lemma ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i)
    (w : forall (i : Nat) (hi : i < n), F.map' i (i + 1) =
      eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm) : F = G :=
  Functor.ext_of_iso
    (isoMk (fun i => eqToIso (h i)) (fun i hi => by simp [w i hi])) h

/-- Constructor for morphisms in `ComposableArrows C 0`. -/
@[simps!]
/--
Definition of `homMk₀` / `homMk₀` 的定义

English:
definition homMk₀
  signature: {F G : ComposableArrows C 0} (f : F.obj' 0 ⟶ G.obj' 0)
  body: homMk (fun i => match i with
    | ⟨0, _⟩ => f) (fun i hi => by simp at hi)

@[ext]

中文:
定义 homMk₀
  签名: {F G : ComposableArrows C 0} (f : F.obj' 0 ⟶ G.obj' 0)
  定义体: homMk (fun i => match i with
    | ⟨0, _⟩ => f) (fun i hi => by simp at hi)

@[ext]
-/
def homMk₀ {F G : ComposableArrows C 0} (f : F.obj' 0 ⟶ G.obj' 0) : F ⟶ G :=
  homMk (fun i => match i with
    | ⟨0, _⟩ => f) (fun i hi => by simp at hi)

@[ext]
/--
lemma `hom_ext₀` / 引理 `hom_ext₀`

English:
lemma hom_ext₀
  statement: {F G : ComposableArrows C 0} {φ φ' : F ⟶ G}
  proof: by
  ext i
  fin_cases i
  exact h

中文:
引理 hom_ext₀
  结论: {F G : ComposableArrows C 0} {φ φ' : F ⟶ G}
  证明: by
  ext i
  fin_cases i
  exact h

Depends on / 依赖: fin_cases
-/
lemma hom_ext₀ {F G : ComposableArrows C 0} {φ φ' : F ⟶ G}
    (h : app' φ 0 = app' φ' 0) :
    φ = φ' := by
  ext i
  fin_cases i
  exact h

/-- Constructor for isomorphisms in `ComposableArrows C 0`. -/
@[simps!]
/--
Definition of `isoMk₀` / `isoMk₀` 的定义

English:
definition isoMk₀
  signature: {F G : ComposableArrows C 0} (e : F.obj' 0 ≅ G.obj' 0)
  body: homMk₀ e.hom
  inv := homMk₀ e.inv

中文:
定义 isoMk₀
  签名: {F G : ComposableArrows C 0} (e : F.obj' 0 ≅ G.obj' 0)
  定义体: homMk₀ e.hom
  inv := homMk₀ e.inv

Depends on / 依赖: e.hom
-/
def isoMk₀ {F G : ComposableArrows C 0} (e : F.obj' 0 ≅ G.obj' 0) : F ≅ G where
  hom := homMk₀ e.hom
  inv := homMk₀ e.inv

/--
lemma `isIso_iff₀` / 引理 `isIso_iff₀`

English:
lemma isIso_iff₀
  given: {F G : ComposableArrows C 0} (f : F ⟶ G)
  proof: by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => h 0, fun _ i => by fin_cases i; assumption⟩

中文:
引理 isIso_iff₀
  条件: {F G : ComposableArrows C 0} (f : F ⟶ G)
  证明: by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => h 0, fun _ i => by fin_cases i; assumption⟩

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, fin_cases, isIso_iff_isIso_app
-/
lemma isIso_iff₀ {F G : ComposableArrows C 0} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => h 0, fun _ i => by fin_cases i; assumption⟩

/--
lemma `ext₀` / 引理 `ext₀`

English:
lemma ext₀
  given: {F G : ComposableArrows C 0} (h : F.obj' 0 = G.obj 0)
  statement: F = G
  proof: ext (fun i => match i with
    | ⟨0, _⟩ => h) (fun i hi => by simp at hi)

中文:
引理 ext₀
  条件: {F G : ComposableArrows C 0} (h : F.obj' 0 = G.obj 0)
  结论: F = G
  证明: ext (fun i => match i with
    | ⟨0, _⟩ => h) (fun i hi => by simp at hi)
-/
lemma ext₀ {F G : ComposableArrows C 0} (h : F.obj' 0 = G.obj 0) : F = G :=
  ext (fun i => match i with
    | ⟨0, _⟩ => h) (fun i hi => by simp at hi)

/--
lemma `mk₀_surjective` / 引理 `mk₀_surjective`

English:
lemma mk₀_surjective
  given: (F : ComposableArrows C 0)
  statement: exists (X : C), F = mk₀ X
  proof: ⟨F.obj' 0, ext₀ rfl⟩

中文:
引理 mk₀_surjective
  条件: (F : ComposableArrows C 0)
  结论: 存在 (X : C), F = mk₀ X
  证明: ⟨F.obj' 0, ext₀ rfl⟩

Depends on / 依赖: F.obj
-/
lemma mk₀_surjective (F : ComposableArrows C 0) : exists (X : C), F = mk₀ X :=
  ⟨F.obj' 0, ext₀ rfl⟩

/-- Constructor for morphisms in `ComposableArrows C 1`. -/
@[simps!]
/--
Definition of `homMk₁` / `homMk₁` 的定义

English:
definition homMk₁
  signature: {F G : ComposableArrows C 1}
  body: homMk (fun i => match i with
      | ⟨0, _⟩ => left
      | ⟨1, _⟩ => right) (by
          intro i hi
          obtain rfl : i = 0 := by simpa using hi
          exact w)

@[ext]

中文:
定义 homMk₁
  签名: {F G : ComposableArrows C 1}
  定义体: homMk (fun i => match i with
      | ⟨0, _⟩ => left
      | ⟨1, _⟩ => right) (by
          intro i hi
          obtain rfl : i = 0 := by simpa using hi
          exact w)

@[ext]

Depends on / 依赖: cat_disch
-/
def homMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ⟶ G.obj' 0) (right : F.obj' 1 ⟶ G.obj' 1)
    (w : F.map' 0 1 ≫ right = left ≫ G.map' 0 1 := by cat_disch) :
    F ⟶ G :=
  homMk (fun i => match i with
      | ⟨0, _⟩ => left
      | ⟨1, _⟩ => right) (by
          intro i hi
          obtain rfl : i = 0 := by simpa using hi
          exact w)

@[ext]
/--
lemma `hom_ext₁` / 引理 `hom_ext₁`

English:
lemma hom_ext₁
  statement: {F G : ComposableArrows C 1} {φ φ' : F ⟶ G}
  proof: by
  ext i
  match i with
    | 0 => exact h₀
    | 1 => exact h₁

中文:
引理 hom_ext₁
  结论: {F G : ComposableArrows C 1} {φ φ' : F ⟶ G}
  证明: by
  ext i
  match i with
    | 0 => exact h₀
    | 1 => exact h₁
-/
lemma hom_ext₁ {F G : ComposableArrows C 1} {φ φ' : F ⟶ G}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
    φ = φ' := by
  ext i
  match i with
    | 0 => exact h₀
    | 1 => exact h₁

/-- Constructor for isomorphisms in `ComposableArrows C 1`. -/
@[simps!]
/--
Definition of `isoMk₁` / `isoMk₁` 的定义

English:
definition isoMk₁
  signature: {F G : ComposableArrows C 1}
  body: homMk₁ left.hom right.hom w
  inv := homMk₁ left.inv right.inv (by
    rw [← cancel_mono right.hom]; rw [assoc]; rw [assoc]; rw [w]; rw [right.inv_hom_id]; rw [left.inv_hom_id_assoc]
    apply comp_id)

中文:
定义 isoMk₁
  签名: {F G : ComposableArrows C 1}
  定义体: homMk₁ left.hom right.hom w
  inv := homMk₁ left.inv right.inv (by
    rw [← cancel_mono right.hom]; rw [assoc]; rw [assoc]; rw [w]; rw [right.inv_hom_id]; rw [left.inv_hom_id_assoc]
    apply comp_id)

Depends on / 依赖: cancel_mono, cat_disch, comp_id, inv_hom_id, inv_hom_id_assoc, left.hom, left.inv, left.inv_hom_id_assoc, right.hom, right.inv, right.inv_hom_id
-/
def isoMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ≅ G.obj' 0) (right : F.obj' 1 ≅ G.obj' 1)
    (w : F.map' 0 1 ≫ right.hom = left.hom ≫ G.map' 0 1 := by cat_disch) :
    F ≅ G where
  hom := homMk₁ left.hom right.hom w
  inv := homMk₁ left.inv right.inv (by
    rw [← cancel_mono right.hom]; rw [assoc]; rw [assoc]; rw [w]; rw [right.inv_hom_id]; rw [left.inv_hom_id_assoc]
    apply comp_id)

/--
lemma `map'_eq_hom₁` / 引理 `map'_eq_hom₁`

English:
lemma map'_eq_hom₁
  given: (F : ComposableArrows C 1)
  statement: F.map' 0 1 = F.hom
  proof: rfl

中文:
引理 map'_eq_hom₁
  条件: (F : ComposableArrows C 1)
  结论: F.map' 0 1 = F.hom
  证明: rfl
-/
lemma map'_eq_hom₁ (F : ComposableArrows C 1) : F.map' 0 1 = F.hom := rfl

/--
lemma `isIso_iff₁` / 引理 `isIso_iff₁`

English:
lemma isIso_iff₁
  given: {F G : ComposableArrows C 1} (f : F ⟶ G)
  proof: by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => ⟨h 0, h 1⟩, fun _ i => by fin_cases i <;> tauto⟩

中文:
引理 isIso_iff₁
  条件: {F G : ComposableArrows C 1} (f : F ⟶ G)
  证明: by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => ⟨h 0, h 1⟩, fun _ i => by fin_cases i <;> tauto⟩

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, fin_cases, isIso_iff_isIso_app
-/
lemma isIso_iff₁ {F G : ComposableArrows C 1} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => ⟨h 0, h 1⟩, fun _ i => by fin_cases i <;> tauto⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ext₁` / 引理 `ext₁`

English:
lemma ext₁
  statement: {F G : ComposableArrows C 1}
  proof: Functor.ext_of_iso (isoMk₁ (eqToIso left) (eqToIso right) (by simp [map'_eq_hom₁, w]))
    (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> rfl)

中文:
引理 ext₁
  结论: {F G : ComposableArrows C 1}
  证明: Functor.ext_of_iso (isoMk₁ (eqToIso left) (eqToIso right) (by simp [map'_eq_hom₁, w]))
    (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> rfl)

Depends on / 依赖: Functor, Functor.ext_of_iso, eqToIso, ext_of_iso, fin_cases
-/
lemma ext₁ {F G : ComposableArrows C 1}
    (left : F.left = G.left) (right : F.right = G.right)
    (w : F.hom = eqToHom left ≫ G.hom ≫ eqToHom right.symm) : F = G :=
  Functor.ext_of_iso (isoMk₁ (eqToIso left) (eqToIso right) (by simp [map'_eq_hom₁, w]))
    (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> rfl)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mk₁_surjective` / 引理 `mk₁_surjective`

English:
lemma mk₁_surjective
  given: (X : ComposableArrows C 1)
  statement: exists (X₀ X₁ : C) (f : X₀ ⟶ X₁), X = mk₁ f
  proof: ⟨_, _, X.map' 0 1, ext₁ rfl rfl (by simp)⟩

中文:
引理 mk₁_surjective
  条件: (X : ComposableArrows C 1)
  结论: 存在 (X₀ X₁ : C) (f : X₀ ⟶ X₁), X = mk₁ f
  证明: ⟨_, _, X.map' 0 1, ext₁ rfl rfl (by simp)⟩

Depends on / 依赖: X.map
-/
lemma mk₁_surjective (X : ComposableArrows C 1) : exists (X₀ X₁ : C) (f : X₀ ⟶ X₁), X = mk₁ f :=
  ⟨_, _, X.map' 0 1, ext₁ rfl rfl (by simp)⟩

/--
lemma `mk₁_eqToHom_comp` / 引理 `mk₁_eqToHom_comp`

English:
lemma mk₁_eqToHom_comp
  given: {X₀' X₀ X₁ : C} (h : X₀' = X₀) (f : X₀ ⟶ X₁)
  proof: by
  cat_disch

中文:
引理 mk₁_eqToHom_comp
  条件: {X₀' X₀ X₁ : C} (h : X₀' = X₀) (f : X₀ ⟶ X₁)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mk₁_eqToHom_comp {X₀' X₀ X₁ : C} (h : X₀' = X₀) (f : X₀ ⟶ X₁) :
    ComposableArrows.mk₁ (eqToHom h ≫ f) = ComposableArrows.mk₁ f := by
  cat_disch

/--
lemma `mk₁_comp_eqToHom` / 引理 `mk₁_comp_eqToHom`

English:
lemma mk₁_comp_eqToHom
  given: {X₀ X₁ X₁' : C} (f : X₀ ⟶ X₁) (h : X₁ = X₁')
  proof: by
  cat_disch

中文:
引理 mk₁_comp_eqToHom
  条件: {X₀ X₁ X₁' : C} (f : X₀ ⟶ X₁) (h : X₁ = X₁')
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mk₁_comp_eqToHom {X₀ X₁ X₁' : C} (f : X₀ ⟶ X₁) (h : X₁ = X₁') :
    ComposableArrows.mk₁ (f ≫ eqToHom h) = ComposableArrows.mk₁ f := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `mk₁_hom` / 引理 `mk₁_hom`

English:
lemma mk₁_hom
  given: (X : ComposableArrows C 1)
  proof: ext₁ rfl rfl (by simp)

中文:
引理 mk₁_hom
  条件: (X : ComposableArrows C 1)
  证明: ext₁ rfl rfl (by simp)
-/
lemma mk₁_hom (X : ComposableArrows C 1) :
    mk₁ X.hom = X :=
  ext₁ rfl rfl (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The bijection between `ComposableArrows C 1` and `Arrow C`. -/
@[simps]
/--
Definition of `arrowEquiv` / `arrowEquiv` 的定义

English:
definition arrowEquiv
  signature: : ComposableArrows C 1 ≃ Arrow C where
  body: Arrow.mk F.hom
  invFun f := mk₁ f.hom
  left_inv F := ComposableArrows.ext₁ rfl rfl (by simp)
  right_inv _ := rfl

中文:
定义 arrowEquiv
  签名: : ComposableArrows C 1 ≃ 箭头 C where
  定义体: Arrow.mk F.hom
  invFun f := mk₁ f.hom
  left_inv F := ComposableArrows.ext₁ rfl rfl (by simp)
  right_inv _ := rfl

Depends on / 依赖: Arrow.mk, F.hom
-/
def arrowEquiv : ComposableArrows C 1 ≃ Arrow C where
  toFun F := Arrow.mk F.hom
  invFun f := mk₁ f.hom
  left_inv F := ComposableArrows.ext₁ rfl rfl (by simp)
  right_inv _ := rfl

variable (F)

namespace Precomp

variable (X : C)

/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: : Fin (n + 1 + 1) -> C

中文:
定义 obj
  签名: : 有限集 (n + 1 + 1) -> C
-/
def obj : Fin (n + 1 + 1) -> C
  | ⟨0, _⟩ => X
  | ⟨i + 1, hi⟩ => F.obj' i

@[simp]
/--
lemma `obj_zero` / 引理 `obj_zero`

English:
lemma obj_zero
  statement: obj F X 0 = X
  proof: rfl

@[simp]

中文:
引理 obj_zero
  结论: obj F X 0 = X
  证明: rfl

@[simp]
-/
lemma obj_zero : obj F X 0 = X := rfl

@[simp]
/--
lemma `obj_one` / 引理 `obj_one`

English:
lemma obj_one
  statement: obj F X 1 = F.obj' 0
  proof: rfl

@[simp]

中文:
引理 obj_one
  结论: obj F X 1 = F.obj' 0
  证明: rfl

@[simp]
-/
lemma obj_one : obj F X 1 = F.obj' 0 := rfl

@[simp]
/--
lemma `obj_succ` / 引理 `obj_succ`

English:
lemma obj_succ
  given: (i : Nat) (hi : i + 1 < n + 1 + 1)
  statement: obj F X ⟨i + 1, hi⟩ = F.obj' i
  proof: rfl

中文:
引理 obj_succ
  条件: (i : 自然数) (hi : i + 1 < n + 1 + 1)
  结论: obj F X ⟨i + 1, hi⟩ = F.obj' i
  证明: rfl
-/
lemma obj_succ (i : Nat) (hi : i + 1 < n + 1 + 1) : obj F X ⟨i + 1, hi⟩ = F.obj' i := rfl

variable {X} (f : X ⟶ F.left)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : forall (i j : Fin (n + 1 + 1)) (_ : i <= j), obj F X i ⟶ obj F X j

中文:
定义 map
  签名: : 对任意 (i j : 有限集 (n + 1 + 1)) (_ : i <= j), obj F X i ⟶ obj F X j
-/
def map : forall (i j : Fin (n + 1 + 1)) (_ : i <= j), obj F X i ⟶ obj F X j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 X
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨0, _⟩, ⟨j + 2, hj⟩, _ => f ≫ F.map' 0 (j + 1)
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij => F.map' i j (by simpa using hij)

@[simp]
/--
lemma `map_zero_zero` / 引理 `map_zero_zero`

English:
lemma map_zero_zero
  statement: map F f 0 0 (by simp) = 𝟙 X
  proof: rfl

@[simp]

中文:
引理 map_zero_zero
  结论: map F f 0 0 (by simp) = 𝟙 X
  证明: rfl

@[simp]
-/
lemma map_zero_zero : map F f 0 0 (by simp) = 𝟙 X := rfl

@[simp]
/--
lemma `map_one_one` / 引理 `map_one_one`

English:
lemma map_one_one
  statement: map F f 1 1 (by simp) = F.map (𝟙 _)
  proof: rfl

@[simp]

中文:
引理 map_one_one
  结论: map F f 1 1 (by simp) = F.map (𝟙 _)
  证明: rfl

@[simp]
-/
lemma map_one_one : map F f 1 1 (by simp) = F.map (𝟙 _) := rfl

@[simp]
/--
lemma `map_zero_one` / 引理 `map_zero_one`

English:
lemma map_zero_one
  statement: map F f 0 1 (by simp) = f
  proof: rfl

@[simp]

中文:
引理 map_zero_one
  结论: map F f 0 1 (by simp) = f
  证明: rfl

@[simp]
-/
lemma map_zero_one : map F f 0 1 (by simp) = f := rfl

@[simp]
/--
lemma `map_zero_one'` / 引理 `map_zero_one'`

English:
lemma map_zero_one'
  statement: map F f 0 ⟨0 + 1, by simp⟩ (by simp) = f
  proof: rfl

@[simp]

中文:
引理 map_zero_one'
  结论: map F f 0 ⟨0 + 1, by simp⟩ (by simp) = f
  证明: rfl

@[simp]
-/
lemma map_zero_one' : map F f 0 ⟨0 + 1, by simp⟩ (by simp) = f := rfl

@[simp]
/--
lemma `map_zero_succ_succ` / 引理 `map_zero_succ_succ`

English:
lemma map_zero_succ_succ
  given: (j : Nat) (hj : j + 2 < n + 1 + 1)
  proof: rfl

@[simp]

中文:
引理 map_zero_succ_succ
  条件: (j : 自然数) (hj : j + 2 < n + 1 + 1)
  证明: rfl

@[simp]
-/
lemma map_zero_succ_succ (j : Nat) (hj : j + 2 < n + 1 + 1) :
    map F f 0 ⟨j + 2, hj⟩ (by simp) = f ≫ F.map' 0 (j + 1) := rfl

@[simp]
/--
lemma `map_succ_succ` / 引理 `map_succ_succ`

English:
lemma map_succ_succ
  statement: (i j : Nat) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1)
  proof: rfl

@[simp]

中文:
引理 map_succ_succ
  结论: (i j : 自然数) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1)
  证明: rfl

@[simp]
-/
lemma map_succ_succ (i j : Nat) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1)
    (hij : i + 1 <= j + 1) :
    map F f ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ hij = F.map' i j := rfl

@[simp]
/--
lemma `map_one_succ` / 引理 `map_one_succ`

English:
lemma map_one_succ
  given: (j : Nat) (hj : j + 1 < n + 1 + 1)
  proof: rfl

中文:
引理 map_one_succ
  条件: (j : 自然数) (hj : j + 1 < n + 1 + 1)
  证明: rfl
-/
lemma map_one_succ (j : Nat) (hj : j + 1 < n + 1 + 1) :
    map F f 1 ⟨j + 1, hj⟩ (by simp [Fin.le_def]) = F.map' 0 j := rfl

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (i : Fin (n + 1 + 1))
  statement: map F f i i (by simp) = 𝟙 _
  proof: by
  obtain ⟨_ | _, hi⟩ := i <;> simp

中文:
引理 map_id
  条件: (i : 有限集 (n + 1 + 1))
  结论: map F f i i (by simp) = 𝟙 _
  证明: by
  obtain ⟨_ | _, hi⟩ := i <;> simp
-/
lemma map_id (i : Fin (n + 1 + 1)) : map F f i i (by simp) = 𝟙 _ := by
  obtain ⟨_ | _, hi⟩ := i <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {i j k : Fin (n + 1 + 1)} (hij : i <= j) (hjk : j <= k)
  proof: by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  cases i
  · obtain _ | _ | j := j
    · dsimp
      rw [id_comp]
    · obtain _ | _ | k := k
      · simp at hjk
      · simp
      · rfl
    · obtain _ | _ | k := k
      · simp [Fin.ext_iff] at hjk
      · simp [Fin.le_def] at 

中文:
引理 map_comp
  条件: {i j k : 有限集 (n + 1 + 1)} (hij : i <= j) (hjk : j <= k)
  证明: by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  cases i
  · obtain _ | _ | j := j
    · dsimp
      rw [id_comp]
    · obtain _ | _ | k := k
      · simp at hjk
      · simp
      · rfl
    · obtain _ | _ | k := k
      · simp [Fin.ext_iff] at hjk
      · simp [Fin.le_def] at 

Depends on / 依赖: F.map_comp, Fin.ext_iff, Fin.le_def, ext_iff, homOfLE_comp, id_comp, le_def, map_comp
-/
lemma map_comp {i j k : Fin (n + 1 + 1)} (hij : i <= j) (hjk : j <= k) :
    map F f i k (hij.trans hjk) = map F f i j hij ≫ map F f j k hjk := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  cases i
  · obtain _ | _ | j := j
    · dsimp
      rw [id_comp]
    · obtain _ | _ | k := k
      · simp at hjk
      · simp
      · rfl
    · obtain _ | _ | k := k
      · simp [Fin.ext_iff] at hjk
      · simp [Fin.le_def] at hjk
      · dsimp
        rw [assoc]; rw [← F.map_comp]; rw [homOfLE_comp]
  · obtain _ | j := j
    · simp [Fin.ext_iff] at hij
    · obtain _ | k := k
      · simp [Fin.ext_iff] at hjk
      · dsimp
        rw [← F.map_comp]; rw [homOfLE_comp]

end Precomp

/-- "Precomposition" of `F : ComposableArrows C n` by a morphism `f : X ⟶ F.left`. -/
@[simps]
/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: {X : C} (f : X ⟶ F.left)
  body: Precomp.obj F X
  map g := Precomp.map F f _ _ (leOfHom g)
  map_id := Precomp.map_id F f
  map_comp g g' := Precomp.map_comp F f (leOfHom g) (leOfHom g')

中文:
定义 precomp
  签名: {X : C} (f : X ⟶ F.left)
  定义体: Precomp.obj F X
  map g := Precomp.map F f _ _ (leOfHom g)
  map_id := Precomp.map_id F f
  map_comp g g' := Precomp.map_comp F f (leOfHom g) (leOfHom g')

Depends on / 依赖: Precomp, Precomp.obj
-/
def precomp {X : C} (f : X ⟶ F.left) : ComposableArrows C (n + 1) where
  obj := Precomp.obj F X
  map g := Precomp.map F f _ _ (leOfHom g)
  map_id := Precomp.map_id F f
  map_comp g g' := Precomp.map_comp F f (leOfHom g) (leOfHom g')

/--
Definition of `mk₂` / `mk₂` 的定义

English:
abbreviation mk₂
  signature: {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
  body: (mk₁ g).precomp f

中文:
缩写 mk₂
  签名: {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
  定义体: (mk₁ g).precomp f

Depends on / 依赖: precomp
-/
abbrev mk₂ {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) : ComposableArrows C 2 :=
  (mk₁ g).precomp f

/--
Definition of `mk₃` / `mk₃` 的定义

English:
abbreviation mk₃
  signature: {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
  body: (mk₂ g h).precomp f

中文:
缩写 mk₃
  签名: {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
  定义体: (mk₂ g h).precomp f

Depends on / 依赖: precomp
-/
abbrev mk₃ {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) : ComposableArrows C 3 :=
  (mk₂ g h).precomp f

/--
Definition of `mk₄` / `mk₄` 的定义

English:
abbreviation mk₄
  signature: {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)
  body: (mk₃ g h i).precomp f

中文:
缩写 mk₄
  签名: {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)
  定义体: (mk₃ g h i).precomp f

Depends on / 依赖: precomp
-/
abbrev mk₄ {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) :
    ComposableArrows C 4 :=
  (mk₃ g h i).precomp f

/--
Definition of `mk₅` / `mk₅` 的定义

English:
abbreviation mk₅
  signature: {X₀ X₁ X₂ X₃ X₄ X₅ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
  body: (mk₄ g h i j).precomp f

中文:
缩写 mk₅
  签名: {X₀ X₁ X₂ X₃ X₄ X₅ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
  定义体: (mk₄ g h i j).precomp f

Depends on / 依赖: precomp
-/
abbrev mk₅ {X₀ X₁ X₂ X₃ X₄ X₅ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) :
    ComposableArrows C 5 :=
  (mk₄ g h i j).precomp f

section

variable {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)

/-! These examples are meant to test the good definitional properties of `precomp`,
and that `dsimp` can see through. -/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
example : map' (mk₂ f g) 0 1 = f := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₂ f g) 1 2 = g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₂ f g) 0 2 = f ≫ g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : (mk₂ f g).hom = f ≫ g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₂ f g) 0 0 = 𝟙 _ := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₂ f g) 1 1 = 𝟙 _ := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₂ f g) 2 2 = 𝟙 _ := by dsimp

set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₃ f g h) 0 1 = f := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₃ f g h) 1 2 = g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₃ f g h) 2 3 = h := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₃ f g h) 0 3 = f ≫ g ≫ h := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : (mk₃ f g h).hom = f ≫ g ≫ h := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₃ f g h) 0 2 = f ≫ g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
example : map' (mk₃ f g h) 1 3 = g ≫ h := by dsimp

end

/-- The map `ComposableArrows C m → ComposableArrows C n` obtained by precomposition with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`. -/
@[simps!]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (F : ComposableArrows C m) (Φ : Fin (n + 1) ⥤ Fin (m + 1))
  body: Φ ⋙ F

中文:
定义 whiskerLeft
  签名: (F : ComposableArrows C m) (Φ : 有限集 (n + 1) ⥤ 有限集 (m + 1))
  定义体: Φ ⋙ F
-/
def whiskerLeft (F : ComposableArrows C m) (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    ComposableArrows C n := Φ ⋙ F

/-- The functor `ComposableArrows C m ⥤ ComposableArrows C n` obtained by precomposition with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`. -/
@[simps!]
/--
Definition of `whiskerLeftFunctor` / `whiskerLeftFunctor` 的定义

English:
definition whiskerLeftFunctor
  signature: (Φ : Fin (n + 1) ⥤ Fin (m + 1))
  body: F.whiskerLeft Φ
  map f := Functor.whiskerLeft Φ f

中文:
定义 whiskerLeftFunctor
  签名: (Φ : 有限集 (n + 1) ⥤ 有限集 (m + 1))
  定义体: F.whiskerLeft Φ
  map f := Functor.whiskerLeft Φ f

Depends on / 依赖: F.whiskerLeft, whiskerLeft
-/
def whiskerLeftFunctor (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    ComposableArrows C m ⥤ ComposableArrows C n where
  obj F := F.whiskerLeft Φ
  map f := Functor.whiskerLeft Φ f

/-- The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.succ`. -/
@[simps]
/--
Definition of `_root_.Fin.succFunctor` / `_root_.Fin.succFunctor` 的定义

English:
definition _root_.Fin.succFunctor
  signature: (n : Nat)
  body: i.succ
  map {_ _} hij := homOfLE (Fin.succ_le_succ_iff.2 (leOfHom hij))

中文:
定义 _root_.有限集.succFunctor
  签名: (n : 自然数)
  定义体: i.succ
  map {_ _} hij := homOfLE (Fin.succ_le_succ_iff.2 (leOfHom hij))

Depends on / 依赖: i.succ
-/
def _root_.Fin.succFunctor (n : Nat) : Fin n ⥤ Fin (n + 1) where
  obj i := i.succ
  map {_ _} hij := homOfLE (Fin.succ_le_succ_iff.2 (leOfHom hij))

/-- The functor `Fin (l + 1) ⥤ Fin (n + 1)` which sends `i` to `k + i` -/
@[simps!]
/--
Definition of `_root_.Fin.natAddLEFunctor` / `_root_.Fin.natAddLEFunctor` 的定义

English:
definition _root_.Fin.natAddLEFunctor
  signature: {n k l : Nat} (h : k + l <= n)
  body: fun ⟨i, _⟩ => ⟨k + i , by lia⟩
  map {_ _} hij := homOfLE (by rw [Fin.le_iff_val_le_val]; simpa using (leOfHom hij))

中文:
定义 _root_.有限集.natAddLEFunctor
  签名: {n k l : 自然数} (h : k + l <= n)
  定义体: fun ⟨i, _⟩ => ⟨k + i , by lia⟩
  map {_ _} hij := homOfLE (by rw [Fin.le_iff_val_le_val]; simpa using (leOfHom hij))
-/
def _root_.Fin.natAddLEFunctor {n k l : Nat} (h : k + l <= n) : Fin (l + 1) ⥤ Fin (n + 1) where
  obj := fun ⟨i, _⟩ => ⟨k + i , by lia⟩
  map {_ _} hij := homOfLE (by rw [Fin.le_iff_val_le_val]; simpa using (leOfHom hij))

/-- The functor `ComposableArrows C n ⥤ ComposableArrows C l` obtained by precomposition with
the functor `Fin.natAddLEFunctor`. -/
@[simps!]
/--
Definition of `natAddLEFunctor` / `natAddLEFunctor` 的定义

English:
definition natAddLEFunctor
  signature: {n k l : Nat} (h : k + l <= n)
  body: whiskerLeftFunctor (Fin.natAddLEFunctor h)

中文:
定义 natAddLEFunctor
  签名: {n k l : 自然数} (h : k + l <= n)
  定义体: whiskerLeftFunctor (Fin.natAddLEFunctor h)

Depends on / 依赖: Fin.natAddLEFunctor, natAddLEFunctor, whiskerLeftFunctor
-/
def natAddLEFunctor {n k l : Nat} (h : k + l <= n) :
    ComposableArrows C n ⥤ ComposableArrows C l :=
  whiskerLeftFunctor (Fin.natAddLEFunctor h)

/--
lemma `natAddLEFunctor_obj'` / 引理 `natAddLEFunctor_obj'`

English:
lemma natAddLEFunctor_obj'
  statement: {n k l i : Nat} (h : k + l <= n) (R : ComposableArrows C n)
  proof: rfl

中文:
引理 natAddLEFunctor_obj'
  结论: {n k l i : 自然数} (h : k + l <= n) (R : ComposableArrows C n)
  证明: rfl

Depends on / 依赖: R.obj, natAddLEFunctor
-/
lemma natAddLEFunctor_obj' {n k l i : Nat} (h : k + l <= n) (R : ComposableArrows C n)
    (_ : i <= l := by lia) :
    ((natAddLEFunctor h).obj R).obj' i = R.obj' (k + i) := rfl

/--
lemma `natAddLEFunctor_app'` / 引理 `natAddLEFunctor_app'`

English:
lemma natAddLEFunctor_app'
  statement: {n k l i : Nat} (h : k + l <= n) {R₁ R₂ : ComposableArrows C n}
  proof: rfl

中文:
引理 natAddLEFunctor_app'
  结论: {n k l i : 自然数} (h : k + l <= n) {R₁ R₂ : ComposableArrows C n}
  证明: rfl

Depends on / 依赖: natAddLEFunctor
-/
lemma natAddLEFunctor_app' {n k l i : Nat} (h : k + l <= n) {R₁ R₂ : ComposableArrows C n}
    (φ : R₁ ⟶ R₂) (_ : i <= l := by lia) :
    app' ((natAddLEFunctor h).map φ) i = app' φ (k + i) := rfl

/-- The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the first arrow. -/
@[simps!]
/--
Definition of `δ₀Functor` / `δ₀Functor` 的定义

English:
definition δ₀Functor
  signature: : ComposableArrows C (n + 1) ⥤ ComposableArrows C n
  body: whiskerLeftFunctor (Fin.succFunctor (n + 1))

中文:
定义 δ₀Functor
  签名: : ComposableArrows C (n + 1) ⥤ ComposableArrows C n
  定义体: whiskerLeftFunctor (Fin.succFunctor (n + 1))

Depends on / 依赖: Fin.succFunctor, succFunctor, whiskerLeftFunctor
-/
def δ₀Functor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (Fin.succFunctor (n + 1))

/--
Definition of `δ₀` / `δ₀` 的定义

English:
abbreviation δ₀
  signature: (F : ComposableArrows C (n + 1))
  body: δ₀Functor.obj F

@[simp]

中文:
缩写 δ₀
  签名: (F : ComposableArrows C (n + 1))
  定义体: δ₀Functor.obj F

@[simp]

Depends on / 依赖: Functor.obj
-/
abbrev δ₀ (F : ComposableArrows C (n + 1)) := δ₀Functor.obj F

@[simp]
/--
lemma `precomp_δ₀` / 引理 `precomp_δ₀`

English:
lemma precomp_δ₀
  given: {X : C} (f : X ⟶ F.left)
  statement: (F.precomp f).δ₀ = F
  proof: rfl

中文:
引理 precomp_δ₀
  条件: {X : C} (f : X ⟶ F.left)
  结论: (F.precomp f).δ₀ = F
  证明: rfl
-/
lemma precomp_δ₀ {X : C} (f : X ⟶ F.left) : (F.precomp f).δ₀ = F := rfl

/-- The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.castSucc`. -/
@[simps]
/--
Definition of `_root_.Fin.castSuccFunctor` / `_root_.Fin.castSuccFunctor` 的定义

English:
definition _root_.Fin.castSuccFunctor
  signature: (n : Nat)
  body: i.castSucc
  map hij := hij

中文:
定义 _root_.有限集.castSuccFunctor
  签名: (n : 自然数)
  定义体: i.castSucc
  map hij := hij

Depends on / 依赖: castSucc, i.castSucc
-/
def _root_.Fin.castSuccFunctor (n : Nat) : Fin n ⥤ Fin (n + 1) where
  obj i := i.castSucc
  map hij := hij

/-- The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the last arrow. -/
@[simps!]
/--
Definition of `δlastFunctor` / `δlastFunctor` 的定义

English:
definition δlastFunctor
  signature: : ComposableArrows C (n + 1) ⥤ ComposableArrows C n
  body: whiskerLeftFunctor (Fin.castSuccFunctor (n + 1))

中文:
定义 δlastFunctor
  签名: : ComposableArrows C (n + 1) ⥤ ComposableArrows C n
  定义体: whiskerLeftFunctor (Fin.castSuccFunctor (n + 1))

Depends on / 依赖: Fin.castSuccFunctor, castSuccFunctor, whiskerLeftFunctor
-/
def δlastFunctor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (Fin.castSuccFunctor (n + 1))

/--
Definition of `δlast` / `δlast` 的定义

English:
abbreviation δlast
  signature: (F : ComposableArrows C (n + 1))
  body: δlastFunctor.obj F

中文:
缩写 δlast
  签名: (F : ComposableArrows C (n + 1))
  定义体: δlastFunctor.obj F

Depends on / 依赖: lastFunctor.obj
-/
abbrev δlast (F : ComposableArrows C (n + 1)) := δlastFunctor.obj F

section

variable {F G : ComposableArrows C (n + 1)}


/--
Definition of `homMkSucc` / `homMkSucc` 的定义

English:
definition homMkSucc
  signature: (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
  body: homMk
    (fun i => match i with
      | ⟨0, _⟩ => α
      | ⟨i + 1, hi⟩ => app' β i)
    (fun i hi => by
      obtain _ | i := i
      · exact w
      · exact naturality' β i (i + 1))

中文:
定义 homMkSucc
  签名: (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
  定义体: homMk
    (fun i => match i with
      | ⟨0, _⟩ => α
      | ⟨i + 1, hi⟩ => app' β i)
    (fun i hi => by
      obtain _ | i := i
      · exact w
      · exact naturality' β i (i + 1))

Depends on / 依赖: naturality
-/
def homMkSucc (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
    (w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1) : F ⟶ G :=
  homMk
    (fun i => match i with
      | ⟨0, _⟩ => α
      | ⟨i + 1, hi⟩ => app' β i)
    (fun i hi => by
      obtain _ | i := i
      · exact w
      · exact naturality' β i (i + 1))

variable (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
  (w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1 := by cat_disch)

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMkSucc_app_zero` / 引理 `homMkSucc_app_zero`

English:
lemma homMkSucc_app_zero
  statement: (homMkSucc α β w).app 0 = α
  proof: rfl

中文:
引理 homMkSucc_app_zero
  结论: (homMkSucc α β w).app 0 = α
  证明: rfl
-/
lemma homMkSucc_app_zero : (homMkSucc α β w).app 0 = α := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMkSucc_app_succ` / 引理 `homMkSucc_app_succ`

English:
lemma homMkSucc_app_succ
  given: (i : Nat) (hi : i + 1 < n + 1 + 1)
  proof: rfl

中文:
引理 homMkSucc_app_succ
  条件: (i : 自然数) (hi : i + 1 < n + 1 + 1)
  证明: rfl
-/
lemma homMkSucc_app_succ (i : Nat) (hi : i + 1 < n + 1 + 1) :
    (homMkSucc α β w).app ⟨i + 1, hi⟩ = app' β i := rfl

end

/--
lemma `hom_ext_succ` / 引理 `hom_ext_succ`

English:
lemma hom_ext_succ
  statement: {F G : ComposableArrows C (n + 1)} {f g : F ⟶ G}
  proof: by
  ext ⟨i, hi⟩
  obtain _ | i := i
  · exact h₀
  · exact congr_app h₁ ⟨i, by valid⟩

中文:
引理 hom_ext_succ
  结论: {F G : ComposableArrows C (n + 1)} {f g : F ⟶ G}
  证明: by
  ext ⟨i, hi⟩
  obtain _ | i := i
  · exact h₀
  · exact congr_app h₁ ⟨i, by valid⟩

Depends on / 依赖: congr_app
-/
lemma hom_ext_succ {F G : ComposableArrows C (n + 1)} {f g : F ⟶ G}
    (h₀ : app' f 0 = app' g 0) (h₁ : δ₀Functor.map f = δ₀Functor.map g) : f = g := by
  ext ⟨i, hi⟩
  obtain _ | i := i
  · exact h₀
  · exact congr_app h₁ ⟨i, by valid⟩

set_option backward.isDefEq.respectTransparency false in
/-- Inductive construction of isomorphisms in `ComposableArrows C (n + 1)`: in order to
construct an isomorphism `F ≅ G`, it suffices to provide `α : F.obj' 0 ≅ G.obj' 0` and
`β : F.δ₀ ≅ G.δ₀` such that `F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1`. -/
@[simps]
/--
Definition of `isoMkSucc` / `isoMkSucc` 的定义

English:
definition isoMkSucc
  signature: {F G : ComposableArrows C (n + 1)} (α : F.obj' 0 ≅ G.obj' 0)
  body: homMkSucc α.hom β.hom w
  inv := homMkSucc α.inv β.inv (by
    rw [← cancel_epi α.hom]; rw [← reassoc_of% w]; rw [α.hom_inv_id_assoc]; rw [β.hom_inv_id_app]
    dsimp
    rw [comp_id])
  hom_inv_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp
  inv_hom_id := by
    apply hom_

中文:
定义 isoMkSucc
  签名: {F G : ComposableArrows C (n + 1)} (α : F.obj' 0 ≅ G.obj' 0)
  定义体: homMkSucc α.hom β.hom w
  inv := homMkSucc α.inv β.inv (by
    rw [← cancel_epi α.hom]; rw [← reassoc_of% w]; rw [α.hom_inv_id_assoc]; rw [β.hom_inv_id_app]
    dsimp
    rw [comp_id])
  hom_inv_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp
  inv_hom_id := by
    apply hom_

Depends on / 依赖: homMkSucc
-/
def isoMkSucc {F G : ComposableArrows C (n + 1)} (α : F.obj' 0 ≅ G.obj' 0)
    (β : F.δ₀ ≅ G.δ₀) (w : F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1) : F ≅ G where
  hom := homMkSucc α.hom β.hom w
  inv := homMkSucc α.inv β.inv (by
    rw [← cancel_epi α.hom]; rw [← reassoc_of% w]; rw [α.hom_inv_id_assoc]; rw [β.hom_inv_id_app]
    dsimp
    rw [comp_id])
  hom_inv_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp
  inv_hom_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ext_succ` / 引理 `ext_succ`

English:
lemma ext_succ
  statement: {F G : ComposableArrows C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0)
  proof: by
  have : forall i, F.obj i = G.obj i := by
    intro ⟨i, hi⟩
    rcases i with - | i
    · exact h₀
    · exact Functor.congr_obj h ⟨i, by valid⟩
  exact Functor.ext_of_iso (isoMkSucc (eqToIso h₀) (eqToIso h) (by
      rw [w]
      dsimp [app']
      rw [eqToHom_app]; rw [assoc]; rw [assoc]; rw [

中文:
引理 ext_succ
  结论: {F G : ComposableArrows C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0)
  证明: by
  have : forall i, F.obj i = G.obj i := by
    intro ⟨i, hi⟩
    rcases i with - | i
    · exact h₀
    · exact Functor.congr_obj h ⟨i, by valid⟩
  exact Functor.ext_of_iso (isoMkSucc (eqToIso h₀) (eqToIso h) (by
      rw [w]
      dsimp [app']
      rw [eqToHom_app]; rw [assoc]; rw [assoc]; rw [

Depends on / 依赖: F.obj, Functor, Functor.congr_obj, Functor.ext_of_iso, G.obj, comp_id, congr_obj, eqToHom_app, eqToHom_refl, eqToHom_trans, eqToIso, ext_of_iso, isoMkSucc
-/
lemma ext_succ {F G : ComposableArrows C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0)
    (h : F.δ₀ = G.δ₀) (w : F.map' 0 1 = eqToHom h₀ ≫ G.map' 0 1 ≫
      eqToHom (Functor.congr_obj h.symm 0)) : F = G := by
  have : forall i, F.obj i = G.obj i := by
    intro ⟨i, hi⟩
    rcases i with - | i
    · exact h₀
    · exact Functor.congr_obj h ⟨i, by valid⟩
  exact Functor.ext_of_iso (isoMkSucc (eqToIso h₀) (eqToIso h) (by
      rw [w]
      dsimp [app']
      rw [eqToHom_app]; rw [assoc]; rw [assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [comp_id])) this
    (by rintro ⟨_ | _, hi⟩ <;> simp)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `precomp_surjective` / 引理 `precomp_surjective`

English:
lemma precomp_surjective
  given: (F : ComposableArrows C (n + 1))
  proof: ⟨F.δ₀, _, F.map' 0 1, ext_succ rfl (by simp) (by simp)⟩

中文:
引理 precomp_surjective
  条件: (F : ComposableArrows C (n + 1))
  证明: ⟨F.δ₀, _, F.map' 0 1, ext_succ rfl (by simp) (by simp)⟩

Depends on / 依赖: F.map, ext_succ
-/
lemma precomp_surjective (F : ComposableArrows C (n + 1)) :
    exists (F₀ : ComposableArrows C n) (X₀ : C) (f₀ : X₀ ⟶ F₀.left), F = F₀.precomp f₀ :=
  ⟨F.δ₀, _, F.map' 0 1, ext_succ rfl (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
    (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `homMk₂` / `homMk₂` 的定义

English:
definition homMk₂
  signature: : f ⟶ g
  body: homMkSucc app₀ (homMk₁ app₁ app₂ w₁) w₀

中文:
定义 homMk₂
  签名: : f ⟶ g
  定义体: homMkSucc app₀ (homMk₁ app₁ app₂ w₁) w₀

Depends on / 依赖: homMkSucc
-/
def homMk₂ : f ⟶ g := homMkSucc app₀ (homMk₁ app₁ app₂ w₁) w₀

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₂_app_zero` / 引理 `homMk₂_app_zero`

English:
lemma homMk₂_app_zero
  statement: (homMk₂ app₀ app₁ app₂ w₀ w₁).app 0 = app₀
  proof: rfl

中文:
引理 homMk₂_app_zero
  结论: (homMk₂ app₀ app₁ app₂ w₀ w₁).app 0 = app₀
  证明: rfl
-/
lemma homMk₂_app_zero : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₂_app_one` / 引理 `homMk₂_app_one`

English:
lemma homMk₂_app_one
  statement: (homMk₂ app₀ app₁ app₂ w₀ w₁).app 1 = app₁
  proof: rfl

中文:
引理 homMk₂_app_one
  结论: (homMk₂ app₀ app₁ app₂ w₀ w₁).app 1 = app₁
  证明: rfl
-/
lemma homMk₂_app_one : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₂_app_two` / 引理 `homMk₂_app_two`

English:
lemma homMk₂_app_two
  statement: (homMk₂ app₀ app₁ app₂ w₀ w₁).app 2 = app₂
  proof: rfl

中文:
引理 homMk₂_app_two
  结论: (homMk₂ app₀ app₁ app₂ w₀ w₁).app 2 = app₂
  证明: rfl
-/
lemma homMk₂_app_two : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 2 = app₂ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₂_app_two'` / 引理 `homMk₂_app_two'`

English:
lemma homMk₂_app_two'
  statement: (homMk₂ app₀ app₁ app₂ w₀ w₁).app ⟨2, by valid⟩ = app₂
  proof: rfl

中文:
引理 homMk₂_app_two'
  结论: (homMk₂ app₀ app₁ app₂ w₀ w₁).app ⟨2, by valid⟩ = app₂
  证明: rfl
-/
lemma homMk₂_app_two' : (homMk₂ app₀ app₁ app₂ w₀ w₁).app ⟨2, by valid⟩ = app₂ := rfl

end

@[ext]
/--
lemma `hom_ext₂` / 引理 `hom_ext₂`

English:
lemma hom_ext₂
  statement: {f g : ComposableArrows C 2} {φ φ' : f ⟶ g}
  proof: hom_ext_succ h₀ (hom_ext₁ h₁ h₂)

中文:
引理 hom_ext₂
  结论: {f g : ComposableArrows C 2} {φ φ' : f ⟶ g}
  证明: hom_ext_succ h₀ (hom_ext₁ h₁ h₂)

Depends on / 依赖: hom_ext_succ
-/
lemma hom_ext₂ {f g : ComposableArrows C 2} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₁ h₁ h₂)

/-- Constructor for isomorphisms in `ComposableArrows C 2`. -/
@[simps]
/--
Definition of `isoMk₂` / `isoMk₂` 的定义

English:
definition isoMk₂
  signature: {f g : ComposableArrows C 2}
  body: homMk₂ app₀.hom app₁.hom app₂.hom w₀ w₁
  inv := homMk₂ app₀.inv app₁.inv app₂.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])

中文:
定义 isoMk₂
  签名: {f g : ComposableArrows C 2}
  定义体: homMk₂ app₀.hom app₁.hom app₂.hom w₀ w₁
  inv := homMk₂ app₀.inv app₁.inv app₂.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])

Depends on / 依赖: cancel_epi, cat_disch, comp_id, f.map, g.map, hom_inv_id, hom_inv_id_assoc, reassoc_of
-/
def isoMk₂ {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1 := by cat_disch)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2 := by cat_disch) : f ≅ g where
  hom := homMk₂ app₀.hom app₁.hom app₂.hom w₀ w₁
  inv := homMk₂ app₀.inv app₁.inv app₂.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])

/--
lemma `isIso_iff₂` / 引理 `isIso_iff₂`

English:
lemma isIso_iff₂
  given: {F G : ComposableArrows C 2} (f : F ⟶ G)
  proof: by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => ⟨h 0, h 1, h 2⟩, fun _ i => by fin_cases i <;> tauto⟩

中文:
引理 isIso_iff₂
  条件: {F G : ComposableArrows C 2} (f : F ⟶ G)
  证明: by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => ⟨h 0, h 1, h 2⟩, fun _ i => by fin_cases i <;> tauto⟩

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, fin_cases, isIso_iff_isIso_app
-/
lemma isIso_iff₂ {F G : ComposableArrows C 2} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) ∧ IsIso (f.app 2) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h => ⟨h 0, h 1, h 2⟩, fun _ i => by fin_cases i <;> tauto⟩

/--
lemma `ext₂` / 引理 `ext₂`

English:
lemma ext₂
  statement: {f g : ComposableArrows C 2}
  proof: ext_succ h₀ (ext₁ h₁ h₂ w₁) w₀

中文:
引理 ext₂
  结论: {f g : ComposableArrows C 2}
  证明: ext_succ h₀ (ext₁ h₁ h₂ w₁) w₀

Depends on / 依赖: ext_succ
-/
lemma ext₂ {f g : ComposableArrows C 2}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm) : f = g :=
  ext_succ h₀ (ext₁ h₁ h₂ w₁) w₀

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mk₂_surjective` / 引理 `mk₂_surjective`

English:
lemma mk₂_surjective
  given: (X : ComposableArrows C 2)
  proof: ⟨_, _, _, X.map' 0 1, X.map' 1 2, ext₂ rfl rfl rfl (by simp) (by simp)⟩

中文:
引理 mk₂_surjective
  条件: (X : ComposableArrows C 2)
  证明: ⟨_, _, _, X.map' 0 1, X.map' 1 2, ext₂ rfl rfl rfl (by simp) (by simp)⟩

Depends on / 依赖: X.map
-/
lemma mk₂_surjective (X : ComposableArrows C 2) :
    exists (X₀ X₁ X₂ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂), X = mk₂ f₀ f₁ :=
  ⟨_, _, _, X.map' 0 1, X.map' 1 2, ext₂ rfl rfl rfl (by simp) (by simp)⟩

/--
lemma `ext₂_of_arrow` / 引理 `ext₂_of_arrow`

English:
lemma ext₂_of_arrow
  statement: {f g : ComposableArrows C 2}
  proof: by
  obtain ⟨x₀, x₁, x₂, f, f', rfl⟩ := mk₂_surjective f
  obtain ⟨y₀, y₁, y₂, g, g', rfl⟩ := mk₂_surjective g
  obtain rfl : x₀ = y₀ := congr_arg Arrow.leftFunc.obj h₀₁
  obtain rfl : x₁ = y₁ := congr_arg Arrow.rightFunc.obj h₀₁
  obtain rfl : x₂ = y₂ := congr_arg Arrow.rightFunc.obj h₁₂
  obtain r

中文:
引理 ext₂_of_arrow
  结论: {f g : ComposableArrows C 2}
  证明: by
  obtain ⟨x₀, x₁, x₂, f, f', rfl⟩ := mk₂_surjective f
  obtain ⟨y₀, y₁, y₂, g, g', rfl⟩ := mk₂_surjective g
  obtain rfl : x₀ = y₀ := congr_arg Arrow.leftFunc.obj h₀₁
  obtain rfl : x₁ = y₁ := congr_arg Arrow.rightFunc.obj h₀₁
  obtain rfl : x₂ = y₂ := congr_arg Arrow.rightFunc.obj h₁₂
  obtain r

Depends on / 依赖: Arrow.leftFunc.obj, Arrow.mk_inj, Arrow.rightFunc.obj, congr_arg, leftFunc, mk_inj, rightFunc
-/
lemma ext₂_of_arrow {f g : ComposableArrows C 2}
    (h₀₁ : Arrow.mk (f.map' 0 1) = Arrow.mk (g.map' 0 1))
    (h₁₂ : Arrow.mk (f.map' 1 2) = Arrow.mk (g.map' 1 2)) : f = g := by
  obtain ⟨x₀, x₁, x₂, f, f', rfl⟩ := mk₂_surjective f
  obtain ⟨y₀, y₁, y₂, g, g', rfl⟩ := mk₂_surjective g
  obtain rfl : x₀ = y₀ := congr_arg Arrow.leftFunc.obj h₀₁
  obtain rfl : x₁ = y₁ := congr_arg Arrow.rightFunc.obj h₀₁
  obtain rfl : x₂ = y₂ := congr_arg Arrow.rightFunc.obj h₁₂
  obtain rfl : f = g := by rwa [← Arrow.mk_inj]
  obtain rfl : f' = g' := by rwa [← Arrow.mk_inj]
  rfl

section

variable
  {f g : ComposableArrows C 3}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `homMk₃` / `homMk₃` 的定义

English:
definition homMk₃
  signature: : f ⟶ g
  body: homMkSucc app₀ (homMk₂ app₁ app₂ app₃ w₁ w₂) w₀

中文:
定义 homMk₃
  签名: : f ⟶ g
  定义体: homMkSucc app₀ (homMk₂ app₁ app₂ app₃ w₁ w₂) w₀

Depends on / 依赖: homMkSucc
-/
def homMk₃ : f ⟶ g := homMkSucc app₀ (homMk₂ app₁ app₂ app₃ w₁ w₂) w₀

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₃_app_zero` / 引理 `homMk₃_app_zero`

English:
lemma homMk₃_app_zero
  statement: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 0 = app₀
  proof: rfl

中文:
引理 homMk₃_app_zero
  结论: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 0 = app₀
  证明: rfl

Depends on / 依赖: reflectsLimit_of_reflectsLimitsOfShape
-/
lemma homMk₃_app_zero : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₃_app_one` / 引理 `homMk₃_app_one`

English:
lemma homMk₃_app_one
  statement: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 1 = app₁
  proof: rfl

中文:
引理 homMk₃_app_one
  结论: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 1 = app₁
  证明: rfl

Depends on / 依赖: reflectsColimit_of_reflectsColimitsOfShape
-/
lemma homMk₃_app_one : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₃_app_two` / 引理 `homMk₃_app_two`

English:
lemma homMk₃_app_two
  statement: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨2, by valid⟩ = app₂
  proof: rfl

中文:
引理 homMk₃_app_two
  结论: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨2, by valid⟩ = app₂
  证明: rfl

Depends on / 依赖: Category, reflectsLimitsOfShape_of_reflectsLimits
-/
lemma homMk₃_app_two : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨2, by valid⟩ = app₂ :=
  rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₃_app_three` / 引理 `homMk₃_app_three`

English:
lemma homMk₃_app_three
  statement: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨3, by valid⟩ = app₃
  proof: rfl

中文:
引理 homMk₃_app_three
  结论: (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨3, by valid⟩ = app₃
  证明: rfl

Depends on / 依赖: reflectsColimitsOfShape_of_reflectsColimits
-/
lemma homMk₃_app_three : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨3, by valid⟩ = app₃ :=
  rfl

end

@[ext]
/--
lemma `hom_ext₃` / 引理 `hom_ext₃`

English:
lemma hom_ext₃
  statement: {f g : ComposableArrows C 3} {φ φ' : f ⟶ g}
  proof: hom_ext_succ h₀ (hom_ext₂ h₁ h₂ h₃)

中文:
引理 hom_ext₃
  结论: {f g : ComposableArrows C 3} {φ φ' : f ⟶ g}
  证明: hom_ext_succ h₀ (hom_ext₂ h₁ h₂ h₃)

Depends on / 依赖: hom_ext_succ
-/
lemma hom_ext₃ {f g : ComposableArrows C 3} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₂ h₁ h₂ h₃)

/-- Constructor for isomorphisms in `ComposableArrows C 3`. -/
@[simps]
/--
Definition of `isoMk₃` / `isoMk₃` 的定义

English:
definition isoMk₃
  signature: {f g : ComposableArrows C 3}
  body: homMk₃ app₀.hom app₁.hom app₂.hom app₃.hom w₀ w₁ w₂
  inv := homMk₃ app₀.inv app₁.inv app₂.inv app₃.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, ap

中文:
定义 isoMk₃
  签名: {f g : ComposableArrows C 3}
  定义体: homMk₃ app₀.hom app₁.hom app₂.hom app₃.hom w₀ w₁ w₂
  inv := homMk₃ app₀.inv app₁.inv app₂.inv app₃.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, ap
-/
def isoMk₃ {f g : ComposableArrows C 3}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3) : f ≅ g where
  hom := homMk₃ app₀.hom app₁.hom app₂.hom app₃.hom w₀ w₁ w₂
  inv := homMk₃ app₀.inv app₁.inv app₂.inv app₃.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])
    (by rw [← cancel_epi app₂.hom, ← reassoc_of% w₂, app₃.hom_inv_id,
      comp_id, app₂.hom_inv_id_assoc])

/--
lemma `ext₃` / 引理 `ext₃`

English:
lemma ext₃
  statement: {f g : ComposableArrows C 3}
  proof: ext_succ h₀ (ext₂ h₁ h₂ h₃ w₁ w₂) w₀

中文:
引理 ext₃
  结论: {f g : ComposableArrows C 3}
  证明: ext_succ h₀ (ext₂ h₁ h₂ h₃ w₁ w₂) w₀

Depends on / 依赖: ext_succ
-/
lemma ext₃ {f g : ComposableArrows C 3}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm) : f = g :=
  ext_succ h₀ (ext₂ h₁ h₂ h₃ w₁ w₂) w₀

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mk₃_surjective` / 引理 `mk₃_surjective`

English:
lemma mk₃_surjective
  given: (X : ComposableArrows C 3)
  proof: ⟨_, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3,
    ext₃ rfl rfl rfl rfl (by simp) (by simp) (by simp)⟩

中文:
引理 mk₃_surjective
  条件: (X : ComposableArrows C 3)
  证明: ⟨_, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3,
    ext₃ rfl rfl rfl rfl (by simp) (by simp) (by simp)⟩

Depends on / 依赖: X.map
-/
lemma mk₃_surjective (X : ComposableArrows C 3) :
    exists (X₀ X₁ X₂ X₃ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃), X = mk₃ f₀ f₁ f₂ :=
  ⟨_, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3,
    ext₃ rfl rfl rfl rfl (by simp) (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 4}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3) (app₄ : f.obj' 4 ⟶ g.obj' 4)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)
  (w₃ : f.map' 3 4 ≫ app₄ = app₃ ≫ g.map' 3 4 := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `homMk₄` / `homMk₄` 的定义

English:
definition homMk₄
  signature: : f ⟶ g
  body: homMkSucc app₀ (homMk₃ app₁ app₂ app₃ app₄ w₁ w₂ w₃) w₀

中文:
定义 homMk₄
  签名: : f ⟶ g
  定义体: homMkSucc app₀ (homMk₃ app₁ app₂ app₃ app₄ w₁ w₂ w₃) w₀

Depends on / 依赖: homMkSucc
-/
def homMk₄ : f ⟶ g := homMkSucc app₀ (homMk₃ app₁ app₂ app₃ app₄ w₁ w₂ w₃) w₀

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₄_app_zero` / 引理 `homMk₄_app_zero`

English:
lemma homMk₄_app_zero
  statement: (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 0 = app₀
  proof: rfl

中文:
引理 homMk₄_app_zero
  结论: (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 0 = app₀
  证明: rfl
-/
lemma homMk₄_app_zero : (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₄_app_one` / 引理 `homMk₄_app_one`

English:
lemma homMk₄_app_one
  statement: (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 1 = app₁
  proof: rfl

中文:
引理 homMk₄_app_one
  结论: (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 1 = app₁
  证明: rfl
-/
lemma homMk₄_app_one : (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₄_app_two` / 引理 `homMk₄_app_two`

English:
lemma homMk₄_app_two
  proof: rfl

中文:
引理 homMk₄_app_two
  证明: rfl
-/
lemma homMk₄_app_two :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨2, by valid⟩ = app₂ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₄_app_three` / 引理 `homMk₄_app_three`

English:
lemma homMk₄_app_three
  proof: rfl

中文:
引理 homMk₄_app_three
  证明: rfl
-/
lemma homMk₄_app_three :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨3, by valid⟩ = app₃ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₄_app_four` / 引理 `homMk₄_app_four`

English:
lemma homMk₄_app_four
  proof: rfl

中文:
引理 homMk₄_app_four
  证明: rfl
-/
lemma homMk₄_app_four :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨4, by valid⟩ = app₄ := rfl

end

@[ext]
/--
lemma `hom_ext₄` / 引理 `hom_ext₄`

English:
lemma hom_ext₄
  statement: {f g : ComposableArrows C 4} {φ φ' : f ⟶ g}
  proof: hom_ext_succ h₀ (hom_ext₃ h₁ h₂ h₃ h₄)

中文:
引理 hom_ext₄
  结论: {f g : ComposableArrows C 4} {φ φ' : f ⟶ g}
  证明: hom_ext_succ h₀ (hom_ext₃ h₁ h₂ h₃ h₄)

Depends on / 依赖: hom_ext_succ
-/
lemma hom_ext₄ {f g : ComposableArrows C 4} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) (h₄ : app' φ 4 = app' φ' 4) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₃ h₁ h₂ h₃ h₄)

/--
lemma `map'_inv_eq_inv_map'` / 引理 `map'_inv_eq_inv_map'`

English:
lemma map'_inv_eq_inv_map'
  statement: {n m : Nat} (h : n + 1 <= m) {f g : ComposableArrows C m}
  proof: by
  rw [← cancel_epi app.hom]; rw [← reassoc_of% w]; rw [app'.hom_inv_id]; rw [comp_id]; rw [app.hom_inv_id_assoc]

中文:
引理 map'_inv_eq_inv_map'
  结论: {n m : 自然数} (h : n + 1 <= m) {f g : ComposableArrows C m}
  证明: by
  rw [← cancel_epi app.hom]; rw [← reassoc_of% w]; rw [app'.hom_inv_id]; rw [comp_id]; rw [app.hom_inv_id_assoc]
-/
lemma map'_inv_eq_inv_map' {n m : Nat} (h : n + 1 <= m) {f g : ComposableArrows C m}
    (app : f.obj' n ≅ g.obj' n) (app' : f.obj' (n + 1) ≅ g.obj' (n + 1))
    (w : f.map' n (n + 1) ≫ app'.hom = app.hom ≫ g.map' n (n + 1)) :
    map' g n (n + 1) ≫ app'.inv = app.inv ≫ map' f n (n + 1) := by
  rw [← cancel_epi app.hom]; rw [← reassoc_of% w]; rw [app'.hom_inv_id]; rw [comp_id]; rw [app.hom_inv_id_assoc]

/-- Constructor for isomorphisms in `ComposableArrows C 4`. -/
@[simps]
/--
Definition of `isoMk₄` / `isoMk₄` 的定义

English:
definition isoMk₄
  signature: {f g : ComposableArrows C 4}
  body: homMk₄ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom w₀ w₁ w₂ w₃
  inv := homMk₄ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂]

中文:
定义 isoMk₄
  签名: {f g : ComposableArrows C 4}
  定义体: homMk₄ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom w₀ w₁ w₂ w₃
  inv := homMk₄ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂]
-/
def isoMk₄ {f g : ComposableArrows C 4}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3) (app₄ : f.obj' 4 ≅ g.obj' 4)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3)
    (w₃ : f.map' 3 4 ≫ app₄.hom = app₃.hom ≫ g.map' 3 4) :
    f ≅ g where
  hom := homMk₄ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom w₀ w₁ w₂ w₃
  inv := homMk₄ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂])
    (by rw [map'_inv_eq_inv_map' (by valid) app₃ app₄ w₃])

/--
lemma `ext₄` / 引理 `ext₄`

English:
lemma ext₄
  statement: {f g : ComposableArrows C 4}
  proof: ext_succ h₀ (ext₃ h₁ h₂ h₃ h₄ w₁ w₂ w₃) w₀

中文:
引理 ext₄
  结论: {f g : ComposableArrows C 4}
  证明: ext_succ h₀ (ext₃ h₁ h₂ h₃ h₄ w₁ w₂ w₃) w₀

Depends on / 依赖: ext_succ
-/
lemma ext₄ {f g : ComposableArrows C 4}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3) (h₄ : f.obj' 4 = g.obj' 4)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm)
    (w₃ : f.map' 3 4 = eqToHom h₃ ≫ g.map' 3 4 ≫ eqToHom h₄.symm) :
    f = g :=
  ext_succ h₀ (ext₃ h₁ h₂ h₃ h₄ w₁ w₂ w₃) w₀

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mk₄_surjective` / 引理 `mk₄_surjective`

English:
lemma mk₄_surjective
  given: (X : ComposableArrows C 4)
  proof: ⟨_, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4,
    ext₄ rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp)⟩

中文:
引理 mk₄_surjective
  条件: (X : ComposableArrows C 4)
  证明: ⟨_, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4,
    ext₄ rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp)⟩

Depends on / 依赖: X.map
-/
lemma mk₄_surjective (X : ComposableArrows C 4) :
    exists (X₀ X₁ X₂ X₃ X₄ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄),
      X = mk₄ f₀ f₁ f₂ f₃ :=
  ⟨_, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4,
    ext₄ rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 5}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3) (app₄ : f.obj' 4 ⟶ g.obj' 4) (app₅ : f.obj' 5 ⟶ g.obj' 5)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)
  (w₃ : f.map' 3 4 ≫ app₄ = app₃ ≫ g.map' 3 4 := by cat_disch)
  (w₄ : f.map' 4 5 ≫ app₅ = app₄ ≫ g.map' 4 5 := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `homMk₅` / `homMk₅` 的定义

English:
definition homMk₅
  signature: : f ⟶ g
  body: homMkSucc app₀ (homMk₄ app₁ app₂ app₃ app₄ app₅ w₁ w₂ w₃ w₄) w₀

中文:
定义 homMk₅
  签名: : f ⟶ g
  定义体: homMkSucc app₀ (homMk₄ app₁ app₂ app₃ app₄ app₅ w₁ w₂ w₃ w₄) w₀

Depends on / 依赖: homMkSucc
-/
def homMk₅ : f ⟶ g := homMkSucc app₀ (homMk₄ app₁ app₂ app₃ app₄ app₅ w₁ w₂ w₃ w₄) w₀

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₅_app_zero` / 引理 `homMk₅_app_zero`

English:
lemma homMk₅_app_zero
  statement: (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 0 = app₀
  proof: rfl

中文:
引理 homMk₅_app_zero
  结论: (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 0 = app₀
  证明: rfl
-/
lemma homMk₅_app_zero : (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₅_app_one` / 引理 `homMk₅_app_one`

English:
lemma homMk₅_app_one
  statement: (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 1 = app₁
  proof: rfl

中文:
引理 homMk₅_app_one
  结论: (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 1 = app₁
  证明: rfl
-/
lemma homMk₅_app_one : (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₅_app_two` / 引理 `homMk₅_app_two`

English:
lemma homMk₅_app_two
  proof: rfl

中文:
引理 homMk₅_app_two
  证明: rfl
-/
lemma homMk₅_app_two :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨2, by valid⟩ = app₂ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₅_app_three` / 引理 `homMk₅_app_three`

English:
lemma homMk₅_app_three
  proof: rfl

中文:
引理 homMk₅_app_three
  证明: rfl
-/
lemma homMk₅_app_three :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨3, by valid⟩ = app₃ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₅_app_four` / 引理 `homMk₅_app_four`

English:
lemma homMk₅_app_four
  proof: rfl

中文:
引理 homMk₅_app_four
  证明: rfl
-/
lemma homMk₅_app_four :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨4, by valid⟩ = app₄ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `homMk₅_app_five` / 引理 `homMk₅_app_five`

English:
lemma homMk₅_app_five
  proof: rfl

中文:
引理 homMk₅_app_five
  证明: rfl
-/
lemma homMk₅_app_five :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨5, by valid⟩ = app₅ := rfl

end

@[ext]
/--
lemma `hom_ext₅` / 引理 `hom_ext₅`

English:
lemma hom_ext₅
  statement: {f g : ComposableArrows C 5} {φ φ' : f ⟶ g}
  proof: hom_ext_succ h₀ (hom_ext₄ h₁ h₂ h₃ h₄ h₅)

中文:
引理 hom_ext₅
  结论: {f g : ComposableArrows C 5} {φ φ' : f ⟶ g}
  证明: hom_ext_succ h₀ (hom_ext₄ h₁ h₂ h₃ h₄ h₅)

Depends on / 依赖: hom_ext_succ
-/
lemma hom_ext₅ {f g : ComposableArrows C 5} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) (h₄ : app' φ 4 = app' φ' 4) (h₅ : app' φ 5 = app' φ' 5) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₄ h₁ h₂ h₃ h₄ h₅)

/-- Constructor for isomorphisms in `ComposableArrows C 5`. -/
@[simps]
/--
Definition of `isoMk₅` / `isoMk₅` 的定义

English:
definition isoMk₅
  signature: {f g : ComposableArrows C 5}
  body: homMk₅ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom app₅.hom w₀ w₁ w₂ w₃ w₄
  inv := homMk₅ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv app₅.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by

中文:
定义 isoMk₅
  签名: {f g : ComposableArrows C 5}
  定义体: homMk₅ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom app₅.hom w₀ w₁ w₂ w₃ w₄
  inv := homMk₅ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv app₅.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by
-/
def isoMk₅ {f g : ComposableArrows C 5}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3) (app₄ : f.obj' 4 ≅ g.obj' 4) (app₅ : f.obj' 5 ≅ g.obj' 5)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3)
    (w₃ : f.map' 3 4 ≫ app₄.hom = app₃.hom ≫ g.map' 3 4)
    (w₄ : f.map' 4 5 ≫ app₅.hom = app₄.hom ≫ g.map' 4 5) :
    f ≅ g where
  hom := homMk₅ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom app₅.hom w₀ w₁ w₂ w₃ w₄
  inv := homMk₅ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv app₅.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂])
    (by rw [map'_inv_eq_inv_map' (by valid) app₃ app₄ w₃])
    (by rw [map'_inv_eq_inv_map' (by valid) app₄ app₅ w₄])

/--
lemma `ext₅` / 引理 `ext₅`

English:
lemma ext₅
  statement: {f g : ComposableArrows C 5}
  proof: ext_succ h₀ (ext₄ h₁ h₂ h₃ h₄ h₅ w₁ w₂ w₃ w₄) w₀

中文:
引理 ext₅
  结论: {f g : ComposableArrows C 5}
  证明: ext_succ h₀ (ext₄ h₁ h₂ h₃ h₄ h₅ w₁ w₂ w₃ w₄) w₀

Depends on / 依赖: ext_succ
-/
lemma ext₅ {f g : ComposableArrows C 5}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3) (h₄ : f.obj' 4 = g.obj' 4) (h₅ : f.obj' 5 = g.obj' 5)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm)
    (w₃ : f.map' 3 4 = eqToHom h₃ ≫ g.map' 3 4 ≫ eqToHom h₄.symm)
    (w₄ : f.map' 4 5 = eqToHom h₄ ≫ g.map' 4 5 ≫ eqToHom h₅.symm) :
    f = g :=
  ext_succ h₀ (ext₄ h₁ h₂ h₃ h₄ h₅ w₁ w₂ w₃ w₄) w₀

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mk₅_surjective` / 引理 `mk₅_surjective`

English:
lemma mk₅_surjective
  given: (X : ComposableArrows C 5)
  proof: ⟨_, _, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4, X.map' 4 5,
    ext₅ rfl rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp)⟩

中文:
引理 mk₅_surjective
  条件: (X : ComposableArrows C 5)
  证明: ⟨_, _, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4, X.map' 4 5,
    ext₅ rfl rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp)⟩

Depends on / 依赖: X.map
-/
lemma mk₅_surjective (X : ComposableArrows C 5) :
    exists (X₀ X₁ X₂ X₃ X₄ X₅ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
      (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅), X = mk₅ f₀ f₁ f₂ f₃ f₄ :=
  ⟨_, _, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4, X.map' 4 5,
    ext₅ rfl rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp)⟩

/--
Definition of `arrow` / `arrow` 的定义

English:
definition arrow
  signature: (i : Nat) (hi : i < n := by valid)
  body: mk₁ (F.map' i (i + 1))

中文:
定义 arrow
  签名: (i : 自然数) (hi : i < n := by valid)
  定义体: mk₁ (F.map' i (i + 1))

Depends on / 依赖: ComposableArrows, F.map
-/
def arrow (i : Nat) (hi : i < n := by valid) :
    ComposableArrows C 1 := mk₁ (F.map' i (i + 1))

section mkOfObjOfMapSucc

variable (obj : Fin (n + 1) -> C) (mapSucc : forall (i : Fin n), obj i.castSucc ⟶ obj i.succ)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mkOfObjOfMapSucc_exists` / 引理 `mkOfObjOfMapSucc_exists`

English:
lemma mkOfObjOfMapSucc_exists
  statement: exists (F : ComposableArrows C n) (e : forall i, F.obj i ≅ obj i),
  proof: by
  induction n with
  | zero => exact ⟨mk₀ (obj 0), fun 0 => Iso.refl _, fun i hi => by simp at hi⟩
  | succ n hn =>
    obtain ⟨F, e, h⟩ := hn (fun i => obj i.succ) (fun i => mapSucc i.succ)
    refine ⟨F.precomp (mapSucc 0 ≫ (e 0).inv), fun i => match i with
      | 0 => Iso.refl _
      | ⟨i + 

中文:
引理 mkOfObjOfMapSucc_存在
  结论: 存在 (F : ComposableArrows C n) (e : 对任意 i, F.obj i ≅ obj i),
  证明: by
  induction n with
  | zero => exact ⟨mk₀ (obj 0), fun 0 => Iso.refl _, fun i hi => by simp at hi⟩
  | succ n hn =>
    obtain ⟨F, e, h⟩ := hn (fun i => obj i.succ) (fun i => mapSucc i.succ)
    refine ⟨F.precomp (mapSucc 0 ≫ (e 0).inv), fun i => match i with
      | 0 => Iso.refl _
      | ⟨i + 

Depends on / 依赖: F.precomp, Iso.refl, i.succ, mapSucc, precomp
-/
lemma mkOfObjOfMapSucc_exists : exists (F : ComposableArrows C n) (e : forall i, F.obj i ≅ obj i),
    forall (i : Nat) (hi : i < n), mapSucc ⟨i, hi⟩ =
      (e ⟨i, _⟩).inv ≫ F.map' i (i + 1) ≫ (e ⟨i + 1, _⟩).hom := by
  induction n with
  | zero => exact ⟨mk₀ (obj 0), fun 0 => Iso.refl _, fun i hi => by simp at hi⟩
  | succ n hn =>
    obtain ⟨F, e, h⟩ := hn (fun i => obj i.succ) (fun i => mapSucc i.succ)
    refine ⟨F.precomp (mapSucc 0 ≫ (e 0).inv), fun i => match i with
      | 0 => Iso.refl _
      | ⟨i + 1, hi⟩ => e _, fun i hi => ?_⟩
    obtain _ | i := i
    · simp
    · exact h i (by valid)

/--
Definition of `mkOfObjOfMapSucc` / `mkOfObjOfMapSucc` 的定义

English:
definition mkOfObjOfMapSucc
  signature: : ComposableArrows C n
  body: (mkOfObjOfMapSucc_exists obj mapSucc).choose.copyObj obj
    (mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose

@[simp]

中文:
定义 mkOfObjOfMapSucc
  签名: : ComposableArrows C n
  定义体: (mkOfObjOfMapSucc_exists obj mapSucc).choose.copyObj obj
    (mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose

@[simp]

Depends on / 依赖: choose.copyObj, choose_spec, choose_spec.choose, copyObj, mapSucc, mkOfObjOfMapSucc_exists
-/
noncomputable def mkOfObjOfMapSucc : ComposableArrows C n :=
  (mkOfObjOfMapSucc_exists obj mapSucc).choose.copyObj obj
    (mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose

@[simp]
/--
lemma `mkOfObjOfMapSucc_obj` / 引理 `mkOfObjOfMapSucc_obj`

English:
lemma mkOfObjOfMapSucc_obj
  given: (i : Fin (n + 1))
  proof: rfl

中文:
引理 mkOfObjOfMapSucc_obj
  条件: (i : 有限集 (n + 1))
  证明: rfl
-/
lemma mkOfObjOfMapSucc_obj (i : Fin (n + 1)) :
    (mkOfObjOfMapSucc obj mapSucc).obj i = obj i := rfl

/--
lemma `mkOfObjOfMapSucc_map_succ` / 引理 `mkOfObjOfMapSucc_map_succ`

English:
lemma mkOfObjOfMapSucc_map_succ
  given: (i : Nat) (hi : i < n := by valid)
  proof: ((mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose_spec i hi).symm

中文:
引理 mkOfObjOfMapSucc_map_succ
  条件: (i : 自然数) (hi : i < n := by valid)
  证明: ((mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose_spec i hi).symm

Depends on / 依赖: choose_spec, choose_spec.choose_spec, mapSucc, mkOfObjOfMapSucc, mkOfObjOfMapSucc_exists
-/
lemma mkOfObjOfMapSucc_map_succ (i : Nat) (hi : i < n := by valid) :
    (mkOfObjOfMapSucc obj mapSucc).map' i (i + 1) = mapSucc ⟨i, hi⟩ :=
  ((mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose_spec i hi).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mkOfObjOfMapSucc_arrow` / 引理 `mkOfObjOfMapSucc_arrow`

English:
lemma mkOfObjOfMapSucc_arrow
  given: (i : Nat) (hi : i < n := by valid)
  proof: ext₁ rfl rfl (by simpa using! mkOfObjOfMapSucc_map_succ obj mapSucc i hi)

中文:
引理 mkOfObjOfMapSucc_arrow
  条件: (i : 自然数) (hi : i < n := by valid)
  证明: ext₁ rfl rfl (by simpa using! mkOfObjOfMapSucc_map_succ obj mapSucc i hi)

Depends on / 依赖: mapSucc, mkOfObjOfMapSucc, mkOfObjOfMapSucc_map_succ
-/
lemma mkOfObjOfMapSucc_arrow (i : Nat) (hi : i < n := by valid) :
    (mkOfObjOfMapSucc obj mapSucc).arrow i = mk₁ (mapSucc ⟨i, hi⟩) :=
  ext₁ rfl rfl (by simpa using! mkOfObjOfMapSucc_map_succ obj mapSucc i hi)

end mkOfObjOfMapSucc

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
suppress_compilation in
variable (C n) in
/-- The equivalence `(ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n` obtained
by reversing the arrows. -/
@[simps!]
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: : (ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n
  body: ((orderDualEquivalence (Fin (n + 1))).symm.trans
      Fin.revOrderIso.equivalence).symm.congrLeft.op.trans
    (Functor.leftOpRightOpEquiv (Fin (n + 1)) C)

中文:
定义 opEquivalence
  签名: : (ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n
  定义体: ((orderDualEquivalence (Fin (n + 1))).symm.trans
      Fin.revOrderIso.equivalence).symm.congrLeft.op.trans
    (Functor.leftOpRightOpEquiv (Fin (n + 1)) C)

Depends on / 依赖: Fin.revOrderIso.equivalence, Functor, Functor.leftOpRightOpEquiv, congrLeft, equivalence, leftOpRightOpEquiv, orderDualEquivalence, revOrderIso, symm.congrLeft.op.trans, symm.trans
-/
def opEquivalence : (ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n :=
  ((orderDualEquivalence (Fin (n + 1))).symm.trans
      Fin.revOrderIso.equivalence).symm.congrLeft.op.trans
    (Functor.leftOpRightOpEquiv (Fin (n + 1)) C)

end ComposableArrows

section

open ComposableArrows

variable {C} {D : Type*} [Category* D] (G : C ⥤ D) (n : Nat)

/-- The functor `ComposableArrows C n ⥤ ComposableArrows D n` obtained by postcomposition
with a functor `C ⥤ D`. -/
@[simps!]
/--
Definition of `Functor.mapComposableArrows` / `Functor.mapComposableArrows` 的定义

English:
definition Functor.mapComposableArrows
  signature: :
  body: (whiskeringRight _ _ _).obj G

中文:
定义 函子.mapComposableArrows
  签名: :
  定义体: (whiskeringRight _ _ _).obj G

Depends on / 依赖: whiskeringRight
-/
def Functor.mapComposableArrows :
    ComposableArrows C n ⥤ ComposableArrows D n :=
  (whiskeringRight _ _ _).obj G

/-- The isomorphism between `(G.mapComposableArrows 1).obj (.mk₁ f)` and
`.mk₁ (G.map f)`. -/
@[simps!]
/--
Definition of `Functor.mapComposableArrowsObjMk₁Iso` / `Functor.mapComposableArrowsObjMk₁Iso` 的定义

English:
definition Functor.mapComposableArrowsObjMk₁Iso
  signature: {X Y : C} (f : X ⟶ Y)
  body: isoMk₁ (Iso.refl _) (Iso.refl _)

中文:
定义 函子.mapComposableArrowsObjMk₁Iso
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: isoMk₁ (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl
-/
def Functor.mapComposableArrowsObjMk₁Iso {X Y : C} (f : X ⟶ Y) :
    (G.mapComposableArrows 1).obj (.mk₁ f) ≅ .mk₁ (G.map f) :=
  isoMk₁ (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `(G.mapComposableArrows 2).obj (.mk₂ f g)` and
`.mk₂ (G.map f) (G.map g)`. -/
@[simps!]
/--
Definition of `Functor.mapComposableArrowsObjMk₂Iso` / `Functor.mapComposableArrowsObjMk₂Iso` 的定义

English:
definition Functor.mapComposableArrowsObjMk₂Iso
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: isoMk₂ (Iso.refl _) (Iso.refl _) (Iso.refl _)

suppress_compilation in

中文:
定义 函子.mapComposableArrowsObjMk₂Iso
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: isoMk₂ (Iso.refl _) (Iso.refl _) (Iso.refl _)

suppress_compilation in

Depends on / 依赖: Iso.refl
-/
def Functor.mapComposableArrowsObjMk₂Iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (G.mapComposableArrows 2).obj (.mk₂ f g) ≅ .mk₂ (G.map f) (G.map g) :=
  isoMk₂ (Iso.refl _) (Iso.refl _) (Iso.refl _)

suppress_compilation in
/--
Definition of `Functor.mapComposableArrowsOpIso` / `Functor.mapComposableArrowsOpIso` 的定义

English:
definition Functor.mapComposableArrowsOpIso
  signature: :
  body: Iso.refl _

中文:
定义 函子.mapComposableArrowsOpIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Functor.mapComposableArrowsOpIso :
    G.mapComposableArrows n ⋙ (opEquivalence D n).functor.rightOp ≅
      (opEquivalence C n).functor.rightOp ⋙ (G.op.mapComposableArrows n).op :=
  Iso.refl _

end

end CategoryTheory
