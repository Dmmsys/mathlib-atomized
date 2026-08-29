/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Bundle

Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.

We represent a bundle `E` over a base space `B` as a dependent type `E : B → Type*`.

We define `Bundle.TotalSpace F E` to be the type of pairs `⟨b, x⟩`, where `b : B` and `x : E b`.
This type is isomorphic to `Σ x, E x` and uses an extra argument `F` for reasons explained below. In
general, the constructions of fiber bundles we will make will be of this form.

## Main Definitions

* `Bundle.TotalSpace` the total space of a bundle.
* `Bundle.TotalSpace.proj` the projection from the total space to the base space.
* `Bundle.TotalSpace.mk` the constructor for the total space.

## Implementation Notes

- We use a custom structure for the total space of a bundle instead of using a type synonym for the
  canonical disjoint union `Σ x, E x` because the total space usually has a different topology and
  Lean 4 `simp` fails to apply lemmas about `Σ x, E x` to elements of the total space.

- The definition of `Bundle.TotalSpace` has an unused argument `F`. The reason is that in some
  constructions (e.g., the bundle of continuous linear maps) we need access to the atlas of
  trivializations of original fiber bundles to construct the topology on the total space of the new
  fiber bundle.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/

@[expose] public section

assert_not_exists RelIso

open Function Set

namespace Bundle

variable {B F : Type*} (E : B -> Type*)

/-- `Bundle.TotalSpace F E` is the total space of the bundle. It consists of pairs
`(proj : B, snd : E proj)`.
-/
@[ext]
/--
Definition of `TotalSpace` / `TotalSpace` 的定义

English:
structure TotalSpace
  parameters: (F : Type*) (E : B -> Type*)
  axioms and operations (2):
    - proj : B
    - snd : E proj

中文:
结构 TotalSpace
  参数: (F : 类型) (E : B -> 类型)
  公理与运算 (2 个):
    - proj : B
    - snd : E proj
-/
structure TotalSpace (F : Type*) (E : B -> Type*) where
  /-- `Bundle.TotalSpace.proj` is the canonical projection `Bundle.TotalSpace F E → B` from the
  total space to the base space. -/
  proj : B
  snd : E proj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: B] [Inhabited (E default)] : Inhabited (TotalSpace F E)
  body: ⟨⟨default, default⟩⟩

中文:
实例 [Inhabited
  签名: B] [Inhabited (E default)] : Inhabited (TotalSpace F E)
  定义体: ⟨⟨default, default⟩⟩
-/
instance [Inhabited B] [Inhabited (E default)] : Inhabited (TotalSpace F E) :=
  ⟨⟨default, default⟩⟩

variable {E}

@[inherit_doc]
scoped notation:max "π " F':max E':max => Bundle.TotalSpace.proj (F := F') (E := E')

/--
Definition of `TotalSpace.mk'` / `TotalSpace.mk'` 的定义

English:
abbreviation TotalSpace.mk'
  signature: (F : Type*) (x : B) (y : E x)
  body: ⟨x, y⟩

中文:
缩写 TotalSpace.mk'
  签名: (F : 类型) (x : B) (y : E x)
  定义体: ⟨x, y⟩
-/
abbrev TotalSpace.mk' (F : Type*) (x : B) (y : E x) : TotalSpace F E := ⟨x, y⟩

/--
theorem `TotalSpace.mk_cast` / 定理 `TotalSpace.mk_cast`

English:
theorem TotalSpace.mk_cast
  given: {x x' : B} (h : x = x') (b : E x)
  proof: by subst h; rfl

@[simp 1001, mfld_simps 1001]

中文:
定理 TotalSpace.mk_cast
  条件: {x x' : B} (h : x = x') (b : E x)
  证明: by subst h; rfl

@[simp 1001, mfld_simps 1001]
-/
theorem TotalSpace.mk_cast {x x' : B} (h : x = x') (b : E x) :
    .mk' F x' (cast (congr_arg E h) b) = TotalSpace.mk x b := by subst h; rfl

@[simp 1001, mfld_simps 1001]
/--
theorem `TotalSpace.mk_inj` / 定理 `TotalSpace.mk_inj`

English:
theorem TotalSpace.mk_inj
  given: {b : B} {y y' : E b}
  statement: mk' F b y = mk' F b y' ↔ y = y'
  proof: by
  simp [TotalSpace.ext_iff]

中文:
定理 TotalSpace.mk_inj
  条件: {b : B} {y y' : E b}
  结论: mk' F b y = mk' F b y' ↔ y = y'
  证明: by
  simp [TotalSpace.ext_iff]

Depends on / 依赖: TotalSpace, TotalSpace.ext_iff, ext_iff
-/
theorem TotalSpace.mk_inj {b : B} {y y' : E b} : mk' F b y = mk' F b y' ↔ y = y' := by
  simp [TotalSpace.ext_iff]

/--
theorem `TotalSpace.mk_injective` / 定理 `TotalSpace.mk_injective`

English:
theorem TotalSpace.mk_injective
  given: (b : B)
  statement: Injective (mk b : E b -> TotalSpace F E)
  proof: fun _ _ =>
  mk_inj.1

中文:
定理 TotalSpace.mk_injective
  条件: (b : B)
  结论: Injective (mk b : E b -> TotalSpace F E)
  证明: fun _ _ =>
  mk_inj.1
-/
theorem TotalSpace.mk_injective (b : B) : Injective (mk b : E b -> TotalSpace F E) := fun _ _ =>
  mk_inj.1

instance {x : B} : CoeTC (E x) (TotalSpace F E) :=
  ⟨TotalSpace.mk x⟩

/--
theorem `TotalSpace.eta` / 定理 `TotalSpace.eta`

English:
theorem TotalSpace.eta
  given: (z : TotalSpace F E)
  statement: TotalSpace.mk z.proj z.2 = z
  proof: rfl

@[simp]

中文:
定理 TotalSpace.eta
  条件: (z : TotalSpace F E)
  结论: TotalSpace.mk z.proj z.2 = z
  证明: rfl

@[simp]
-/
theorem TotalSpace.eta (z : TotalSpace F E) : TotalSpace.mk z.proj z.2 = z := rfl

@[simp]
/--
theorem `TotalSpace.exists` / 定理 `TotalSpace.exists`

English:
theorem TotalSpace.exists
  given: {p : TotalSpace F E -> Prop}
  statement: (exists x, p x) ↔ exists b y, p ⟨b, y⟩
  proof: ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨b, y, h⟩ => ⟨⟨b, y⟩, h⟩⟩

@[simp]

中文:
定理 TotalSpace.exists
  条件: {p : TotalSpace F E -> 命题}
  结论: (存在 x, p x) ↔ 存在 b y, p ⟨b, y⟩
  证明: ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨b, y, h⟩ => ⟨⟨b, y⟩, h⟩⟩

@[simp]
-/
theorem TotalSpace.exists {p : TotalSpace F E -> Prop} : (exists x, p x) ↔ exists b y, p ⟨b, y⟩ :=
  ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨b, y, h⟩ => ⟨⟨b, y⟩, h⟩⟩

@[simp]
/--
theorem `TotalSpace.range_mk` / 定理 `TotalSpace.range_mk`

English:
theorem TotalSpace.range_mk
  given: (b : B)
  statement: range ((↑) : E b -> TotalSpace F E) = π F E ⁻¹' {b}
  proof: by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rfl
  · rintro ⟨_, x⟩ rfl
    exact ⟨x, rfl⟩

中文:
定理 TotalSpace.range_mk
  条件: (b : B)
  结论: range ((↑) : E b -> TotalSpace F E) = π F E ⁻¹' {b}
  证明: by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rfl
  · rintro ⟨_, x⟩ rfl
    exact ⟨x, rfl⟩

Depends on / 依赖: Subset, Subset.antisymm, antisymm
-/
theorem TotalSpace.range_mk (b : B) : range ((↑) : E b -> TotalSpace F E) = π F E ⁻¹' {b} := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rfl
  · rintro ⟨_, x⟩ rfl
    exact ⟨x, rfl⟩

/-- Notation for the direct sum of two bundles over the same base. -/
notation:100 E₁ " ×ᵇ " E₂ => fun x => E₁ x × E₂ x

/-- `Bundle.Trivial B F` is the trivial bundle over `B` of fiber `F`. -/
@[reducible, nolint unusedArguments]
/--
Definition of `Trivial` / `Trivial` 的定义

English:
definition Trivial
  signature: (B : Type*) (F : Type*)
  body: fun _ => F

中文:
定义 Trivial
  签名: (B : 类型) (F : 类型)
  定义体: fun _ => F
-/
def Trivial (B : Type*) (F : Type*) : B -> Type _ := fun _ => F

/--
Definition of `TotalSpace.trivialSnd` / `TotalSpace.trivialSnd` 的定义

English:
definition TotalSpace.trivialSnd
  signature: (B : Type*) (F : Type*)
  body: TotalSpace.snd

中文:
定义 TotalSpace.trivialSnd
  签名: (B : 类型) (F : 类型)
  定义体: TotalSpace.snd

Depends on / 依赖: TotalSpace, TotalSpace.snd
-/
def TotalSpace.trivialSnd (B : Type*) (F : Type*) : TotalSpace F (Bundle.Trivial B F) -> F :=
  TotalSpace.snd

/-- A trivial bundle is equivalent to the product `B × F`. -/
@[simps (attr := mfld_simps)]
/--
Definition of `TotalSpace.toProd` / `TotalSpace.toProd` 的定义

English:
definition TotalSpace.toProd
  signature: (B F : Type*)
  body: (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩

中文:
定义 TotalSpace.toProd
  签名: (B F : 类型)
  定义体: (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩
-/
def TotalSpace.toProd (B F : Type*) : (TotalSpace F fun _ : B => F) ≃ B × F where
  toFun x := (x.1, x.2)
  invFun x := ⟨x.1, x.2⟩

section Pullback

variable {B' : Type*}

/--
Definition of `Pullback` / `Pullback` 的定义

English:
definition Pullback
  signature: (f : B' -> B) (E : B -> Type*)
  body: fun x => E (f x)

@[inherit_doc]
notation f " *ᵖ " E:arg => Pullback f E

中文:
定义 Pullback
  签名: (f : B' -> B) (E : B -> 类型)
  定义体: fun x => E (f x)

@[inherit_doc]
notation f " *ᵖ " E:arg => Pullback f E
-/
def Pullback (f : B' -> B) (E : B -> Type*) : B' -> Type _ := fun x => E (f x)

@[inherit_doc]
notation f " *ᵖ " E:arg => Pullback f E

instance {f : B' -> B} {x : B'} [Nonempty (E (f x))] : Nonempty ((f *ᵖ E) x) :=
  ‹Nonempty (E (f x))›

/-- Natural embedding of the total space of `f *ᵖ E` into `B' × TotalSpace F E`. -/
@[simp]
/--
Definition of `pullbackTotalSpaceEmbedding` / `pullbackTotalSpaceEmbedding` 的定义

English:
definition pullbackTotalSpaceEmbedding
  signature: (f : B' -> B)
  body: fun z => (z.proj, TotalSpace.mk (f z.proj) z.2)

中文:
定义 pullbackTotalSpaceEmbedding
  签名: (f : B' -> B)
  定义体: fun z => (z.proj, TotalSpace.mk (f z.proj) z.2)

Depends on / 依赖: TotalSpace, TotalSpace.mk, z.proj
-/
def pullbackTotalSpaceEmbedding (f : B' -> B) : TotalSpace F (f *ᵖ E) -> B' × TotalSpace F E :=
  fun z => (z.proj, TotalSpace.mk (f z.proj) z.2)

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces. -/
@[simps (attr := mfld_simps)]
/--
Definition of `Pullback.lift` / `Pullback.lift` 的定义

English:
definition Pullback.lift
  signature: (f : B' -> B)
  body: fun z => ⟨f z.proj, z.2⟩

@[simp, mfld_simps]

中文:
定义 Pullback.lift
  签名: (f : B' -> B)
  定义体: fun z => ⟨f z.proj, z.2⟩

@[simp, mfld_simps]

Depends on / 依赖: z.proj
-/
def Pullback.lift (f : B' -> B) : TotalSpace F (f *ᵖ E) -> TotalSpace F E := fun z => ⟨f z.proj, z.2⟩

@[simp, mfld_simps]
/--
theorem `Pullback.lift_mk` / 定理 `Pullback.lift_mk`

English:
theorem Pullback.lift_mk
  given: (f : B' -> B) (x : B') (y : E (f x))
  proof: rfl

中文:
定理 Pullback.lift_mk
  条件: (f : B' -> B) (x : B') (y : E (f x))
  证明: rfl
-/
theorem Pullback.lift_mk (f : B' -> B) (x : B') (y : E (f x)) :
    Pullback.lift f (.mk' F x y) = ⟨f x, y⟩ :=
  rfl

end Pullback

end Bundle
