/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Antoine Labelle, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Combinatorics.Quiver.Push

/-!
## Symmetric quivers and arrow reversal

This file contains constructions related to symmetric quivers:

* `Symmetrify V` adds formal inverses to each arrow of `V`.
* `HasReverse` is the class of quivers where each arrow has an assigned formal inverse.
* `HasInvolutiveReverse` extends `HasReverse` by requiring that the reverse of the reverse
  is equal to the original arrow.
* `Prefunctor.PreserveReverse` is the class of prefunctors mapping reverses to reverses.
* `Symmetrify.of`, `Symmetrify.lift`, and the associated lemmas witness the universal property
  of `Symmetrify`.
-/

@[expose] public section

universe v u w v'

namespace Quiver

/--
Definition of `Symmetrify` / `Symmetrify` 的定义

English:
definition Symmetrify
  signature: (V : Type*)
  body: V

中文:
定义 Symmetrify
  签名: (V : 类型)
  定义体: V
-/
def Symmetrify (V : Type*) := V

/--
Instance `symmetrifyQuiver` / 实例 `symmetrifyQuiver`

English:
instance symmetrifyQuiver
  signature: (V : Type u) [Quiver V]
  body: ⟨fun a b : V => (a ⟶ b) oplus (b ⟶ a)⟩

中文:
实例 symmetrifyQuiver
  签名: (V : 类型u) [Quiver V]
  定义体: ⟨fun a b : V => (a ⟶ b) oplus (b ⟶ a)⟩
-/
instance symmetrifyQuiver (V : Type u) [Quiver V] : Quiver (Symmetrify V) :=
  ⟨fun a b : V => (a ⟶ b) oplus (b ⟶ a)⟩

variable (U V W : Type*) [Quiver.{u} U] [Quiver.{v} V] [Quiver.{w} W]

/--
Definition of `HasReverse` / `HasReverse` 的定义

English:
class HasReverse
  parameters: where
  axioms and operations (1):
    - reverse' : forall {a b : V}, (a ⟶ b) -> (b ⟶ a)

中文:
类 HasReverse
  参数: where
  公理与运算 (1 个):
    - reverse' : 对任意 {a b : V}, (a ⟶ b) -> (b ⟶ a)
-/
class HasReverse where
  /-- the map which sends an arrow to its reverse -/
  reverse' : forall {a b : V}, (a ⟶ b) -> (b ⟶ a)

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: {V} [Quiver.{v} V] [HasReverse V] {a b : V}
  body: HasReverse.reverse'

中文:
定义 reverse
  签名: {V} [Quiver.{v} V] [HasReverse V] {a b : V}
  定义体: HasReverse.reverse'

Depends on / 依赖: HasReverse, HasReverse.reverse, reverse
-/
def reverse {V} [Quiver.{v} V] [HasReverse V] {a b : V} : (a ⟶ b) -> (b ⟶ a) :=
  HasReverse.reverse'

/--
Definition of `HasInvolutiveReverse` / `HasInvolutiveReverse` 的定义

English:
class HasInvolutiveReverse
  parameters: extends HasReverse V
  extends: HasReverse V
  axioms and operations (1):
    - inv' : forall {a b : V} (f : a ⟶ b), reverse (reverse f) = f

中文:
类 HasInvolutiveReverse
  参数: extends HasReverse V
  继承: HasReverse V
  公理与运算 (1 个):
    - inv' : 对任意 {a b : V} (f : a ⟶ b), reverse (reverse f) = f
-/
class HasInvolutiveReverse extends HasReverse V where
  /-- `reverse` is involutive -/
  inv' : forall {a b : V} (f : a ⟶ b), reverse (reverse f) = f

variable {U V W}

@[simp]
/--
theorem `reverse_reverse` / 定理 `reverse_reverse`

English:
theorem reverse_reverse
  given: [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
  proof: by apply h.inv'

@[simp]

中文:
定理 reverse_reverse
  条件: [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
  证明: by apply h.inv'

@[simp]

Depends on / 依赖: h.inv
-/
theorem reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b) :
    reverse (reverse f) = f := by apply h.inv'

@[simp]
/--
theorem `reverse_inj` / 定理 `reverse_inj`

English:
theorem reverse_inj
  statement: [h : HasInvolutiveReverse V] {a b : V}
  proof: by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr

中文:
定理 reverse_inj
  结论: [h : HasInvolutiveReverse V] {a b : V}
  证明: by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr

Depends on / 依赖: Quiver, Quiver.reverse, congr_arg, reverse
-/
theorem reverse_inj [h : HasInvolutiveReverse V] {a b : V}
    (f g : a ⟶ b) : reverse f = reverse g ↔ f = g := by
  constructor
  · rintro h
    simpa using congr_arg Quiver.reverse h
  · rintro h
    congr

/--
theorem `eq_reverse_iff` / 定理 `eq_reverse_iff`

English:
theorem eq_reverse_iff
  statement: [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
  proof: by
  rw [← reverse_inj]; rw [reverse_reverse]

中文:
定理 eq_reverse_iff
  结论: [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
  证明: by
  rw [← reverse_inj]; rw [reverse_reverse]

Depends on / 依赖: reverse_inj, reverse_reverse
-/
theorem eq_reverse_iff [h : HasInvolutiveReverse V] {a b : V} (f : a ⟶ b)
    (g : b ⟶ a) : f = reverse g ↔ reverse f = g := by
  rw [← reverse_inj]; rw [reverse_reverse]

section MapReverse

variable [HasReverse U] [HasReverse V] [HasReverse W]

/--
Definition of `_root_.Prefunctor.MapReverse` / `_root_.Prefunctor.MapReverse` 的定义

English:
class _root_.Prefunctor.MapReverse
  parameters: (φ : U ⥤q V)
  axioms and operations (1):
    - map_reverse' : forall {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)

中文:
类 _root_.Prefunctor.MapReverse
  参数: (φ : U ⥤q V)
  公理与运算 (1 个):
    - map_reverse' : 对任意 {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)
-/
class _root_.Prefunctor.MapReverse (φ : U ⥤q V) : Prop where
  /-- The image of a reverse is the reverse of the image. -/
  map_reverse' : forall {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e)

@[simp]
/--
theorem `_root_.Prefunctor.map_reverse` / 定理 `_root_.Prefunctor.map_reverse`

English:
theorem _root_.Prefunctor.map_reverse
  statement: (φ : U ⥤q V) [φ.MapReverse]
  proof: Prefunctor.MapReverse.map_reverse' e

中文:
定理 _root_.Prefunctor.map_reverse
  结论: (φ : U ⥤q V) [φ.MapReverse]
  证明: Prefunctor.MapReverse.map_reverse' e

Depends on / 依赖: MapReverse, Prefunctor, Prefunctor.MapReverse.map_reverse, map_reverse
-/
theorem _root_.Prefunctor.map_reverse (φ : U ⥤q V) [φ.MapReverse]
    {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
  Prefunctor.MapReverse.map_reverse' e

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_root_.Prefunctor.mapReverseComp` / 实例 `_root_.Prefunctor.mapReverseComp`

English:
instance _root_.Prefunctor.mapReverseComp
  body: by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']

中文:
实例 _root_.Prefunctor.mapReverseComp
  定义体: by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']

Depends on / 依赖: MapReverse, Prefunctor, Prefunctor.MapReverse.map_reverse, Prefunctor.comp_map, comp_map, map_reverse
-/
instance _root_.Prefunctor.mapReverseComp
    (φ : U ⥤q V) (ψ : V ⥤q W) [φ.MapReverse] [ψ.MapReverse] :
    (φ ⋙q ψ).MapReverse where
  map_reverse' e := by
    simp only [Prefunctor.comp_map, Prefunctor.MapReverse.map_reverse']

/--
Instance `_root_.Prefunctor.mapReverseId` / 实例 `_root_.Prefunctor.mapReverseId`

English:
instance _root_.Prefunctor.mapReverseId
  signature: :
  body: rfl

中文:
实例 _root_.Prefunctor.mapReverseId
  签名: :
  定义体: rfl

Depends on / 依赖: _apply, comapDomain, smul_apply
-/
instance _root_.Prefunctor.mapReverseId :
    (Prefunctor.id U).MapReverse where
  map_reverse' _ := rfl

end MapReverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasReverse (Symmetrify V)
  body: ⟨fun e => e.swap⟩

中文:
实例 :
  签名: HasReverse (Symmetrify V)
  定义体: ⟨fun e => e.swap⟩

Depends on / 依赖: e.swap
-/
instance : HasReverse (Symmetrify V) :=
  ⟨fun e => e.swap⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: ⟨fun e => e.swap⟩
  inv' e := congr_fun Sum.swap_swap_eq e

@[simp]

中文:
实例 :
  定义体: ⟨fun e => e.swap⟩
  inv' e := congr_fun Sum.swap_swap_eq e

@[simp]

Depends on / 依赖: e.swap
-/
instance :
    HasInvolutiveReverse
      (Symmetrify V) where
  toHasReverse := ⟨fun e => e.swap⟩
  inv' e := congr_fun Sum.swap_swap_eq e

@[simp]
/--
theorem `symmetrify_reverse` / 定理 `symmetrify_reverse`

English:
theorem symmetrify_reverse
  given: {a b : Symmetrify V} (e : a ⟶ b)
  statement: reverse e = e.swap
  proof: rfl

中文:
定理 symmetrify_reverse
  条件: {a b : Symmetrify V} (e : a ⟶ b)
  结论: reverse e = e.swap
  证明: rfl
-/
theorem symmetrify_reverse {a b : Symmetrify V} (e : a ⟶ b) : reverse e = e.swap :=
  rfl

section Paths

/--
Definition of `Hom.toPos` / `Hom.toPos` 的定义

English:
abbreviation Hom.toPos
  signature: {X Y : V} (f : X ⟶ Y)
  body: Sum.inl f

中文:
缩写 Hom.toPos
  签名: {X Y : V} (f : X ⟶ Y)
  定义体: Sum.inl f

Depends on / 依赖: Sum.inl
-/
abbrev Hom.toPos {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom X Y :=
  Sum.inl f

/--
Definition of `Hom.toNeg` / `Hom.toNeg` 的定义

English:
abbreviation Hom.toNeg
  signature: {X Y : V} (f : X ⟶ Y)
  body: Sum.inr f

中文:
缩写 Hom.toNeg
  签名: {X Y : V} (f : X ⟶ Y)
  定义体: Sum.inr f

Depends on / 依赖: Sum.inr
-/
abbrev Hom.toNeg {X Y : V} (f : X ⟶ Y) : (Quiver.symmetrifyQuiver V).Hom Y X :=
  Sum.inr f

/-- Reverse the direction of a path. -/
@[simp]
/--
Definition of `Path.reverse` / `Path.reverse` 的定义

English:
definition Path.reverse
  signature: [HasReverse V] {a : V}

中文:
定义 Path.reverse
  签名: [HasReverse V] {a : V}
-/
def Path.reverse [HasReverse V] {a : V} : forall {b}, Path a b -> Path b a
  | _, Path.nil => Path.nil
  | _, Path.cons p e => (Quiver.reverse e).toPath.comp p.reverse

@[simp]
/--
theorem `Path.reverse_toPath` / 定理 `Path.reverse_toPath`

English:
theorem Path.reverse_toPath
  given: [HasReverse V] {a b : V} (f : a ⟶ b)
  proof: rfl

@[simp]

中文:
定理 Path.reverse_toPath
  条件: [HasReverse V] {a b : V} (f : a ⟶ b)
  证明: rfl

@[simp]
-/
theorem Path.reverse_toPath [HasReverse V] {a b : V} (f : a ⟶ b) :
    f.toPath.reverse = (Quiver.reverse f).toPath :=
  rfl

@[simp]
/--
theorem `Path.reverse_comp` / 定理 `Path.reverse_comp`

English:
theorem Path.reverse_comp
  given: [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c)
  proof: by
  induction q with
  | nil => simp
  | cons _ _ h => simp [h]

@[simp]

中文:
定理 Path.reverse_comp
  条件: [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c)
  证明: by
  induction q with
  | nil => simp
  | cons _ _ h => simp [h]

@[simp]
-/
theorem Path.reverse_comp [HasReverse V] {a b c : V} (p : Path a b) (q : Path b c) :
    (p.comp q).reverse = q.reverse.comp p.reverse := by
  induction q with
  | nil => simp
  | cons _ _ h => simp [h]

@[simp]
/--
theorem `Path.reverse_reverse` / 定理 `Path.reverse_reverse`

English:
theorem Path.reverse_reverse
  given: [h : HasInvolutiveReverse V] {a b : V} (p : Path a b)
  proof: by
  induction p with
  | nil => simp
  | cons _ _ h =>
    rw [Path.reverse]; rw [Path.reverse_comp]; rw [h]; rw [Path.reverse_toPath]; rw [Quiver.reverse_reverse]
    rfl

中文:
定理 Path.reverse_reverse
  条件: [h : HasInvolutiveReverse V] {a b : V} (p : Path a b)
  证明: by
  induction p with
  | nil => simp
  | cons _ _ h =>
    rw [Path.reverse]; rw [Path.reverse_comp]; rw [h]; rw [Path.reverse_toPath]; rw [Quiver.reverse_reverse]
    rfl

Depends on / 依赖: Path.reverse, Path.reverse_comp, Path.reverse_toPath, Quiver, Quiver.reverse_reverse, reverse, reverse_comp, reverse_reverse, reverse_toPath
-/
theorem Path.reverse_reverse [h : HasInvolutiveReverse V] {a b : V} (p : Path a b) :
    p.reverse.reverse = p := by
  induction p with
  | nil => simp
  | cons _ _ h =>
    rw [Path.reverse]; rw [Path.reverse_comp]; rw [h]; rw [Path.reverse_toPath]; rw [Quiver.reverse_reverse]
    rfl

end Paths

namespace Symmetrify

/-- The inclusion of a quiver in its symmetrification -/
@[simps]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : Prefunctor V (Symmetrify V) where
  body: id
  map := Sum.inl

中文:
定义 of
  签名: : Prefunctor V (Symmetrify V) where
  定义体: id
  map := Sum.inl
-/
def of : Prefunctor V (Symmetrify V) where
  obj := id
  map := Sum.inl

variable {V' : Type*} [Quiver.{v'} V']

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: [HasReverse V'] (φ : Prefunctor V V')
  body: φ.obj
  map
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)

中文:
定义 lift
  签名: [HasReverse V'] (φ : Prefunctor V V')
  定义体: φ.obj
  map
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)
-/
def lift [HasReverse V'] (φ : Prefunctor V V') :
    Prefunctor (Symmetrify V) V' where
  obj := φ.obj
  map
  | Sum.inl g => φ.map g
  | Sum.inr g => reverse (φ.map g)

/--
theorem `lift_spec` / 定理 `lift_spec`

English:
theorem lift_spec
  given: [HasReverse V'] (φ : Prefunctor V V')
  proof: by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl

中文:
定理 lift_spec
  条件: [HasReverse V'] (φ : Prefunctor V V')
  证明: by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl

Depends on / 依赖: Prefunctor, Prefunctor.ext, fapply
-/
theorem lift_spec [HasReverse V'] (φ : Prefunctor V V') :
    Symmetrify.of.comp (Symmetrify.lift φ) = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rfl

/--
theorem `lift_reverse` / 定理 `lift_reverse`

English:
theorem lift_reverse
  statement: [h : HasInvolutiveReverse V']
  proof: by
  dsimp [Symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl

中文:
定理 lift_reverse
  结论: [h : HasInvolutiveReverse V']
  证明: by
  dsimp [Symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl

Depends on / 依赖: Symmetrify, Symmetrify.lift, reverse_reverse
-/
theorem lift_reverse [h : HasInvolutiveReverse V']
    (φ : Prefunctor V V') {X Y : Symmetrify V} (f : X ⟶ Y) :
    (Symmetrify.lift φ).map (Quiver.reverse f) = Quiver.reverse ((Symmetrify.lift φ).map f) := by
  dsimp [Symmetrify.lift]; cases f
  · simp only
    rfl
  · simp only [reverse_reverse]
    rfl

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
  proof: by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · exact hΦinv (Sum.inl _)

中文:
定理 lift_unique
  结论: [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
  证明: by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · exact hΦinv (Sum.inl _)

Depends on / 依赖: Prefunctor, Prefunctor.ext, Sum.inl, fapply
-/
theorem lift_unique [HasReverse V'] (φ : V ⥤q V') (Φ : Symmetrify V ⥤q V') (hΦ : (of ⋙q Φ) = φ)
    (hΦinv : forall {X Y : Symmetrify V} (f : X ⟶ Y),
      Φ.map (Quiver.reverse f) = Quiver.reverse (Φ.map f)) :
    Φ = Symmetrify.lift φ := by
  subst_vars
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    cases f
    · rfl
    · exact hΦinv (Sum.inl _)

/-- A prefunctor canonically defines a prefunctor of the symmetrifications. -/
@[simps]
/--
Definition of `_root_.Prefunctor.symmetrify` / `_root_.Prefunctor.symmetrify` 的定义

English:
definition _root_.Prefunctor.symmetrify
  signature: (φ : U ⥤q V)
  body: φ.obj
  map := Sum.map φ.map φ.map

中文:
定义 _root_.Prefunctor.symmetrify
  签名: (φ : U ⥤q V)
  定义体: φ.obj
  map := Sum.map φ.map φ.map
-/
def _root_.Prefunctor.symmetrify (φ : U ⥤q V) : Symmetrify U ⥤q Symmetrify V where
  obj := φ.obj
  map := Sum.map φ.map φ.map

/--
Instance `_root_.Prefunctor.symmetrify_mapReverse` / 实例 `_root_.Prefunctor.symmetrify_mapReverse`

English:
instance _root_.Prefunctor.symmetrify_mapReverse
  signature: (φ : U ⥤q V)
  body: ⟨fun e => by cases e <;> rfl⟩

中文:
实例 _root_.Prefunctor.symmetrify_mapReverse
  签名: (φ : U ⥤q V)
  定义体: ⟨fun e => by cases e <;> rfl⟩
-/
instance _root_.Prefunctor.symmetrify_mapReverse (φ : U ⥤q V) :
    Prefunctor.MapReverse φ.symmetrify :=
  ⟨fun e => by cases e <;> rfl⟩

end Symmetrify

namespace Push

variable {V' : Type*} (σ : V -> V')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasReverse
  signature: V] : HasReverse (Quiver.Push σ) where
  body: fun
              | PushQuiver.arrow f => PushQuiver.arrow (reverse f)

中文:
实例 [HasReverse
  签名: V] : HasReverse (Quiver.Push σ) where
  定义体: fun
              | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
-/
instance [HasReverse V] : HasReverse (Quiver.Push σ) where
  reverse' := fun
              | PushQuiver.arrow f => PushQuiver.arrow (reverse f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : HasInvolutiveReverse V] :
  body: fun
  | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
  inv' := fun
  | PushQuiver.arrow f => by dsimp [reverse]; congr; apply h.inv'

中文:
实例 [h
  签名: : HasInvolutiveReverse V] :
  定义体: fun
  | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
  inv' := fun
  | PushQuiver.arrow f => by dsimp [reverse]; congr; apply h.inv'
-/
instance [h : HasInvolutiveReverse V] :
    HasInvolutiveReverse (Push σ) where
  reverse' := fun
  | PushQuiver.arrow f => PushQuiver.arrow (reverse f)
  inv' := fun
  | PushQuiver.arrow f => by dsimp [reverse]; congr; apply h.inv'

/--
theorem `of_reverse` / 定理 `of_reverse`

English:
theorem of_reverse
  given: [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y)
  proof: rfl

中文:
定理 of_reverse
  条件: [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y)
  证明: rfl
-/
theorem of_reverse [HasInvolutiveReverse V] (X Y : V) (f : X ⟶ Y) :
    (reverse <| (Push.of σ).map f) = (Push.of σ).map (reverse f) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `ofMapReverse` / 实例 `ofMapReverse`

English:
instance ofMapReverse
  signature: [h : HasInvolutiveReverse V]
  body: ⟨by simp [of_reverse]⟩

中文:
实例 ofMapReverse
  签名: [h : HasInvolutiveReverse V]
  定义体: ⟨by simp [of_reverse]⟩

Depends on / 依赖: of_reverse
-/
instance ofMapReverse [h : HasInvolutiveReverse V] : (Push.of σ).MapReverse :=
  ⟨by simp [of_reverse]⟩

end Push

end Quiver
