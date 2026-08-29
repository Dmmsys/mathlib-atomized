/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Relator
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.SimpRw
public import Mathlib.Order.Defs.Prop
public import Mathlib.Order.Defs.Unbundled
public import Batteries.Logic
public import Batteries.Tactic.Trans

/-!
# Relation closures

This file defines the reflexive, symmetric, transitive, reflexive transitive and equivalence
closures of relations and proves some basic results on them.

Note that this is about unbundled relations, that is terms of types of the form `α → β → Prop`. For
the bundled version, see `Rel`.

## Definitions

* `Relation.ReflGen`: Reflexive closure. `ReflGen r` relates everything `r` related, plus for all
  `a` it relates `a` with itself. So `ReflGen r a b ↔ r a b ∨ a = b`.
* `Relation.SymmGen`: Symmetric closure. This is also the comparability relation,
  such that `SymmGen r a b` means that either `r a b` or `r b a` (see `Mathlib.Order.Comparable`)
* `Relation.TransGen`: Transitive closure. `TransGen r` relates everything `r` related
  transitively. So `TransGen r a b ↔ ∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b`.
* `Relation.ReflTransGen`: Reflexive transitive closure. `ReflTransGen r` relates everything
  `r` related transitively, plus for all `a` it relates `a` with itself. So
  `ReflTransGen r a b ↔ (∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b) ∨ a = b`. It is the same as
  the reflexive closure of the transitive closure, or the transitive closure of the reflexive
  closure. In terms of rewriting systems, this means that `a` can be rewritten to `b` in a number of
  rewrites.
* `Relation.EqvGen`: Equivalence closure. `EqvGen r` relates everything `ReflTransGen r` relates,
  plus for all related pairs it relates them in the opposite order.
* `Relation.Comp`: Relation composition. We provide notation `∘r`. For `r : α → β → Prop` and
  `s : β → γ → Prop`, `r ∘r s` relates `a : α` and `c : γ` iff there exists `b : β` that's related
  to both.
* `Relation.Map`: Image of a relation under a pair of maps. For `r : α → β → Prop`, `f : α → γ`,
  `g : β → δ`, `Map r f g` is the relation `γ → δ → Prop` relating `f a` and `g b` for all `a`, `b`
  related by `r`.
* `Relation.Join`: Join of a relation. For `r : α → α → Prop`, `Join r a b ↔ ∃ c, r a c ∧ r b c`. In
  terms of rewriting systems, this means that `a` and `b` can be rewritten to the same term.
-/

@[expose] public section


open Function

variable {α β γ δ ε ζ : Type*}

/--
theorem `Subrelation.antisymm` / 定理 `Subrelation.antisymm`

English:
theorem Subrelation.antisymm
  given: {r r' : α -> α -> Prop} (h1 : r <= r') (h2 : r' <= r)
  proof: funext₂ fun a b => propext ⟨h1 a b, h2 a b⟩

中文:
定理 Subrelation.antisymm
  条件: {r r' : α -> α -> 命题} (h1 : r <= r') (h2 : r' <= r)
  证明: funext₂ fun a b => propext ⟨h1 a b, h2 a b⟩

Depends on / 依赖: propext
-/
theorem Subrelation.antisymm {r r' : α -> α -> Prop} (h1 : r <= r') (h2 : r' <= r) :
    r = r' :=
  funext₂ fun a b => propext ⟨h1 a b, h2 a b⟩

section NeImp

variable {r : α -> α -> Prop}

@[deprecated (since := "2026-03-27")] alias Std.Refl.reflexive := refl

@[deprecated (since := "2026-01-09")] alias IsRefl.reflexive := refl

/--
theorem `Std.Refl.rel_of_ne_imp` / 定理 `Std.Refl.rel_of_ne_imp`

English:
theorem Std.Refl.rel_of_ne_imp
  given: [Std.Refl r] {x y : α} (hr : x != y -> r x y)
  statement: r x y
  proof: by
  grind [Std.Refl]

@[deprecated (since := "2026-03-27")] alias Reflexive.rel_of_ne_imp := Std.Refl.rel_of_ne_imp

中文:
定理 Std.Refl.rel_of_ne_imp
  条件: [Std.Refl r] {x y : α} (hr : x != y -> r x y)
  结论: r x y
  证明: by
  grind [Std.Refl]

@[deprecated (since := "2026-03-27")] alias Reflexive.rel_of_ne_imp := Std.Refl.rel_of_ne_imp

Depends on / 依赖: Std.Refl
-/
theorem Std.Refl.rel_of_ne_imp [Std.Refl r] {x y : α} (hr : x != y -> r x y) : r x y := by
  grind [Std.Refl]

@[deprecated (since := "2026-03-27")] alias Reflexive.rel_of_ne_imp := Std.Refl.rel_of_ne_imp

/--
theorem `Std.Refl.ne_imp_iff` / 定理 `Std.Refl.ne_imp_iff`

English:
theorem Std.Refl.ne_imp_iff
  given: [Std.Refl r] {x y : α}
  statement: x != y -> r x y ↔ r x y
  proof: ⟨Std.Refl.rel_of_ne_imp, fun hr _ => hr⟩

@[deprecated (since := "2026-03-27")] alias Reflexive.ne_imp_iff := Std.Refl.ne_imp_iff
@[deprecated (since := "2026-03-27")] alias reflexive_ne_imp_iff := Std.Refl.ne_imp_iff

中文:
定理 Std.Refl.ne_imp_iff
  条件: [Std.Refl r] {x y : α}
  结论: x != y -> r x y ↔ r x y
  证明: ⟨Std.Refl.rel_of_ne_imp, fun hr _ => hr⟩

@[deprecated (since := "2026-03-27")] alias Reflexive.ne_imp_iff := Std.Refl.ne_imp_iff
@[deprecated (since := "2026-03-27")] alias reflexive_ne_imp_iff := Std.Refl.ne_imp_iff

Depends on / 依赖: Std.Refl.rel_of_ne_imp, rel_of_ne_imp
-/
theorem Std.Refl.ne_imp_iff [Std.Refl r] {x y : α} : x != y -> r x y ↔ r x y :=
  ⟨Std.Refl.rel_of_ne_imp, fun hr _ => hr⟩

@[deprecated (since := "2026-03-27")] alias Reflexive.ne_imp_iff := Std.Refl.ne_imp_iff
@[deprecated (since := "2026-03-27")] alias reflexive_ne_imp_iff := Std.Refl.ne_imp_iff

/--
theorem `refl_iff_eq_le` / 定理 `refl_iff_eq_le`

English:
theorem refl_iff_eq_le
  statement: Std.Refl r ↔ Eq <= r
  proof: by
  unfold Pi.hasLe Prop.le
  grind [Std.Refl]

@[deprecated (since := "2026-06-30")] alias refl_iff_subrelation_eq := refl_iff_eq_le
@[deprecated (since := "2026-03-27")] alias reflexive_iff_subrelation_eq := refl_iff_eq_le

中文:
定理 refl_iff_eq_le
  结论: Std.Refl r ↔ 相等 <= r
  证明: by
  unfold Pi.hasLe Prop.le
  grind [Std.Refl]

@[deprecated (since := "2026-06-30")] alias refl_iff_subrelation_eq := refl_iff_eq_le
@[deprecated (since := "2026-03-27")] alias reflexive_iff_subrelation_eq := refl_iff_eq_le

Depends on / 依赖: Pi.hasLe, Prop.le, Std.Refl
-/
theorem refl_iff_eq_le : Std.Refl r ↔ Eq <= r := by
  unfold Pi.hasLe Prop.le
  grind [Std.Refl]

@[deprecated (since := "2026-06-30")] alias refl_iff_subrelation_eq := refl_iff_eq_le
@[deprecated (since := "2026-03-27")] alias reflexive_iff_subrelation_eq := refl_iff_eq_le

/--
theorem `irrefl_iff_le_ne` / 定理 `irrefl_iff_le_ne`

English:
theorem irrefl_iff_le_ne
  statement: Std.Irrefl r ↔ r <= Ne
  proof: by
  unfold Pi.hasLe Prop.le
  grind [Std.Irrefl]

@[deprecated (since := "2026-06-30")] alias irrefl_iff_subrelation_ne := irrefl_iff_le_ne
@[deprecated (since := "2026-02-12")] alias irreflexive_iff_subrelation_ne := irrefl_iff_le_ne

中文:
定理 irrefl_iff_le_ne
  结论: Std.Irrefl r ↔ r <= 不等
  证明: by
  unfold Pi.hasLe Prop.le
  grind [Std.Irrefl]

@[deprecated (since := "2026-06-30")] alias irrefl_iff_subrelation_ne := irrefl_iff_le_ne
@[deprecated (since := "2026-02-12")] alias irreflexive_iff_subrelation_ne := irrefl_iff_le_ne

Depends on / 依赖: Irrefl, Pi.hasLe, Prop.le, Std.Irrefl
-/
theorem irrefl_iff_le_ne : Std.Irrefl r ↔ r <= Ne := by
  unfold Pi.hasLe Prop.le
  grind [Std.Irrefl]

@[deprecated (since := "2026-06-30")] alias irrefl_iff_subrelation_ne := irrefl_iff_le_ne
@[deprecated (since := "2026-02-12")] alias irreflexive_iff_subrelation_ne := irrefl_iff_le_ne

/--
theorem `Std.Symm.iff` / 定理 `Std.Symm.iff`

English:
theorem Std.Symm.iff
  given: [Std.Symm r] (x y : α)
  statement: r x y ↔ r y x
  proof: ⟨symm_of r, symm_of r⟩

@[deprecated (since := "2026-06-10")] protected alias Symmetric.iff := Std.Symm.iff

中文:
定理 Std.Symm.iff
  条件: [Std.Symm r] (x y : α)
  结论: r x y ↔ r y x
  证明: ⟨symm_of r, symm_of r⟩

@[deprecated (since := "2026-06-10")] protected alias Symmetric.iff := Std.Symm.iff
-/
protected theorem Std.Symm.iff [Std.Symm r] (x y : α) : r x y ↔ r y x :=
  ⟨symm_of r, symm_of r⟩

@[deprecated (since := "2026-06-10")] protected alias Symmetric.iff := Std.Symm.iff

/--
theorem `Std.Symm.flip_eq` / 定理 `Std.Symm.flip_eq`

English:
theorem Std.Symm.flip_eq
  given: [Std.Symm r]
  statement: flip r = r
  proof: funext₂ fun _ _ => propext Std.Symm.iff (r := r) ..

@[deprecated (since := "2026-06-10")] alias Symmetric.flip_eq := Std.Symm.flip_eq

中文:
定理 Std.Symm.flip_eq
  条件: [Std.Symm r]
  结论: flip r = r
  证明: funext₂ fun _ _ => propext Std.Symm.iff (r := r) ..

@[deprecated (since := "2026-06-10")] alias Symmetric.flip_eq := Std.Symm.flip_eq

Depends on / 依赖: Std.Symm.iff, propext
-/
theorem Std.Symm.flip_eq [Std.Symm r] : flip r = r :=
funext₂ fun _ _ => propext Std.Symm.iff (r := r) ..

@[deprecated (since := "2026-06-10")] alias Symmetric.flip_eq := Std.Symm.flip_eq

/--
theorem `Std.Symm.swap_eq` / 定理 `Std.Symm.swap_eq`

English:
theorem Std.Symm.swap_eq
  given: [Std.Symm r]
  statement: swap r = r
  proof: Std.Symm.flip_eq

@[deprecated (since := "2026-06-10")] alias Symmetric.swap_eq := Std.Symm.swap_eq

中文:
定理 Std.Symm.swap_eq
  条件: [Std.Symm r]
  结论: swap r = r
  证明: Std.Symm.flip_eq

@[deprecated (since := "2026-06-10")] alias Symmetric.swap_eq := Std.Symm.swap_eq

Depends on / 依赖: Std.Symm.flip_eq, flip_eq
-/
theorem Std.Symm.swap_eq [Std.Symm r] : swap r = r :=
  Std.Symm.flip_eq

@[deprecated (since := "2026-06-10")] alias Symmetric.swap_eq := Std.Symm.swap_eq

/--
theorem `flip_eq_iff` / 定理 `flip_eq_iff`

English:
theorem flip_eq_iff
  statement: flip r = r ↔ Std.Symm r
  proof: .mp⟩, fun _ => Std.Symm.flip_eq⟩ ⟨fun h => ⟨fun _ _ => congr_fun₂ h ..

中文:
定理 flip_eq_iff
  结论: flip r = r ↔ Std.Symm r
  证明: .mp⟩, fun _ => Std.Symm.flip_eq⟩ ⟨fun h => ⟨fun _ _ => congr_fun₂ h ..

Depends on / 依赖: Std.Symm.flip_eq, flip_eq
-/
theorem flip_eq_iff : flip r = r ↔ Std.Symm r :=
.mp⟩, fun _ => Std.Symm.flip_eq⟩ ⟨fun h => ⟨fun _ _ => congr_fun₂ h ..

/--
theorem `swap_eq_iff` / 定理 `swap_eq_iff`

English:
theorem swap_eq_iff
  statement: swap r = r ↔ Std.Symm r
  proof: flip_eq_iff

中文:
定理 swap_eq_iff
  结论: swap r = r ↔ Std.Symm r
  证明: flip_eq_iff

Depends on / 依赖: flip_eq_iff
-/
theorem swap_eq_iff : swap r = r ↔ Std.Symm r :=
  flip_eq_iff

end NeImp

section Comap

variable {r : β -> β -> Prop}

/--
Instance `Std.Refl.comap` / 实例 `Std.Refl.comap`

English:
instance Std.Refl.comap
  signature: [Std.Refl r] (f : α -> β)
  body: refl f a

@[deprecated (since := "2026-03-27")] alias Reflexive.comap := Std.Refl.comap

中文:
实例 Std.Refl.comap
  签名: [Std.Refl r] (f : α -> β)
  定义体: refl f a

@[deprecated (since := "2026-03-27")] alias Reflexive.comap := Std.Refl.comap
-/
instance Std.Refl.comap [Std.Refl r] (f : α -> β) : Std.Refl (r on f) where
refl a := refl f a

@[deprecated (since := "2026-03-27")] alias Reflexive.comap := Std.Refl.comap

/--
Instance `Std.Symm.comap` / 实例 `Std.Symm.comap`

English:
instance Std.Symm.comap
  signature: [Std.Symm r] (f : α -> β)
  body: symm_of r hab

@[deprecated (since := "2026-06-10")] alias Symmetric.comap := Std.Symm.comap

中文:
实例 Std.Symm.comap
  签名: [Std.Symm r] (f : α -> β)
  定义体: symm_of r hab

@[deprecated (since := "2026-06-10")] alias Symmetric.comap := Std.Symm.comap

Depends on / 依赖: symm_of
-/
instance Std.Symm.comap [Std.Symm r] (f : α -> β) : Std.Symm (r on f) where
  symm _ _ hab := symm_of r hab

@[deprecated (since := "2026-06-10")] alias Symmetric.comap := Std.Symm.comap

/--
Instance `IsTrans.comap` / 实例 `IsTrans.comap`

English:
instance IsTrans.comap
  signature: [IsTrans β r] (f : α -> β)
  body: trans_of r

@[deprecated (since := "2026-02-21")] alias Transitive.comap := IsTrans.comap

中文:
实例 是Trans.comap
  签名: [是Trans β r] (f : α -> β)
  定义体: trans_of r

@[deprecated (since := "2026-02-21")] alias Transitive.comap := IsTrans.comap

Depends on / 依赖: trans_of
-/
instance IsTrans.comap [IsTrans β r] (f : α -> β) : IsTrans α (r on f) where
  trans _ _ _ := trans_of r

@[deprecated (since := "2026-02-21")] alias Transitive.comap := IsTrans.comap

/--
Instance `IsEquiv.comap` / 实例 `IsEquiv.comap`

English:
instance IsEquiv.comap
  signature: [IsEquiv β r] (f : α -> β)

中文:
实例 Is等价.comap
  签名: [Is等价 β r] (f : α -> β)
-/
instance IsEquiv.comap [IsEquiv β r] (f : α -> β) : IsEquiv α (r on f) where

/--
theorem `Equivalence.comap` / 定理 `Equivalence.comap`

English:
theorem Equivalence.comap
  given: (h : Equivalence r) (f : α -> β)
  statement: Equivalence (r on f)
  proof: ⟨fun a => h.refl (f a), h.symm, h.trans⟩

中文:
定理 等价.comap
  条件: (h : 等价 r) (f : α -> β)
  结论: 等价 (r on f)
  证明: ⟨fun a => h.refl (f a), h.symm, h.trans⟩

Depends on / 依赖: h.refl, h.symm, h.trans
-/
theorem Equivalence.comap (h : Equivalence r) (f : α -> β) : Equivalence (r on f) :=
  ⟨fun a => h.refl (f a), h.symm, h.trans⟩

end Comap

namespace Relation

section Comp

variable {r : α -> β -> Prop} {p : β -> γ -> Prop} {q : γ -> δ -> Prop}

/--
Definition of `Comp` / `Comp` 的定义

English:
definition Comp
  signature: (r : α -> β -> Prop) (p : β -> γ -> Prop) (a : α) (c : γ)
  body: exists b, r a b ∧ p b c

@[inherit_doc]
local infixr:80 " ∘r " => Relation.Comp

@[simp]

中文:
定义 复合
  签名: (r : α -> β -> 命题) (p : β -> γ -> 命题) (a : α) (c : γ)
  定义体: exists b, r a b ∧ p b c

@[inherit_doc]
local infixr:80 " ∘r " => Relation.Comp

@[simp]
-/
def Comp (r : α -> β -> Prop) (p : β -> γ -> Prop) (a : α) (c : γ) : Prop :=
  exists b, r a b ∧ p b c

@[inherit_doc]
local infixr:80 " ∘r " => Relation.Comp

@[simp]
/--
theorem `comp_eq_fun` / 定理 `comp_eq_fun`

English:
theorem comp_eq_fun
  given: (f : γ -> β)
  statement: r ∘r (· = f ·) = (r · <| f ·)
  proof: by
  ext x y
  simp [Comp]

@[simp]

中文:
定理 comp_eq_fun
  条件: (f : γ -> β)
  结论: r ∘r (· = f ·) = (r · <| f ·)
  证明: by
  ext x y
  simp [Comp]

@[simp]
-/
theorem comp_eq_fun (f : γ -> β) : r ∘r (· = f ·) = (r · <| f ·) := by
  ext x y
  simp [Comp]

@[simp]
/--
theorem `comp_eq` / 定理 `comp_eq`

English:
theorem comp_eq
  statement: r ∘r (· = ·) = r
  proof: comp_eq_fun ..

@[simp]

中文:
定理 comp_eq
  结论: r ∘r (· = ·) = r
  证明: comp_eq_fun ..

@[simp]

Depends on / 依赖: comp_eq_fun
-/
theorem comp_eq : r ∘r (· = ·) = r := comp_eq_fun ..

@[simp]
/--
theorem `fun_eq_comp` / 定理 `fun_eq_comp`

English:
theorem fun_eq_comp
  given: (f : γ -> α)
  statement: (f · = ·) ∘r r = (r <| f ·)
  proof: by
  ext x y
  simp [Comp]

@[simp]

中文:
定理 fun_eq_comp
  条件: (f : γ -> α)
  结论: (f · = ·) ∘r r = (r <| f ·)
  证明: by
  ext x y
  simp [Comp]

@[simp]
-/
theorem fun_eq_comp (f : γ -> α) : (f · = ·) ∘r r = (r <| f ·) := by
  ext x y
  simp [Comp]

@[simp]
/--
theorem `eq_comp` / 定理 `eq_comp`

English:
theorem eq_comp
  statement: (· = ·) ∘r r = r
  proof: fun_eq_comp ..

@[simp]

中文:
定理 eq_comp
  结论: (· = ·) ∘r r = r
  证明: fun_eq_comp ..

@[simp]

Depends on / 依赖: fun_eq_comp
-/
theorem eq_comp : (· = ·) ∘r r = r := fun_eq_comp ..

@[simp]
/--
theorem `iff_comp` / 定理 `iff_comp`

English:
theorem iff_comp
  given: {r : Prop -> α -> Prop}
  statement: (· ↔ ·) ∘r r = r
  proof: by
  grind [eq_comp]

@[simp]

中文:
定理 iff_comp
  条件: {r : 命题 -> α -> 命题}
  结论: (· ↔ ·) ∘r r = r
  证明: by
  grind [eq_comp]

@[simp]

Depends on / 依赖: eq_comp
-/
theorem iff_comp {r : Prop -> α -> Prop} : (· ↔ ·) ∘r r = r := by
  grind [eq_comp]

@[simp]
/--
theorem `comp_iff` / 定理 `comp_iff`

English:
theorem comp_iff
  given: {r : α -> Prop -> Prop}
  statement: r ∘r (· ↔ ·) = r
  proof: by
  grind [comp_eq]

中文:
定理 comp_iff
  条件: {r : α -> 命题 -> 命题}
  结论: r ∘r (· ↔ ·) = r
  证明: by
  grind [comp_eq]

Depends on / 依赖: comp_eq
-/
theorem comp_iff {r : α -> Prop -> Prop} : r ∘r (· ↔ ·) = r := by
  grind [comp_eq]

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: (r ∘r p) ∘r q = r ∘r p ∘r q
  proof: by
  funext a d
  apply propext
  constructor
  · exact fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ => ⟨b, hab, c, hbc, hcd⟩
  · exact fun ⟨b, hab, c, hbc, hcd⟩ => ⟨c, ⟨b, hab, hbc⟩, hcd⟩

中文:
定理 comp_assoc
  结论: (r ∘r p) ∘r q = r ∘r p ∘r q
  证明: by
  funext a d
  apply propext
  constructor
  · exact fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ => ⟨b, hab, c, hbc, hcd⟩
  · exact fun ⟨b, hab, c, hbc, hcd⟩ => ⟨c, ⟨b, hab, hbc⟩, hcd⟩

Depends on / 依赖: propext
-/
theorem comp_assoc : (r ∘r p) ∘r q = r ∘r p ∘r q := by
  funext a d
  apply propext
  constructor
  · exact fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ => ⟨b, hab, c, hbc, hcd⟩
  · exact fun ⟨b, hab, c, hbc, hcd⟩ => ⟨c, ⟨b, hab, hbc⟩, hcd⟩

/--
theorem `flip_comp` / 定理 `flip_comp`

English:
theorem flip_comp
  statement: flip (r ∘r p) = flip p ∘r flip r
  proof: by
  funext c a
  apply propext
  constructor
  · exact fun ⟨b, hab, hbc⟩ => ⟨b, hbc, hab⟩
  · exact fun ⟨b, hbc, hab⟩ => ⟨b, hab, hbc⟩

中文:
定理 flip_comp
  结论: flip (r ∘r p) = flip p ∘r flip r
  证明: by
  funext c a
  apply propext
  constructor
  · exact fun ⟨b, hab, hbc⟩ => ⟨b, hbc, hab⟩
  · exact fun ⟨b, hbc, hab⟩ => ⟨b, hab, hbc⟩

Depends on / 依赖: propext
-/
theorem flip_comp : flip (r ∘r p) = flip p ∘r flip r := by
  funext c a
  apply propext
  constructor
  · exact fun ⟨b, hab, hbc⟩ => ⟨b, hbc, hab⟩
  · exact fun ⟨b, hbc, hab⟩ => ⟨b, hab, hbc⟩

end Comp

section Fibration

variable (rα : α -> α -> Prop) (rβ : β -> β -> Prop) (f : α -> β)

/--
Definition of `Fibration` / `Fibration` 的定义

English:
definition Fibration
  body: forall ⦃a b⦄, rβ b (f a) -> exists a', rα a' a ∧ f a' = b

中文:
定义 纤维化
  定义体: forall ⦃a b⦄, rβ b (f a) -> exists a', rα a' a ∧ f a' = b
-/
def Fibration :=
  forall ⦃a b⦄, rβ b (f a) -> exists a', rα a' a ∧ f a' = b

variable {rα rβ}

/--
theorem `_root_.Acc.of_fibration` / 定理 `_root_.Acc.of_fibration`

English:
theorem _root_.Acc.of_fibration
  given: (fib : Fibration rα rβ f) {a} (ha : Acc rα a)
  statement: Acc rβ (f a)
  proof: by
  induction ha with | intro a _ ih => ?_
  refine Acc.intro (f a) fun b hr => ?_
  obtain ⟨a', hr', rfl⟩ := fib hr
  exact ih a' hr'

中文:
定理 _root_.Acc.of_fibration
  条件: (fib : 纤维化 rα rβ f) {a} (ha : Acc rα a)
  结论: Acc rβ (f a)
  证明: by
  induction ha with | intro a _ ih => ?_
  refine Acc.intro (f a) fun b hr => ?_
  obtain ⟨a', hr', rfl⟩ := fib hr
  exact ih a' hr'

Depends on / 依赖: Acc.intro
-/
theorem _root_.Acc.of_fibration (fib : Fibration rα rβ f) {a} (ha : Acc rα a) : Acc rβ (f a) := by
  induction ha with | intro a _ ih => ?_
  refine Acc.intro (f a) fun b hr => ?_
  obtain ⟨a', hr', rfl⟩ := fib hr
  exact ih a' hr'

/--
theorem `_root_.Acc.of_downward_closed` / 定理 `_root_.Acc.of_downward_closed`

English:
theorem _root_.Acc.of_downward_closed
  statement: (dc : forall {a b}, rβ b (f a) -> exists c, f c = b) (a : α)
  proof: ha.of_fibration f fun a _ h =>
    let ⟨a', he⟩ := dc h
    ⟨a', by simp_all [InvImage], he⟩

中文:
定理 _root_.Acc.of_downward_closed
  结论: (dc : 对任意 {a b}, rβ b (f a) -> 存在 c, f c = b) (a : α)
  证明: ha.of_fibration f fun a _ h =>
    let ⟨a', he⟩ := dc h
    ⟨a', by simp_all [InvImage], he⟩

Depends on / 依赖: InvImage, ha.of_fibration, modularCyclotomicCharacter, modularCyclotomicCharacter.toFun_spec, of_fibration, toFun_spec
-/
theorem _root_.Acc.of_downward_closed (dc : forall {a b}, rβ b (f a) -> exists c, f c = b) (a : α)
    (ha : Acc (InvImage rβ f) a) : Acc rβ (f a) :=
  ha.of_fibration f fun a _ h =>
    let ⟨a', he⟩ := dc h
    ⟨a', by simp_all [InvImage], he⟩

end Fibration

section Map
variable {r : α -> β -> Prop} {f : α -> γ} {g : β -> δ} {c : γ} {d : δ}

/--
Definition of `Map` / `Map` 的定义

English:
definition Map
  signature: (r : α -> β -> Prop) (f : α -> γ) (g : β -> δ)
  body: fun c d =>
  exists a b, r a b ∧ f a = c ∧ g b = d

中文:
定义 Map
  签名: (r : α -> β -> 命题) (f : α -> γ) (g : β -> δ)
  定义体: fun c d =>
  exists a b, r a b ∧ f a = c ∧ g b = d

Depends on / 依赖: modularCyclotomicCharacter, modularCyclotomicCharacter.toFun_unique, toFun_unique
-/
protected def Map (r : α -> β -> Prop) (f : α -> γ) (g : β -> δ) : γ -> δ -> Prop := fun c d =>
  exists a b, r a b ∧ f a = c ∧ g b = d

/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  statement: Relation.Map r f g c d ↔ exists a b, r a b ∧ f a = c ∧ g b = d
  proof: Iff.rfl

中文:
引理 map_apply
  结论: 关系.Map r f g c d ↔ 存在 a b, r a b ∧ f a = c ∧ g b = d
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma map_apply : Relation.Map r f g c d ↔ exists a b, r a b ∧ f a = c ∧ g b = d := Iff.rfl

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (r : α -> β -> Prop) (f₁ : α -> γ) (g₁ : β -> δ) (f₂ : γ -> ε) (g₂ : δ -> ζ)
  proof: by
  grind [Relation.Map]

@[simp]

中文:
引理 map_map
  条件: (r : α -> β -> 命题) (f₁ : α -> γ) (g₁ : β -> δ) (f₂ : γ -> ε) (g₂ : δ -> ζ)
  证明: by
  grind [Relation.Map]

@[simp]
-/
@[simp] lemma map_map (r : α -> β -> Prop) (f₁ : α -> γ) (g₁ : β -> δ) (f₂ : γ -> ε) (g₂ : δ -> ζ) :
    Relation.Map (Relation.Map r f₁ g₁) f₂ g₂ = Relation.Map r (f₂ ∘ f₁) (g₂ ∘ g₁) := by
  grind [Relation.Map]

@[simp]
/--
lemma `map_apply_apply` / 引理 `map_apply_apply`

English:
lemma map_apply_apply
  given: (hf : Injective f) (hg : Injective g) (r : α -> β -> Prop) (a : α) (b : β)
  proof: by simp [Relation.Map, hf.eq_iff, hg.eq_iff]

中文:
引理 map_apply_apply
  条件: (hf : 单射 f) (hg : 单射 g) (r : α -> β -> 命题) (a : α) (b : β)
  证明: by simp [Relation.Map, hf.eq_iff, hg.eq_iff]

Depends on / 依赖: Relation, Relation.Map, eq_iff, hf.eq_iff, hg.eq_iff
-/
lemma map_apply_apply (hf : Injective f) (hg : Injective g) (r : α -> β -> Prop) (a : α) (b : β) :
    Relation.Map r f g (f a) (g b) ↔ r a b := by simp [Relation.Map, hf.eq_iff, hg.eq_iff]

/--
lemma `map_id_id` / 引理 `map_id_id`

English:
lemma map_id_id
  given: (r : α -> β -> Prop)
  statement: Relation.Map r id id = r
  proof: by ext; simp [Relation.Map]

中文:
引理 map_id_id
  条件: (r : α -> β -> 命题)
  结论: 关系.Map r id id = r
  证明: by ext; simp [Relation.Map]
-/
@[simp] lemma map_id_id (r : α -> β -> Prop) : Relation.Map r id id = r := by ext; simp [Relation.Map]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Decidable
  signature: (exists a b, r a b ∧ f a = c ∧ g b = d)] : Decidable (Relation.Map r f g c d)
  body: ‹Decidable _›

中文:
实例 [可判定
  签名: (存在 a b, r a b ∧ f a = c ∧ g b = d)] : 可判定 (关系.Map r f g c d)
  定义体: ‹Decidable _›

Depends on / 依赖: Decidable
-/
instance [Decidable (exists a b, r a b ∧ f a = c ∧ g b = d)] : Decidable (Relation.Map r f g c d) :=
  ‹Decidable _›

/--
lemma `_root_.Std.Refl.map` / 引理 `_root_.Std.Refl.map`

English:
lemma _root_.Std.Refl.map
  given: {r : α -> α -> Prop} [Std.Refl r] {f : α -> β} (hf : f.Surjective)
  proof: by
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨y, y, refl y, rfl, rfl⟩

@[deprecated (since := "2026-03-27")] alias map_reflexive := Std.Refl.map

中文:
引理 _root_.Std.Refl.map
  条件: {r : α -> α -> 命题} [Std.Refl r] {f : α -> β} (hf : f.满射)
  证明: by
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨y, y, refl y, rfl, rfl⟩

@[deprecated (since := "2026-03-27")] alias map_reflexive := Std.Refl.map
-/
lemma _root_.Std.Refl.map {r : α -> α -> Prop} [Std.Refl r] {f : α -> β} (hf : f.Surjective) :
    Std.Refl (Relation.Map r f f) where
  refl x := by
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨y, y, refl y, rfl, rfl⟩

@[deprecated (since := "2026-03-27")] alias map_reflexive := Std.Refl.map

/--
Instance `_root_.Std.Symm.map` / 实例 `_root_.Std.Symm.map`

English:
instance _root_.Std.Symm.map
  signature: {r : α -> α -> Prop} [Std.Symm r] (f : α -> β)
  body: by
    rintro ⟨x, y, hxy, rfl, rfl⟩
    exact ⟨y, x, symm hxy, rfl, rfl⟩

@[deprecated (since := "2026-06-10")] alias map_symmetric := Std.Symm.map

中文:
实例 _root_.Std.Symm.map
  签名: {r : α -> α -> 命题} [Std.Symm r] (f : α -> β)
  定义体: by
    rintro ⟨x, y, hxy, rfl, rfl⟩
    exact ⟨y, x, symm hxy, rfl, rfl⟩

@[deprecated (since := "2026-06-10")] alias map_symmetric := Std.Symm.map
-/
instance _root_.Std.Symm.map {r : α -> α -> Prop} [Std.Symm r] (f : α -> β) :
    Std.Symm (Relation.Map r f f) where
  symm _ _ := by
    rintro ⟨x, y, hxy, rfl, rfl⟩
    exact ⟨y, x, symm hxy, rfl, rfl⟩

@[deprecated (since := "2026-06-10")] alias map_symmetric := Std.Symm.map

/--
lemma `_root_.IsTrans.map` / 引理 `_root_.IsTrans.map`

English:
lemma _root_.IsTrans.map
  statement: {r : α -> α -> Prop} [IsTrans α r] {f : α -> β}
  proof: by
  refine ⟨fun _ _ _ ⟨x, y, hxy, hx, hy⟩ ⟨y', z, hyz, hy', hz⟩ => ?_⟩
exact ⟨x, z, trans_of r hxy trans_of r (hf y y' <| hy' ▸ hy) hyz, hx, hz⟩

@[deprecated (since := "2026-03-27")] alias isTrans_map := IsTrans.map

@[deprecated (since := "2026-02-21")] alias map_transitive := isTrans_map

中文:
引理 _root_.是Trans.map
  结论: {r : α -> α -> 命题} [是Trans α r] {f : α -> β}
  证明: by
  refine ⟨fun _ _ _ ⟨x, y, hxy, hx, hy⟩ ⟨y', z, hyz, hy', hz⟩ => ?_⟩
exact ⟨x, z, trans_of r hxy trans_of r (hf y y' <| hy' ▸ hy) hyz, hx, hz⟩

@[deprecated (since := "2026-03-27")] alias isTrans_map := IsTrans.map

@[deprecated (since := "2026-02-21")] alias map_transitive := isTrans_map

Depends on / 依赖: trans_of
-/
lemma _root_.IsTrans.map {r : α -> α -> Prop} [IsTrans α r] {f : α -> β}
    (hf : forall x y, f x = f y -> r x y) : IsTrans β (Relation.Map r f f) := by
  refine ⟨fun _ _ _ ⟨x, y, hxy, hx, hy⟩ ⟨y', z, hyz, hy', hz⟩ => ?_⟩
exact ⟨x, z, trans_of r hxy trans_of r (hf y y' <| hy' ▸ hy) hyz, hx, hz⟩

@[deprecated (since := "2026-03-27")] alias isTrans_map := IsTrans.map

@[deprecated (since := "2026-02-21")] alias map_transitive := isTrans_map

/--
lemma `map_equivalence` / 引理 `map_equivalence`

English:
lemma map_equivalence
  statement: {r : α -> α -> Prop} (hr : Equivalence r) (f : α -> β) (hf : f.Surjective)
  proof: hr.stdRefl.map hf
  symm := @(hr.stdSymm.map f |>.symm)
  trans := @(hr.isTrans.map hf_ker |>.trans)

中文:
引理 map_equivalence
  结论: {r : α -> α -> 命题} (hr : 等价 r) (f : α -> β) (hf : f.满射)
  证明: hr.stdRefl.map hf
  symm := @(hr.stdSymm.map f |>.symm)
  trans := @(hr.isTrans.map hf_ker |>.trans)

Depends on / 依赖: hr.stdRefl.map, stdRefl
-/
lemma map_equivalence {r : α -> α -> Prop} (hr : Equivalence r) (f : α -> β) (hf : f.Surjective)
    (hf_ker : forall x y, f x = f y -> r x y) : Equivalence (Relation.Map r f f) where
.refl refl := hr.stdRefl.map hf
  symm := @(hr.stdSymm.map f |>.symm)
  trans := @(hr.isTrans.map hf_ker |>.trans)

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  given: {r s : α -> β -> Prop} {f : α -> γ} {g : β -> δ} (h : r <= s)
  proof: fun _ _ ⟨x, y, hxy, hx, hy⟩ => ⟨x, y, h _ _ hxy, hx, hy⟩

中文:
引理 map_mono
  条件: {r s : α -> β -> 命题} {f : α -> γ} {g : β -> δ} (h : r <= s)
  证明: fun _ _ ⟨x, y, hxy, hx, hy⟩ => ⟨x, y, h _ _ hxy, hx, hy⟩
-/
lemma map_mono {r s : α -> β -> Prop} {f : α -> γ} {g : β -> δ} (h : r <= s) :
    Relation.Map r f g <= Relation.Map s f g :=
  fun _ _ ⟨x, y, hxy, hx, hy⟩ => ⟨x, y, h _ _ hxy, hx, hy⟩

/--
lemma `le_onFun_map` / 引理 `le_onFun_map`

English:
lemma le_onFun_map
  given: {r : α -> α -> Prop} (f : α -> β)
  statement: r <= (Relation.Map r f f on f)
  proof: by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]

中文:
引理 le_onFun_map
  条件: {r : α -> α -> 命题} (f : α -> β)
  结论: r <= (关系.Map r f f on f)
  证明: by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]

Depends on / 依赖: Pi.hasLe, Prop.le, Relation, Relation.Map
-/
lemma le_onFun_map {r : α -> α -> Prop} (f : α -> β) : r <= (Relation.Map r f f on f) := by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]

/--
lemma `onFun_map_eq_of_injective` / 引理 `onFun_map_eq_of_injective`

English:
lemma onFun_map_eq_of_injective
  given: {r : α -> α -> Prop} {f : α -> β} (hinj : f.Injective)
  proof: by
  ext x y
  exact ⟨fun ⟨x', y', hr, hx, hy⟩ => hinj hx ▸ hinj hy ▸ hr, fun h => ⟨x, y, h, rfl, rfl⟩⟩

中文:
引理 onFun_map_eq_of_injective
  条件: {r : α -> α -> 命题} {f : α -> β} (hinj : f.单射)
  证明: by
  ext x y
  exact ⟨fun ⟨x', y', hr, hx, hy⟩ => hinj hx ▸ hinj hy ▸ hr, fun h => ⟨x, y, h, rfl, rfl⟩⟩
-/
lemma onFun_map_eq_of_injective {r : α -> α -> Prop} {f : α -> β} (hinj : f.Injective) :
    (Relation.Map r f f on f) = r := by
  ext x y
  exact ⟨fun ⟨x', y', hr, hx, hy⟩ => hinj hx ▸ hinj hy ▸ hr, fun h => ⟨x, y, h, rfl, rfl⟩⟩

/--
lemma `map_onFun_le` / 引理 `map_onFun_le`

English:
lemma map_onFun_le
  given: {r : β -> β -> Prop} (f : α -> β)
  statement: Relation.Map (r on f) f f <= r
  proof: by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]

中文:
引理 map_onFun_le
  条件: {r : β -> β -> 命题} (f : α -> β)
  结论: 关系.Map (r on f) f f <= r
  证明: by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]

Depends on / 依赖: Pi.hasLe, Prop.le, Relation, Relation.Map
-/
lemma map_onFun_le {r : β -> β -> Prop} (f : α -> β) : Relation.Map (r on f) f f <= r := by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]

/--
lemma `map_onFun_eq_of_surjective` / 引理 `map_onFun_eq_of_surjective`

English:
lemma map_onFun_eq_of_surjective
  given: {r : β -> β -> Prop} {f : α -> β} (hsurj : f.Surjective)
  proof: by
  ext x y
  have _ := hsurj x
  have _ := hsurj y
  grind [Relation.Map]

中文:
引理 map_onFun_eq_of_surjective
  条件: {r : β -> β -> 命题} {f : α -> β} (hsurj : f.满射)
  证明: by
  ext x y
  have _ := hsurj x
  have _ := hsurj y
  grind [Relation.Map]

Depends on / 依赖: Relation, Relation.Map
-/
lemma map_onFun_eq_of_surjective {r : β -> β -> Prop} {f : α -> β} (hsurj : f.Surjective) :
    Relation.Map (r on f) f f = r := by
  ext x y
  have _ := hsurj x
  have _ := hsurj y
  grind [Relation.Map]

/--
lemma `map_onFun_map_eq_map` / 引理 `map_onFun_map_eq_map`

English:
lemma map_onFun_map_eq_map
  given: {r : α -> α -> Prop} (f : α -> β)
  proof: by
  grind [Relation.Map]

中文:
引理 map_onFun_map_eq_map
  条件: {r : α -> α -> 命题} (f : α -> β)
  证明: by
  grind [Relation.Map]

Depends on / 依赖: Relation, Relation.Map
-/
lemma map_onFun_map_eq_map {r : α -> α -> Prop} (f : α -> β) :
    Relation.Map (Relation.Map r f f on f) f f = Relation.Map r f f := by
  grind [Relation.Map]

/--
lemma `onFun_map_onFun_eq_onFun` / 引理 `onFun_map_onFun_eq_onFun`

English:
lemma onFun_map_onFun_eq_onFun
  given: {r : β -> β -> Prop} (f : α -> β)
  proof: by
  grind [Relation.Map]

中文:
引理 onFun_map_onFun_eq_onFun
  条件: {r : β -> β -> 命题} (f : α -> β)
  证明: by
  grind [Relation.Map]

Depends on / 依赖: Relation, Relation.Map
-/
lemma onFun_map_onFun_eq_onFun {r : β -> β -> Prop} (f : α -> β) :
    (Relation.Map (r on f) f f on f) = (r on f) := by
  grind [Relation.Map]

/--
lemma `onFun_map_onFun_iff_onFun` / 引理 `onFun_map_onFun_iff_onFun`

English:
lemma onFun_map_onFun_iff_onFun
  given: {r : β -> β -> Prop} (f : α -> β) (a₁ a₂ : α)
  proof: by
  grind [Relation.Map]

中文:
引理 onFun_map_onFun_iff_onFun
  条件: {r : β -> β -> 命题} (f : α -> β) (a₁ a₂ : α)
  证明: by
  grind [Relation.Map]

Depends on / 依赖: Relation, Relation.Map
-/
lemma onFun_map_onFun_iff_onFun {r : β -> β -> Prop} (f : α -> β) (a₁ a₂ : α) :
    Relation.Map (r on f) f f (f a₁) (f a₂) ↔ r (f a₁) (f a₂) := by
  grind [Relation.Map]

end Map

variable {r : α -> α -> Prop} {a b c : α}

/-- `ReflTransGen r`: reflexive transitive closure of `r` -/
@[mk_iff ReflTransGen.cases_tail_iff, grind]
/--
Inductive type `ReflTransGen` / 归纳类型 `ReflTransGen`

English:
inductive ReflTransGen
  parameters: (r : α -> α -> Prop) (a : α)
  constructors (2):
    - refl: ReflTransGen r a a
    - tail: {b c : α} : ReflTransGen r a b -> r b c -> ReflTransGen r a c

中文:
归纳类型 ReflTransGen
  参数: (r : α -> α -> 命题) (a : α)
  构造子 (2 个):
    - refl: ReflTransGen r a a
    - tail: {b c : α} : ReflTransGen r a b -> r b c -> ReflTransGen r a c
-/
inductive ReflTransGen (r : α -> α -> Prop) (a : α) : α -> Prop
  | refl : ReflTransGen r a a
  | tail {b c : α} : ReflTransGen r a b -> r b c -> ReflTransGen r a c

attribute [refl] ReflTransGen.refl

/-- `ReflGen r`: reflexive closure of `r` -/
@[mk_iff, grind]
/--
Inductive type `ReflGen` / 归纳类型 `ReflGen`

English:
inductive ReflGen
  parameters: (r : α -> α -> Prop) (a : α)
  constructors (2):
    - refl: ReflGen r a a
    - single: {b : α} : r a b -> ReflGen r a b

中文:
归纳类型 ReflGen
  参数: (r : α -> α -> 命题) (a : α)
  构造子 (2 个):
    - refl: ReflGen r a a
    - single: {b : α} : r a b -> ReflGen r a b
-/
inductive ReflGen (r : α -> α -> Prop) (a : α) : α -> Prop
  | refl : ReflGen r a a
  | single {b : α} : r a b -> ReflGen r a b

attribute [refl] ReflGen.refl
attribute [grind =] reflGen_iff

/--
Definition of `SymmGen` / `SymmGen` 的定义

English:
definition SymmGen
  signature: (r : α -> α -> Prop) (a b : α)
  body: r a b ∨ r b a

中文:
定义 SymmGen
  签名: (r : α -> α -> 命题) (a b : α)
  定义体: r a b ∨ r b a
-/
def SymmGen (r : α -> α -> Prop) (a b : α) : Prop :=
  r a b ∨ r b a

variable (r) in
/-- `EqvGen r`: equivalence closure of `r`. -/
@[mk_iff]
/--
Inductive type `EqvGen` / 归纳类型 `EqvGen`

English:
inductive EqvGen
  parameters: : α -> α -> Prop
  constructors (4):
    - rel: x y : r x y -> EqvGen x y
    - refl: x : EqvGen x x
    - symm: x y : EqvGen x y -> EqvGen y x
    - trans: x y z : EqvGen x y -> EqvGen y z -> EqvGen x z

中文:
归纳类型 EqvGen
  参数: : α -> α -> 命题
  构造子 (4 个):
    - rel: x y : r x y -> EqvGen x y
    - refl: x : EqvGen x x
    - symm: x y : EqvGen x y -> EqvGen y x
    - trans: x y z : EqvGen x y -> EqvGen y z -> EqvGen x z
-/
inductive EqvGen : α -> α -> Prop
  | rel x y : r x y -> EqvGen x y
  | refl x : EqvGen x x
  | symm x y : EqvGen x y -> EqvGen y x
  | trans x y z : EqvGen x y -> EqvGen y z -> EqvGen x z

attribute [mk_iff] TransGen
attribute [grind] TransGen

/--
theorem `reflGen_le_reflTransGen` / 定理 `reflGen_le_reflTransGen`

English:
theorem reflGen_le_reflTransGen
  statement: ReflGen r <= ReflTransGen r

中文:
定理 reflGen_le_reflTransGen
  结论: ReflGen r <= ReflTransGen r
-/
theorem reflGen_le_reflTransGen : ReflGen r <= ReflTransGen r
  | a, _, .refl => by rfl
  | _, _, .single h => ReflTransGen.tail ReflTransGen.refl h

namespace ReflGen

/--
theorem `to_reflTransGen` / 定理 `to_reflTransGen`

English:
theorem to_reflTransGen
  given: {a b}
  statement: ReflGen r a b -> ReflTransGen r a b
  proof: reflGen_le_reflTransGen a b

中文:
定理 to_reflTransGen
  条件: {a b}
  结论: ReflGen r a b -> ReflTransGen r a b
  证明: reflGen_le_reflTransGen a b

Depends on / 依赖: reflGen_le_reflTransGen
-/
theorem to_reflTransGen {a b} : ReflGen r a b -> ReflTransGen r a b :=
  reflGen_le_reflTransGen a b

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {p : α -> α -> Prop} (hp : r <= p)
  statement: ReflGen r <= ReflGen p

中文:
定理 mono
  条件: {p : α -> α -> 命题} (hp : r <= p)
  结论: ReflGen r <= ReflGen p
-/
theorem mono {p : α -> α -> Prop} (hp : r <= p) : ReflGen r <= ReflGen p
  | a, _, ReflGen.refl => by rfl
  | a, b, single h => single (hp a b h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Refl (ReflGen r)
  body: ⟨@refl α r⟩

中文:
实例 :
  签名: Std.Refl (ReflGen r)
  定义体: ⟨@refl α r⟩
-/
instance : Std.Refl (ReflGen r) :=
  ⟨@refl α r⟩

/--
Instance `stdSymm` / 实例 `stdSymm`

English:
instance stdSymm
  signature: [Std.Symm r]
  body: stdSymm

中文:
实例 stdSymm
  签名: [Std.Symm r]
  定义体: stdSymm
-/
instance stdSymm [Std.Symm r] : Std.Symm (ReflGen r) where
  symm _ _
    | refl => refl
| single h => single symm h

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTrans
  signature: α r] : IsPreorder α (ReflGen r) where
  body: by
    obtain (rfl | h₂) := h₂
    · exact h₁
    obtain (rfl | h₁) := h₁
    · exact single h₂
    exact single (trans_of r h₁ h₂)

中文:
实例 [是Trans
  签名: α r] : 是预序 α (ReflGen r) where
  定义体: by
    obtain (rfl | h₂) := h₂
    · exact h₁
    obtain (rfl | h₁) := h₁
    · exact single h₂
    exact single (trans_of r h₁ h₂)

Depends on / 依赖: single, trans_of
-/
instance [IsTrans α r] : IsPreorder α (ReflGen r) where
  trans a b c h₁ h₂ := by
    obtain (rfl | h₂) := h₂
    · exact h₁
    obtain (rfl | h₁) := h₁
    · exact single h₂
    exact single (trans_of r h₁ h₂)

end ReflGen

namespace SymmGen

/--
theorem `of_rel` / 定理 `of_rel`

English:
theorem of_rel
  given: (h : r a b)
  statement: SymmGen r a b
  proof: Or.inl h

中文:
定理 of_rel
  条件: (h : r a b)
  结论: SymmGen r a b
  证明: Or.inl h

Depends on / 依赖: Or.inl
-/
theorem of_rel (h : r a b) : SymmGen r a b :=
  Or.inl h

/--
theorem `of_rel_symm` / 定理 `of_rel_symm`

English:
theorem of_rel_symm
  given: (h : r b a)
  statement: SymmGen r a b
  proof: Or.inr h

中文:
定理 of_rel_symm
  条件: (h : r b a)
  结论: SymmGen r a b
  证明: Or.inr h

Depends on / 依赖: Or.inr
-/
theorem of_rel_symm (h : r b a) : SymmGen r a b :=
  Or.inr h

/--
theorem `swap` / 定理 `swap`

English:
theorem swap
  given: (h : SymmGen r b a)
  statement: SymmGen (swap r) a b
  proof: by
  induction h with
  | inl hba => exact of_rel hba
  | inr hab => exact of_rel_symm hab

@[simp, refl]

中文:
定理 swap
  条件: (h : SymmGen r b a)
  结论: SymmGen (swap r) a b
  证明: by
  induction h with
  | inl hba => exact of_rel hba
  | inr hab => exact of_rel_symm hab

@[simp, refl]

Depends on / 依赖: of_rel, of_rel_symm
-/
theorem swap (h : SymmGen r b a) : SymmGen (swap r) a b := by
  induction h with
  | inl hba => exact of_rel hba
  | inr hab => exact of_rel_symm hab

@[simp, refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (r : α -> α -> Prop) [Std.Refl r] (a : α)
  statement: SymmGen r a a
  proof: .of_rel (_root_.refl _)

中文:
定理 refl
  条件: (r : α -> α -> 命题) [Std.Refl r] (a : α)
  结论: SymmGen r a a
  证明: .of_rel (_root_.refl _)

Depends on / 依赖: _root_, _root_.refl, of_rel
-/
theorem refl (r : α -> α -> Prop) [Std.Refl r] (a : α) : SymmGen r a a :=
  .of_rel (_root_.refl _)

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  given: [Std.Refl r]
  statement: SymmGen r a a
  proof: .refl ..

中文:
定理 rfl
  条件: [Std.Refl r]
  结论: SymmGen r a a
  证明: .refl ..
-/
theorem rfl [Std.Refl r] : SymmGen r a a := .refl ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] : Std.Refl (SymmGen r) where
  body: .refl r

@[symm]

中文:
实例 [Std.Refl
  签名: r] : Std.Refl (SymmGen r) where
  定义体: .refl r

@[symm]
-/
instance [Std.Refl r] : Std.Refl (SymmGen r) where
  refl := .refl r

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  statement: SymmGen r a b -> SymmGen r b a
  proof: Or.symm

中文:
定理 symm
  结论: SymmGen r a b -> SymmGen r b a
  证明: Or.symm

Depends on / 依赖: Or.symm
-/
theorem symm : SymmGen r a b -> SymmGen r b a :=
  Or.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (SymmGen r)
  body: SymmGen.symm

中文:
实例 :
  签名: Std.Symm (SymmGen r)
  定义体: SymmGen.symm

Depends on / 依赖: SymmGen, SymmGen.symm
-/
instance : Std.Symm (SymmGen r) where
  symm _ _ := SymmGen.symm

/--
Instance `decidableRel` / 实例 `decidableRel`

English:
instance decidableRel
  signature: [DecidableRel r]
  body: fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

中文:
实例 decidableRel
  签名: [DecidableRel r]
  定义体: fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

Depends on / 依赖: Decidable
-/
instance decidableRel [DecidableRel r] : DecidableRel (SymmGen r) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  given: {α : Type*} [LE α] {a b : α} (h : a <= b)
  statement: SymmGen (· <= ·) a b
  proof: .of_rel h

中文:
定理 of_le
  条件: {α : 类型} [LE α] {a b : α} (h : a <= b)
  结论: SymmGen (· <= ·) a b
  证明: .of_rel h

Depends on / 依赖: of_rel
-/
theorem of_le {α : Type*} [LE α] {a b : α} (h : a <= b) : SymmGen (· <= ·) a b := .of_rel h
/--
theorem `of_ge` / 定理 `of_ge`

English:
theorem of_ge
  given: {α : Type*} [LE α] {a b : α} (h : b <= a)
  statement: SymmGen (· <= ·) a b
  proof: .of_rel_symm h

alias _root_.LE.le.symmGen := SymmGen.of_le
alias _root_.LE.le.symmGen_symm := SymmGen.of_ge

中文:
定理 of_ge
  条件: {α : 类型} [LE α] {a b : α} (h : b <= a)
  结论: SymmGen (· <= ·) a b
  证明: .of_rel_symm h

alias _root_.LE.le.symmGen := SymmGen.of_le
alias _root_.LE.le.symmGen_symm := SymmGen.of_ge

Depends on / 依赖: of_rel_symm
-/
theorem of_ge {α : Type*} [LE α] {a b : α} (h : b <= a) : SymmGen (· <= ·) a b := .of_rel_symm h

alias _root_.LE.le.symmGen := SymmGen.of_le
alias _root_.LE.le.symmGen_symm := SymmGen.of_ge

end SymmGen

namespace ReflTransGen

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c)
  statement: ReflTransGen r a c
  proof: by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

中文:
定理 trans
  条件: (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c)
  结论: ReflTransGen r a c
  证明: by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

Depends on / 依赖: hac.tail
-/
theorem trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

/--
theorem `single` / 定理 `single`

English:
theorem single
  given: (hab : r a b)
  statement: ReflTransGen r a b
  proof: refl.tail hab

中文:
定理 single
  条件: (hab : r a b)
  结论: ReflTransGen r a b
  证明: refl.tail hab

Depends on / 依赖: refl.tail
-/
theorem single (hab : r a b) : ReflTransGen r a b :=
  refl.tail hab

/--
theorem `le_reflTransGen` / 定理 `le_reflTransGen`

English:
theorem le_reflTransGen
  statement: r <= ReflTransGen r
  proof: fun _ _ => single

中文:
定理 le_reflTransGen
  结论: r <= ReflTransGen r
  证明: fun _ _ => single

Depends on / 依赖: single
-/
theorem le_reflTransGen : r <= ReflTransGen r :=
  fun _ _ => single

/--
theorem `head` / 定理 `head`

English:
theorem head
  given: (hab : r a b) (hbc : ReflTransGen r b c)
  statement: ReflTransGen r a c
  proof: by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd

中文:
定理 head
  条件: (hab : r a b) (hbc : ReflTransGen r b c)
  结论: ReflTransGen r a c
  证明: by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd

Depends on / 依赖: hac.tail, refl.tail
-/
theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd

/--
Instance `stdSymm` / 实例 `stdSymm`

English:
instance stdSymm
  signature: [Std.Symm r]
  body: by
    induction h with
    | refl => rfl
| tail _ b c => apply c.head symm b

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm

中文:
实例 stdSymm
  签名: [Std.Symm r]
  定义体: by
    induction h with
    | refl => rfl
| tail _ b c => apply c.head symm b

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm

Depends on / 依赖: c.head
-/
instance stdSymm [Std.Symm r] : Std.Symm (ReflTransGen r) where
  symm x y h := by
    induction h with
    | refl => rfl
| tail _ b c => apply c.head symm b

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm

/--
theorem `cases_tail` / 定理 `cases_tail`

English:
theorem cases_tail
  statement: ReflTransGen r a b -> b = a ∨ exists c, ReflTransGen r a c ∧ r c b
  proof: (cases_tail_iff r a b).1

@[elab_as_elim]

中文:
定理 cases_tail
  结论: ReflTransGen r a b -> b = a ∨ 存在 c, ReflTransGen r a c ∧ r c b
  证明: (cases_tail_iff r a b).1

@[elab_as_elim]

Depends on / 依赖: cases_tail_iff
-/
theorem cases_tail : ReflTransGen r a b -> b = a ∨ exists c, ReflTransGen r a c ∧ r c b :=
  (cases_tail_iff r a b).1

@[elab_as_elim]
/--
theorem `head_induction_on` / 定理 `head_induction_on`

English:
theorem head_induction_on
  statement: {motive : forall a : α, ReflTransGen r a b -> Prop} {a : α}
  proof: by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
  apply ih
  · exact head hbc _ refl
  · exact fun h1 h2 => head h1 (h2.tail hbc)

@[elab_as_elim]

中文:
定理 head_induction_on
  结论: {motive : 对任意 a : α, ReflTransGen r a b -> 命题} {a : α}
  证明: by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
  apply ih
  · exact head hbc _ refl
  · exact fun h1 h2 => head h1 (h2.tail hbc)

@[elab_as_elim]

Depends on / 依赖: h2.tail
-/
theorem head_induction_on {motive : forall a : α, ReflTransGen r a b -> Prop} {a : α}
    (h : ReflTransGen r a b) (refl : motive b refl)
    (head : forall {a c} (h' : r a c) (h : ReflTransGen r c b), motive c h -> motive a (h.head h')) :
    motive a h := by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
  apply ih
  · exact head hbc _ refl
  · exact fun h1 h2 => head h1 (h2.tail hbc)

@[elab_as_elim]
/--
theorem `trans_induction_on` / 定理 `trans_induction_on`

English:
theorem trans_induction_on
  statement: {motive : forall {a b : α}, ReflTransGen r a b -> Prop} {a b : α}
  proof: by
  induction h with
  | refl => exact refl a
  | tail hab hbc ih => exact trans hab (.single hbc) ih (single hbc)

中文:
定理 trans_induction_on
  结论: {motive : 对任意 {a b : α}, ReflTransGen r a b -> 命题} {a b : α}
  证明: by
  induction h with
  | refl => exact refl a
  | tail hab hbc ih => exact trans hab (.single hbc) ih (single hbc)

Depends on / 依赖: single
-/
theorem trans_induction_on {motive : forall {a b : α}, ReflTransGen r a b -> Prop} {a b : α}
    (h : ReflTransGen r a b) (refl : forall a, @motive a a refl)
    (single : forall {a b} (h : r a b), motive (single h))
    (trans : forall {a b c} (h₁ : ReflTransGen r a b) (h₂ : ReflTransGen r b c), motive h₁ -> motive h₂ ->
      motive (h₁.trans h₂)) : motive h := by
  induction h with
  | refl => exact refl a
  | tail hab hbc ih => exact trans hab (.single hbc) ih (single hbc)

/--
theorem `cases_head` / 定理 `cases_head`

English:
theorem cases_head
  given: (h : ReflTransGen r a b)
  statement: a = b ∨ exists c, r a c ∧ ReflTransGen r c b
  proof: by
  induction h using Relation.ReflTransGen.head_induction_on <;> grind

中文:
定理 cases_head
  条件: (h : ReflTransGen r a b)
  结论: a = b ∨ 存在 c, r a c ∧ ReflTransGen r c b
  证明: by
  induction h using Relation.ReflTransGen.head_induction_on <;> grind

Depends on / 依赖: ReflTransGen, Relation, Relation.ReflTransGen.head_induction_on, head_induction_on
-/
theorem cases_head (h : ReflTransGen r a b) : a = b ∨ exists c, r a c ∧ ReflTransGen r c b := by
  induction h using Relation.ReflTransGen.head_induction_on <;> grind

/--
theorem `cases_head_iff` / 定理 `cases_head_iff`

English:
theorem cases_head_iff
  statement: ReflTransGen r a b ↔ a = b ∨ exists c, r a c ∧ ReflTransGen r c b
  proof: by
  use cases_head
  rintro (rfl | ⟨c, hac, hcb⟩)
  · rfl
  · exact head hac hcb

中文:
定理 cases_head_iff
  结论: ReflTransGen r a b ↔ a = b ∨ 存在 c, r a c ∧ ReflTransGen r c b
  证明: by
  use cases_head
  rintro (rfl | ⟨c, hac, hcb⟩)
  · rfl
  · exact head hac hcb

Depends on / 依赖: cases_head
-/
theorem cases_head_iff : ReflTransGen r a b ↔ a = b ∨ exists c, r a c ∧ ReflTransGen r c b := by
  use cases_head
  rintro (rfl | ⟨c, hac, hcb⟩)
  · rfl
  · exact head hac hcb

/--
theorem `total_of_right_unique` / 定理 `total_of_right_unique`

English:
theorem total_of_right_unique
  statement: (U : Relator.RightUnique r) (ab : ReflTransGen r a b)
  proof: by
  induction ab with
  | refl => exact Or.inl ac
  | tail _ bd IH =>
    rcases IH with (IH | IH)
    · rcases cases_head IH with (rfl | ⟨e, be, ec⟩)
      · exact Or.inr (single bd)
      · cases U bd be
        exact Or.inl ec
    · exact Or.inr (IH.tail bd)

中文:
定理 total_of_right_unique
  结论: (U : Relator.RightUnique r) (ab : ReflTransGen r a b)
  证明: by
  induction ab with
  | refl => exact Or.inl ac
  | tail _ bd IH =>
    rcases IH with (IH | IH)
    · rcases cases_head IH with (rfl | ⟨e, be, ec⟩)
      · exact Or.inr (single bd)
      · cases U bd be
        exact Or.inl ec
    · exact Or.inr (IH.tail bd)

Depends on / 依赖: IH.tail, Or.inl, Or.inr, cases_head, single
-/
theorem total_of_right_unique (U : Relator.RightUnique r) (ab : ReflTransGen r a b)
    (ac : ReflTransGen r a c) : ReflTransGen r b c ∨ ReflTransGen r c b := by
  induction ab with
  | refl => exact Or.inl ac
  | tail _ bd IH =>
    rcases IH with (IH | IH)
    · rcases cases_head IH with (rfl | ⟨e, be, ec⟩)
      · exact Or.inr (single bd)
      · cases U bd be
        exact Or.inl ec
    · exact Or.inr (IH.tail bd)

end ReflTransGen

/--
theorem `transGen_le_reflTransGen` / 定理 `transGen_le_reflTransGen`

English:
theorem transGen_le_reflTransGen
  statement: TransGen r <= ReflTransGen r
  proof: by
  intro a _ h
  induction h with
  | single h => exact ReflTransGen.single h
  | tail _ bc ab => exact ReflTransGen.tail ab bc

中文:
定理 transGen_le_reflTransGen
  结论: TransGen r <= ReflTransGen r
  证明: by
  intro a _ h
  induction h with
  | single h => exact ReflTransGen.single h
  | tail _ bc ab => exact ReflTransGen.tail ab bc

Depends on / 依赖: ReflTransGen, ReflTransGen.single, ReflTransGen.tail, single
-/
theorem transGen_le_reflTransGen : TransGen r <= ReflTransGen r := by
  intro a _ h
  induction h with
  | single h => exact ReflTransGen.single h
  | tail _ bc ab => exact ReflTransGen.tail ab bc

namespace TransGen

/--
theorem `to_reflTransGen` / 定理 `to_reflTransGen`

English:
theorem to_reflTransGen
  given: {a b}
  statement: TransGen r a b -> ReflTransGen r a b
  proof: transGen_le_reflTransGen a b

中文:
定理 to_reflTransGen
  条件: {a b}
  结论: TransGen r a b -> ReflTransGen r a b
  证明: transGen_le_reflTransGen a b

Depends on / 依赖: transGen_le_reflTransGen
-/
theorem to_reflTransGen {a b} : TransGen r a b -> ReflTransGen r a b :=
  transGen_le_reflTransGen a b

/--
theorem `trans_left` / 定理 `trans_left`

English:
theorem trans_left
  given: (hab : TransGen r a b) (hbc : ReflTransGen r b c)
  statement: TransGen r a c
  proof: by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

中文:
定理 trans_left
  条件: (hab : TransGen r a b) (hbc : ReflTransGen r b c)
  结论: TransGen r a c
  证明: by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

Depends on / 依赖: hac.tail
-/
theorem trans_left (hab : TransGen r a b) (hbc : ReflTransGen r b c) : TransGen r a c := by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

attribute [trans] trans

/--
theorem `head'` / 定理 `head'`

English:
theorem head'
  given: (hab : r a b) (hbc : ReflTransGen r b c)
  statement: TransGen r a c
  proof: trans_left (single hab) hbc

中文:
定理 head'
  条件: (hab : r a b) (hbc : ReflTransGen r b c)
  结论: TransGen r a c
  证明: trans_left (single hab) hbc

Depends on / 依赖: single, trans_left
-/
theorem head' (hab : r a b) (hbc : ReflTransGen r b c) : TransGen r a c :=
  trans_left (single hab) hbc

/--
theorem `tail'` / 定理 `tail'`

English:
theorem tail'
  given: (hab : ReflTransGen r a b) (hbc : r b c)
  statement: TransGen r a c
  proof: by
  induction hab generalizing c with
  | refl => exact single hbc
  | tail _ hdb IH => exact tail (IH hdb) hbc

中文:
定理 tail'
  条件: (hab : ReflTransGen r a b) (hbc : r b c)
  结论: TransGen r a c
  证明: by
  induction hab generalizing c with
  | refl => exact single hbc
  | tail _ hdb IH => exact tail (IH hdb) hbc

Depends on / 依赖: generalizing, single
-/
theorem tail' (hab : ReflTransGen r a b) (hbc : r b c) : TransGen r a c := by
  induction hab generalizing c with
  | refl => exact single hbc
  | tail _ hdb IH => exact tail (IH hdb) hbc

/--
theorem `head` / 定理 `head`

English:
theorem head
  given: (hab : r a b) (hbc : TransGen r b c)
  statement: TransGen r a c
  proof: head' hab hbc.to_reflTransGen

@[elab_as_elim]

中文:
定理 head
  条件: (hab : r a b) (hbc : TransGen r b c)
  结论: TransGen r a c
  证明: head' hab hbc.to_reflTransGen

@[elab_as_elim]

Depends on / 依赖: hbc.to_reflTransGen, to_reflTransGen
-/
theorem head (hab : r a b) (hbc : TransGen r b c) : TransGen r a c :=
  head' hab hbc.to_reflTransGen

@[elab_as_elim]
/--
theorem `head_induction_on` / 定理 `head_induction_on`

English:
theorem head_induction_on
  statement: {motive : forall a : α, TransGen r a b -> Prop} {a : α} (h : TransGen r a b)
  proof: by
  induction h with
  | single h => exact single h
  | @tail b c _ hbc h_ih =>
  apply h_ih
  · exact fun h => head h (.single hbc) (single hbc)
  · exact fun hab hbc => head hab _

@[elab_as_elim]

中文:
定理 head_induction_on
  结论: {motive : 对任意 a : α, TransGen r a b -> 命题} {a : α} (h : TransGen r a b)
  证明: by
  induction h with
  | single h => exact single h
  | @tail b c _ hbc h_ih =>
  apply h_ih
  · exact fun h => head h (.single hbc) (single hbc)
  · exact fun hab hbc => head hab _

@[elab_as_elim]

Depends on / 依赖: h_ih, single
-/
theorem head_induction_on {motive : forall a : α, TransGen r a b -> Prop} {a : α} (h : TransGen r a b)
    (single : forall {a} (h : r a b), motive a (single h))
    (head : forall {a c} (h' : r a c) (h : TransGen r c b), motive c h -> motive a (h.head h')) :
    motive a h := by
  induction h with
  | single h => exact single h
  | @tail b c _ hbc h_ih =>
  apply h_ih
  · exact fun h => head h (.single hbc) (single hbc)
  · exact fun hab hbc => head hab _

@[elab_as_elim]
/--
theorem `trans_induction_on` / 定理 `trans_induction_on`

English:
theorem trans_induction_on
  statement: {motive : forall {a b : α}, TransGen r a b -> Prop} {a b : α}
  proof: by
  induction h with
  | single h => exact single h
  | tail hab hbc h_ih => exact trans hab (.single hbc) h_ih (single hbc)

中文:
定理 trans_induction_on
  结论: {motive : 对任意 {a b : α}, TransGen r a b -> 命题} {a b : α}
  证明: by
  induction h with
  | single h => exact single h
  | tail hab hbc h_ih => exact trans hab (.single hbc) h_ih (single hbc)

Depends on / 依赖: h_ih, single
-/
theorem trans_induction_on {motive : forall {a b : α}, TransGen r a b -> Prop} {a b : α}
    (h : TransGen r a b) (single : forall {a b} (h : r a b), motive (single h))
    (trans : forall {a b c} (h₁ : TransGen r a b) (h₂ : TransGen r b c), motive h₁ -> motive h₂ ->
      motive (h₁.trans h₂)) :
    motive h := by
  induction h with
  | single h => exact single h
  | tail hab hbc h_ih => exact trans hab (.single hbc) h_ih (single hbc)

/--
theorem `trans_right` / 定理 `trans_right`

English:
theorem trans_right
  given: (hab : ReflTransGen r a b) (hbc : TransGen r b c)
  statement: TransGen r a c
  proof: by
  induction hbc with
  | single hbc => exact tail' hab hbc
  | tail _ hcd hac => exact hac.tail hcd

中文:
定理 trans_right
  条件: (hab : ReflTransGen r a b) (hbc : TransGen r b c)
  结论: TransGen r a c
  证明: by
  induction hbc with
  | single hbc => exact tail' hab hbc
  | tail _ hcd hac => exact hac.tail hcd

Depends on / 依赖: hac.tail, single
-/
theorem trans_right (hab : ReflTransGen r a b) (hbc : TransGen r b c) : TransGen r a c := by
  induction hbc with
  | single hbc => exact tail' hab hbc
  | tail _ hcd hac => exact hac.tail hcd

/--
theorem `tail'_iff` / 定理 `tail'_iff`

English:
theorem tail'_iff
  statement: TransGen r a c ↔ exists b, ReflTransGen r a b ∧ r b c
  proof: by
  refine ⟨fun h => ?_, fun ⟨b, hab, hbc⟩ => tail' hab hbc⟩
  cases h with
  | single hac => exact ⟨_, by rfl, hac⟩
  | tail hab hbc => exact ⟨_, hab.to_reflTransGen, hbc⟩

中文:
定理 tail'_iff
  结论: TransGen r a c ↔ 存在 b, ReflTransGen r a b ∧ r b c
  证明: by
  refine ⟨fun h => ?_, fun ⟨b, hab, hbc⟩ => tail' hab hbc⟩
  cases h with
  | single hac => exact ⟨_, by rfl, hac⟩
  | tail hab hbc => exact ⟨_, hab.to_reflTransGen, hbc⟩
-/
theorem tail'_iff : TransGen r a c ↔ exists b, ReflTransGen r a b ∧ r b c := by
  refine ⟨fun h => ?_, fun ⟨b, hab, hbc⟩ => tail' hab hbc⟩
  cases h with
  | single hac => exact ⟨_, by rfl, hac⟩
  | tail hab hbc => exact ⟨_, hab.to_reflTransGen, hbc⟩

/--
theorem `head'_iff` / 定理 `head'_iff`

English:
theorem head'_iff
  statement: TransGen r a c ↔ exists b, r a b ∧ ReflTransGen r b c
  proof: by
  refine ⟨fun h => ?_, fun ⟨b, hab, hbc⟩ => head' hab hbc⟩
  induction h with
  | single hac => exact ⟨_, hac, by rfl⟩
  | tail _ hbc IH =>
  rcases IH with ⟨d, had, hdb⟩
  exact ⟨_, had, hdb.tail hbc⟩

中文:
定理 head'_iff
  结论: TransGen r a c ↔ 存在 b, r a b ∧ ReflTransGen r b c
  证明: by
  refine ⟨fun h => ?_, fun ⟨b, hab, hbc⟩ => head' hab hbc⟩
  induction h with
  | single hac => exact ⟨_, hac, by rfl⟩
  | tail _ hbc IH =>
  rcases IH with ⟨d, had, hdb⟩
  exact ⟨_, had, hdb.tail hbc⟩
-/
theorem head'_iff : TransGen r a c ↔ exists b, r a b ∧ ReflTransGen r b c := by
  refine ⟨fun h => ?_, fun ⟨b, hab, hbc⟩ => head' hab hbc⟩
  induction h with
  | single hac => exact ⟨_, hac, by rfl⟩
  | tail _ hbc IH =>
  rcases IH with ⟨d, had, hdb⟩
  exact ⟨_, had, hdb.tail hbc⟩

/--
Instance `stdSymm` / 实例 `stdSymm`

English:
instance stdSymm
  signature: [Std.Symm r]
  body: by
    induction h with
| single i => exact .single symm i
    | tail _ h₁ h₂ => exact .head (symm h₁) h₂

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm

中文:
实例 stdSymm
  签名: [Std.Symm r]
  定义体: by
    induction h with
| single i => exact .single symm i
    | tail _ h₁ h₂ => exact .head (symm h₁) h₂

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm

Depends on / 依赖: single
-/
instance stdSymm [Std.Symm r] : Std.Symm (TransGen r) where
  symm x y h := by
    induction h with
| single i => exact .single symm i
    | tail _ h₁ h₂ => exact .head (symm h₁) h₂

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans α (TransGen r)
  body: TransGen.trans

中文:
实例 :
  签名: 是Trans α (TransGen r)
  定义体: TransGen.trans

Depends on / 依赖: TransGen, TransGen.trans
-/
instance : IsTrans α (TransGen r) where
  trans _ _ _ := TransGen.trans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] : IsPreorder α (TransGen r) where
  body: .single (refl x)

中文:
实例 [Std.Refl
  签名: r] : 是预序 α (TransGen r) where
  定义体: .single (refl x)

Depends on / 依赖: single
-/
instance [Std.Refl r] : IsPreorder α (TransGen r) where
  refl x := .single (refl x)

end TransGen

section reflGen

@[grind =]
/--
lemma `reflGen_eq_self` / 引理 `reflGen_eq_self`

English:
lemma reflGen_eq_self
  given: [Std.Refl r]
  statement: ReflGen r = r
  proof: by
  ext x y
  simpa only [reflGen_iff, or_iff_right_iff_imp] using fun h => h ▸ refl y

@[deprecated inferInstance (since := "2026-03-27")]

中文:
引理 reflGen_eq_self
  条件: [Std.Refl r]
  结论: ReflGen r = r
  证明: by
  ext x y
  simpa only [reflGen_iff, or_iff_right_iff_imp] using fun h => h ▸ refl y

@[deprecated inferInstance (since := "2026-03-27")]

Depends on / 依赖: or_iff_right_iff_imp, reflGen_iff
-/
lemma reflGen_eq_self [Std.Refl r] : ReflGen r = r := by
  ext x y
  simpa only [reflGen_iff, or_iff_right_iff_imp] using fun h => h ▸ refl y

@[deprecated inferInstance (since := "2026-03-27")]
/--
lemma `reflexive_reflGen` / 引理 `reflexive_reflGen`

English:
lemma reflexive_reflGen
  statement: Std.Refl (ReflGen r)
  proof: inferInstance

中文:
引理 reflexive_reflGen
  结论: Std.Refl (ReflGen r)
  证明: inferInstance
-/
lemma reflexive_reflGen : Std.Refl (ReflGen r) := inferInstance

/--
lemma `reflGen_minimal` / 引理 `reflGen_minimal`

English:
lemma reflGen_minimal
  given: {r' : α -> α -> Prop} [Std.Refl r'] (h : r <= r')
  statement: ReflGen r <= r'
  proof: by
  simpa [reflGen_eq_self] using ReflGen.mono h

中文:
引理 reflGen_minimal
  条件: {r' : α -> α -> 命题} [Std.Refl r'] (h : r <= r')
  结论: ReflGen r <= r'
  证明: by
  simpa [reflGen_eq_self] using ReflGen.mono h

Depends on / 依赖: ReflGen, ReflGen.mono, reflGen_eq_self
-/
lemma reflGen_minimal {r' : α -> α -> Prop} [Std.Refl r'] (h : r <= r') : ReflGen r <= r' := by
  simpa [reflGen_eq_self] using ReflGen.mono h

end reflGen

section SymmGen

/--
theorem `symmGen_swap` / 定理 `symmGen_swap`

English:
theorem symmGen_swap
  given: (r : α -> α -> Prop)
  statement: SymmGen (swap r) = SymmGen r
  proof: funext₂ fun _ _ => propext or_comm

中文:
定理 symmGen_swap
  条件: (r : α -> α -> 命题)
  结论: SymmGen (swap r) = SymmGen r
  证明: funext₂ fun _ _ => propext or_comm

Depends on / 依赖: or_comm, propext
-/
theorem symmGen_swap (r : α -> α -> Prop) : SymmGen (swap r) = SymmGen r :=
  funext₂ fun _ _ => propext or_comm

/--
theorem `symmGen_swap_apply` / 定理 `symmGen_swap_apply`

English:
theorem symmGen_swap_apply
  given: (r : α -> α -> Prop)
  statement: SymmGen (swap r) a b ↔ SymmGen r a b
  proof: or_comm

中文:
定理 symmGen_swap_apply
  条件: (r : α -> α -> 命题)
  结论: SymmGen (swap r) a b ↔ SymmGen r a b
  证明: or_comm

Depends on / 依赖: or_comm
-/
theorem symmGen_swap_apply (r : α -> α -> Prop) : SymmGen (swap r) a b ↔ SymmGen r a b :=
  or_comm

/--
theorem `symmGen_comm` / 定理 `symmGen_comm`

English:
theorem symmGen_comm
  given: {a b : α}
  statement: SymmGen r a b ↔ SymmGen r b a
  proof: or_comm

@[simp]

中文:
定理 symmGen_comm
  条件: {a b : α}
  结论: SymmGen r a b ↔ SymmGen r b a
  证明: or_comm

@[simp]

Depends on / 依赖: or_comm
-/
theorem symmGen_comm {a b : α} : SymmGen r a b ↔ SymmGen r b a :=
  or_comm

@[simp]
/--
theorem `symmGen_of_total` / 定理 `symmGen_of_total`

English:
theorem symmGen_of_total
  given: [Std.Total r] (a b : α)
  statement: SymmGen r a b
  proof: Std.Total.total a b

中文:
定理 symmGen_of_total
  条件: [Std.全 r] (a b : α)
  结论: SymmGen r a b
  证明: Std.Total.total a b

Depends on / 依赖: Std.Total.total
-/
theorem symmGen_of_total [Std.Total r] (a b : α) : SymmGen r a b :=
  Std.Total.total a b

end SymmGen

section TransGen

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (TransGen r) r (TransGen r)
  body: ⟨TransGen.tail⟩

中文:
实例 :
  签名: Trans (TransGen r) r (TransGen r)
  定义体: ⟨TransGen.tail⟩

Depends on / 依赖: TransGen, TransGen.tail
-/
instance : Trans (TransGen r) r (TransGen r) :=
  ⟨TransGen.tail⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans r (TransGen r) (TransGen r)
  body: ⟨TransGen.head⟩

中文:
实例 :
  签名: Trans r (TransGen r) (TransGen r)
  定义体: ⟨TransGen.head⟩

Depends on / 依赖: TransGen, TransGen.head
-/
instance : Trans r (TransGen r) (TransGen r) :=
  ⟨TransGen.head⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (TransGen r) (ReflTransGen r) (TransGen r)
  body: ⟨TransGen.trans_left⟩

中文:
实例 :
  签名: Trans (TransGen r) (ReflTransGen r) (TransGen r)
  定义体: ⟨TransGen.trans_left⟩

Depends on / 依赖: TransGen, TransGen.trans_left, trans_left
-/
instance : Trans (TransGen r) (ReflTransGen r) (TransGen r) :=
  ⟨TransGen.trans_left⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (ReflTransGen r) (TransGen r) (TransGen r)
  body: ⟨TransGen.trans_right⟩

@[grind =]

中文:
实例 :
  签名: Trans (ReflTransGen r) (TransGen r) (TransGen r)
  定义体: ⟨TransGen.trans_right⟩

@[grind =]

Depends on / 依赖: TransGen, TransGen.trans_right, trans_right
-/
instance : Trans (ReflTransGen r) (TransGen r) (TransGen r) :=
  ⟨TransGen.trans_right⟩

@[grind =]
/--
theorem `transGen_eq_self` / 定理 `transGen_eq_self`

English:
theorem transGen_eq_self
  given: [IsTrans α r]
  statement: TransGen r = r
  proof: funext₂ fun a b => propext
    ⟨fun h => by
      induction h with
      | single hc => exact hc
      | tail _ hcd hac => exact IsTrans.trans _ _ _ hac hcd, TransGen.single⟩

@[deprecated inferInstance (since := "2026-02-21")]

中文:
定理 transGen_eq_self
  条件: [是Trans α r]
  结论: TransGen r = r
  证明: funext₂ fun a b => propext
    ⟨fun h => by
      induction h with
      | single hc => exact hc
      | tail _ hcd hac => exact IsTrans.trans _ _ _ hac hcd, TransGen.single⟩

@[deprecated inferInstance (since := "2026-02-21")]

Depends on / 依赖: IsTrans, IsTrans.trans, TransGen, TransGen.single, propext, single
-/
theorem transGen_eq_self [IsTrans α r] : TransGen r = r :=
funext₂ fun a b => propext
    ⟨fun h => by
      induction h with
      | single hc => exact hc
      | tail _ hcd hac => exact IsTrans.trans _ _ _ hac hcd, TransGen.single⟩

@[deprecated inferInstance (since := "2026-02-21")]
/--
theorem `transitive_transGen` / 定理 `transitive_transGen`

English:
theorem transitive_transGen
  statement: IsTrans α (TransGen r)
  proof: inferInstance

@[deprecated transGen_eq_self (since := "2026-03-27"), grind =]

中文:
定理 transitive_transGen
  结论: 是Trans α (TransGen r)
  证明: inferInstance

@[deprecated transGen_eq_self (since := "2026-03-27"), grind =]
-/
theorem transitive_transGen : IsTrans α (TransGen r) := inferInstance

@[deprecated transGen_eq_self (since := "2026-03-27"), grind =]
/--
theorem `transGen_idem` / 定理 `transGen_idem`

English:
theorem transGen_idem
  statement: TransGen (TransGen r) = TransGen r
  proof: transGen_eq_self

中文:
定理 transGen_idem
  结论: TransGen (TransGen r) = TransGen r
  证明: transGen_eq_self

Depends on / 依赖: transGen_eq_self
-/
theorem transGen_idem : TransGen (TransGen r) = TransGen r :=
  transGen_eq_self

/--
theorem `TransGen.lift` / 定理 `TransGen.lift`

English:
theorem TransGen.lift
  given: {p : β -> β -> Prop} (f : α -> β) (h : r <= (p on f))
  proof: by
  intro a _ hab
  induction hab with
  | single hac => exact TransGen.single (h a _ hac)
  | tail _ hcd hac => exact TransGen.tail hac (h _ _ hcd)

中文:
定理 TransGen.lift
  条件: {p : β -> β -> 命题} (f : α -> β) (h : r <= (p on f))
  证明: by
  intro a _ hab
  induction hab with
  | single hac => exact TransGen.single (h a _ hac)
  | tail _ hcd hac => exact TransGen.tail hac (h _ _ hcd)

Depends on / 依赖: TransGen, TransGen.single, TransGen.tail, single
-/
theorem TransGen.lift {p : β -> β -> Prop} (f : α -> β) (h : r <= (p on f)) :
    TransGen r <= (TransGen p on f) := by
  intro a _ hab
  induction hab with
  | single hac => exact TransGen.single (h a _ hac)
  | tail _ hcd hac => exact TransGen.tail hac (h _ _ hcd)

/--
theorem `TransGen.lift'` / 定理 `TransGen.lift'`

English:
theorem TransGen.lift'
  given: {p : β -> β -> Prop} (f : α -> β) (h : r <= (TransGen p on f))
  proof: by
  intro _ _ hab
  simpa [transGen_eq_self] using hab.lift f h

中文:
定理 TransGen.lift'
  条件: {p : β -> β -> 命题} (f : α -> β) (h : r <= (TransGen p on f))
  证明: by
  intro _ _ hab
  simpa [transGen_eq_self] using hab.lift f h

Depends on / 依赖: hab.lift, transGen_eq_self
-/
theorem TransGen.lift' {p : β -> β -> Prop} (f : α -> β) (h : r <= (TransGen p on f)) :
    TransGen r <= (TransGen p on f) := by
  intro _ _ hab
  simpa [transGen_eq_self] using hab.lift f h

/--
theorem `TransGen.closed` / 定理 `TransGen.closed`

English:
theorem TransGen.closed
  given: {p : α -> α -> Prop}
  statement: r <= TransGen p -> TransGen r <= TransGen p
  proof: TransGen.lift' id

中文:
定理 TransGen.closed
  条件: {p : α -> α -> 命题}
  结论: r <= TransGen p -> TransGen r <= TransGen p
  证明: TransGen.lift' id

Depends on / 依赖: TransGen, TransGen.lift
-/
theorem TransGen.closed {p : α -> α -> Prop} : r <= TransGen p -> TransGen r <= TransGen p :=
  TransGen.lift' id

/--
lemma `TransGen.closed'` / 引理 `TransGen.closed'`

English:
lemma TransGen.closed'
  statement: {P : α -> Prop} (dc : forall {a b}, r a b -> P b -> P a)
  proof: h.head_induction_on dc fun hr _ hi => dc hr ∘ hi

中文:
引理 TransGen.closed'
  结论: {P : α -> 命题} (dc : 对任意 {a b}, r a b -> P b -> P a)
  证明: h.head_induction_on dc fun hr _ hi => dc hr ∘ hi

Depends on / 依赖: h.head_induction_on, head_induction_on
-/
lemma TransGen.closed' {P : α -> Prop} (dc : forall {a b}, r a b -> P b -> P a)
    {a b : α} (h : TransGen r a b) : P b -> P a :=
  h.head_induction_on dc fun hr _ hi => dc hr ∘ hi

/--
theorem `TransGen.mono` / 定理 `TransGen.mono`

English:
theorem TransGen.mono
  given: {p : α -> α -> Prop}
  statement: r <= p -> TransGen r <= TransGen p
  proof: TransGen.lift id

中文:
定理 TransGen.mono
  条件: {p : α -> α -> 命题}
  结论: r <= p -> TransGen r <= TransGen p
  证明: TransGen.lift id

Depends on / 依赖: TransGen, TransGen.lift
-/
theorem TransGen.mono {p : α -> α -> Prop} : r <= p -> TransGen r <= TransGen p :=
  TransGen.lift id

/--
lemma `transGen_minimal` / 引理 `transGen_minimal`

English:
lemma transGen_minimal
  given: {r' : α -> α -> Prop} [IsTrans α r'] (h : r <= r')
  statement: TransGen r <= r'
  proof: by
  simpa [transGen_eq_self] using TransGen.mono h

中文:
引理 transGen_minimal
  条件: {r' : α -> α -> 命题} [是Trans α r'] (h : r <= r')
  结论: TransGen r <= r'
  证明: by
  simpa [transGen_eq_self] using TransGen.mono h

Depends on / 依赖: TransGen, TransGen.mono, transGen_eq_self
-/
lemma transGen_minimal {r' : α -> α -> Prop} [IsTrans α r'] (h : r <= r') : TransGen r <= r' := by
  simpa [transGen_eq_self] using TransGen.mono h

/--
theorem `TransGen.swap` / 定理 `TransGen.swap`

English:
theorem TransGen.swap
  statement: swap (TransGen r) <= TransGen (swap r)
  proof: by
  intro _ _ h
  induction h with
  | single h => exact TransGen.single h
  | tail _ hbc ih => exact ih.head hbc

中文:
定理 TransGen.swap
  结论: swap (TransGen r) <= TransGen (swap r)
  证明: by
  intro _ _ h
  induction h with
  | single h => exact TransGen.single h
  | tail _ hbc ih => exact ih.head hbc

Depends on / 依赖: TransGen, TransGen.single, ih.head, single
-/
theorem TransGen.swap : swap (TransGen r) <= TransGen (swap r) := by
  intro _ _ h
  induction h with
  | single h => exact TransGen.single h
  | tail _ hbc ih => exact ih.head hbc

/--
theorem `transGen_swap` / 定理 `transGen_swap`

English:
theorem transGen_swap
  statement: TransGen (swap r) a b ↔ TransGen r b a
  proof: ⟨TransGen.swap b a, TransGen.swap a b⟩

中文:
定理 transGen_swap
  结论: TransGen (swap r) a b ↔ TransGen r b a
  证明: ⟨TransGen.swap b a, TransGen.swap a b⟩

Depends on / 依赖: TransGen, TransGen.swap
-/
theorem transGen_swap : TransGen (swap r) a b ↔ TransGen r b a :=
  ⟨TransGen.swap b a, TransGen.swap a b⟩

end TransGen

section ReflTransGen

open ReflTransGen

@[grind =]
/--
theorem `reflTransGen_iff_eq` / 定理 `reflTransGen_iff_eq`

English:
theorem reflTransGen_iff_eq
  given: (h : forall b, ¬r a b)
  statement: ReflTransGen r a b ↔ b = a
  proof: by
  rw [cases_head_iff]; simp [h, eq_comm]

@[grind =]

中文:
定理 reflTransGen_iff_eq
  条件: (h : 对任意 b, ¬r a b)
  结论: ReflTransGen r a b ↔ b = a
  证明: by
  rw [cases_head_iff]; simp [h, eq_comm]

@[grind =]

Depends on / 依赖: cases_head_iff, eq_comm
-/
theorem reflTransGen_iff_eq (h : forall b, ¬r a b) : ReflTransGen r a b ↔ b = a := by
  rw [cases_head_iff]; simp [h, eq_comm]

@[grind =]
/--
theorem `reflTransGen_iff_eq_or_transGen` / 定理 `reflTransGen_iff_eq_or_transGen`

English:
theorem reflTransGen_iff_eq_or_transGen
  statement: ReflTransGen r a b ↔ b = a ∨ TransGen r a b
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | refl => exact Or.inl rfl
    | tail hac hcb => exact Or.inr (TransGen.tail' hac hcb)
  · rcases h with (rfl | h)
    · rfl
    · exact h.to_reflTransGen

中文:
定理 reflTransGen_iff_eq_or_transGen
  结论: ReflTransGen r a b ↔ b = a ∨ TransGen r a b
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | refl => exact Or.inl rfl
    | tail hac hcb => exact Or.inr (TransGen.tail' hac hcb)
  · rcases h with (rfl | h)
    · rfl
    · exact h.to_reflTransGen

Depends on / 依赖: Or.inl, Or.inr, TransGen, TransGen.tail, h.to_reflTransGen, to_reflTransGen
-/
theorem reflTransGen_iff_eq_or_transGen : ReflTransGen r a b ↔ b = a ∨ TransGen r a b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | refl => exact Or.inl rfl
    | tail hac hcb => exact Or.inr (TransGen.tail' hac hcb)
  · rcases h with (rfl | h)
    · rfl
    · exact h.to_reflTransGen

/--
theorem `ReflTransGen.lift` / 定理 `ReflTransGen.lift`

English:
theorem ReflTransGen.lift
  given: {p : β -> β -> Prop} (f : α -> β) (h : r <= (p on f))
  proof: fun _ _ hab => trans_induction_on hab (fun _ => refl) (single ∘ h _ _) fun _ _ => trans

中文:
定理 ReflTransGen.lift
  条件: {p : β -> β -> 命题} (f : α -> β) (h : r <= (p on f))
  证明: fun _ _ hab => trans_induction_on hab (fun _ => refl) (single ∘ h _ _) fun _ _ => trans

Depends on / 依赖: single, trans_induction_on
-/
theorem ReflTransGen.lift {p : β -> β -> Prop} (f : α -> β) (h : r <= (p on f)) :
    ReflTransGen r <= (ReflTransGen p on f) :=
  fun _ _ hab => trans_induction_on hab (fun _ => refl) (single ∘ h _ _) fun _ _ => trans

/--
theorem `ReflTransGen.mono` / 定理 `ReflTransGen.mono`

English:
theorem ReflTransGen.mono
  given: {p : α -> α -> Prop}
  statement: r <= p -> ReflTransGen r <= ReflTransGen p
  proof: ReflTransGen.lift id

@[grind =]

中文:
定理 ReflTransGen.mono
  条件: {p : α -> α -> 命题}
  结论: r <= p -> ReflTransGen r <= ReflTransGen p
  证明: ReflTransGen.lift id

@[grind =]

Depends on / 依赖: ReflTransGen, ReflTransGen.lift
-/
theorem ReflTransGen.mono {p : α -> α -> Prop} : r <= p -> ReflTransGen r <= ReflTransGen p :=
  ReflTransGen.lift id

@[grind =]
/--
theorem `reflTransGen_eq_self` / 定理 `reflTransGen_eq_self`

English:
theorem reflTransGen_eq_self
  given: [Std.Refl r] [IsTrans α r]
  statement: ReflTransGen r = r
  proof: funext₂ fun a b => propext
    ⟨fun h => by
      induction h with
      | refl => exact refl a
      | tail _ h₂ IH => exact IsTrans.trans _ _ _ IH h₂, single⟩

中文:
定理 reflTransGen_eq_self
  条件: [Std.Refl r] [是Trans α r]
  结论: ReflTransGen r = r
  证明: funext₂ fun a b => propext
    ⟨fun h => by
      induction h with
      | refl => exact refl a
      | tail _ h₂ IH => exact IsTrans.trans _ _ _ IH h₂, single⟩

Depends on / 依赖: IsTrans, IsTrans.trans, propext, single
-/
theorem reflTransGen_eq_self [Std.Refl r] [IsTrans α r] : ReflTransGen r = r :=
  funext₂ fun a b => propext
    ⟨fun h => by
      induction h with
      | refl => exact refl a
      | tail _ h₂ IH => exact IsTrans.trans _ _ _ IH h₂, single⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans r (ReflTransGen r) (ReflTransGen r)
  body: ⟨head⟩

中文:
实例 :
  签名: Trans r (ReflTransGen r) (ReflTransGen r)
  定义体: ⟨head⟩
-/
instance : Trans r (ReflTransGen r) (ReflTransGen r) :=
  ⟨head⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans (ReflTransGen r) r (ReflTransGen r)
  body: ⟨tail⟩

中文:
实例 :
  签名: Trans (ReflTransGen r) r (ReflTransGen r)
  定义体: ⟨tail⟩
-/
instance : Trans (ReflTransGen r) r (ReflTransGen r) :=
  ⟨tail⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreorder α (ReflTransGen r)
  body: @ReflTransGen.refl α r
  trans := @ReflTransGen.trans α r

@[deprecated inferInstance (since := "2026-03-27")]

中文:
实例 :
  签名: 是预序 α (ReflTransGen r)
  定义体: @ReflTransGen.refl α r
  trans := @ReflTransGen.trans α r

@[deprecated inferInstance (since := "2026-03-27")]

Depends on / 依赖: ReflTransGen, ReflTransGen.refl
-/
instance : IsPreorder α (ReflTransGen r) where
  refl := @ReflTransGen.refl α r
  trans := @ReflTransGen.trans α r

@[deprecated inferInstance (since := "2026-03-27")]
/--
theorem `reflexive_reflTransGen` / 定理 `reflexive_reflTransGen`

English:
theorem reflexive_reflTransGen
  statement: Std.Refl (ReflTransGen r)
  proof: inferInstance

@[deprecated inferInstance (since := "2026-02-21")]

中文:
定理 reflexive_reflTransGen
  结论: Std.Refl (ReflTransGen r)
  证明: inferInstance

@[deprecated inferInstance (since := "2026-02-21")]
-/
theorem reflexive_reflTransGen : Std.Refl (ReflTransGen r) := inferInstance

@[deprecated inferInstance (since := "2026-02-21")]
/--
theorem `transitive_reflTransGen` / 定理 `transitive_reflTransGen`

English:
theorem transitive_reflTransGen
  statement: IsTrans α (ReflTransGen r)
  proof: inferInstance

@[deprecated reflTransGen_eq_self (since := "2026-03-27"), grind =]

中文:
定理 transitive_reflTransGen
  结论: 是Trans α (ReflTransGen r)
  证明: inferInstance

@[deprecated reflTransGen_eq_self (since := "2026-03-27"), grind =]
-/
theorem transitive_reflTransGen : IsTrans α (ReflTransGen r) := inferInstance

@[deprecated reflTransGen_eq_self (since := "2026-03-27"), grind =]
/--
theorem `reflTransGen_idem` / 定理 `reflTransGen_idem`

English:
theorem reflTransGen_idem
  statement: ReflTransGen (ReflTransGen r) = ReflTransGen r
  proof: reflTransGen_eq_self

中文:
定理 reflTransGen_idem
  结论: ReflTransGen (ReflTransGen r) = ReflTransGen r
  证明: reflTransGen_eq_self

Depends on / 依赖: reflTransGen_eq_self
-/
theorem reflTransGen_idem : ReflTransGen (ReflTransGen r) = ReflTransGen r :=
  reflTransGen_eq_self

/--
theorem `ReflTransGen.lift'` / 定理 `ReflTransGen.lift'`

English:
theorem ReflTransGen.lift'
  given: {p : β -> β -> Prop} (f : α -> β) (h : r <= (ReflTransGen p on f))
  proof: by
  intro _ _ hab
  simpa [reflTransGen_eq_self] using hab.lift f h

中文:
定理 ReflTransGen.lift'
  条件: {p : β -> β -> 命题} (f : α -> β) (h : r <= (ReflTransGen p on f))
  证明: by
  intro _ _ hab
  simpa [reflTransGen_eq_self] using hab.lift f h

Depends on / 依赖: hab.lift, reflTransGen_eq_self
-/
theorem ReflTransGen.lift' {p : β -> β -> Prop} (f : α -> β) (h : r <= (ReflTransGen p on f)) :
    ReflTransGen r <= (ReflTransGen p on f) := by
  intro _ _ hab
  simpa [reflTransGen_eq_self] using hab.lift f h

/--
theorem `reflTransGen_closed` / 定理 `reflTransGen_closed`

English:
theorem reflTransGen_closed
  given: {p : α -> α -> Prop}
  proof: ReflTransGen.lift' id

中文:
定理 reflTransGen_closed
  条件: {p : α -> α -> 命题}
  证明: ReflTransGen.lift' id

Depends on / 依赖: ReflTransGen, ReflTransGen.lift
-/
theorem reflTransGen_closed {p : α -> α -> Prop} :
    r <= ReflTransGen p -> ReflTransGen r <= ReflTransGen p :=
  ReflTransGen.lift' id

/--
theorem `ReflTransGen.swap` / 定理 `ReflTransGen.swap`

English:
theorem ReflTransGen.swap
  statement: swap (ReflTransGen r) <= ReflTransGen (swap r)
  proof: by
  intro _ _ h
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.head hbc

中文:
定理 ReflTransGen.swap
  结论: swap (ReflTransGen r) <= ReflTransGen (swap r)
  证明: by
  intro _ _ h
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.head hbc

Depends on / 依赖: ih.head
-/
theorem ReflTransGen.swap : swap (ReflTransGen r) <= ReflTransGen (swap r) := by
  intro _ _ h
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.head hbc

/--
theorem `reflTransGen_swap` / 定理 `reflTransGen_swap`

English:
theorem reflTransGen_swap
  statement: ReflTransGen (swap r) a b ↔ ReflTransGen r b a
  proof: ⟨ReflTransGen.swap b a, ReflTransGen.swap a b⟩

中文:
定理 reflTransGen_swap
  结论: ReflTransGen (swap r) a b ↔ ReflTransGen r b a
  证明: ⟨ReflTransGen.swap b a, ReflTransGen.swap a b⟩

Depends on / 依赖: ReflTransGen, ReflTransGen.swap
-/
theorem reflTransGen_swap : ReflTransGen (swap r) a b ↔ ReflTransGen r b a :=
  ⟨ReflTransGen.swap b a, ReflTransGen.swap a b⟩

/--
lemma `reflGen_transGen` / 引理 `reflGen_transGen`

English:
lemma reflGen_transGen
  statement: ReflGen (TransGen r) = ReflTransGen r
  proof: by
  ext x y
  simp_rw [reflTransGen_iff_eq_or_transGen, reflGen_iff]

中文:
引理 reflGen_transGen
  结论: ReflGen (TransGen r) = ReflTransGen r
  证明: by
  ext x y
  simp_rw [reflTransGen_iff_eq_or_transGen, reflGen_iff]
-/
@[simp, grind =] lemma reflGen_transGen : ReflGen (TransGen r) = ReflTransGen r := by
  ext x y
  simp_rw [reflTransGen_iff_eq_or_transGen, reflGen_iff]

/--
lemma `transGen_reflGen` / 引理 `transGen_reflGen`

English:
lemma transGen_reflGen
  statement: TransGen (ReflGen r) = ReflTransGen r
  proof: by
  ext x y
  refine ⟨fun h => ?_, fun h => ?_⟩
.to_reflTransGen · simpa [reflTransGen_eq_self] using h.mono reflGen_le_reflTransGen x y
  · obtain (rfl | h) := reflTransGen_iff_eq_or_transGen.mp h
    · exact .single .refl
    · exact h.mono (fun _ _ => .single) x y

中文:
引理 transGen_reflGen
  结论: TransGen (ReflGen r) = ReflTransGen r
  证明: by
  ext x y
  refine ⟨fun h => ?_, fun h => ?_⟩
.to_reflTransGen · simpa [reflTransGen_eq_self] using h.mono reflGen_le_reflTransGen x y
  · obtain (rfl | h) := reflTransGen_iff_eq_or_transGen.mp h
    · exact .single .refl
    · exact h.mono (fun _ _ => .single) x y
-/
@[simp, grind =] lemma transGen_reflGen : TransGen (ReflGen r) = ReflTransGen r := by
  ext x y
  refine ⟨fun h => ?_, fun h => ?_⟩
.to_reflTransGen · simpa [reflTransGen_eq_self] using h.mono reflGen_le_reflTransGen x y
  · obtain (rfl | h) := reflTransGen_iff_eq_or_transGen.mp h
    · exact .single .refl
    · exact h.mono (fun _ _ => .single) x y

/--
lemma `reflTransGen_reflGen` / 引理 `reflTransGen_reflGen`

English:
lemma reflTransGen_reflGen
  statement: ReflTransGen (ReflGen r) = ReflTransGen r
  proof: by
  simp only [← transGen_reflGen, reflGen_eq_self]

中文:
引理 reflTransGen_reflGen
  结论: ReflTransGen (ReflGen r) = ReflTransGen r
  证明: by
  simp only [← transGen_reflGen, reflGen_eq_self]
-/
@[simp, grind =] lemma reflTransGen_reflGen : ReflTransGen (ReflGen r) = ReflTransGen r := by
  simp only [← transGen_reflGen, reflGen_eq_self]

/--
lemma `reflTransGen_transGen` / 引理 `reflTransGen_transGen`

English:
lemma reflTransGen_transGen
  statement: ReflTransGen (TransGen r) = ReflTransGen r
  proof: by
  simp only [← reflGen_transGen, transGen_eq_self]

@[grind =]

中文:
引理 reflTransGen_transGen
  结论: ReflTransGen (TransGen r) = ReflTransGen r
  证明: by
  simp only [← reflGen_transGen, transGen_eq_self]

@[grind =]
-/
@[simp, grind =] lemma reflTransGen_transGen : ReflTransGen (TransGen r) = ReflTransGen r := by
  simp only [← reflGen_transGen, transGen_eq_self]

@[grind =]
/--
lemma `reflTransGen_eq_transGen` / 引理 `reflTransGen_eq_transGen`

English:
lemma reflTransGen_eq_transGen
  given: [Std.Refl r]
  statement: ReflTransGen r = TransGen r
  proof: by
  rw [← transGen_reflGen]; rw [reflGen_eq_self]

@[grind =]

中文:
引理 reflTransGen_eq_transGen
  条件: [Std.Refl r]
  结论: ReflTransGen r = TransGen r
  证明: by
  rw [← transGen_reflGen]; rw [reflGen_eq_self]

@[grind =]

Depends on / 依赖: reflGen_eq_self, transGen_reflGen
-/
lemma reflTransGen_eq_transGen [Std.Refl r] : ReflTransGen r = TransGen r := by
  rw [← transGen_reflGen]; rw [reflGen_eq_self]

@[grind =]
/--
lemma `reflTransGen_eq_reflGen` / 引理 `reflTransGen_eq_reflGen`

English:
lemma reflTransGen_eq_reflGen
  given: [IsTrans α r]
  statement: ReflTransGen r = ReflGen r
  proof: by
  rw [← reflGen_transGen]; rw [transGen_eq_self]

中文:
引理 reflTransGen_eq_reflGen
  条件: [是Trans α r]
  结论: ReflTransGen r = ReflGen r
  证明: by
  rw [← reflGen_transGen]; rw [transGen_eq_self]

Depends on / 依赖: reflGen_transGen, transGen_eq_self
-/
lemma reflTransGen_eq_reflGen [IsTrans α r] : ReflTransGen r = ReflGen r := by
  rw [← reflGen_transGen]; rw [transGen_eq_self]

end ReflTransGen

namespace EqvGen

variable (r)

/--
theorem `is_equivalence` / 定理 `is_equivalence`

English:
theorem is_equivalence
  statement: Equivalence (@EqvGen α r)
  proof: Equivalence.mk EqvGen.refl (EqvGen.symm _ _) (EqvGen.trans _ _ _)

.isEquiv instance : IsEquiv α (EqvGen r) := is_equivalence _

中文:
定理 is_equivalence
  结论: 等价 (@EqvGen α r)
  证明: Equivalence.mk EqvGen.refl (EqvGen.symm _ _) (EqvGen.trans _ _ _)

.isEquiv instance : IsEquiv α (EqvGen r) := is_equivalence _

Depends on / 依赖: Equivalence, Equivalence.mk, EqvGen, EqvGen.refl, EqvGen.symm, EqvGen.trans
-/
theorem is_equivalence : Equivalence (@EqvGen α r) :=
  Equivalence.mk EqvGen.refl (EqvGen.symm _ _) (EqvGen.trans _ _ _)

.isEquiv instance : IsEquiv α (EqvGen r) := is_equivalence _

/-- `EqvGen.setoid r` is the setoid generated by a relation `r`.

The motivation for this definition is that `Quot r` behaves like `Quotient (EqvGen.setoid r)`,
see for example `Quot.eqvGen_exact` and `Quot.eqvGen_sound`. -/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: : Setoid α
  body: Setoid.mk _ (EqvGen.is_equivalence r)

中文:
定义 setoid
  签名: : 集合等价关系 α
  定义体: Setoid.mk _ (EqvGen.is_equivalence r)

Depends on / 依赖: EqvGen, EqvGen.is_equivalence, Setoid, Setoid.mk, is_equivalence
-/
def setoid : Setoid α :=
  Setoid.mk _ (EqvGen.is_equivalence r)

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {r p : α -> α -> Prop} (hrp : r <= p)
  statement: EqvGen r <= EqvGen p
  proof: by
  intro _ _ h
  induction h with
  | rel a b h => exact EqvGen.rel _ _ (hrp _ _ h)
  | refl => exact EqvGen.refl _
  | symm a b _ ih => exact EqvGen.symm _ _ ih
  | trans a b c _ _ hab hbc => exact EqvGen.trans _ _ _ hab hbc

中文:
定理 mono
  条件: {r p : α -> α -> 命题} (hrp : r <= p)
  结论: EqvGen r <= EqvGen p
  证明: by
  intro _ _ h
  induction h with
  | rel a b h => exact EqvGen.rel _ _ (hrp _ _ h)
  | refl => exact EqvGen.refl _
  | symm a b _ ih => exact EqvGen.symm _ _ ih
  | trans a b c _ _ hab hbc => exact EqvGen.trans _ _ _ hab hbc

Depends on / 依赖: EqvGen, EqvGen.refl, EqvGen.rel, EqvGen.symm, EqvGen.trans
-/
theorem mono {r p : α -> α -> Prop} (hrp : r <= p) : EqvGen r <= EqvGen p := by
  intro _ _ h
  induction h with
  | rel a b h => exact EqvGen.rel _ _ (hrp _ _ h)
  | refl => exact EqvGen.refl _
  | symm a b _ ih => exact EqvGen.symm _ _ ih
  | trans a b c _ _ hab hbc => exact EqvGen.trans _ _ _ hab hbc

/--
lemma `eqvGen_le` / 引理 `eqvGen_le`

English:
lemma eqvGen_le
  given: {r r' : α -> α -> Prop} [IsEquiv α r'] (h : r <= r')
  statement: EqvGen r <= r'

中文:
引理 eqvGen_le
  条件: {r r' : α -> α -> 命题} [Is等价 α r'] (h : r <= r')
  结论: EqvGen r <= r'
-/
lemma eqvGen_le {r r' : α -> α -> Prop} [IsEquiv α r'] (h : r <= r') : EqvGen r <= r'
  | _, _, .refl _ => _root_.refl _
  | _, _, .symm _ _ hxy => _root_.symm (eqvGen_le h _ _ hxy)
  | _, _, .trans _ _ _ hxy hyz => _root_.trans (eqvGen_le h _ _ hxy) (eqvGen_le h _ _ hyz)
  | _, _, .rel _ _ hab => h _ _ hab

/--
lemma `eqvGen_mono` / 引理 `eqvGen_mono`

English:
lemma eqvGen_mono
  given: {r r' : α -> α -> Prop} (h : r <= r')
  statement: EqvGen r <= EqvGen r'

中文:
引理 eqvGen_mono
  条件: {r r' : α -> α -> 命题} (h : r <= r')
  结论: EqvGen r <= EqvGen r'
-/
lemma eqvGen_mono {r r' : α -> α -> Prop} (h : r <= r') : EqvGen r <= EqvGen r'
  | _, _, .refl _ => .refl _
  | _, _, .symm _ _ hxy => .symm _ _ (eqvGen_mono h _ _ hxy)
  | _, _, .trans _ _ _ hxy hyz => .trans _ _ _ (eqvGen_mono h _ _ hxy) (eqvGen_mono h _ _ hyz)
  | _, _, .rel _ _ hab => .rel _ _ (h _ _ hab)

/--
lemma `reflGen_le_eqvGen` / 引理 `reflGen_le_eqvGen`

English:
lemma reflGen_le_eqvGen
  statement: ReflGen r <= EqvGen r

中文:
引理 reflGen_le_eqvGen
  结论: ReflGen r <= EqvGen r
-/
lemma reflGen_le_eqvGen : ReflGen r <= EqvGen r
  | _, _, .refl => .refl _
  | _, _, .single h => .rel _ _ h

/--
lemma `symmGen_le_eqvGen` / 引理 `symmGen_le_eqvGen`

English:
lemma symmGen_le_eqvGen
  statement: SymmGen r <= EqvGen r

中文:
引理 symmGen_le_eqvGen
  结论: SymmGen r <= EqvGen r
-/
lemma symmGen_le_eqvGen : SymmGen r <= EqvGen r
  | _, _, .inl h => .rel _ _ h
| _, _, .inr h => _root_.symm .rel _ _ h

/--
lemma `transGen_le_eqvGen` / 引理 `transGen_le_eqvGen`

English:
lemma transGen_le_eqvGen
  statement: TransGen r <= EqvGen r
  proof: by
  intro _ _ h
  induction h using TransGen.trans_induction_on with
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h

中文:
引理 transGen_le_eqvGen
  结论: TransGen r <= EqvGen r
  证明: by
  intro _ _ h
  induction h using TransGen.trans_induction_on with
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h

Depends on / 依赖: TransGen, TransGen.trans_induction_on, _root_, _root_.trans, single, trans_induction_on
-/
lemma transGen_le_eqvGen : TransGen r <= EqvGen r := by
  intro _ _ h
  induction h using TransGen.trans_induction_on with
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h

/--
lemma `reflTransGen_le_eqvGen` / 引理 `reflTransGen_le_eqvGen`

English:
lemma reflTransGen_le_eqvGen
  statement: ReflTransGen r <= EqvGen r
  proof: by
  intro _ _ h
  induction h using ReflTransGen.trans_induction_on with
  | refl => exact .refl _
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h

@[simp, grind =]

中文:
引理 reflTransGen_le_eqvGen
  结论: ReflTransGen r <= EqvGen r
  证明: by
  intro _ _ h
  induction h using ReflTransGen.trans_induction_on with
  | refl => exact .refl _
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h

@[simp, grind =]

Depends on / 依赖: ReflTransGen, ReflTransGen.trans_induction_on, _root_, _root_.trans, single, trans_induction_on
-/
lemma reflTransGen_le_eqvGen : ReflTransGen r <= EqvGen r := by
  intro _ _ h
  induction h using ReflTransGen.trans_induction_on with
  | refl => exact .refl _
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h

@[simp, grind =]
/--
lemma `eqvGen_reflGen` / 引理 `eqvGen_reflGen`

English:
lemma eqvGen_reflGen
  statement: EqvGen (ReflGen r) = EqvGen r
  proof: Subrelation.antisymm
    (eqvGen_le (reflGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]

中文:
引理 eqvGen_reflGen
  结论: EqvGen (ReflGen r) = EqvGen r
  证明: Subrelation.antisymm
    (eqvGen_le (reflGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]

Depends on / 依赖: Subrelation, Subrelation.antisymm, antisymm, eqvGen_le, eqvGen_mono, reflGen_le_eqvGen, single
-/
lemma eqvGen_reflGen : EqvGen (ReflGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (reflGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]
/--
lemma `eqvGen_transGen` / 引理 `eqvGen_transGen`

English:
lemma eqvGen_transGen
  statement: EqvGen (TransGen r) = EqvGen r
  proof: Subrelation.antisymm
    (eqvGen_le (transGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]

中文:
引理 eqvGen_transGen
  结论: EqvGen (TransGen r) = EqvGen r
  证明: Subrelation.antisymm
    (eqvGen_le (transGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]

Depends on / 依赖: Subrelation, Subrelation.antisymm, antisymm, eqvGen_le, eqvGen_mono, single, transGen_le_eqvGen
-/
lemma eqvGen_transGen : EqvGen (TransGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (transGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]
/--
lemma `eqvGen_symmGen` / 引理 `eqvGen_symmGen`

English:
lemma eqvGen_symmGen
  statement: EqvGen (SymmGen r) = EqvGen r
  proof: Subrelation.antisymm
    (eqvGen_le (symmGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .inl)

@[simp, grind =]

中文:
引理 eqvGen_symmGen
  结论: EqvGen (SymmGen r) = EqvGen r
  证明: Subrelation.antisymm
    (eqvGen_le (symmGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .inl)

@[simp, grind =]

Depends on / 依赖: Subrelation, Subrelation.antisymm, antisymm, eqvGen_le, eqvGen_mono, symmGen_le_eqvGen
-/
lemma eqvGen_symmGen : EqvGen (SymmGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (symmGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .inl)

@[simp, grind =]
/--
lemma `eqvGen_reflTransGen` / 引理 `eqvGen_reflTransGen`

English:
lemma eqvGen_reflTransGen
  statement: EqvGen (ReflTransGen r) = EqvGen r
  proof: Subrelation.antisymm
    (eqvGen_le (reflTransGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[grind =]

中文:
引理 eqvGen_reflTransGen
  结论: EqvGen (ReflTransGen r) = EqvGen r
  证明: Subrelation.antisymm
    (eqvGen_le (reflTransGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[grind =]

Depends on / 依赖: Subrelation, Subrelation.antisymm, antisymm, eqvGen_le, eqvGen_mono, reflTransGen_le_eqvGen, single
-/
lemma eqvGen_reflTransGen : EqvGen (ReflTransGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (reflTransGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[grind =]
/--
lemma `eqvGen_eq_reflTransGen` / 引理 `eqvGen_eq_reflTransGen`

English:
lemma eqvGen_eq_reflTransGen
  given: [Std.Symm r]
  statement: EqvGen r = ReflTransGen r
  proof: have : IsEquiv α (ReflTransGen r) := ⟨⟩
  Subrelation.antisymm (eqvGen_le fun _ _ => .single) (reflTransGen_le_eqvGen _)

中文:
引理 eqvGen_eq_reflTransGen
  条件: [Std.Symm r]
  结论: EqvGen r = ReflTransGen r
  证明: have : IsEquiv α (ReflTransGen r) := ⟨⟩
  Subrelation.antisymm (eqvGen_le fun _ _ => .single) (reflTransGen_le_eqvGen _)

Depends on / 依赖: IsEquiv, ReflTransGen, Subrelation, Subrelation.antisymm, antisymm, eqvGen_le, reflTransGen_le_eqvGen, single
-/
lemma eqvGen_eq_reflTransGen [Std.Symm r] : EqvGen r = ReflTransGen r :=
  have : IsEquiv α (ReflTransGen r) := ⟨⟩
  Subrelation.antisymm (eqvGen_le fun _ _ => .single) (reflTransGen_le_eqvGen _)

/--
lemma `reflTransGen_symmGen` / 引理 `reflTransGen_symmGen`

English:
lemma reflTransGen_symmGen
  statement: ReflTransGen (SymmGen r) = EqvGen r
  proof: by
  rw [← eqvGen_eq_reflTransGen]; rw [eqvGen_symmGen]

中文:
引理 reflTransGen_symmGen
  结论: ReflTransGen (SymmGen r) = EqvGen r
  证明: by
  rw [← eqvGen_eq_reflTransGen]; rw [eqvGen_symmGen]

Depends on / 依赖: eqvGen_eq_reflTransGen, eqvGen_symmGen
-/
lemma reflTransGen_symmGen : ReflTransGen (SymmGen r) = EqvGen r := by
  rw [← eqvGen_eq_reflTransGen]; rw [eqvGen_symmGen]

end EqvGen

/--
Definition of `Join` / `Join` 的定义

English:
definition Join
  signature: (r : α -> α -> Prop)
  body: fun a b => exists c, r a c ∧ r b c

中文:
定义 并
  签名: (r : α -> α -> 命题)
  定义体: fun a b => exists c, r a c ∧ r b c
-/
def Join (r : α -> α -> Prop) : α -> α -> Prop := fun a b => exists c, r a c ∧ r b c

section Join

open ReflTransGen ReflGen

/--
theorem `church_rosser` / 定理 `church_rosser`

English:
theorem church_rosser
  statement: (h : forall a b c, r a b -> r a c -> exists d, ReflGen r b d ∧ ReflTransGen r c d)
  proof: by
  induction hab with
  | refl => exact ⟨c, hac, refl⟩
  | @tail d e _ hde ih =>
    rcases ih with ⟨b, hdb, hcb⟩
    have : exists a, ReflTransGen r e a ∧ ReflGen r b a := by
      clear hcb
      induction hdb with
      | refl => exact ⟨e, refl, ReflGen.single hde⟩
      | @tail f b _ hfb ih =>

中文:
定理 church_rosser
  结论: (h : 对任意 a b c, r a b -> r a c -> 存在 d, ReflGen r b d ∧ ReflTransGen r c d)
  证明: by
  induction hab with
  | refl => exact ⟨c, hac, refl⟩
  | @tail d e _ hde ih =>
    rcases ih with ⟨b, hdb, hcb⟩
    have : exists a, ReflTransGen r e a ∧ ReflGen r b a := by
      clear hcb
      induction hdb with
      | refl => exact ⟨e, refl, ReflGen.single hde⟩
      | @tail f b _ hfb ih =>

Depends on / 依赖: ReflGen, ReflGen.refl, ReflGen.single, ReflTransGen, hea.tail, hea.trans, single
-/
theorem church_rosser (h : forall a b c, r a b -> r a c -> exists d, ReflGen r b d ∧ ReflTransGen r c d)
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : Join (ReflTransGen r) b c := by
  induction hab with
  | refl => exact ⟨c, hac, refl⟩
  | @tail d e _ hde ih =>
    rcases ih with ⟨b, hdb, hcb⟩
    have : exists a, ReflTransGen r e a ∧ ReflGen r b a := by
      clear hcb
      induction hdb with
      | refl => exact ⟨e, refl, ReflGen.single hde⟩
      | @tail f b _ hfb ih =>
        rcases ih with ⟨a, hea, hfa⟩
        cases hfa with
        | refl => exact ⟨b, hea.tail hfb, ReflGen.refl⟩
        | single hfa =>
          rcases h _ _ _ hfb hfa with ⟨c, hbc, hac⟩
          exact ⟨c, hea.trans hac, hbc⟩
    rcases this with ⟨a, hea, hba⟩
    cases hba with
    | refl => exact ⟨b, hea, hcb⟩
    | single hba => exact ⟨a, hea, hcb.tail hba⟩

/--
theorem `le_join_of_refl` / 定理 `le_join_of_refl`

English:
theorem le_join_of_refl
  given: [Std.Refl r]
  statement: r <= Join r
  proof: fun _ b hab => ⟨b, hab, refl b⟩

@[deprecated (since := "2026-06-30")] alias join_of_single := le_join_of_refl

中文:
定理 le_join_of_refl
  条件: [Std.Refl r]
  结论: r <= 并 r
  证明: fun _ b hab => ⟨b, hab, refl b⟩

@[deprecated (since := "2026-06-30")] alias join_of_single := le_join_of_refl
-/
theorem le_join_of_refl [Std.Refl r] : r <= Join r :=
  fun _ b hab => ⟨b, hab, refl b⟩

@[deprecated (since := "2026-06-30")] alias join_of_single := le_join_of_refl

/--
Instance `Join.symm` / 实例 `Join.symm`

English:
instance Join.symm
  signature: : Std.Symm (Join r) where
  body: fun ⟨c, hac, hcb⟩ => ⟨c, hcb, hac⟩

@[deprecated (since := "2026-06-10")] alias symmetric_join := Join.symm

中文:
实例 并.symm
  签名: : Std.Symm (并 r) where
  定义体: fun ⟨c, hac, hcb⟩ => ⟨c, hcb, hac⟩

@[deprecated (since := "2026-06-10")] alias symmetric_join := Join.symm
-/
protected instance Join.symm : Std.Symm (Join r) where
  symm _ _ := fun ⟨c, hac, hcb⟩ => ⟨c, hcb, hac⟩

@[deprecated (since := "2026-06-10")] alias symmetric_join := Join.symm

/--
Instance `Join.refl` / 实例 `Join.refl`

English:
instance Join.refl
  signature: [Std.Refl r]
  body: ⟨a, _root_.refl a, _root_.refl a⟩

@[deprecated (since := "2026-06-10")] alias reflexive_join := Join.refl

中文:
实例 并.refl
  签名: [Std.Refl r]
  定义体: ⟨a, _root_.refl a, _root_.refl a⟩

@[deprecated (since := "2026-06-10")] alias reflexive_join := Join.refl
-/
protected instance Join.refl [Std.Refl r] : Std.Refl (Join r) where
  refl a := ⟨a, _root_.refl a, _root_.refl a⟩

@[deprecated (since := "2026-06-10")] alias reflexive_join := Join.refl

/--
theorem `isTrans_join` / 定理 `isTrans_join`

English:
theorem isTrans_join
  given: [IsTrans α r] (h : forall a b c, r a b -> r a c -> Join r b c)
  proof: ⟨fun _a b _c ⟨x, hax, hbx⟩ ⟨y, hby, hcy⟩ =>
  let ⟨z, hxz, hyz⟩ := h b x y hbx hby
  ⟨z, trans_of r hax hxz, trans_of r hcy hyz⟩⟩

@[deprecated (since := "2026-02-21")] alias transitive_join := isTrans_join

中文:
定理 isTrans_join
  条件: [是Trans α r] (h : 对任意 a b c, r a b -> r a c -> 并 r b c)
  证明: ⟨fun _a b _c ⟨x, hax, hbx⟩ ⟨y, hby, hcy⟩ =>
  let ⟨z, hxz, hyz⟩ := h b x y hbx hby
  ⟨z, trans_of r hax hxz, trans_of r hcy hyz⟩⟩

@[deprecated (since := "2026-02-21")] alias transitive_join := isTrans_join

Depends on / 依赖: trans_of
-/
theorem isTrans_join [IsTrans α r] (h : forall a b c, r a b -> r a c -> Join r b c) :
    IsTrans α (Join r) :=
  ⟨fun _a b _c ⟨x, hax, hbx⟩ ⟨y, hby, hcy⟩ =>
  let ⟨z, hxz, hyz⟩ := h b x y hbx hby
  ⟨z, trans_of r hax hxz, trans_of r hcy hyz⟩⟩

@[deprecated (since := "2026-02-21")] alias transitive_join := isTrans_join

/--
theorem `equivalence_join` / 定理 `equivalence_join`

English:
theorem equivalence_join
  given: [IsPreorder α r] (h : forall a b c, r a b -> r a c -> Join r b c)
  proof: .trans _ _ _⟩ ⟨Join.refl.refl, Join.symm.symm _ _, isTrans_join h

中文:
定理 equivalence_join
  条件: [是预序 α r] (h : 对任意 a b c, r a b -> r a c -> 并 r b c)
  证明: .trans _ _ _⟩ ⟨Join.refl.refl, Join.symm.symm _ _, isTrans_join h

Depends on / 依赖: Join.refl.refl, Join.symm.symm, isTrans_join
-/
theorem equivalence_join [IsPreorder α r] (h : forall a b c, r a b -> r a c -> Join r b c) :
    Equivalence (Join r) :=
.trans _ _ _⟩ ⟨Join.refl.refl, Join.symm.symm _ _, isTrans_join h

/--
theorem `equivalence_join_reflTransGen` / 定理 `equivalence_join_reflTransGen`

English:
theorem equivalence_join_reflTransGen
  proof: equivalence_join fun _ _ _ => church_rosser h

中文:
定理 equivalence_join_reflTransGen
  证明: equivalence_join fun _ _ _ => church_rosser h

Depends on / 依赖: church_rosser, equivalence_join
-/
theorem equivalence_join_reflTransGen
    (h : forall a b c, r a b -> r a c -> exists d, ReflGen r b d ∧ ReflTransGen r c d) :
    Equivalence (Join (ReflTransGen r)) :=
  equivalence_join fun _ _ _ => church_rosser h

/--
theorem `join_le_of_equivalence_of_le` / 定理 `join_le_of_equivalence_of_le`

English:
theorem join_le_of_equivalence_of_le
  given: {r' : α -> α -> Prop} (hr : Equivalence r) (h : r' <= r)
  proof: fun a b ⟨c, hac, hbc⟩ => hr.trans (h a c hac) (hr.symm <| h b c hbc)

@[deprecated (since := "2026-06-30")] alias join_of_equivalence := join_le_of_equivalence_of_le

中文:
定理 join_le_of_equivalence_of_le
  条件: {r' : α -> α -> 命题} (hr : 等价 r) (h : r' <= r)
  证明: fun a b ⟨c, hac, hbc⟩ => hr.trans (h a c hac) (hr.symm <| h b c hbc)

@[deprecated (since := "2026-06-30")] alias join_of_equivalence := join_le_of_equivalence_of_le

Depends on / 依赖: hr.symm, hr.trans
-/
theorem join_le_of_equivalence_of_le {r' : α -> α -> Prop} (hr : Equivalence r) (h : r' <= r) :
    Join r' <= r :=
  fun a b ⟨c, hac, hbc⟩ => hr.trans (h a c hac) (hr.symm <| h b c hbc)

@[deprecated (since := "2026-06-30")] alias join_of_equivalence := join_le_of_equivalence_of_le

/--
theorem `reflTransGen_le_of_le` / 定理 `reflTransGen_le_of_le`

English:
theorem reflTransGen_le_of_le
  statement: {r' : α -> α -> Prop} [Std.Refl r] [IsTrans α r]
  proof: by
  simpa [reflTransGen_eq_self] using ReflTransGen.mono h

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_isTrans_reflexive := reflTransGen_le_of_le

@[deprecated (since := "2026-02-21")]
alias reflTransGen_of_transitive_reflexive := reflTransGen_le_of_le

中文:
定理 reflTransGen_le_of_le
  结论: {r' : α -> α -> 命题} [Std.Refl r] [是Trans α r]
  证明: by
  simpa [reflTransGen_eq_self] using ReflTransGen.mono h

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_isTrans_reflexive := reflTransGen_le_of_le

@[deprecated (since := "2026-02-21")]
alias reflTransGen_of_transitive_reflexive := reflTransGen_le_of_le

Depends on / 依赖: ReflTransGen, ReflTransGen.mono, reflTransGen_eq_self
-/
theorem reflTransGen_le_of_le {r' : α -> α -> Prop} [Std.Refl r] [IsTrans α r]
    (h : r' <= r) : ReflTransGen r' <= r := by
  simpa [reflTransGen_eq_self] using ReflTransGen.mono h

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_isTrans_reflexive := reflTransGen_le_of_le

@[deprecated (since := "2026-02-21")]
alias reflTransGen_of_transitive_reflexive := reflTransGen_le_of_le

/--
theorem `reflTransGen_le_of_equivalence_of_le` / 定理 `reflTransGen_le_of_equivalence_of_le`

English:
theorem reflTransGen_le_of_equivalence_of_le
  given: {r' : α -> α -> Prop} (hr : Equivalence r)
  proof: @reflTransGen_le_of_le _ _ _ hr.stdRefl hr.isTrans

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_equivalence := reflTransGen_le_of_equivalence_of_le

中文:
定理 reflTransGen_le_of_equivalence_of_le
  条件: {r' : α -> α -> 命题} (hr : 等价 r)
  证明: @reflTransGen_le_of_le _ _ _ hr.stdRefl hr.isTrans

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_equivalence := reflTransGen_le_of_equivalence_of_le

Depends on / 依赖: hr.isTrans, hr.stdRefl, isTrans, reflTransGen_le_of_le, stdRefl
-/
theorem reflTransGen_le_of_equivalence_of_le {r' : α -> α -> Prop} (hr : Equivalence r) :
    r' <= r -> ReflTransGen r' <= r :=
  @reflTransGen_le_of_le _ _ _ hr.stdRefl hr.isTrans

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_equivalence := reflTransGen_le_of_equivalence_of_le

end Join

end Relation

section EqvGen

open Relation

variable {r : α -> α -> Prop} {a b : α}

/--
theorem `Quot.eqvGen_exact` / 定理 `Quot.eqvGen_exact`

English:
theorem Quot.eqvGen_exact
  given: (H : Quot.mk r a = Quot.mk r b)
  statement: EqvGen r a b
  proof: @Quotient.exact _ (EqvGen.setoid r) a b (congrArg
    (Quot.lift (Quotient.mk (EqvGen.setoid r)) (fun x y h => Quot.sound (EqvGen.rel x y h))) H)

中文:
定理 商.eqvGen_exact
  条件: (H : 商.mk r a = 商.mk r b)
  结论: EqvGen r a b
  证明: @Quotient.exact _ (EqvGen.setoid r) a b (congrArg
    (Quot.lift (Quotient.mk (EqvGen.setoid r)) (fun x y h => Quot.sound (EqvGen.rel x y h))) H)

Depends on / 依赖: EqvGen, EqvGen.rel, EqvGen.setoid, Quot.lift, Quot.sound, Quotient, Quotient.exact, Quotient.mk, setoid
-/
theorem Quot.eqvGen_exact (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotient.exact _ (EqvGen.setoid r) a b (congrArg
    (Quot.lift (Quotient.mk (EqvGen.setoid r)) (fun x y h => Quot.sound (EqvGen.rel x y h))) H)

/--
theorem `Quot.eqvGen_sound` / 定理 `Quot.eqvGen_sound`

English:
theorem Quot.eqvGen_sound
  given: (H : EqvGen r a b)
  statement: Quot.mk r a = Quot.mk r b
  proof: EqvGen.rec
    (fun _ _ h => Quot.sound h)
    (fun _ => rfl)
    (fun _ _ _ IH => Eq.symm IH)
    (fun _ _ _ _ _ IH₁ IH₂ => Eq.trans IH₁ IH₂)
    H

中文:
定理 商.eqvGen_sound
  条件: (H : EqvGen r a b)
  结论: 商.mk r a = 商.mk r b
  证明: EqvGen.rec
    (fun _ _ h => Quot.sound h)
    (fun _ => rfl)
    (fun _ _ _ IH => Eq.symm IH)
    (fun _ _ _ _ _ IH₁ IH₂ => Eq.trans IH₁ IH₂)
    H

Depends on / 依赖: Eq.symm, Eq.trans, EqvGen, EqvGen.rec, Quot.sound
-/
theorem Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = Quot.mk r b :=
  EqvGen.rec
    (fun _ _ h => Quot.sound h)
    (fun _ => rfl)
    (fun _ _ _ IH => Eq.symm IH)
    (fun _ _ _ _ _ IH₁ IH₂ => Eq.trans IH₁ IH₂)
    H

/--
theorem `Equivalence.eqvGen_iff` / 定理 `Equivalence.eqvGen_iff`

English:
theorem Equivalence.eqvGen_iff
  given: (h : Equivalence r)
  statement: EqvGen r a b ↔ r a b
  proof: Iff.intro
    (by
      intro h
      induction h with
      | rel => assumption
      | refl => exact h.1 _
      | symm => apply h.symm; assumption
      | trans _ _ _ _ _ hab hbc => exact h.trans hab hbc)
    (EqvGen.rel a b)

中文:
定理 等价.eqvGen_iff
  条件: (h : 等价 r)
  结论: EqvGen r a b ↔ r a b
  证明: Iff.intro
    (by
      intro h
      induction h with
      | rel => assumption
      | refl => exact h.1 _
      | symm => apply h.symm; assumption
      | trans _ _ _ _ _ hab hbc => exact h.trans hab hbc)
    (EqvGen.rel a b)

Depends on / 依赖: EqvGen, EqvGen.rel, Iff.intro, h.symm, h.trans
-/
theorem Equivalence.eqvGen_iff (h : Equivalence r) : EqvGen r a b ↔ r a b :=
  Iff.intro
    (by
      intro h
      induction h with
      | rel => assumption
      | refl => exact h.1 _
      | symm => apply h.symm; assumption
      | trans _ _ _ _ _ hab hbc => exact h.trans hab hbc)
    (EqvGen.rel a b)

/--
theorem `Equivalence.eqvGen_eq` / 定理 `Equivalence.eqvGen_eq`

English:
theorem Equivalence.eqvGen_eq
  given: (h : Equivalence r)
  statement: EqvGen r = r
  proof: funext fun _ => funext fun _ => propext h.eqvGen_iff

中文:
定理 等价.eqvGen_eq
  条件: (h : 等价 r)
  结论: EqvGen r = r
  证明: funext fun _ => funext fun _ => propext h.eqvGen_iff

Depends on / 依赖: eqvGen_iff, h.eqvGen_iff, propext
-/
theorem Equivalence.eqvGen_eq (h : Equivalence r) : EqvGen r = r :=
funext fun _ => funext fun _ => propext h.eqvGen_iff

end EqvGen
