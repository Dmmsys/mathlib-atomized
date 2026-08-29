/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.FixedPoints.Defs

/-!
# Fixed points of a self-map

We prove some simple lemmas about `IsFixedPt` and `∘`, `iterate`, and `Semiconj`.

## Tags

fixed point
-/

public section

open Equiv

universe u v

variable {α β : Type*} {f fa g : α -> α} {x : α} {fb : β -> β} {e : Perm α}

namespace Function

open Function (Commute)

namespace IsFixedPt

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hf : IsFixedPt f x) (hg : IsFixedPt g x)
  statement: IsFixedPt (f ∘ g) x
  proof: calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf

中文:
定理 comp
  条件: (hf : IsFixedPt f x) (hg : IsFixedPt g x)
  结论: IsFixedPt (f ∘ g) x
  证明: calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf
-/
protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
  calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf

/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: (hf : IsFixedPt f x) (n : Nat)
  statement: IsFixedPt f^[n] x
  proof: iterate_fixed hf n

中文:
定理 iterate
  条件: (hf : IsFixedPt f x) (n : 自然数)
  结论: IsFixedPt f^[n] x
  证明: iterate_fixed hf n
-/
protected theorem iterate (hf : IsFixedPt f x) (n : Nat) : IsFixedPt f^[n] x :=
  iterate_fixed hf n

/--
theorem `left_of_comp` / 定理 `left_of_comp`

English:
theorem left_of_comp
  given: (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x)
  statement: IsFixedPt f x
  proof: calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg

中文:
定理 left_of_comp
  条件: (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x)
  结论: IsFixedPt f x
  证明: calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg

Depends on / 依赖: congr_arg, hg.symm
-/
theorem left_of_comp (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x) : IsFixedPt f x :=
  calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg

/--
theorem `to_leftInverse` / 定理 `to_leftInverse`

English:
theorem to_leftInverse
  given: (hf : IsFixedPt f x) (h : LeftInverse g f)
  statement: IsFixedPt g x
  proof: calc
    g x = g (f x) := congr_arg g hf.symm
    _ = x := h x

中文:
定理 to_leftInverse
  条件: (hf : IsFixedPt f x) (h : LeftInverse g f)
  结论: IsFixedPt g x
  证明: calc
    g x = g (f x) := congr_arg g hf.symm
    _ = x := h x

Depends on / 依赖: congr_arg, hf.symm
-/
theorem to_leftInverse (hf : IsFixedPt f x) (h : LeftInverse g f) : IsFixedPt g x :=
  calc
    g x = g (f x) := congr_arg g hf.symm
    _ = x := h x

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: {x : α} (hx : IsFixedPt fa x) {g : α -> β} (h : Semiconj g fa fb)
  proof: calc
    fb (g x) = g (fa x) := (h.eq x).symm
    _ = g x := congr_arg g hx

中文:
定理 map
  条件: {x : α} (hx : IsFixedPt fa x) {g : α -> β} (h : Semiconj g fa fb)
  证明: calc
    fb (g x) = g (fa x) := (h.eq x).symm
    _ = g x := congr_arg g hx
-/
protected theorem map {x : α} (hx : IsFixedPt fa x) {g : α -> β} (h : Semiconj g fa fb) :
    IsFixedPt fb (g x) :=
  calc
    fb (g x) = g (fa x) := (h.eq x).symm
    _ = g x := congr_arg g hx

/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  given: {x : α} (hx : IsFixedPt f x)
  statement: IsFixedPt f (f x)
  proof: by convert! hx

中文:
定理 apply
  条件: {x : α} (hx : IsFixedPt f x)
  结论: IsFixedPt f (f x)
  证明: by convert! hx
-/
protected theorem apply {x : α} (hx : IsFixedPt f x) : IsFixedPt f (f x) := by convert! hx

/--
theorem `preimage_iterate` / 定理 `preimage_iterate`

English:
theorem preimage_iterate
  given: {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : Nat)
  proof: by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n

中文:
定理 preimage_iterate
  条件: {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : 自然数)
  证明: by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n

Depends on / 依赖: Set.preimage_iterate_eq, h.iterate, iterate, preimage_iterate_eq
-/
theorem preimage_iterate {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : Nat) :
    IsFixedPt (Set.preimage f^[n]) s := by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n

/--
lemma `image_iterate` / 引理 `image_iterate`

English:
lemma image_iterate
  given: {s : Set α} (h : IsFixedPt (Set.image f) s) (n : Nat)
  proof: Set.image_iterate_eq ▸ h.iterate n

中文:
引理 image_iterate
  条件: {s : Set α} (h : IsFixedPt (Set.image f) s) (n : 自然数)
  证明: Set.image_iterate_eq ▸ h.iterate n

Depends on / 依赖: Set.image_iterate_eq, h.iterate, image_iterate_eq, iterate
-/
lemma image_iterate {s : Set α} (h : IsFixedPt (Set.image f) s) (n : Nat) :
    IsFixedPt (Set.image f^[n]) s :=
  Set.image_iterate_eq ▸ h.iterate n

/--
theorem `equiv_symm` / 定理 `equiv_symm`

English:
theorem equiv_symm
  given: (h : IsFixedPt e x)
  statement: IsFixedPt e.symm x
  proof: h.to_leftInverse e.leftInverse_symm

@[simp]

中文:
定理 equiv_symm
  条件: (h : IsFixedPt e x)
  结论: IsFixedPt e.symm x
  证明: h.to_leftInverse e.leftInverse_symm

@[simp]
-/
protected theorem equiv_symm (h : IsFixedPt e x) : IsFixedPt e.symm x :=
  h.to_leftInverse e.leftInverse_symm

@[simp]
/--
theorem `equiv_symm_iff` / 定理 `equiv_symm_iff`

English:
theorem equiv_symm_iff
  statement: IsFixedPt e.symm x ↔ IsFixedPt e x
  proof: ⟨fun h => e.symm_symm ▸ h.equiv_symm, .equiv_symm⟩

中文:
定理 equiv_symm_iff
  结论: IsFixedPt e.symm x ↔ IsFixedPt e x
  证明: ⟨fun h => e.symm_symm ▸ h.equiv_symm, .equiv_symm⟩

Depends on / 依赖: e.symm_symm, equiv_symm, h.equiv_symm, symm_symm
-/
theorem equiv_symm_iff : IsFixedPt e.symm x ↔ IsFixedPt e x :=
  ⟨fun h => e.symm_symm ▸ h.equiv_symm, .equiv_symm⟩

/--
theorem `perm_inv` / 定理 `perm_inv`

English:
theorem perm_inv
  given: (h : IsFixedPt e x)
  statement: IsFixedPt (⇑e⁻¹) x
  proof: h.equiv_symm

中文:
定理 perm_inv
  条件: (h : IsFixedPt e x)
  结论: IsFixedPt (⇑e⁻¹) x
  证明: h.equiv_symm
-/
protected theorem perm_inv (h : IsFixedPt e x) : IsFixedPt (⇑e⁻¹) x :=
  h.equiv_symm

/--
theorem `perm_pow` / 定理 `perm_pow`

English:
theorem perm_pow
  given: (h : IsFixedPt e x) (n : Nat)
  statement: IsFixedPt (⇑(e ^ n)) x
  proof: h.iterate _

中文:
定理 perm_pow
  条件: (h : IsFixedPt e x) (n : 自然数)
  结论: IsFixedPt (⇑(e ^ n)) x
  证明: h.iterate _
-/
protected theorem perm_pow (h : IsFixedPt e x) (n : Nat) : IsFixedPt (⇑(e ^ n)) x := h.iterate _

/--
theorem `perm_zpow` / 定理 `perm_zpow`

English:
theorem perm_zpow
  given: (h : IsFixedPt e x)
  statement: forall n : Int, IsFixedPt (⇑(e ^ n)) x

中文:
定理 perm_zpow
  条件: (h : IsFixedPt e x)
  结论: 对任意 n : 整数, IsFixedPt (⇑(e ^ n)) x
-/
protected theorem perm_zpow (h : IsFixedPt e x) : forall n : Int, IsFixedPt (⇑(e ^ n)) x
  | Int.ofNat _ => h.perm_pow _
  | Int.negSucc n => (h.perm_pow <| n + 1).perm_inv

end IsFixedPt

@[simp]
/--
theorem `fixedPoints_symm` / 定理 `fixedPoints_symm`

English:
theorem fixedPoints_symm
  statement: fixedPoints e.symm = fixedPoints e
  proof: by
  simp [Set.ext_iff]

@[simp]

中文:
定理 fixedPoints_symm
  结论: fixedPoints e.symm = fixedPoints e
  证明: by
  simp [Set.ext_iff]

@[simp]

Depends on / 依赖: Set.ext_iff, ext_iff
-/
theorem fixedPoints_symm : fixedPoints e.symm = fixedPoints e := by
  simp [Set.ext_iff]

@[simp]
/--
theorem `Injective.isFixedPt_apply_iff` / 定理 `Injective.isFixedPt_apply_iff`

English:
theorem Injective.isFixedPt_apply_iff
  given: (hf : Injective f) {x : α}
  proof: ⟨fun h => hf h.eq, IsFixedPt.apply⟩

中文:
定理 Injective.isFixedPt_apply_iff
  条件: (hf : Injective f) {x : α}
  证明: ⟨fun h => hf h.eq, IsFixedPt.apply⟩

Depends on / 依赖: IsFixedPt, IsFixedPt.apply, h.eq
-/
theorem Injective.isFixedPt_apply_iff (hf : Injective f) {x : α} :
    IsFixedPt f (f x) ↔ IsFixedPt f x :=
  ⟨fun h => hf h.eq, IsFixedPt.apply⟩

/--
theorem `Semiconj.mapsTo_fixedPoints` / 定理 `Semiconj.mapsTo_fixedPoints`

English:
theorem Semiconj.mapsTo_fixedPoints
  given: {g : α -> β} (h : Semiconj g fa fb)
  proof: fun _ hx => hx.map h

中文:
定理 Semiconj.mapsTo_fixedPoints
  条件: {g : α -> β} (h : Semiconj g fa fb)
  证明: fun _ hx => hx.map h

Depends on / 依赖: hx.map
-/
theorem Semiconj.mapsTo_fixedPoints {g : α -> β} (h : Semiconj g fa fb) :
    Set.MapsTo g (fixedPoints fa) (fixedPoints fb) := fun _ hx => hx.map h

/--
theorem `invOn_fixedPoints_comp` / 定理 `invOn_fixedPoints_comp`

English:
theorem invOn_fixedPoints_comp
  given: (f : α -> β) (g : β -> α)
  proof: ⟨fun _ => id, fun _ => id⟩

中文:
定理 invOn_fixedPoints_comp
  条件: (f : α -> β) (g : β -> α)
  证明: ⟨fun _ => id, fun _ => id⟩
-/
theorem invOn_fixedPoints_comp (f : α -> β) (g : β -> α) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  ⟨fun _ => id, fun _ => id⟩

/--
theorem `mapsTo_fixedPoints_comp` / 定理 `mapsTo_fixedPoints_comp`

English:
theorem mapsTo_fixedPoints_comp
  given: (f : α -> β) (g : β -> α)
  proof: fun _ hx => hx.map fun _ => rfl

中文:
定理 mapsTo_fixedPoints_comp
  条件: (f : α -> β) (g : β -> α)
  证明: fun _ hx => hx.map fun _ => rfl

Depends on / 依赖: hx.map
-/
theorem mapsTo_fixedPoints_comp (f : α -> β) (g : β -> α) :
    Set.MapsTo f (fixedPoints <| g ∘ f) (fixedPoints <| f ∘ g) := fun _ hx => hx.map fun _ => rfl

/--
theorem `bijOn_fixedPoints_comp` / 定理 `bijOn_fixedPoints_comp`

English:
theorem bijOn_fixedPoints_comp
  given: (f : α -> β) (g : β -> α)
  proof: (invOn_fixedPoints_comp f g).bijOn (mapsTo_fixedPoints_comp g f) (mapsTo_fixedPoints_comp f g)

中文:
定理 bijOn_fixedPoints_comp
  条件: (f : α -> β) (g : β -> α)
  证明: (invOn_fixedPoints_comp f g).bijOn (mapsTo_fixedPoints_comp g f) (mapsTo_fixedPoints_comp f g)

Depends on / 依赖: invOn_fixedPoints_comp, mapsTo_fixedPoints_comp
-/
theorem bijOn_fixedPoints_comp (f : α -> β) (g : β -> α) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| g ∘ f) :=
  (invOn_fixedPoints_comp f g).bijOn (mapsTo_fixedPoints_comp g f) (mapsTo_fixedPoints_comp f g)

/--
theorem `Commute.invOn_fixedPoints_comp` / 定理 `Commute.invOn_fixedPoints_comp`

English:
theorem Commute.invOn_fixedPoints_comp
  given: (h : Commute f g)
  proof: by
  simpa only [h.comp_eq] using Function.invOn_fixedPoints_comp f g

中文:
定理 Commute.invOn_fixedPoints_comp
  条件: (h : Commute f g)
  证明: by
  simpa only [h.comp_eq] using Function.invOn_fixedPoints_comp f g

Depends on / 依赖: Function, Function.invOn_fixedPoints_comp, comp_eq, h.comp_eq, invOn_fixedPoints_comp
-/
theorem Commute.invOn_fixedPoints_comp (h : Commute f g) :
    Set.InvOn f g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using Function.invOn_fixedPoints_comp f g

/--
theorem `Commute.left_bijOn_fixedPoints_comp` / 定理 `Commute.left_bijOn_fixedPoints_comp`

English:
theorem Commute.left_bijOn_fixedPoints_comp
  given: (h : Commute f g)
  proof: by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp g f

中文:
定理 Commute.left_bijOn_fixedPoints_comp
  条件: (h : Commute f g)
  证明: by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp g f

Depends on / 依赖: bijOn_fixedPoints_comp, comp_eq, h.comp_eq
-/
theorem Commute.left_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn f (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp g f

/--
theorem `Commute.right_bijOn_fixedPoints_comp` / 定理 `Commute.right_bijOn_fixedPoints_comp`

English:
theorem Commute.right_bijOn_fixedPoints_comp
  given: (h : Commute f g)
  proof: by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp f g

中文:
定理 Commute.right_bijOn_fixedPoints_comp
  条件: (h : Commute f g)
  证明: by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp f g

Depends on / 依赖: bijOn_fixedPoints_comp, comp_eq, h.comp_eq
-/
theorem Commute.right_bijOn_fixedPoints_comp (h : Commute f g) :
    Set.BijOn g (fixedPoints <| f ∘ g) (fixedPoints <| f ∘ g) := by
  simpa only [h.comp_eq] using bijOn_fixedPoints_comp f g

end Function
