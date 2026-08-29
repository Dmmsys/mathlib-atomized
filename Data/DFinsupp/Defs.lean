/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Group.Basic

/-!
# Dependent functions with finite support

For a non-dependent version see `Mathlib/Data/Finsupp/Defs.lean`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `DFinsupp β`, mirroring the `α →₀ β`
notation used for `Finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `DFinsupp (fun a ↦ DFinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `DFinsupp.support'`) as a `Multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`Finset`; it allows us to add together two finitely-supported functions without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `DFinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `DFinsupp`: with `DFinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `Decidable` argument; and with
`DFinsupp.sumAddHom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`Finsupp` takes an altogether different approach here; it uses `Classical.Decidable` and declares
the `Add` instance as noncomputable. This design difference is independent of the fact that
`DFinsupp` is dependently-typed and `Finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/

@[expose] public section

assert_not_exists Finset.prod Submonoid

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}

variable (β) in
/--
Definition of `DFinsupp` / `DFinsupp` 的定义

English:
structure DFinsupp
  parameters: [forall i, Zero (β i)]
  (no additional axioms)

中文:
结构 直和有限支撑
  参数: [对任意 i, 零 (β i)]
  (无附加公理)
-/
structure DFinsupp [forall i, Zero (β i)] : Type max u v where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `DFinsupp`). -/
  toFun : forall i, β i
  /-- The support of a dependent function with finite support (aka `DFinsupp`). -/
  support' : Trunc { s : Multiset ι // forall i, i in s ∨ toFun i = 0 }

/-- `Π₀ i, β i` denotes the type of dependent functions with finite support `DFinsupp β`. -/
notation3 "Π₀ "(...)", "r:(scoped f => DFinsupp f) => r

namespace DFinsupp

section Basic

variable [forall i, Zero (β i)] [forall i, Zero (β₁ i)] [forall i, Zero (β₂ i)]

/--
Instance `instDFunLike` / 实例 `instDFunLike`

English:
instance instDFunLike
  signature: : DFunLike (Π₀ i, β i) ι β
  body: ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ => fun (h : f₁ = f₂) => by
    subst h
    congr
    subsingleton ⟩

@[simp]

中文:
实例 instDFunLike
  签名: : 依赖函数状 (Π₀ i, β i) ι β
  定义体: ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ => fun (h : f₁ = f₂) => by
    subst h
    congr
    subsingleton ⟩

@[simp]

Depends on / 依赖: _eq_mapIdxMGo, f.toFun, mapIdxMAux, subsingleton
-/
instance instDFunLike : DFunLike (Π₀ i, β i) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ => fun (h : f₁ = f₂) => by
    subst h
    congr
    subsingleton ⟩

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : Π₀ i, β i)
  statement: f.toFun = f
  proof: rfl

@[ext, grind ext]

中文:
定理 toFun_eq_coe
  条件: (f : Π₀ i, β i)
  结论: f.toFun = f
  证明: rfl

@[ext, grind ext]
-/
theorem toFun_eq_coe (f : Π₀ i, β i) : f.toFun = f :=
  rfl

@[ext, grind ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : Π₀ i, β i} (h : forall i, f i = g i)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : Π₀ i, β i} (h : 对任意 i, f i = g i)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g :=
  DFunLike.ext _ _ h

/--
lemma `ne_iff` / 引理 `ne_iff`

English:
lemma ne_iff
  given: {f g : Π₀ i, β i}
  statement: f != g ↔ exists i, f i != g i
  proof: DFunLike.ne_iff

中文:
引理 ne_iff
  条件: {f g : Π₀ i, β i}
  结论: f != g ↔ 存在 i, f i != g i
  证明: DFunLike.ne_iff

Depends on / 依赖: DFunLike, DFunLike.ne_iff, ne_iff
-/
lemma ne_iff {f g : Π₀ i, β i} : f != g ↔ exists i, f i != g i := DFunLike.ne_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (Π₀ i, β i)
  body: ⟨⟨0, Trunc.mk ⟨∅, fun _ => Or.inr rfl⟩⟩⟩

中文:
实例 :
  签名: 零 (Π₀ i, β i)
  定义体: ⟨⟨0, Trunc.mk ⟨∅, fun _ => Or.inr rfl⟩⟩⟩

Depends on / 依赖: Or.inr, Trunc.mk
-/
instance : Zero (Π₀ i, β i) :=
⟨⟨0, Trunc.mk ⟨∅, fun _ => Or.inr rfl⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Π₀ i, β i)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (Π₀ i, β i)
  定义体: ⟨0⟩
-/
instance : Inhabited (Π₀ i, β i) :=
  ⟨0⟩

/--
lemma `coe_mk'` / 引理 `coe_mk'`

English:
lemma coe_mk'
  given: (f : forall i, β i) (s)
  statement: ⇑(⟨f, s⟩ : Π₀ i, β i) = f
  proof: rfl

中文:
引理 coe_mk'
  条件: (f : 对任意 i, β i) (s)
  结论: ⇑(⟨f, s⟩ : Π₀ i, β i) = f
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mk' (f : forall i, β i) (s) : ⇑(⟨f, s⟩ : Π₀ i, β i) = f := rfl

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ⇑(0 : Π₀ i, β i) = 0
  proof: rfl

中文:
引理 coe_zero
  结论: ⇑(0 : Π₀ i, β i) = 0
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : Π₀ i, β i) = 0 := rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (i : ι)
  statement: (0 : Π₀ i, β i) i = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (i : ι)
  结论: (0 : Π₀ i, β i) i = 0
  证明: rfl
-/
theorem zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 :=
  rfl

/--
Definition of `mapRange` / `mapRange` 的定义

English:
definition mapRange
  signature: (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (x : Π₀ i, β₁ i)
  body: ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s.1, fun i => (s.2 i).imp_right fun h : x i = 0 => by
      rw [← hf i]; rw [← h]⟩⟩

@[simp]

中文:
定义 mapRange
  签名: (f : 对任意 i, β₁ i -> β₂ i) (hf : 对任意 i, f i 0 = 0) (x : Π₀ i, β₁ i)
  定义体: ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s.1, fun i => (s.2 i).imp_right fun h : x i = 0 => by
      rw [← hf i]; rw [← h]⟩⟩

@[simp]

Depends on / 依赖: imp_right, support, x.support
-/
def mapRange (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (x : Π₀ i, β₁ i) : Π₀ i, β₂ i :=
  ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s.1, fun i => (s.2 i).imp_right fun h : x i = 0 => by
      rw [← hf i]; rw [← h]⟩⟩

@[simp]
/--
theorem `mapRange_apply` / 定理 `mapRange_apply`

English:
theorem mapRange_apply
  given: (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι)
  proof: rfl

@[simp]

中文:
定理 mapRange_apply
  条件: (f : 对任意 i, β₁ i -> β₂ i) (hf : 对任意 i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι)
  证明: rfl

@[simp]
-/
theorem mapRange_apply (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) :
    mapRange f hf g i = f i (g i) :=
  rfl

@[simp]
/--
theorem `mapRange_id` / 定理 `mapRange_id`

English:
theorem mapRange_id
  given: (h : forall i, id (0 : β₁ i) = 0 := fun _ => rfl) (g : Π₀ i : ι, β₁ i)
  proof: by
  ext
  rfl

中文:
定理 mapRange_id
  条件: (h : 对任意 i, id (0 : β₁ i) = 0 := fun _ => rfl) (g : Π₀ i : ι, β₁ i)
  证明: by
  ext
  rfl
-/
theorem mapRange_id (h : forall i, id (0 : β₁ i) = 0 := fun _ => rfl) (g : Π₀ i : ι, β₁ i) :
    mapRange (fun i => (id : β₁ i -> β₁ i)) h g = g := by
  ext
  rfl

/--
theorem `mapRange_comp` / 定理 `mapRange_comp`

English:
theorem mapRange_comp
  statement: (f : forall i, β₁ i -> β₂ i) (f₂ : forall i, β i -> β₁ i) (hf : forall i, f i 0 = 0)
  proof: by
  ext
  simp only [mapRange_apply]; rfl

@[simp]

中文:
定理 mapRange_comp
  结论: (f : 对任意 i, β₁ i -> β₂ i) (f₂ : 对任意 i, β i -> β₁ i) (hf : 对任意 i, f i 0 = 0)
  证明: by
  ext
  simp only [mapRange_apply]; rfl

@[simp]

Depends on / 依赖: mapRange_apply
-/
theorem mapRange_comp (f : forall i, β₁ i -> β₂ i) (f₂ : forall i, β i -> β₁ i) (hf : forall i, f i 0 = 0)
    (hf₂ : forall i, f₂ i 0 = 0) (h : forall i, (f i ∘ f₂ i) 0 = 0) (g : Π₀ i : ι, β i) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) := by
  ext
  simp only [mapRange_apply]; rfl

@[simp]
/--
theorem `mapRange_zero` / 定理 `mapRange_zero`

English:
theorem mapRange_zero
  given: (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0)
  proof: by
  ext
  simp only [mapRange_apply, coe_zero, Pi.zero_apply, hf]

中文:
定理 mapRange_zero
  条件: (f : 对任意 i, β₁ i -> β₂ i) (hf : 对任意 i, f i 0 = 0)
  证明: by
  ext
  simp only [mapRange_apply, coe_zero, Pi.zero_apply, hf]

Depends on / 依赖: Pi.zero_apply, coe_zero, mapRange_apply, zero_apply
-/
theorem mapRange_zero (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) :
    mapRange f hf (0 : Π₀ i, β₁ i) = 0 := by
  ext
  simp only [mapRange_apply, coe_zero, Pi.zero_apply, hf]

/--
Definition of `zipWith` / `zipWith` 的定义

English:
definition zipWith
  signature: (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i)
  body: ⟨fun i => f i (x i) (y i), by
    refine x.support'.bind fun xs => ?_
    refine y.support'.map fun ys => ?_
    refine ⟨xs + ys, fun i => ?_⟩
    obtain h1 | (h1 : x i = 0) := xs.prop i
    · grind
    obtain h2 | (h2 : y i = 0) := ys.prop i
    · grind
    grind⟩

@[simp, grind =]

中文:
定义 zipWith
  签名: (f : 对任意 i, β₁ i -> β₂ i -> β i) (hf : 对任意 i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i)
  定义体: ⟨fun i => f i (x i) (y i), by
    refine x.support'.bind fun xs => ?_
    refine y.support'.map fun ys => ?_
    refine ⟨xs + ys, fun i => ?_⟩
    obtain h1 | (h1 : x i = 0) := xs.prop i
    · grind
    obtain h2 | (h2 : y i = 0) := ys.prop i
    · grind
    grind⟩

@[simp, grind =]

Depends on / 依赖: support, x.support, xs.prop, y.support, ys.prop
-/
def zipWith (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i) :
    Π₀ i, β i :=
  ⟨fun i => f i (x i) (y i), by
    refine x.support'.bind fun xs => ?_
    refine y.support'.map fun ys => ?_
    refine ⟨xs + ys, fun i => ?_⟩
    obtain h1 | (h1 : x i = 0) := xs.prop i
    · grind
    obtain h2 | (h2 : y i = 0) := ys.prop i
    · grind
    grind⟩

@[simp, grind =]
/--
theorem `zipWith_apply` / 定理 `zipWith_apply`

English:
theorem zipWith_apply
  statement: (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i)
  proof: rfl

中文:
定理 zipWith_apply
  结论: (f : 对任意 i, β₁ i -> β₂ i -> β i) (hf : 对任意 i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i)
  证明: rfl
-/
theorem zipWith_apply (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i)
    (g₂ : Π₀ i, β₂ i) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  rfl

section Piecewise

variable (x y : Π₀ i, β i) (s : Set ι) [forall i, Decidable (i in s)]

/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: : Π₀ i, β i
  body: zipWith (fun i x y => if i in s then x else y) (fun _ => ite_self 0) x y

中文:
定义 piecewise
  签名: : Π₀ i, β i
  定义体: zipWith (fun i x y => if i in s then x else y) (fun _ => ite_self 0) x y

Depends on / 依赖: ite_self, zipWith
-/
def piecewise : Π₀ i, β i :=
  zipWith (fun i x y => if i in s then x else y) (fun _ => ite_self 0) x y

/--
theorem `piecewise_apply` / 定理 `piecewise_apply`

English:
theorem piecewise_apply
  given: (i : ι)
  statement: x.piecewise y s i = if i in s then x i else y i
  proof: rfl

@[simp, norm_cast]

中文:
定理 piecewise_apply
  条件: (i : ι)
  结论: x.piecewise y s i = if i in s then x i else y i
  证明: rfl

@[simp, norm_cast]
-/
theorem piecewise_apply (i : ι) : x.piecewise y s i = if i in s then x i else y i :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_piecewise` / 定理 `coe_piecewise`

English:
theorem coe_piecewise
  statement: ⇑(x.piecewise y s) = s.piecewise x y
  proof: rfl

中文:
定理 coe_piecewise
  结论: ⇑(x.piecewise y s) = s.piecewise x y
  证明: rfl
-/
theorem coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y :=
  rfl

end Piecewise

end Basic

section Algebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddZeroClass (β i)] : Add (Π₀ i, β i)
  body: ⟨zipWith (fun _ => (· + ·)) fun _ => add_zero 0⟩

中文:
实例 [对任意
  签名: i, 加法零类 (β i)] : 加法 (Π₀ i, β i)
  定义体: ⟨zipWith (fun _ => (· + ·)) fun _ => add_zero 0⟩

Depends on / 依赖: add_zero, zipWith
-/
instance [forall i, AddZeroClass (β i)] : Add (Π₀ i, β i) :=
  ⟨zipWith (fun _ => (· + ·)) fun _ => add_zero 0⟩

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι)
  proof: rfl

@[simp, norm_cast]

中文:
定理 add_apply
  条件: [对任意 i, 加法零类 (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι)
  证明: rfl

@[simp, norm_cast]
-/
theorem add_apply [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
    (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i)
  statement: ⇑(g₁ + g₂) = g₁ + g₂
  proof: rfl

中文:
定理 coe_add
  条件: [对任意 i, 加法零类 (β i)] (g₁ g₂ : Π₀ i, β i)
  结论: ⇑(g₁ + g₂) = g₁ + g₂
  证明: rfl
-/
theorem coe_add [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ + g₂) = g₁ + g₂ :=
  rfl

/--
Instance `addZeroClass` / 实例 `addZeroClass`

English:
instance addZeroClass
  signature: [forall i, AddZeroClass (β i)]
  body: DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

中文:
实例 addZeroClass
  签名: [对任意 i, 加法零类 (β i)]
  定义体: DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addZeroClass, addZeroClass, coe_add, coe_injective, coe_zero
-/
instance addZeroClass [forall i, AddZeroClass (β i)] : AddZeroClass (Π₀ i, β i) :=
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

/--
Instance `instIsLeftCancelAdd` / 实例 `instIsLeftCancelAdd`

English:
instance instIsLeftCancelAdd
  signature: [forall i, AddZeroClass (β i)] [forall i, IsLeftCancelAdd (β i)]
  body: ext fun x => add_left_cancel DFunLike.congr_fun h x

中文:
实例 instIsLeftCancelAdd
  签名: [对任意 i, 加法零类 (β i)] [对任意 i, 是左消去加法 (β i)]
  定义体: ext fun x => add_left_cancel DFunLike.congr_fun h x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, add_left_cancel, congr_fun
-/
instance instIsLeftCancelAdd [forall i, AddZeroClass (β i)] [forall i, IsLeftCancelAdd (β i)] :
    IsLeftCancelAdd (Π₀ i, β i) where
add_left_cancel _ _ _ h := ext fun x => add_left_cancel DFunLike.congr_fun h x

/--
Instance `instIsRightCancelAdd` / 实例 `instIsRightCancelAdd`

English:
instance instIsRightCancelAdd
  signature: [forall i, AddZeroClass (β i)] [forall i, IsRightCancelAdd (β i)]
  body: ext fun x => add_right_cancel DFunLike.congr_fun h x

中文:
实例 instIsRightCancelAdd
  签名: [对任意 i, 加法零类 (β i)] [对任意 i, 是右消去加法 (β i)]
  定义体: ext fun x => add_right_cancel DFunLike.congr_fun h x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, add_right_cancel, congr_fun
-/
instance instIsRightCancelAdd [forall i, AddZeroClass (β i)] [forall i, IsRightCancelAdd (β i)] :
    IsRightCancelAdd (Π₀ i, β i) where
add_right_cancel _ _ _ h := ext fun x => add_right_cancel DFunLike.congr_fun h x

/--
Instance `instIsCancelAdd` / 实例 `instIsCancelAdd`

English:
instance instIsCancelAdd
  signature: [forall i, AddZeroClass (β i)] [forall i, IsCancelAdd (β i)]

中文:
实例 instIsCancelAdd
  签名: [对任意 i, 加法零类 (β i)] [对任意 i, 是消去加法 (β i)]
-/
instance instIsCancelAdd [forall i, AddZeroClass (β i)] [forall i, IsCancelAdd (β i)] :
    IsCancelAdd (Π₀ i, β i) where

/--
Instance `hasNatScalar` / 实例 `hasNatScalar`

English:
instance hasNatScalar
  signature: [forall i, AddMonoid (β i)]
  body: ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => nsmul_zero _⟩

中文:
实例 has自然数Scalar
  签名: [对任意 i, 加法幺半群 (β i)]
  定义体: ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => nsmul_zero _⟩

Depends on / 依赖: mapRange, nsmul_zero, v.mapRange
-/
instance hasNatScalar [forall i, AddMonoid (β i)] : SMul Nat (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => nsmul_zero _⟩

/--
theorem `nsmul_apply` / 定理 `nsmul_apply`

English:
theorem nsmul_apply
  given: [forall i, AddMonoid (β i)] (b : Nat) (v : Π₀ i, β i) (i : ι)
  statement: (b • v) i = b • v i
  proof: rfl

@[simp, norm_cast]

中文:
定理 nsmul_apply
  条件: [对任意 i, 加法幺半群 (β i)] (b : 自然数) (v : Π₀ i, β i) (i : ι)
  结论: (b • v) i = b • v i
  证明: rfl

@[simp, norm_cast]
-/
theorem nsmul_apply [forall i, AddMonoid (β i)] (b : Nat) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: [forall i, AddMonoid (β i)] (b : Nat) (v : Π₀ i, β i)
  statement: ⇑(b • v) = b • ⇑v
  proof: rfl

中文:
定理 coe_nsmul
  条件: [对任意 i, 加法幺半群 (β i)] (b : 自然数) (v : Π₀ i, β i)
  结论: ⇑(b • v) = b • ⇑v
  证明: rfl
-/
theorem coe_nsmul [forall i, AddMonoid (β i)] (b : Nat) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddMonoid (β i)] : AddMonoid (Π₀ i, β i)
  body: DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

中文:
实例 [对任意
  签名: i, 加法幺半群 (β i)] : 加法幺半群 (Π₀ i, β i)
  定义体: DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addMonoid, addMonoid, coe_add, coe_injective, coe_nsmul, coe_zero
-/
instance [forall i, AddMonoid (β i)] : AddMonoid (Π₀ i, β i) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: [forall i, AddZeroClass (β i)]
  body: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]

中文:
定义 coeFnAddMonoidHom
  签名: [对任意 i, 加法零类 (β i)]
  定义体: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
-/
def coeFnAddMonoidHom [forall i, AddZeroClass (β i)] : (Π₀ i, β i) ->+ forall i, β i where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/--
lemma `coeFnAddMonoidHom_apply` / 引理 `coeFnAddMonoidHom_apply`

English:
lemma coeFnAddMonoidHom_apply
  given: [forall i, AddZeroClass (β i)] (v : Π₀ i, β i)
  statement: coeFnAddMonoidHom v = v
  proof: rfl

中文:
引理 coeFnAddMonoidHom_apply
  条件: [对任意 i, 加法零类 (β i)] (v : Π₀ i, β i)
  结论: coeFnAddMonoidHom v = v
  证明: rfl
-/
lemma coeFnAddMonoidHom_apply [forall i, AddZeroClass (β i)] (v : Π₀ i, β i) : coeFnAddMonoidHom v = v :=
  rfl

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: [forall i, AddCommMonoid (β i)]
  body: fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

中文:
实例 addCommMonoid
  签名: [对任意 i, 加法交换幺半群 (β i)]
  定义体: fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommMonoid, addCommMonoid, coe_add, coe_injective, coe_nsmul, coe_zero, fast_instance
-/
instance addCommMonoid [forall i, AddCommMonoid (β i)] : AddCommMonoid (Π₀ i, β i) :=
  fast_instance% DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddGroup (β i)] : Neg (Π₀ i, β i)
  body: ⟨fun f => f.mapRange (fun _ => Neg.neg) fun _ => neg_zero⟩

中文:
实例 [对任意
  签名: i, 加法群 (β i)] : 取负 (Π₀ i, β i)
  定义体: ⟨fun f => f.mapRange (fun _ => Neg.neg) fun _ => neg_zero⟩

Depends on / 依赖: Neg.neg, f.mapRange, mapRange, neg_zero
-/
instance [forall i, AddGroup (β i)] : Neg (Π₀ i, β i) :=
  ⟨fun f => f.mapRange (fun _ => Neg.neg) fun _ => neg_zero⟩

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: [forall i, AddGroup (β i)] (g : Π₀ i, β i) (i : ι)
  statement: (-g) i = -g i
  proof: rfl

中文:
定理 neg_apply
  条件: [对任意 i, 加法群 (β i)] (g : Π₀ i, β i) (i : ι)
  结论: (-g) i = -g i
  证明: rfl
-/
theorem neg_apply [forall i, AddGroup (β i)] (g : Π₀ i, β i) (i : ι) : (-g) i = -g i :=
  rfl

/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: [forall i, AddGroup (β i)] (g : Π₀ i, β i)
  statement: ⇑(-g) = -g
  proof: rfl

中文:
引理 coe_neg
  条件: [对任意 i, 加法群 (β i)] (g : Π₀ i, β i)
  结论: ⇑(-g) = -g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_neg [forall i, AddGroup (β i)] (g : Π₀ i, β i) : ⇑(-g) = -g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddGroup (β i)] : Sub (Π₀ i, β i)
  body: ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩

中文:
实例 [对任意
  签名: i, 加法群 (β i)] : 减法 (Π₀ i, β i)
  定义体: ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩

Depends on / 依赖: Sub.sub, sub_zero, zipWith
-/
instance [forall i, AddGroup (β i)] : Sub (Π₀ i, β i) :=
  ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: [forall i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι)
  statement: (g₁ - g₂) i = g₁ i - g₂ i
  proof: rfl

@[simp, norm_cast]

中文:
定理 sub_apply
  条件: [对任意 i, 加法群 (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι)
  结论: (g₁ - g₂) i = g₁ i - g₂ i
  证明: rfl

@[simp, norm_cast]
-/
theorem sub_apply [forall i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: [forall i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i)
  statement: ⇑(g₁ - g₂) = g₁ - g₂
  proof: rfl

中文:
定理 coe_sub
  条件: [对任意 i, 加法群 (β i)] (g₁ g₂ : Π₀ i, β i)
  结论: ⇑(g₁ - g₂) = g₁ - g₂
  证明: rfl
-/
theorem coe_sub [forall i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl

/--
Instance `hasIntScalar` / 实例 `hasIntScalar`

English:
instance hasIntScalar
  signature: [forall i, AddGroup (β i)]
  body: ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => zsmul_zero _⟩

中文:
实例 has整数Scalar
  签名: [对任意 i, 加法群 (β i)]
  定义体: ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => zsmul_zero _⟩

Depends on / 依赖: mapRange, v.mapRange, zsmul_zero
-/
instance hasIntScalar [forall i, AddGroup (β i)] : SMul Int (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => zsmul_zero _⟩

/--
theorem `zsmul_apply` / 定理 `zsmul_apply`

English:
theorem zsmul_apply
  given: [forall i, AddGroup (β i)] (b : Int) (v : Π₀ i, β i) (i : ι)
  statement: (b • v) i = b • v i
  proof: rfl

@[simp, norm_cast]

中文:
定理 zsmul_apply
  条件: [对任意 i, 加法群 (β i)] (b : 整数) (v : Π₀ i, β i) (i : ι)
  结论: (b • v) i = b • v i
  证明: rfl

@[simp, norm_cast]
-/
theorem zsmul_apply [forall i, AddGroup (β i)] (b : Int) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: [forall i, AddGroup (β i)] (b : Int) (v : Π₀ i, β i)
  statement: ⇑(b • v) = b • ⇑v
  proof: rfl

中文:
定理 coe_zsmul
  条件: [对任意 i, 加法群 (β i)] (b : 整数) (v : Π₀ i, β i)
  结论: ⇑(b • v) = b • ⇑v
  证明: rfl
-/
theorem coe_zsmul [forall i, AddGroup (β i)] (b : Int) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddGroup (β i)] : AddGroup (Π₀ i, β i)
  body: fast_instance% DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

中文:
实例 [对任意
  签名: i, 加法群 (β i)] : 加法群 (Π₀ i, β i)
  定义体: fast_instance% DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addGroup, addGroup, coe_add, coe_injective, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul, fast_instance
-/
instance [forall i, AddGroup (β i)] : AddGroup (Π₀ i, β i) :=
  fast_instance% DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: [forall i, AddCommGroup (β i)]
  body: fast_instance% DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

中文:
实例 addCommGroup
  签名: [对任意 i, 加法交换群 (β i)]
  定义体: fast_instance% DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommGroup, addCommGroup, coe_add, coe_injective, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul, fast_instance
-/
instance addCommGroup [forall i, AddCommGroup (β i)] : AddCommGroup (Π₀ i, β i) :=
  fast_instance% DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub
    (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

end Algebra

section FilterAndSubtypeDomain

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (x : Π₀ i, β i)
  body: ⟨fun i => if p i then x i else 0,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = 0 => by simp only [H, ite_self]⟩⟩

@[simp, grind =]

中文:
定义 filter
  签名: [对任意 i, 零 (β i)] (p : ι -> 命题) [DecidablePred p] (x : Π₀ i, β i)
  定义体: ⟨fun i => if p i then x i else 0,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = 0 => by simp only [H, ite_self]⟩⟩

@[simp, grind =]

Depends on / 依赖: imp_right, ite_self, support, x.support, xs.prop
-/
def filter [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun i => if p i then x i else 0,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = 0 => by simp only [H, ite_self]⟩⟩

@[simp, grind =]
/--
theorem `filter_apply` / 定理 `filter_apply`

English:
theorem filter_apply
  given: [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (i : ι) (f : Π₀ i, β i)
  proof: rfl

中文:
定理 filter_apply
  条件: [对任意 i, 零 (β i)] (p : ι -> 命题) [DecidablePred p] (i : ι) (f : Π₀ i, β i)
  证明: rfl
-/
theorem filter_apply [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (i : ι) (f : Π₀ i, β i) :
    f.filter p i = if p i then f i else 0 :=
  rfl

/--
theorem `filter_apply_pos` / 定理 `filter_apply_pos`

English:
theorem filter_apply_pos
  statement: [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
  proof: by grind

中文:
定理 filter_apply_pos
  结论: [对任意 i, 零 (β i)] {p : ι -> 命题} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
  证明: by grind
-/
theorem filter_apply_pos [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : p i) : f.filter p i = f i := by grind

/--
theorem `filter_apply_neg` / 定理 `filter_apply_neg`

English:
theorem filter_apply_neg
  statement: [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
  proof: by grind

中文:
定理 filter_apply_neg
  结论: [对任意 i, 零 (β i)] {p : ι -> 命题} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
  证明: by grind
-/
theorem filter_apply_neg [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : ¬p i) : f.filter p i = 0 := by grind

/--
theorem `filter_add_filter_not` / 定理 `filter_add_filter_not`

English:
theorem filter_add_filter_not
  statement: [forall i, AddZeroClass (β i)] (f : Π₀ i, β i) (p : ι -> Prop)
  proof: ext fun i => by
    simp only [add_apply, filter_apply]; split_ifs <;> simp only [add_zero, zero_add]

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

@[simp]

中文:
定理 filter_add_filter_not
  结论: [对任意 i, 加法零类 (β i)] (f : Π₀ i, β i) (p : ι -> 命题)
  证明: ext fun i => by
    simp only [add_apply, filter_apply]; split_ifs <;> simp only [add_zero, zero_add]

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

@[simp]
-/
@[simp] theorem filter_add_filter_not [forall i, AddZeroClass (β i)] (f : Π₀ i, β i) (p : ι -> Prop)
    [DecidablePred p] : (f.filter p + f.filter fun i => ¬p i) = f :=
  ext fun i => by
    simp only [add_apply, filter_apply]; split_ifs <;> simp only [add_zero, zero_add]

@[deprecated (since := "2026-05-04")] alias filter_pos_add_filter_neg := filter_add_filter_not

@[simp]
/--
theorem `filter_zero` / 定理 `filter_zero`

English:
theorem filter_zero
  given: [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p]
  proof: by
  ext
  simp

@[simp]

中文:
定理 filter_zero
  条件: [对任意 i, 零 (β i)] (p : ι -> 命题) [DecidablePred p]
  证明: by
  ext
  simp

@[simp]
-/
theorem filter_zero [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] :
    (0 : Π₀ i, β i).filter p = 0 := by
  ext
  simp

@[simp]
/--
theorem `filter_add` / 定理 `filter_add`

English:
theorem filter_add
  given: [forall i, AddZeroClass (β i)] (p : ι -> Prop) [DecidablePred p] (f g : Π₀ i, β i)
  proof: by
  ext
  simp [ite_add_zero]

中文:
定理 filter_add
  条件: [对任意 i, 加法零类 (β i)] (p : ι -> 命题) [DecidablePred p] (f g : Π₀ i, β i)
  证明: by
  ext
  simp [ite_add_zero]

Depends on / 依赖: ite_add_zero
-/
theorem filter_add [forall i, AddZeroClass (β i)] (p : ι -> Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f + g).filter p = f.filter p + g.filter p := by
  ext
  simp [ite_add_zero]

variable (γ β)

/-- `DFinsupp.filter` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `filterAddMonoidHom` / `filterAddMonoidHom` 的定义

English:
definition filterAddMonoidHom
  signature: [forall i, AddZeroClass (β i)] (p : ι -> Prop) [DecidablePred p]
  body: filter p
  map_zero' := filter_zero p
  map_add' := filter_add p

中文:
定义 filterAddMonoidHom
  签名: [对任意 i, 加法零类 (β i)] (p : ι -> 命题) [DecidablePred p]
  定义体: filter p
  map_zero' := filter_zero p
  map_add' := filter_add p

Depends on / 依赖: filter
-/
def filterAddMonoidHom [forall i, AddZeroClass (β i)] (p : ι -> Prop) [DecidablePred p] :
    (Π₀ i, β i) ->+ Π₀ i, β i where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := filter_add p

variable {γ β}

@[simp]
/--
theorem `filter_neg` / 定理 `filter_neg`

English:
theorem filter_neg
  given: [forall i, AddGroup (β i)] (p : ι -> Prop) [DecidablePred p] (f : Π₀ i, β i)
  proof: (filterAddMonoidHom β p).map_neg f

@[simp]

中文:
定理 filter_neg
  条件: [对任意 i, 加法群 (β i)] (p : ι -> 命题) [DecidablePred p] (f : Π₀ i, β i)
  证明: (filterAddMonoidHom β p).map_neg f

@[simp]

Depends on / 依赖: filterAddMonoidHom, map_neg
-/
theorem filter_neg [forall i, AddGroup (β i)] (p : ι -> Prop) [DecidablePred p] (f : Π₀ i, β i) :
    (-f).filter p = -f.filter p :=
  (filterAddMonoidHom β p).map_neg f

@[simp]
/--
theorem `filter_sub` / 定理 `filter_sub`

English:
theorem filter_sub
  given: [forall i, AddGroup (β i)] (p : ι -> Prop) [DecidablePred p] (f g : Π₀ i, β i)
  proof: (filterAddMonoidHom β p).map_sub f g

中文:
定理 filter_sub
  条件: [对任意 i, 加法群 (β i)] (p : ι -> 命题) [DecidablePred p] (f g : Π₀ i, β i)
  证明: (filterAddMonoidHom β p).map_sub f g

Depends on / 依赖: filterAddMonoidHom, map_sub
-/
theorem filter_sub [forall i, AddGroup (β i)] (p : ι -> Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f - g).filter p = f.filter p - g.filter p :=
  (filterAddMonoidHom β p).map_sub f g

/--
Definition of `subtypeDomain` / `subtypeDomain` 的定义

English:
definition subtypeDomain
  signature: [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (x : Π₀ i, β i)
  body: ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs.1).attach.map fun j => ⟨j.1, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩

@[simp]

中文:
定义 subtypeDomain
  签名: [对任意 i, 零 (β i)] (p : ι -> 命题) [DecidablePred p] (x : Π₀ i, β i)
  定义体: ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs.1).attach.map fun j => ⟨j.1, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.filter, Multiset.mem_attach, Multiset.mem_filter, Multiset.mem_map, Subtype, Subtype.eta, attach, attach.map, filter, imp_left, mem_attach, mem_filter, mem_map, support, x.support, xs.prop
-/
def subtypeDomain [forall i, Zero (β i)] (p : ι -> Prop) [DecidablePred p] (x : Π₀ i, β i) :
    Π₀ i : Subtype p, β i :=
  ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs.1).attach.map fun j => ⟨j.1, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩

@[simp]
/--
theorem `subtypeDomain_zero` / 定理 `subtypeDomain_zero`

English:
theorem subtypeDomain_zero
  given: [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p]
  proof: rfl

@[simp]

中文:
定理 subtypeDomain_zero
  条件: [对任意 i, 零 (β i)] {p : ι -> 命题} [DecidablePred p]
  证明: rfl

@[simp]
-/
theorem subtypeDomain_zero [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] :
    subtypeDomain p (0 : Π₀ i, β i) = 0 :=
  rfl

@[simp]
/--
theorem `subtypeDomain_apply` / 定理 `subtypeDomain_apply`

English:
theorem subtypeDomain_apply
  statement: [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] {i : Subtype p}
  proof: rfl

@[simp]

中文:
定理 subtypeDomain_apply
  结论: [对任意 i, 零 (β i)] {p : ι -> 命题} [DecidablePred p] {i : 子类型 p}
  证明: rfl

@[simp]
-/
theorem subtypeDomain_apply [forall i, Zero (β i)] {p : ι -> Prop} [DecidablePred p] {i : Subtype p}
    {v : Π₀ i, β i} : (subtypeDomain p v) i = v i :=
  rfl

@[simp]
/--
theorem `subtypeDomain_add` / 定理 `subtypeDomain_add`

English:
theorem subtypeDomain_add
  statement: [forall i, AddZeroClass (β i)] {p : ι -> Prop} [DecidablePred p]
  proof: DFunLike.coe_injective rfl

中文:
定理 subtypeDomain_add
  结论: [对任意 i, 加法零类 (β i)] {p : ι -> 命题} [DecidablePred p]
  证明: DFunLike.coe_injective rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem subtypeDomain_add [forall i, AddZeroClass (β i)] {p : ι -> Prop} [DecidablePred p]
    (v v' : Π₀ i, β i) : (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  DFunLike.coe_injective rfl

variable (γ β)

/-- `subtypeDomain` but as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `subtypeDomainAddMonoidHom` / `subtypeDomainAddMonoidHom` 的定义

English:
definition subtypeDomainAddMonoidHom
  signature: [forall i, AddZeroClass (β i)] (p : ι -> Prop) [DecidablePred p]
  body: subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' := subtypeDomain_add

中文:
定义 subtypeDomainAddMonoidHom
  签名: [对任意 i, 加法零类 (β i)] (p : ι -> 命题) [DecidablePred p]
  定义体: subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' := subtypeDomain_add

Depends on / 依赖: subtypeDomain
-/
def subtypeDomainAddMonoidHom [forall i, AddZeroClass (β i)] (p : ι -> Prop) [DecidablePred p] :
    (Π₀ i : ι, β i) ->+ Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' := subtypeDomain_add

variable {γ β}

@[simp]
/--
theorem `subtypeDomain_neg` / 定理 `subtypeDomain_neg`

English:
theorem subtypeDomain_neg
  given: [forall i, AddGroup (β i)] {p : ι -> Prop} [DecidablePred p] {v : Π₀ i, β i}
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 subtypeDomain_neg
  条件: [对任意 i, 加法群 (β i)] {p : ι -> 命题} [DecidablePred p] {v : Π₀ i, β i}
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem subtypeDomain_neg [forall i, AddGroup (β i)] {p : ι -> Prop} [DecidablePred p] {v : Π₀ i, β i} :
    (-v).subtypeDomain p = -v.subtypeDomain p :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `subtypeDomain_sub` / 定理 `subtypeDomain_sub`

English:
theorem subtypeDomain_sub
  statement: [forall i, AddGroup (β i)] {p : ι -> Prop} [DecidablePred p]
  proof: DFunLike.coe_injective rfl

中文:
定理 subtypeDomain_sub
  结论: [对任意 i, 加法群 (β i)] {p : ι -> 命题} [DecidablePred p]
  证明: DFunLike.coe_injective rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem subtypeDomain_sub [forall i, AddGroup (β i)] {p : ι -> Prop} [DecidablePred p]
    {v v' : Π₀ i, β i} : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  DFunLike.coe_injective rfl

end FilterAndSubtypeDomain

section Basic

variable [forall i, Zero (β i)]

/--
theorem `finite_support` / 定理 `finite_support`

English:
theorem finite_support
  given: (f : Π₀ i, β i)
  statement: Set.Finite { i | f i != 0 }
  proof: Trunc.induction_on f.support' fun xs =>
    xs.1.finite_toSet.subset fun i H => ((xs.prop i).resolve_right H)

中文:
定理 finite_support
  条件: (f : Π₀ i, β i)
  结论: 集合.有限 { i | f i != 0 }
  证明: Trunc.induction_on f.support' fun xs =>
    xs.1.finite_toSet.subset fun i H => ((xs.prop i).resolve_right H)

Depends on / 依赖: Trunc.induction_on, f.support, finite_toSet, finite_toSet.subset, induction_on, resolve_right, subset, support, xs.prop
-/
theorem finite_support (f : Π₀ i, β i) : Set.Finite { i | f i != 0 } :=
  Trunc.induction_on f.support' fun xs =>
    xs.1.finite_toSet.subset fun i H => ((xs.prop i).resolve_right H)

section DecidableEq
variable [DecidableEq ι]

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (s : Finset ι) (x : forall i : (↑s : Set ι), β (i : ι))
  body: ⟨fun i => if H : i in s then x ⟨i, H⟩ else 0,
Trunc.mk ⟨s.1, fun i => if H : i in s then Or.inl H else Or.inr dif_neg H⟩⟩

中文:
定义 mk
  签名: (s : 有限集 ι) (x : 对任意 i : (↑s : 集合 ι), β (i : ι))
  定义体: ⟨fun i => if H : i in s then x ⟨i, H⟩ else 0,
Trunc.mk ⟨s.1, fun i => if H : i in s then Or.inl H else Or.inr dif_neg H⟩⟩

Depends on / 依赖: Or.inl, Or.inr, Trunc.mk, dif_neg
-/
def mk (s : Finset ι) (x : forall i : (↑s : Set ι), β (i : ι)) : Π₀ i, β i :=
  ⟨fun i => if H : i in s then x ⟨i, H⟩ else 0,
Trunc.mk ⟨s.1, fun i => if H : i in s then Or.inl H else Or.inr dif_neg H⟩⟩

variable {s : Finset ι} {x : forall i : (↑s : Set ι), β i} {i : ι}

@[simp, grind =]
/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  statement: (mk s x : forall i, β i) i = if H : i in s then x ⟨i, H⟩ else 0
  proof: rfl

中文:
定理 mk_apply
  结论: (mk s x : 对任意 i, β i) i = if H : i in s then x ⟨i, H⟩ else 0
  证明: rfl
-/
theorem mk_apply : (mk s x : forall i, β i) i = if H : i in s then x ⟨i, H⟩ else 0 :=
  rfl

/--
theorem `mk_of_mem` / 定理 `mk_of_mem`

English:
theorem mk_of_mem
  given: (hi : i in s)
  statement: (mk s x : forall i, β i) i = x ⟨i, hi⟩
  proof: dif_pos hi

中文:
定理 mk_of_mem
  条件: (hi : i in s)
  结论: (mk s x : 对任意 i, β i) i = x ⟨i, hi⟩
  证明: dif_pos hi

Depends on / 依赖: dif_pos
-/
theorem mk_of_mem (hi : i in s) : (mk s x : forall i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi

/--
theorem `mk_of_notMem` / 定理 `mk_of_notMem`

English:
theorem mk_of_notMem
  given: (hi : i ∉ s)
  statement: (mk s x : forall i, β i) i = 0
  proof: dif_neg hi

中文:
定理 mk_of_notMem
  条件: (hi : i ∉ s)
  结论: (mk s x : 对任意 i, β i) i = 0
  证明: dif_neg hi

Depends on / 依赖: dif_neg
-/
theorem mk_of_notMem (hi : i ∉ s) : (mk s x : forall i, β i) i = 0 :=
  dif_neg hi

/--
theorem `mk_injective` / 定理 `mk_injective`

English:
theorem mk_injective
  given: (s : Finset ι)
  statement: Function.Injective (@mk ι β _ _ s)
  proof: by
  intro x y H
  ext i
  have h1 : (mk s x : forall i, β i) i = (mk s y : forall i, β i) i := by grind
  grind

中文:
定理 mk_injective
  条件: (s : 有限集 ι)
  结论: 函数.单射 (@mk ι β _ _ s)
  证明: by
  intro x y H
  ext i
  have h1 : (mk s x : forall i, β i) i = (mk s y : forall i, β i) i := by grind
  grind
-/
theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β _ _ s) := by
  intro x y H
  ext i
  have h1 : (mk s x : forall i, β i) i = (mk s y : forall i, β i) i := by grind
  grind

end DecidableEq

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [forall i, Subsingleton (β i)]
  body: DFunLike.coe_injective.unique

中文:
实例 unique
  签名: [对任意 i, 子单例 (β i)]
  定义体: DFunLike.coe_injective.unique

Depends on / 依赖: DFunLike, DFunLike.coe_injective.unique, coe_injective, unique
-/
instance unique [forall i, Subsingleton (β i)] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique

/--
Instance `uniqueOfIsEmpty` / 实例 `uniqueOfIsEmpty`

English:
instance uniqueOfIsEmpty
  signature: [IsEmpty ι]
  body: DFunLike.coe_injective.unique

中文:
实例 uniqueOfIsEmpty
  签名: [是空 ι]
  定义体: DFunLike.coe_injective.unique

Depends on / 依赖: DFunLike, DFunLike.coe_injective.unique, coe_injective, unique
-/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique

/-- Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
/--
Definition of `equivFunOnFintype` / `equivFunOnFintype` 的定义

English:
definition equivFunOnFintype
  signature: [Fintype ι]
  body: (⇑)
invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl

@[simp]

中文:
定义 equivFunOnFintype
  签名: [有限类型 ι]
  定义体: (⇑)
invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl

@[simp]
-/
def equivFunOnFintype [Fintype ι] : (Π₀ i, β i) ≃ forall i, β i where
  toFun := (⇑)
invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl

@[simp]
/--
theorem `equivFunOnFintype_symm_coe` / 定理 `equivFunOnFintype_symm_coe`

English:
theorem equivFunOnFintype_symm_coe
  given: [Fintype ι] (f : Π₀ i, β i)
  statement: equivFunOnFintype.symm f = f
  proof: Equiv.symm_apply_apply _ _

中文:
定理 equivFunOnFintype_symm_coe
  条件: [有限类型 ι] (f : Π₀ i, β i)
  结论: equivFunOnFintype.symm f = f
  证明: Equiv.symm_apply_apply _ _

Depends on / 依赖: Equiv.symm_apply_apply, symm_apply_apply
-/
theorem equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀ i, β i) : equivFunOnFintype.symm f = f :=
  Equiv.symm_apply_apply _ _

variable [DecidableEq ι]

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (i : ι) (b : β i)
  body: ⟨Pi.single i b,
    Trunc.mk ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩

中文:
定义 single
  签名: (i : ι) (b : β i)
  定义体: ⟨Pi.single i b,
    Trunc.mk ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Pi.single, Pi.single_eq_of_ne, Trunc.mk, eq_or_ne, single, single_eq_of_ne
-/
def single (i : ι) (b : β i) : Π₀ i, β i :=
  ⟨Pi.single i b,
    Trunc.mk ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩

/--
theorem `single_eq_pi_single` / 定理 `single_eq_pi_single`

English:
theorem single_eq_pi_single
  given: {i b}
  statement: ⇑(single i b : Π₀ i, β i) = Pi.single i b
  proof: rfl

@[simp, grind =]

中文:
定理 single_eq_pi_single
  条件: {i b}
  结论: ⇑(single i b : Π₀ i, β i) = 依赖函数类型.single i b
  证明: rfl

@[simp, grind =]
-/
theorem single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = Pi.single i b :=
  rfl

@[simp, grind =]
/--
theorem `single_apply` / 定理 `single_apply`

English:
theorem single_apply
  given: {i i' b}
  proof: by
  rw [single_eq_pi_single]; rw [Pi.single]; rw [Function.update]
  simp [@eq_comm _ i i']

@[simp]

中文:
定理 single_apply
  条件: {i i' b}
  证明: by
  rw [single_eq_pi_single]; rw [Pi.single]; rw [Function.update]
  simp [@eq_comm _ i i']

@[simp]

Depends on / 依赖: Function, Function.update, Pi.single, eq_comm, single, single_eq_pi_single, update
-/
theorem single_apply {i i' b} :
    (single i b : Π₀ i, β i) i' = if h : i = i' then Eq.recOn h b else 0 := by
  rw [single_eq_pi_single]; rw [Pi.single]; rw [Function.update]
  simp [@eq_comm _ i i']

@[simp]
/--
theorem `single_zero` / 定理 `single_zero`

English:
theorem single_zero
  given: (i)
  statement: (single i 0 : Π₀ i, β i) = 0
  proof: DFunLike.coe_injective Pi.single_zero _

中文:
定理 single_zero
  条件: (i)
  结论: (single i 0 : Π₀ i, β i) = 0
  证明: DFunLike.coe_injective Pi.single_zero _

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Pi.single_zero, coe_injective, single_zero
-/
theorem single_zero (i) : (single i 0 : Π₀ i, β i) = 0 :=
DFunLike.coe_injective Pi.single_zero _

/--
theorem `single_eq_same` / 定理 `single_eq_same`

English:
theorem single_eq_same
  given: {i b}
  statement: (single i b : Π₀ i, β i) i = b
  proof: by
  grind

中文:
定理 single_eq_same
  条件: {i b}
  结论: (single i b : Π₀ i, β i) i = b
  证明: by
  grind
-/
theorem single_eq_same {i b} : (single i b : Π₀ i, β i) i = b := by
  grind

/--
theorem `single_eq_of_ne` / 定理 `single_eq_of_ne`

English:
theorem single_eq_of_ne
  given: {i i' b} (h : i' != i)
  statement: (single i b : Π₀ i, β i) i' = 0
  proof: by
  grind

中文:
定理 single_eq_of_ne
  条件: {i i' b} (h : i' != i)
  结论: (single i b : Π₀ i, β i) i' = 0
  证明: by
  grind
-/
theorem single_eq_of_ne {i i' b} (h : i' != i) : (single i b : Π₀ i, β i) i' = 0 := by
  grind

/--
theorem `single_injective` / 定理 `single_injective`

English:
theorem single_injective
  given: {i}
  statement: Function.Injective (single i : β i -> Π₀ i, β i)
  proof: fun _ _ H =>
Pi.single_injective i DFunLike.coe_injective.eq_iff.mpr H

中文:
定理 single_injective
  条件: {i}
  结论: 函数.单射 (single i : β i -> Π₀ i, β i)
  证明: fun _ _ H =>
Pi.single_injective i DFunLike.coe_injective.eq_iff.mpr H
-/
theorem single_injective {i} : Function.Injective (single i : β i -> Π₀ i, β i) := fun _ _ H =>
Pi.single_injective i DFunLike.coe_injective.eq_iff.mpr H

/--
theorem `single_eq_single_iff` / 定理 `single_eq_single_iff`

English:
theorem single_eq_single_iff
  given: (i j : ι) (xi : β i) (xj : β j)
  proof: by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (DFinsupp.single_injective h)⟩
    · have h_coe : ⇑(DFinsupp.single i xi) = DFinsupp.single j xj := congr_arg (⇑) h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [DFinsupp.single_eq_same] at hci hcj
      rw [DFinsupp.single_eq_of_ne hij] at hci
      rw [DFinsupp.single_eq_of_ne (Ne.symm hij)] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
    · rw [hi, hj, DFinsupp.single_zero, DFinsupp.single_zero]

中文:
定理 single_eq_single_iff
  条件: (i j : ι) (xi : β i) (xj : β j)
  证明: by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (DFinsupp.single_injective h)⟩
    · have h_coe : ⇑(DFinsupp.single i xi) = DFinsupp.single j xj := congr_arg (⇑) h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [DFinsupp.single_eq_same] at hci hcj
      rw [DFinsupp.single_eq_of_ne hij] at hci
      rw [DFinsupp.single_eq_of_ne (Ne.symm hij)] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
    · rw [hi, hj, DFinsupp.single_zero, DFinsupp.single_zero]

Depends on / 依赖: DFinsupp, DFinsupp.sin, DFinsupp.single, DFinsupp.single_eq_of_ne, DFinsupp.single_eq_same, DFinsupp.single_injective, Ne.symm, Or.inl, Or.inr, congr_arg, congr_fun, eq_of_heq, h_coe, hcj.symm, heq_of_eq, single, single_eq_of_ne, single_eq_same, single_injective
-/
theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    DFinsupp.single i xi = DFinsupp.single j xj ↔ i = j ∧ xi ≍ xj ∨ xi = 0 ∧ xj = 0 := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (DFinsupp.single_injective h)⟩
    · have h_coe : ⇑(DFinsupp.single i xi) = DFinsupp.single j xj := congr_arg (⇑) h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [DFinsupp.single_eq_same] at hci hcj
      rw [DFinsupp.single_eq_of_ne hij] at hci
      rw [DFinsupp.single_eq_of_ne (Ne.symm hij)] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
    · rw [hi, hj, DFinsupp.single_zero, DFinsupp.single_zero]

/--
theorem `single_left_injective` / 定理 `single_left_injective`

English:
theorem single_left_injective
  given: {b : forall i : ι, β i} (h : forall i, b i != 0)
  proof: fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left

@[simp]

中文:
定理 single_left_injective
  条件: {b : 对任意 i : ι, β i} (h : 对任意 i, b i != 0)
  证明: fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left

@[simp]
-/
theorem single_left_injective {b : forall i : ι, β i} (h : forall i, b i != 0) :
    Function.Injective (fun i => single i (b i) : ι -> Π₀ i, β i) := fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left

@[simp]
/--
theorem `single_eq_zero` / 定理 `single_eq_zero`

English:
theorem single_eq_zero
  given: {i : ι} {xi : β i}
  statement: single i xi = 0 ↔ xi = 0
  proof: by
  rw [← single_zero i]; rw [single_eq_single_iff]
  simp

中文:
定理 single_eq_zero
  条件: {i : ι} {xi : β i}
  结论: single i xi = 0 ↔ xi = 0
  证明: by
  rw [← single_zero i]; rw [single_eq_single_iff]
  simp

Depends on / 依赖: single_eq_single_iff, single_zero
-/
theorem single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 := by
  rw [← single_zero i]; rw [single_eq_single_iff]
  simp

/--
theorem `single_ne_zero` / 定理 `single_ne_zero`

English:
theorem single_ne_zero
  given: {i : ι} {xi : β i}
  statement: single i xi != 0 ↔ xi != 0
  proof: single_eq_zero.not

中文:
定理 single_ne_zero
  条件: {i : ι} {xi : β i}
  结论: single i xi != 0 ↔ xi != 0
  证明: single_eq_zero.not

Depends on / 依赖: single_eq_zero, single_eq_zero.not
-/
theorem single_ne_zero {i : ι} {xi : β i} : single i xi != 0 ↔ xi != 0 :=
  single_eq_zero.not

/--
theorem `filter_single` / 定理 `filter_single`

English:
theorem filter_single
  given: (p : ι -> Prop) [DecidablePred p] (i : ι) (x : β i)
  proof: by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp at this
  grind

@[simp]

中文:
定理 filter_single
  条件: (p : ι -> 命题) [DecidablePred p] (i : ι) (x : β i)
  证明: by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp at this
  grind

@[simp]

Depends on / 依赖: apply_ite, single
-/
theorem filter_single (p : ι -> Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single i x).filter p = if p i then single i x else 0 := by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp at this
  grind

@[simp]
/--
theorem `filter_single_pos` / 定理 `filter_single_pos`

English:
theorem filter_single_pos
  given: {p : ι -> Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i)
  proof: by rw [filter_single, if_pos h]

@[simp]

中文:
定理 filter_single_pos
  条件: {p : ι -> 命题} [DecidablePred p] (i : ι) (x : β i) (h : p i)
  证明: by rw [filter_single, if_pos h]

@[simp]

Depends on / 依赖: filter_single, if_pos
-/
theorem filter_single_pos {p : ι -> Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single i x).filter p = single i x := by rw [filter_single, if_pos h]

@[simp]
/--
theorem `filter_single_neg` / 定理 `filter_single_neg`

English:
theorem filter_single_neg
  given: {p : ι -> Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i)
  proof: by rw [filter_single, if_neg h]

中文:
定理 filter_single_neg
  条件: {p : ι -> 命题} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i)
  证明: by rw [filter_single, if_neg h]

Depends on / 依赖: filter_single, if_neg
-/
theorem filter_single_neg {p : ι -> Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) :
    (single i x).filter p = 0 := by rw [filter_single, if_neg h]

/--
theorem `single_eq_of_sigma_eq` / 定理 `single_eq_of_sigma_eq`

English:
theorem single_eq_of_sigma_eq
  given: {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩)
  proof: by
  cases h
  rfl

@[simp]

中文:
定理 single_eq_of_sigma_eq
  条件: {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : 依赖和类型 β) = ⟨j, xj⟩)
  证明: by
  cases h
  rfl

@[simp]
-/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    DFinsupp.single i xi = DFinsupp.single j xj := by
  cases h
  rfl

@[simp]
/--
theorem `equivFunOnFintype_single` / 定理 `equivFunOnFintype_single`

English:
theorem equivFunOnFintype_single
  given: [Fintype ι] (i : ι) (m : β i)
  proof: rfl

@[simp]

中文:
定理 equivFunOnFintype_single
  条件: [有限类型 ι] (i : ι) (m : β i)
  证明: rfl

@[simp]
-/
theorem equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _) (DFinsupp.single i m) = Pi.single i m := rfl

@[simp]
/--
theorem `equivFunOnFintype_symm_single` / 定理 `equivFunOnFintype_symm_single`

English:
theorem equivFunOnFintype_symm_single
  given: [Fintype ι] (i : ι) (m : β i)
  proof: by
  simp only [← single_eq_pi_single, equivFunOnFintype_symm_coe]

中文:
定理 equivFunOnFintype_symm_single
  条件: [有限类型 ι] (i : ι) (m : β i)
  证明: by
  simp only [← single_eq_pi_single, equivFunOnFintype_symm_coe]

Depends on / 依赖: equivFunOnFintype_symm_coe, single_eq_pi_single
-/
theorem equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _).symm (Pi.single i m) = DFinsupp.single i m := by
  simp only [← single_eq_pi_single, equivFunOnFintype_symm_coe]

/--
lemma `filter_eq` / 引理 `filter_eq`

English:
lemma filter_eq
  given: (f : Π₀ i, β i) (i : ι)
  statement: f.filter (i = ·) = single i (f i)
  proof: by
  ext
  rw [filter_apply]; rw [single_apply]
  split
  · subst i
    simp
  · simp

中文:
引理 filter_eq
  条件: (f : Π₀ i, β i) (i : ι)
  结论: f.filter (i = ·) = single i (f i)
  证明: by
  ext
  rw [filter_apply]; rw [single_apply]
  split
  · subst i
    simp
  · simp
-/
@[simp] lemma filter_eq (f : Π₀ i, β i) (i : ι) : f.filter (i = ·) = single i (f i) := by
  ext
  rw [filter_apply]; rw [single_apply]
  split
  · subst i
    simp
  · simp

/--
lemma `filter_eq'` / 引理 `filter_eq'`

English:
lemma filter_eq'
  given: (f : Π₀ i, β i) (i : ι)
  statement: f.filter (· = i) = single i (f i)
  proof: by
  simp [eq_comm]

中文:
引理 filter_eq'
  条件: (f : Π₀ i, β i) (i : ι)
  结论: f.filter (· = i) = single i (f i)
  证明: by
  simp [eq_comm]
-/
@[simp] lemma filter_eq' (f : Π₀ i, β i) (i : ι) : f.filter (· = i) = single i (f i) := by
  simp [eq_comm]

section SingleAndZipWith

variable [forall i, Zero (β₁ i)] [forall i, Zero (β₂ i)]
@[simp]
/--
theorem `zipWith_single_single` / 定理 `zipWith_single_single`

English:
theorem zipWith_single_single
  statement: (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0)
  proof: by
  grind

中文:
定理 zipWith_single_single
  结论: (f : 对任意 i, β₁ i -> β₂ i -> β i) (hf : 对任意 i, f i 0 0 = 0)
  证明: by
  grind
-/
theorem zipWith_single_single (f : forall i, β₁ i -> β₂ i -> β i) (hf : forall i, f i 0 0 = 0)
    {i} (b₁ : β₁ i) (b₂ : β₂ i) :
    zipWith f hf (single i b₁) (single i b₂) = single i (f i b₁ b₂) := by
  grind

end SingleAndZipWith

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (i : ι) (x : Π₀ i, β i)
  body: ⟨fun j => if j = i then 0 else x.1 j,
    x.support'.map fun xs => ⟨xs.1, fun j => (xs.prop j).imp_right (by simp only [·, ite_self])⟩⟩

@[simp, grind =]

中文:
定义 erase
  签名: (i : ι) (x : Π₀ i, β i)
  定义体: ⟨fun j => if j = i then 0 else x.1 j,
    x.support'.map fun xs => ⟨xs.1, fun j => (xs.prop j).imp_right (by simp only [·, ite_self])⟩⟩

@[simp, grind =]

Depends on / 依赖: imp_right, ite_self, support, x.support, xs.prop
-/
def erase (i : ι) (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun j => if j = i then 0 else x.1 j,
    x.support'.map fun xs => ⟨xs.1, fun j => (xs.prop j).imp_right (by simp only [·, ite_self])⟩⟩

@[simp, grind =]
/--
theorem `erase_apply` / 定理 `erase_apply`

English:
theorem erase_apply
  given: {i j : ι} {f : Π₀ i, β i}
  statement: (f.erase i) j = if j = i then 0 else f j
  proof: rfl

中文:
定理 erase_apply
  条件: {i j : ι} {f : Π₀ i, β i}
  结论: (f.erase i) j = if j = i then 0 else f j
  证明: rfl
-/
theorem erase_apply {i j : ι} {f : Π₀ i, β i} : (f.erase i) j = if j = i then 0 else f j :=
  rfl

/--
theorem `erase_same` / 定理 `erase_same`

English:
theorem erase_same
  given: {i : ι} {f : Π₀ i, β i}
  statement: (f.erase i) i = 0
  proof: by simp

中文:
定理 erase_same
  条件: {i : ι} {f : Π₀ i, β i}
  结论: (f.erase i) i = 0
  证明: by simp
-/
theorem erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 := by simp

/--
theorem `erase_ne` / 定理 `erase_ne`

English:
theorem erase_ne
  given: {i i' : ι} {f : Π₀ i, β i} (h : i' != i)
  statement: (f.erase i) i' = f i'
  proof: by simp [h]

中文:
定理 erase_ne
  条件: {i i' : ι} {f : Π₀ i, β i} (h : i' != i)
  结论: (f.erase i) i' = f i'
  证明: by simp [h]
-/
theorem erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' != i) : (f.erase i) i' = f i' := by simp [h]

/--
theorem `piecewise_single_erase` / 定理 `piecewise_single_erase`

English:
theorem piecewise_single_erase
  given: (x : Π₀ i, β i) (i : ι)
  proof: by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h

中文:
定理 piecewise_single_erase
  条件: (x : Π₀ i, β i) (i : ι)
  证明: by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h

Depends on / 依赖: erase_ne, piecewise_apply, single_eq_same, split_ifs
-/
theorem piecewise_single_erase (x : Π₀ i, β i) (i : ι) :
    (single i (x i)).piecewise (x.erase i) {i} = x := by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h

/--
theorem `erase_eq_sub_single` / 定理 `erase_eq_sub_single`

English:
theorem erase_eq_sub_single
  given: {β : ι -> Type*} [forall i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι)
  proof: by
  ext j
  rcases eq_or_ne j i with (rfl | h)
  · simp
  · simp [erase_ne h, single_eq_of_ne h]

@[simp]

中文:
定理 erase_eq_sub_single
  条件: {β : ι -> 类型} [对任意 i, 加法群 (β i)] (f : Π₀ i, β i) (i : ι)
  证明: by
  ext j
  rcases eq_or_ne j i with (rfl | h)
  · simp
  · simp [erase_ne h, single_eq_of_ne h]

@[simp]

Depends on / 依赖: eq_or_ne, erase_ne, single_eq_of_ne
-/
theorem erase_eq_sub_single {β : ι -> Type*} [forall i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι) :
    f.erase i = f - single i (f i) := by
  ext j
  rcases eq_or_ne j i with (rfl | h)
  · simp
  · simp [erase_ne h, single_eq_of_ne h]

@[simp]
/--
theorem `erase_zero` / 定理 `erase_zero`

English:
theorem erase_zero
  given: (i : ι)
  statement: erase i (0 : Π₀ i, β i) = 0
  proof: ext fun _ => ite_self _

@[simp]

中文:
定理 erase_zero
  条件: (i : ι)
  结论: erase i (0 : Π₀ i, β i) = 0
  证明: ext fun _ => ite_self _

@[simp]

Depends on / 依赖: ite_self
-/
theorem erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0 :=
  ext fun _ => ite_self _

@[simp]
/--
theorem `filter_ne_eq_erase` / 定理 `filter_ne_eq_erase`

English:
theorem filter_ne_eq_erase
  given: (f : Π₀ i, β i) (i : ι)
  statement: f.filter (· != i) = f.erase i
  proof: by
  grind

@[simp]

中文:
定理 filter_ne_eq_erase
  条件: (f : Π₀ i, β i) (i : ι)
  结论: f.filter (· != i) = f.erase i
  证明: by
  grind

@[simp]
-/
theorem filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (· != i) = f.erase i := by
  grind

@[simp]
/--
theorem `filter_ne_eq_erase'` / 定理 `filter_ne_eq_erase'`

English:
theorem filter_ne_eq_erase'
  given: (f : Π₀ i, β i) (i : ι)
  statement: f.filter (i != ·) = f.erase i
  proof: by
  grind

中文:
定理 filter_ne_eq_erase'
  条件: (f : Π₀ i, β i) (i : ι)
  结论: f.filter (i != ·) = f.erase i
  证明: by
  grind
-/
theorem filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter (i != ·) = f.erase i := by
  grind

/--
theorem `erase_single` / 定理 `erase_single`

English:
theorem erase_single
  given: (j : ι) (i : ι) (x : β i)
  proof: by
  rw [← filter_ne_eq_erase]; rw [filter_single]; rw [ite_not]

@[simp]

中文:
定理 erase_single
  条件: (j : ι) (i : ι) (x : β i)
  证明: by
  rw [← filter_ne_eq_erase]; rw [filter_single]; rw [ite_not]

@[simp]

Depends on / 依赖: filter_ne_eq_erase, filter_single, ite_not
-/
theorem erase_single (j : ι) (i : ι) (x : β i) :
    (single i x).erase j = if i = j then 0 else single i x := by
  rw [← filter_ne_eq_erase]; rw [filter_single]; rw [ite_not]

@[simp]
/--
theorem `erase_single_same` / 定理 `erase_single_same`

English:
theorem erase_single_same
  given: (i : ι) (x : β i)
  statement: (single i x).erase i = 0
  proof: by
  rw [erase_single]; rw [if_pos rfl]

@[simp]

中文:
定理 erase_single_same
  条件: (i : ι) (x : β i)
  结论: (single i x).erase i = 0
  证明: by
  rw [erase_single]; rw [if_pos rfl]

@[simp]

Depends on / 依赖: erase_single, if_pos
-/
theorem erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 := by
  rw [erase_single]; rw [if_pos rfl]

@[simp]
/--
theorem `erase_single_ne` / 定理 `erase_single_ne`

English:
theorem erase_single_ne
  given: {i j : ι} (x : β i) (h : i != j)
  statement: (single i x).erase j = single i x
  proof: by
  rw [erase_single]; rw [if_neg h]

中文:
定理 erase_single_ne
  条件: {i j : ι} (x : β i) (h : i != j)
  结论: (single i x).erase j = single i x
  证明: by
  rw [erase_single]; rw [if_neg h]

Depends on / 依赖: erase_single, if_neg
-/
theorem erase_single_ne {i j : ι} (x : β i) (h : i != j) : (single i x).erase j = single i x := by
  rw [erase_single]; rw [if_neg h]

section Update

variable (f : Π₀ i, β i) (i) (b : β i)

/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: : Π₀ i, β i
  body: ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s.1, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = 0) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_of_ne hi.symm b _).trans hj)⟩⟩

中文:
定义 update
  签名: : Π₀ i, β i
  定义体: ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s.1, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = 0) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_of_ne hi.symm b _).trans hj)⟩⟩

Depends on / 依赖: Function, Function.update, Function.update_of_ne, Multiset, Multiset.mem_cons_of_mem, Or.inl, Or.inr, eq_or_ne, f.support, hi.symm, mem_cons_of_mem, s.prop, support, update, update_of_ne
-/
def update : Π₀ i, β i :=
  ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s.1, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = 0) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_of_ne hi.symm b _).trans hj)⟩⟩

variable (j : ι)

/--
lemma `coe_update` / 引理 `coe_update`

English:
lemma coe_update
  statement: (f.update i b : forall i : ι, β i) = Function.update f i b
  proof: rfl

@[simp]

中文:
引理 coe_update
  结论: (f.update i b : 对任意 i : ι, β i) = 函数.update f i b
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coe_update : (f.update i b : forall i : ι, β i) = Function.update f i b := rfl

@[simp]
/--
theorem `update_self` / 定理 `update_self`

English:
theorem update_self
  statement: f.update i (f i) = f
  proof: by
  ext
  simp

@[simp]

中文:
定理 update_self
  结论: f.update i (f i) = f
  证明: by
  ext
  simp

@[simp]
-/
theorem update_self : f.update i (f i) = f := by
  ext
  simp

@[simp]
/--
theorem `update_eq_erase` / 定理 `update_eq_erase`

English:
theorem update_eq_erase
  statement: f.update i 0 = f.erase i
  proof: by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]

中文:
定理 update_eq_erase
  结论: f.update i 0 = f.erase i
  证明: by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]

Depends on / 依赖: eq_or_ne, hi.symm
-/
theorem update_eq_erase : f.update i 0 = f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]

/--
theorem `update_eq_single_add_erase` / 定理 `update_eq_single_add_erase`

English:
theorem update_eq_single_add_erase
  statement: {β : ι -> Type*} [forall i, AddZeroClass (β i)] (f : Π₀ i, β i)
  proof: by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

中文:
定理 update_eq_single_add_erase
  结论: {β : ι -> 类型} [对任意 i, 加法零类 (β i)] (f : Π₀ i, β i)
  证明: by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

Depends on / 依赖: eq_or_ne, h.symm
-/
theorem update_eq_single_add_erase {β : ι -> Type*} [forall i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = single i b + f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

/--
theorem `update_eq_erase_add_single` / 定理 `update_eq_erase_add_single`

English:
theorem update_eq_erase_add_single
  statement: {β : ι -> Type*} [forall i, AddZeroClass (β i)] (f : Π₀ i, β i)
  proof: by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

中文:
定理 update_eq_erase_add_single
  结论: {β : ι -> 类型} [对任意 i, 加法零类 (β i)] (f : Π₀ i, β i)
  证明: by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

Depends on / 依赖: eq_or_ne, h.symm
-/
theorem update_eq_erase_add_single {β : ι -> Type*} [forall i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = f.erase i + single i b := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

/--
theorem `update_eq_sub_add_single` / 定理 `update_eq_sub_add_single`

English:
theorem update_eq_sub_add_single
  statement: {β : ι -> Type*} [forall i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι)
  proof: by
  rw [update_eq_erase_add_single f i b]; rw [erase_eq_sub_single f i]

中文:
定理 update_eq_sub_add_single
  结论: {β : ι -> 类型} [对任意 i, 加法群 (β i)] (f : Π₀ i, β i) (i : ι)
  证明: by
  rw [update_eq_erase_add_single f i b]; rw [erase_eq_sub_single f i]

Depends on / 依赖: erase_eq_sub_single, update_eq_erase_add_single
-/
theorem update_eq_sub_add_single {β : ι -> Type*} [forall i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι)
    (b : β i) : f.update i b = f - single i (f i) + single i b := by
  rw [update_eq_erase_add_single f i b]; rw [erase_eq_sub_single f i]

end Update

end Basic

section DecidableEq
variable [DecidableEq ι]

section AddMonoid

variable [forall i, AddZeroClass (β i)]

@[simp]
/--
theorem `single_add` / 定理 `single_add`

English:
theorem single_add
  given: (i : ι) (b₁ b₂ : β i)
  statement: single i (b₁ + b₂) = single i b₁ + single i b₂
  proof: (zipWith_single_single (fun _ => (· + ·)) _ b₁ b₂).symm

@[simp]

中文:
定理 single_add
  条件: (i : ι) (b₁ b₂ : β i)
  结论: single i (b₁ + b₂) = single i b₁ + single i b₂
  证明: (zipWith_single_single (fun _ => (· + ·)) _ b₁ b₂).symm

@[simp]

Depends on / 依赖: zipWith_single_single
-/
theorem single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
  (zipWith_single_single (fun _ => (· + ·)) _ b₁ b₂).symm

@[simp]
/--
theorem `erase_add` / 定理 `erase_add`

English:
theorem erase_add
  given: (i : ι) (f₁ f₂ : Π₀ i, β i)
  statement: erase i (f₁ + f₂) = erase i f₁ + erase i f₂
  proof: ext fun _ => by simp [ite_zero_add]

中文:
定理 erase_add
  条件: (i : ι) (f₁ f₂ : Π₀ i, β i)
  结论: erase i (f₁ + f₂) = erase i f₁ + erase i f₂
  证明: ext fun _ => by simp [ite_zero_add]

Depends on / 依赖: ite_zero_add
-/
theorem erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + erase i f₂ :=
  ext fun _ => by simp [ite_zero_add]

variable (β)

/-- `DFinsupp.single` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `singleAddHom` / `singleAddHom` 的定义

English:
definition singleAddHom
  signature: (i : ι)
  body: single i
  map_zero' := single_zero i
  map_add' := single_add i

中文:
定义 singleAddHom
  签名: (i : ι)
  定义体: single i
  map_zero' := single_zero i
  map_add' := single_add i

Depends on / 依赖: single
-/
def singleAddHom (i : ι) : β i ->+ Π₀ i, β i where
  toFun := single i
  map_zero' := single_zero i
  map_add' := single_add i

/-- `DFinsupp.erase` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `eraseAddHom` / `eraseAddHom` 的定义

English:
definition eraseAddHom
  signature: (i : ι)
  body: erase i
  map_zero' := erase_zero i
  map_add' := erase_add i

中文:
定义 eraseAddHom
  签名: (i : ι)
  定义体: erase i
  map_zero' := erase_zero i
  map_add' := erase_add i
-/
def eraseAddHom (i : ι) : (Π₀ i, β i) ->+ Π₀ i, β i where
  toFun := erase i
  map_zero' := erase_zero i
  map_add' := erase_add i

variable {β}

@[simp]
/--
theorem `single_neg` / 定理 `single_neg`

English:
theorem single_neg
  given: {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (x : β i)
  proof: (singleAddHom β i).map_neg x

@[simp]

中文:
定理 single_neg
  条件: {β : ι -> 类型v} [对任意 i, 加法群 (β i)] (i : ι) (x : β i)
  证明: (singleAddHom β i).map_neg x

@[simp]

Depends on / 依赖: map_neg, singleAddHom
-/
theorem single_neg {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (x : β i) :
    single i (-x) = -single i x :=
  (singleAddHom β i).map_neg x

@[simp]
/--
theorem `single_sub` / 定理 `single_sub`

English:
theorem single_sub
  given: {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (x y : β i)
  proof: (singleAddHom β i).map_sub x y

@[simp]

中文:
定理 single_sub
  条件: {β : ι -> 类型v} [对任意 i, 加法群 (β i)] (i : ι) (x y : β i)
  证明: (singleAddHom β i).map_sub x y

@[simp]

Depends on / 依赖: map_sub, singleAddHom
-/
theorem single_sub {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (x y : β i) :
    single i (x - y) = single i x - single i y :=
  (singleAddHom β i).map_sub x y

@[simp]
/--
theorem `erase_neg` / 定理 `erase_neg`

English:
theorem erase_neg
  given: {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (f : Π₀ i, β i)
  proof: (eraseAddHom β i).map_neg f

@[simp]

中文:
定理 erase_neg
  条件: {β : ι -> 类型v} [对任意 i, 加法群 (β i)] (i : ι) (f : Π₀ i, β i)
  证明: (eraseAddHom β i).map_neg f

@[simp]

Depends on / 依赖: eraseAddHom, map_neg
-/
theorem erase_neg {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (f : Π₀ i, β i) :
    (-f).erase i = -f.erase i :=
  (eraseAddHom β i).map_neg f

@[simp]
/--
theorem `erase_sub` / 定理 `erase_sub`

English:
theorem erase_sub
  given: {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (f g : Π₀ i, β i)
  proof: (eraseAddHom β i).map_sub f g

中文:
定理 erase_sub
  条件: {β : ι -> 类型v} [对任意 i, 加法群 (β i)] (i : ι) (f g : Π₀ i, β i)
  证明: (eraseAddHom β i).map_sub f g

Depends on / 依赖: eraseAddHom, map_sub
-/
theorem erase_sub {β : ι -> Type v} [forall i, AddGroup (β i)] (i : ι) (f g : Π₀ i, β i) :
    (f - g).erase i = f.erase i - g.erase i :=
  (eraseAddHom β i).map_sub f g

/--
theorem `single_add_erase` / 定理 `single_add_erase`

English:
theorem single_add_erase
  given: (i : ι) (f : Π₀ i, β i)
  statement: single i (f i) + f.erase i = f
  proof: ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, add_zero, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_add]

中文:
定理 single_add_erase
  条件: (i : ι) (f : Π₀ i, β i)
  结论: single i (f i) + f.erase i = f
  证明: ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, add_zero, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_add]

Depends on / 依赖: Ne.symm, add_apply, add_zero, dif_neg, dite_eq_ite, erase_apply, if_neg, if_true, single_apply, zero_add
-/
theorem single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, add_zero, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_add]

/--
theorem `erase_add_single` / 定理 `erase_add_single`

English:
theorem erase_add_single
  given: (i : ι) (f : Π₀ i, β i)
  statement: f.erase i + single i (f i) = f
  proof: ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, zero_add, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zero]

中文:
定理 erase_add_single
  条件: (i : ι) (f : Π₀ i, β i)
  结论: f.erase i + single i (f i) = f
  证明: ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, zero_add, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zero]

Depends on / 依赖: Ne.symm, add_apply, add_zero, dif_neg, dite_eq_ite, erase_apply, if_neg, if_true, single_apply, zero_add
-/
theorem erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, zero_add, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zero]

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {p : (Π₀ i, β i) -> Prop} (f : Π₀ i, β i) (h0 : p 0)
  proof: by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  obtain ⟨s, H⟩ := s
  induction s using Multiset.induction_on generalizing f with
  | empty =>
    have : f = 0 := funext fun i => (H i).resolve_left (Multiset.notMem_zero _)
    subst this
    exact h0
  | cons i s ih => ?_
  have H2 : p (erase i ⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : forall j, j in s ∨ ite (j = i) 0 (f j) = 0 := by grind
    have H3 : forall aux, (⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨i ::ₘ s, aux⟩⟩ : Π₀ i, β i) =
        ⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨s, H2⟩⟩ :=
      fun _ => ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : single i _ + _ = (⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀ i, β i) := single_add_erase _ _
  rw [← H3]
  change p (single i (f i) + _)
  rcases Classical.em (f i = 0) with h | h
  · rw [h, single_zero, zero_add]
    exact H2
  grind

中文:
定理 induction
  结论: {p : (Π₀ i, β i) -> 命题} (f : Π₀ i, β i) (h0 : p 0)
  证明: by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  obtain ⟨s, H⟩ := s
  induction s using Multiset.induction_on generalizing f with
  | empty =>
    have : f = 0 := funext fun i => (H i).resolve_left (Multiset.notMem_zero _)
    subst this
    exact h0
  | cons i s ih => ?_
  have H2 : p (erase i ⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : forall j, j in s ∨ ite (j = i) 0 (f j) = 0 := by grind
    have H3 : forall aux, (⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨i ::ₘ s, aux⟩⟩ : Π₀ i, β i) =
        ⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨s, H2⟩⟩ :=
      fun _ => ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : single i _ + _ = (⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀ i, β i) := single_add_erase _ _
  rw [← H3]
  change p (single i (f i) + _)
  rcases Classical.em (f i = 0) with h | h
  · rw [h, single_zero, zero_add]
    exact H2
  grind
-/
protected theorem induction {p : (Π₀ i, β i) -> Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : forall (i b) (f : Π₀ i, β i), f i = 0 -> b != 0 -> p f -> p (single i b + f)) : p f := by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  obtain ⟨s, H⟩ := s
  induction s using Multiset.induction_on generalizing f with
  | empty =>
    have : f = 0 := funext fun i => (H i).resolve_left (Multiset.notMem_zero _)
    subst this
    exact h0
  | cons i s ih => ?_
  have H2 : p (erase i ⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : forall j, j in s ∨ ite (j = i) 0 (f j) = 0 := by grind
    have H3 : forall aux, (⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨i ::ₘ s, aux⟩⟩ : Π₀ i, β i) =
        ⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨s, H2⟩⟩ :=
      fun _ => ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : single i _ + _ = (⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀ i, β i) := single_add_erase _ _
  rw [← H3]
  change p (single i (f i) + _)
  rcases Classical.em (f i = 0) with h | h
  · rw [h, single_zero, zero_add]
    exact H2
  grind

/--
theorem `induction₂` / 定理 `induction₂`

English:
theorem induction₂
  statement: {p : (Π₀ i, β i) -> Prop} (f : Π₀ i, β i) (h0 : p 0)
  proof: DFinsupp.induction f h0 fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f := by
      ext j; by_cases H : i = j
      · subst H
        simp [h1]
      · simp [H]
Eq.recOn h4 ha i b f h1 h2 h3

中文:
定理 induction₂
  结论: {p : (Π₀ i, β i) -> 命题} (f : Π₀ i, β i) (h0 : p 0)
  证明: DFinsupp.induction f h0 fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f := by
      ext j; by_cases H : i = j
      · subst H
        simp [h1]
      · simp [H]
Eq.recOn h4 ha i b f h1 h2 h3

Depends on / 依赖: DFinsupp, DFinsupp.induction, Eq.recOn, single
-/
theorem induction₂ {p : (Π₀ i, β i) -> Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : forall (i b) (f : Π₀ i, β i), f i = 0 -> b != 0 -> p f -> p (f + single i b)) : p f :=
  DFinsupp.induction f h0 fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f := by
      ext j; by_cases H : i = j
      · subst H
        simp [h1]
      · simp [H]
Eq.recOn h4 ha i b f h1 h2 h3

end AddMonoid

@[simp]
/--
theorem `mk_add` / 定理 `mk_add`

English:
theorem mk_add
  given: [forall i, AddZeroClass (β i)] {s : Finset ι} {x y : forall i : (↑s : Set ι), β i}
  proof: ext fun i => by simp only [add_apply, mk_apply]; split_ifs <;> [rfl; rw [zero_add]]

@[simp]

中文:
定理 mk_add
  条件: [对任意 i, 加法零类 (β i)] {s : 有限集 ι} {x y : 对任意 i : (↑s : 集合 ι), β i}
  证明: ext fun i => by simp only [add_apply, mk_apply]; split_ifs <;> [rfl; rw [zero_add]]

@[simp]

Depends on / 依赖: add_apply, mk_apply, split_ifs, zero_add
-/
theorem mk_add [forall i, AddZeroClass (β i)] {s : Finset ι} {x y : forall i : (↑s : Set ι), β i} :
    mk s (x + y) = mk s x + mk s y :=
  ext fun i => by simp only [add_apply, mk_apply]; split_ifs <;> [rfl; rw [zero_add]]

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: [forall i, Zero (β i)] {s : Finset ι}
  statement: mk s (0 : forall i : (↑s : Set ι), β i.1) = 0
  proof: ext fun i => by simp only [mk_apply]; split_ifs <;> rfl

@[simp]

中文:
定理 mk_zero
  条件: [对任意 i, 零 (β i)] {s : 有限集 ι}
  结论: mk s (0 : 对任意 i : (↑s : 集合 ι), β i.1) = 0
  证明: ext fun i => by simp only [mk_apply]; split_ifs <;> rfl

@[simp]

Depends on / 依赖: mk_apply, split_ifs
-/
theorem mk_zero [forall i, Zero (β i)] {s : Finset ι} : mk s (0 : forall i : (↑s : Set ι), β i.1) = 0 :=
  ext fun i => by simp only [mk_apply]; split_ifs <;> rfl

@[simp]
/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  given: [forall i, AddGroup (β i)] {s : Finset ι} {x : forall i : (↑s : Set ι), β i.1}
  proof: ext fun i => by simp only [neg_apply, mk_apply]; split_ifs <;> [rfl; rw [neg_zero]]

@[simp]

中文:
定理 mk_neg
  条件: [对任意 i, 加法群 (β i)] {s : 有限集 ι} {x : 对任意 i : (↑s : 集合 ι), β i.1}
  证明: ext fun i => by simp only [neg_apply, mk_apply]; split_ifs <;> [rfl; rw [neg_zero]]

@[simp]

Depends on / 依赖: mk_apply, neg_apply, neg_zero, split_ifs
-/
theorem mk_neg [forall i, AddGroup (β i)] {s : Finset ι} {x : forall i : (↑s : Set ι), β i.1} :
    mk s (-x) = -mk s x :=
  ext fun i => by simp only [neg_apply, mk_apply]; split_ifs <;> [rfl; rw [neg_zero]]

@[simp]
/--
theorem `mk_sub` / 定理 `mk_sub`

English:
theorem mk_sub
  given: [forall i, AddGroup (β i)] {s : Finset ι} {x y : forall i : (↑s : Set ι), β i.1}
  proof: ext fun i => by simp only [sub_apply, mk_apply]; split_ifs <;> [rfl; rw [sub_zero]]

中文:
定理 mk_sub
  条件: [对任意 i, 加法群 (β i)] {s : 有限集 ι} {x y : 对任意 i : (↑s : 集合 ι), β i.1}
  证明: ext fun i => by simp only [sub_apply, mk_apply]; split_ifs <;> [rfl; rw [sub_zero]]

Depends on / 依赖: mk_apply, split_ifs, sub_apply, sub_zero
-/
theorem mk_sub [forall i, AddGroup (β i)] {s : Finset ι} {x y : forall i : (↑s : Set ι), β i.1} :
    mk s (x - y) = mk s x - mk s y :=
  ext fun i => by simp only [sub_apply, mk_apply]; split_ifs <;> [rfl; rw [sub_zero]]

/--
Definition of `mkAddGroupHom` / `mkAddGroupHom` 的定义

English:
definition mkAddGroupHom
  signature: [forall i, AddGroup (β i)] (s : Finset ι)
  body: mk s
  map_zero' := mk_zero
  map_add' _ _ := mk_add

中文:
定义 mkAddGroupHom
  签名: [对任意 i, 加法群 (β i)] (s : 有限集 ι)
  定义体: mk s
  map_zero' := mk_zero
  map_add' _ _ := mk_add
-/
def mkAddGroupHom [forall i, AddGroup (β i)] (s : Finset ι) :
    (forall i : (s : Set ι), β ↑i) ->+ Π₀ i : ι, β i where
  toFun := mk s
  map_zero' := mk_zero
  map_add' _ _ := mk_add

section SupportBasic

variable [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (f : Π₀ i, β i)
  body: (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i != 0) by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (hx i).resolve_right h, h⟩

@[simp]

中文:
定义 support
  签名: (f : Π₀ i, β i)
  定义体: (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i != 0) by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (hx i).resolve_right h, h⟩

@[simp]

Depends on / 依赖: Finset, Finset.mem_filter, Multiset, Multiset.mem_toFinset, Multiset.toFinset, Subtype, Subtype.coe_mk, coe_mk, f.support, filter, mem_filter, mem_toFinset, resolve_right, support, toFinset, toFun_eq_coe
-/
def support (f : Π₀ i, β i) : Finset ι :=
(f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i != 0) by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 (hx i).resolve_right h, h⟩

@[simp]
/--
theorem `support_mk_subset` / 定理 `support_mk_subset`

English:
theorem support_mk_subset
  given: {s : Finset ι} {x : forall i : (↑s : Set ι), β i.1}
  statement: (mk s x).support subseteq s
  proof: fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]

中文:
定理 support_mk_subset
  条件: {s : 有限集 ι} {x : 对任意 i : (↑s : 集合 ι), β i.1}
  结论: (mk s x).support subseteq s
  证明: fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]

Depends on / 依赖: Finset, Finset.mem_filter, Multiset, Multiset.mem_toFinset, mem_filter, mem_toFinset
-/
theorem support_mk_subset {s : Finset ι} {x : forall i : (↑s : Set ι), β i.1} : (mk s x).support subseteq s :=
  fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]
/--
theorem `support_mk'_subset` / 定理 `support_mk'_subset`

English:
theorem support_mk'_subset
  given: {f : forall i, β i} {s : Multiset ι} {h}
  proof: fun i H =>
Multiset.mem_toFinset.1 by simpa using (Finset.mem_filter.1 H).1

@[simp, grind =]

中文:
定理 support_mk'_subset
  条件: {f : 对任意 i, β i} {s : Multiset ι} {h}
  证明: fun i H =>
Multiset.mem_toFinset.1 by simpa using (Finset.mem_filter.1 H).1

@[simp, grind =]
-/
theorem support_mk'_subset {f : forall i, β i} {s : Multiset ι} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩).support subseteq s.toFinset := fun i H =>
Multiset.mem_toFinset.1 by simpa using (Finset.mem_filter.1 H).1

@[simp, grind =]
/--
theorem `mem_support_toFun` / 定理 `mem_support_toFun`

English:
theorem mem_support_toFun
  given: (f : Π₀ i, β i) (i)
  statement: i in f.support ↔ f i != 0
  proof: by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter]; rw [Multiset.mem_toFinset]; rw [coe_mk']
  grind

中文:
定理 mem_support_toFun
  条件: (f : Π₀ i, β i) (i)
  结论: i in f.support ↔ f i != 0
  证明: by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter]; rw [Multiset.mem_toFinset]; rw [coe_mk']
  grind

Depends on / 依赖: Finset, Finset.mem_filter, Multiset, Multiset.mem_toFinset, Trunc.induction_on, Trunc.lift_mk, coe_mk, induction_on, lift_mk, mem_filter, mem_toFinset, support
-/
theorem mem_support_toFun (f : Π₀ i, β i) (i) : i in f.support ↔ f i != 0 := by
  obtain ⟨f, s⟩ := f
  induction s using Trunc.induction_on with | _ s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter]; rw [Multiset.mem_toFinset]; rw [coe_mk']
  grind

/--
theorem `eq_mk_support` / 定理 `eq_mk_support`

English:
theorem eq_mk_support
  given: (f : Π₀ i, β i)
  statement: f = mk f.support fun i => f i
  proof: by aesop

中文:
定理 eq_mk_support
  条件: (f : Π₀ i, β i)
  结论: f = mk f.support fun i => f i
  证明: by aesop
-/
theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support fun i => f i := by aesop

/-- Equivalence between dependent functions with finite support `s : Finset ι` and functions
`∀ i, {x : β i // x ≠ 0}`. -/
@[simps]
/--
Definition of `subtypeSupportEqEquiv` / `subtypeSupportEqEquiv` 的定义

English:
definition subtypeSupportEqEquiv
  signature: (s : Finset ι)
  body: ⟨mk s fun i => (f i).1, Finset.ext fun i => by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      i in support (mk s fun i => (f i).1) ↔ exists h : i in s, (f ⟨i, h⟩).1 != 0 := by simp
      _ ↔ exists _ : i in s, True := exists_congr fun h => (iff_true _).mpr (f _).2
      _ ↔ i in s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp

中文:
定义 subtypeSupportEqEquiv
  签名: (s : 有限集 ι)
  定义体: ⟨mk s fun i => (f i).1, Finset.ext fun i => by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      i in support (mk s fun i => (f i).1) ↔ exists h : i in s, (f ⟨i, h⟩).1 != 0 := by simp
      _ ↔ exists _ : i in s, True := exists_congr fun h => (iff_true _).mpr (f _).2
      _ ↔ i in s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp

Depends on / 依赖: Finset, Finset.ext
-/
def subtypeSupportEqEquiv (s : Finset ι) :
    {f : Π₀ i, β i // f.support = s} ≃ forall i : s, {x : β i // x != 0} where
toFun | ⟨f, hf⟩ => fun ⟨i, hi⟩ => ⟨f i, (f.mem_support_toFun i).1 hf.symm ▸ hi⟩
  invFun f := ⟨mk s fun i => (f i).1, Finset.ext fun i => by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      i in support (mk s fun i => (f i).1) ↔ exists h : i in s, (f ⟨i, h⟩).1 != 0 := by simp
      _ ↔ exists _ : i in s, True := exists_congr fun h => (iff_true _).mpr (f _).2
      _ ↔ i in s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp

/-- Equivalence between all dependent finitely supported functions `f : Π₀ i, β i` and type
of pairs `⟨s : Finset ι, f : ∀ i : s, {x : β i // x ≠ 0}⟩`. -/
@[simps! apply_fst apply_snd_coe]
/--
Definition of `sigmaFinsetFunEquiv` / `sigmaFinsetFunEquiv` 的定义

English:
definition sigmaFinsetFunEquiv
  signature: : (Π₀ i, β i) ≃ Σ s : Finset ι, forall i : s, {x : β i // x != 0}
  body: (Equiv.sigmaFiberEquiv DFinsupp.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]

中文:
定义 sigmaFinsetFunEquiv
  签名: : (Π₀ i, β i) ≃ Σ s : 有限集 ι, 对任意 i : s, {x : β i // x != 0}
  定义体: (Equiv.sigmaFiberEquiv DFinsupp.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.support, Equiv.sigmaFiberEquiv, sigmaCongrRight, sigmaFiberEquiv, subtypeSupportEqEquiv, support, symm.trans
-/
def sigmaFinsetFunEquiv : (Π₀ i, β i) ≃ Σ s : Finset ι, forall i : s, {x : β i // x != 0} :=
  (Equiv.sigmaFiberEquiv DFinsupp.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]
/--
theorem `support_zero` / 定理 `support_zero`

English:
theorem support_zero
  statement: (0 : Π₀ i, β i).support = ∅
  proof: rfl

中文:
定理 support_zero
  结论: (0 : Π₀ i, β i).support = ∅
  证明: rfl
-/
theorem support_zero : (0 : Π₀ i, β i).support = ∅ :=
  rfl

/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  given: {f : Π₀ i, β i} {i : ι}
  statement: i in f.support ↔ f i != 0
  proof: f.mem_support_toFun _

中文:
定理 mem_support_iff
  条件: {f : Π₀ i, β i} {i : ι}
  结论: i in f.support ↔ f i != 0
  证明: f.mem_support_toFun _

Depends on / 依赖: f.mem_support_toFun, mem_support_toFun
-/
theorem mem_support_iff {f : Π₀ i, β i} {i : ι} : i in f.support ↔ f i != 0 :=
  f.mem_support_toFun _

/--
theorem `notMem_support_iff` / 定理 `notMem_support_iff`

English:
theorem notMem_support_iff
  given: {f : Π₀ i, β i} {i : ι}
  statement: i ∉ f.support ↔ f i = 0
  proof: not_iff_comm.1 mem_support_iff.symm

@[simp]

中文:
定理 notMem_support_iff
  条件: {f : Π₀ i, β i} {i : ι}
  结论: i ∉ f.support ↔ f i = 0
  证明: not_iff_comm.1 mem_support_iff.symm

@[simp]

Depends on / 依赖: mem_support_iff, mem_support_iff.symm, not_iff_comm
-/
theorem notMem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp]
/--
theorem `support_eq_empty` / 定理 `support_eq_empty`

English:
theorem support_eq_empty
  given: {f : Π₀ i, β i}
  statement: f.support = ∅ ↔ f = 0
  proof: ⟨fun H => ext by simpa [Finset.ext_iff] using H, by simp +contextual⟩

中文:
定理 support_eq_empty
  条件: {f : Π₀ i, β i}
  结论: f.support = ∅ ↔ f = 0
  证明: ⟨fun H => ext by simpa [Finset.ext_iff] using H, by simp +contextual⟩

Depends on / 依赖: Finset, Finset.ext_iff, contextual, ext_iff
-/
theorem support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
⟨fun H => ext by simpa [Finset.ext_iff] using H, by simp +contextual⟩

/--
Instance `decidableZero` / 实例 `decidableZero`

English:
instance decidableZero
  signature: [forall (i) (x : β i), Decidable (x = 0)] (f : Π₀ i, β i)
  body: f.support'.recOnSubsingleton fun s =>
decidable_of_iff (forall i in s.val, f i = 0) by
      constructor
      case mpr => rintro rfl _ _; rfl
      case mp =>
        intro hs₁; ext i
        -- This instance prevent consuming `DecidableEq ι` in the next `by_cases`.
        let := Classical.propDecidable
        by_cases hs₂ : i in s.val
        case pos => exact hs₁ _ hs₂
        case neg => exact (s.prop i).resolve_left hs₂

中文:
实例 decidableZero
  签名: [对任意 (i) (x : β i), 可判定 (x = 0)] (f : Π₀ i, β i)
  定义体: f.support'.recOnSubsingleton fun s =>
decidable_of_iff (forall i in s.val, f i = 0) by
      constructor
      case mpr => rintro rfl _ _; rfl
      case mp =>
        intro hs₁; ext i
        -- This instance prevent consuming `DecidableEq ι` in the next `by_cases`.
        let := Classical.propDecidable
        by_cases hs₂ : i in s.val
        case pos => exact hs₁ _ hs₂
        case neg => exact (s.prop i).resolve_left hs₂

Depends on / 依赖: decidable_of_iff, f.support, recOnSubsingleton, s.val, support
-/
instance decidableZero [forall (i) (x : β i), Decidable (x = 0)] (f : Π₀ i, β i) : Decidable (f = 0) :=
f.support'.recOnSubsingleton fun s =>
decidable_of_iff (forall i in s.val, f i = 0) by
      constructor
      case mpr => rintro rfl _ _; rfl
      case mp =>
        intro hs₁; ext i
        -- This instance prevent consuming `DecidableEq ι` in the next `by_cases`.
        let := Classical.propDecidable
        by_cases hs₂ : i in s.val
        case pos => exact hs₁ _ hs₂
        case neg => exact (s.prop i).resolve_left hs₂

/--
theorem `support_subset_iff` / 定理 `support_subset_iff`

English:
theorem support_subset_iff
  given: {s : Set ι} {f : Π₀ i, β i}
  statement: ↑f.support subseteq s ↔ forall i ∉ s, f i = 0
  proof: by
  simpa [Set.subset_def] using forall_congr' fun i => not_imp_comm

@[simp]

中文:
定理 support_subset_iff
  条件: {s : 集合 ι} {f : Π₀ i, β i}
  结论: ↑f.support subseteq s ↔ 对任意 i ∉ s, f i = 0
  证明: by
  simpa [Set.subset_def] using forall_congr' fun i => not_imp_comm

@[simp]

Depends on / 依赖: Set.subset_def, forall_congr, not_imp_comm, subset_def
-/
theorem support_subset_iff {s : Set ι} {f : Π₀ i, β i} : ↑f.support subseteq s ↔ forall i ∉ s, f i = 0 := by
  simpa [Set.subset_def] using forall_congr' fun i => not_imp_comm

@[simp]
/--
theorem `support_single` / 定理 `support_single`

English:
theorem support_single
  given: {i : ι} {b : β i} (hb : b != 0)
  statement: (single i b).support = {i}
  proof: by
  grind

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single

中文:
定理 support_single
  条件: {i : ι} {b : β i} (hb : b != 0)
  结论: (single i b).support = {i}
  证明: by
  grind

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single
-/
theorem support_single {i : ι} {b : β i} (hb : b != 0) : (single i b).support = {i} := by
  grind

@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single

/--
theorem `support_single_subset` / 定理 `support_single_subset`

English:
theorem support_single_subset
  given: {i : ι} {b : β i}
  statement: (single i b).support subseteq {i}
  proof: support_mk'_subset

中文:
定理 support_single_subset
  条件: {i : ι} {b : β i}
  结论: (single i b).support subseteq {i}
  证明: support_mk'_subset

Depends on / 依赖: _subset, support_mk
-/
theorem support_single_subset {i : ι} {b : β i} : (single i b).support subseteq {i} :=
  support_mk'_subset

section MapRangeAndZipWith

variable [forall i, Zero (β₁ i)] [forall i, Zero (β₂ i)]

/--
theorem `mapRange_def` / 定理 `mapRange_def`

English:
theorem mapRange_def
  statement: [forall (i) (x : β₁ i), Decidable (x != 0)] {f : forall i, β₁ i -> β₂ i}
  proof: by
  ext
  simp_all

@[simp]

中文:
定理 mapRange_def
  结论: [对任意 (i) (x : β₁ i), 可判定 (x != 0)] {f : 对任意 i, β₁ i -> β₂ i}
  证明: by
  ext
  simp_all

@[simp]
-/
theorem mapRange_def [forall (i) (x : β₁ i), Decidable (x != 0)] {f : forall i, β₁ i -> β₂ i}
    {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    mapRange f hf g = mk g.support fun i => f i.1 (g i.1) := by
  ext
  simp_all

@[simp]
/--
theorem `mapRange_single` / 定理 `mapRange_single`

English:
theorem mapRange_single
  given: {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i}
  proof: DFinsupp.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]

omit [DecidableEq ι] in

中文:
定理 mapRange_single
  条件: {f : 对任意 i, β₁ i -> β₂ i} {hf : 对任意 i, f i 0 = 0} {i : ι} {b : β₁ i}
  证明: DFinsupp.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]

omit [DecidableEq ι] in

Depends on / 依赖: DFinsupp, DFinsupp.ext
-/
theorem mapRange_single {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} :
    mapRange f hf (single i b) = single i (f i b) :=
  DFinsupp.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]

omit [DecidableEq ι] in
/--
theorem `mapRange_injective` / 定理 `mapRange_injective`

English:
theorem mapRange_injective
  given: (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0)
  proof: by
  classical exact ⟨fun h i x y eq => single_injective (@h (single i x) (single i y) <| by
simpa using congr_arg _ eq), fun h _ _ eq => DFinsupp.ext fun i => h i congr( eq i)⟩

中文:
定理 mapRange_injective
  条件: (f : 对任意 i, β₁ i -> β₂ i) (hf : 对任意 i, f i 0 = 0)
  证明: by
  classical exact ⟨fun h i x y eq => single_injective (@h (single i x) (single i y) <| by
simpa using congr_arg _ eq), fun h _ _ eq => DFinsupp.ext fun i => h i congr( eq i)⟩

Depends on / 依赖: DFinsupp, DFinsupp.ext, classical, congr_arg, single, single_injective
-/
theorem mapRange_injective (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) :
    Function.Injective (mapRange f hf) ↔ forall i, Function.Injective (f i) := by
  classical exact ⟨fun h i x y eq => single_injective (@h (single i x) (single i y) <| by
simpa using congr_arg _ eq), fun h _ _ eq => DFinsupp.ext fun i => h i congr( eq i)⟩

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq ι] in
/--
theorem `mapRange_surjective` / 定理 `mapRange_surjective`

English:
theorem mapRange_surjective
  given: (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0)
  proof: by
  classical
  refine ⟨fun h i u => ?_, fun h x => ?_⟩
  · obtain ⟨x, hx⟩ := h (single i u)
    exact ⟨x i, by simpa using congr($hx i)⟩
  · obtain ⟨x, s, hs⟩ := x
    have (i : ι) : exists u : β₁ i, f i u = x i ∧ (x i = 0 -> u = 0) :=
      (eq_or_ne (x i) 0).elim
        (fun h => ⟨0, (hf i).trans h.symm, fun _ => rfl⟩)
        (fun h' => by
          obtain ⟨u, hu⟩ := h i (x i)
          exact ⟨u, hu, fun h'' => (h' h'').elim⟩)
    choose y hy using this
    refine ⟨⟨y, Trunc.mk ⟨s, fun i => ?_⟩⟩, ext fun i => ?_⟩
    · exact (hs i).imp_right (hy i).2
    · simp [(hy i).1]

中文:
定理 mapRange_surjective
  条件: (f : 对任意 i, β₁ i -> β₂ i) (hf : 对任意 i, f i 0 = 0)
  证明: by
  classical
  refine ⟨fun h i u => ?_, fun h x => ?_⟩
  · obtain ⟨x, hx⟩ := h (single i u)
    exact ⟨x i, by simpa using congr($hx i)⟩
  · obtain ⟨x, s, hs⟩ := x
    have (i : ι) : exists u : β₁ i, f i u = x i ∧ (x i = 0 -> u = 0) :=
      (eq_or_ne (x i) 0).elim
        (fun h => ⟨0, (hf i).trans h.symm, fun _ => rfl⟩)
        (fun h' => by
          obtain ⟨u, hu⟩ := h i (x i)
          exact ⟨u, hu, fun h'' => (h' h'').elim⟩)
    choose y hy using this
    refine ⟨⟨y, Trunc.mk ⟨s, fun i => ?_⟩⟩, ext fun i => ?_⟩
    · exact (hs i).imp_right (hy i).2
    · simp [(hy i).1]

Depends on / 依赖: Trunc.mk, classical, eq_or_ne, h.symm, imp_right, single
-/
theorem mapRange_surjective (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) :
    Function.Surjective (mapRange f hf) ↔ forall i, Function.Surjective (f i) := by
  classical
  refine ⟨fun h i u => ?_, fun h x => ?_⟩
  · obtain ⟨x, hx⟩ := h (single i u)
    exact ⟨x i, by simpa using congr($hx i)⟩
  · obtain ⟨x, s, hs⟩ := x
    have (i : ι) : exists u : β₁ i, f i u = x i ∧ (x i = 0 -> u = 0) :=
      (eq_or_ne (x i) 0).elim
        (fun h => ⟨0, (hf i).trans h.symm, fun _ => rfl⟩)
        (fun h' => by
          obtain ⟨u, hu⟩ := h i (x i)
          exact ⟨u, hu, fun h'' => (h' h'').elim⟩)
    choose y hy using this
    refine ⟨⟨y, Trunc.mk ⟨s, fun i => ?_⟩⟩, ext fun i => ?_⟩
    · exact (hs i).imp_right (hy i).2
    · simp [(hy i).1]

variable [forall (i) (x : β₁ i), Decidable (x != 0)] [forall (i) (x : β₂ i), Decidable (x != 0)]

/--
theorem `support_mapRange` / 定理 `support_mapRange`

English:
theorem support_mapRange
  given: {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i}
  proof: by simp [mapRange_def]

中文:
定理 support_mapRange
  条件: {f : 对任意 i, β₁ i -> β₂ i} {hf : 对任意 i, f i 0 = 0} {g : Π₀ i, β₁ i}
  证明: by simp [mapRange_def]

Depends on / 依赖: mapRange_def
-/
theorem support_mapRange {f : forall i, β₁ i -> β₂ i} {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    (mapRange f hf g).support subseteq g.support := by simp [mapRange_def]

/--
theorem `zipWith_def` / 定理 `zipWith_def`

English:
theorem zipWith_def
  statement: {ι : Type u} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}
  proof: by
  grind

中文:
定理 zipWith_def
  结论: {ι : 类型u} {β : ι -> 类型v} {β₁ : ι -> 类型v₁} {β₂ : ι -> 类型v₂}
  证明: by
  grind
-/
theorem zipWith_def {ι : Type u} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}
    [dec : DecidableEq ι] [forall i : ι, Zero (β i)] [forall i : ι, Zero (β₁ i)] [forall i : ι, Zero (β₂ i)]
    [forall (i : ι) (x : β₁ i), Decidable (x != 0)] [forall (i : ι) (x : β₂ i), Decidable (x != 0)]
    {f : forall i, β₁ i -> β₂ i -> β i} {hf : forall i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
    zipWith f hf g₁ g₂ = mk (g₁.support union g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) := by
  grind

/--
theorem `support_zipWith` / 定理 `support_zipWith`

English:
theorem support_zipWith
  statement: {f : forall i, β₁ i -> β₂ i -> β i} {hf : forall i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
  proof: by
  grind

中文:
定理 support_zipWith
  结论: {f : 对任意 i, β₁ i -> β₂ i -> β i} {hf : 对任意 i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
  证明: by
  grind
-/
theorem support_zipWith {f : forall i, β₁ i -> β₂ i -> β i} {hf : forall i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
    {g₂ : Π₀ i, β₂ i} : (zipWith f hf g₁ g₂).support subseteq g₁.support union g₂.support := by
  grind

end MapRangeAndZipWith

/--
theorem `erase_def` / 定理 `erase_def`

English:
theorem erase_def
  given: (i : ι) (f : Π₀ i, β i)
  statement: f.erase i = mk (f.support.erase i) fun j => f j.1
  proof: by
  grind

@[simp]

中文:
定理 erase_def
  条件: (i : ι) (f : Π₀ i, β i)
  结论: f.erase i = mk (f.support.erase i) fun j => f j.1
  证明: by
  grind

@[simp]
-/
theorem erase_def (i : ι) (f : Π₀ i, β i) : f.erase i = mk (f.support.erase i) fun j => f j.1 := by
  grind

@[simp]
/--
theorem `support_erase` / 定理 `support_erase`

English:
theorem support_erase
  given: (i : ι) (f : Π₀ i, β i)
  statement: (f.erase i).support = f.support.erase i
  proof: by
  ext
  simp

中文:
定理 support_erase
  条件: (i : ι) (f : Π₀ i, β i)
  结论: (f.erase i).support = f.support.erase i
  证明: by
  ext
  simp
-/
theorem support_erase (i : ι) (f : Π₀ i, β i) : (f.erase i).support = f.support.erase i := by
  ext
  simp

/--
theorem `support_update_ne_zero` / 定理 `support_update_ne_zero`

English:
theorem support_update_ne_zero
  given: (f : Π₀ i, β i) (i : ι) {b : β i} (h : b != 0)
  proof: by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]

中文:
定理 support_update_ne_zero
  条件: (f : Π₀ i, β i) (i : ι) {b : β i} (h : b != 0)
  证明: by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]

Depends on / 依赖: eq_or_ne, hi.symm
-/
theorem support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} (h : b != 0) :
    support (f.update i b) = insert i f.support := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]

/--
theorem `support_update` / 定理 `support_update`

English:
theorem support_update
  given: (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)]
  proof: by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]

中文:
定理 support_update
  条件: (f : Π₀ i, β i) (i : ι) (b : β i) [可判定 (b = 0)]
  证明: by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]

Depends on / 依赖: split_ifs, support_erase, support_update_ne_zero, update_eq_erase
-/
theorem support_update (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)] :
    support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support := by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]

section FilterAndSubtypeDomain

variable {p : ι -> Prop} [DecidablePred p]

/--
theorem `filter_def` / 定理 `filter_def`

English:
theorem filter_def
  given: (f : Π₀ i, β i)
  statement: f.filter p = mk (f.support.filter p) fun i => f i.1
  proof: by
  grind

@[simp]

中文:
定理 filter_def
  条件: (f : Π₀ i, β i)
  结论: f.filter p = mk (f.support.filter p) fun i => f i.1
  证明: by
  grind

@[simp]
-/
theorem filter_def (f : Π₀ i, β i) : f.filter p = mk (f.support.filter p) fun i => f i.1 := by
  grind

@[simp]
/--
theorem `support_filter` / 定理 `support_filter`

English:
theorem support_filter
  given: (f : Π₀ i, β i)
  statement: (f.filter p).support = {x in f.support | p x}
  proof: by
  grind

中文:
定理 support_filter
  条件: (f : Π₀ i, β i)
  结论: (f.filter p).support = {x in f.support | p x}
  证明: by
  grind
-/
theorem support_filter (f : Π₀ i, β i) : (f.filter p).support = {x in f.support | p x} := by
  grind

/--
theorem `subtypeDomain_def` / 定理 `subtypeDomain_def`

English:
theorem subtypeDomain_def
  given: (f : Π₀ i, β i)
  proof: by
  ext i; by_cases h2 : f i != 0 <;> try simp at h2; simp [h2]

@[simp]

中文:
定理 subtypeDomain_def
  条件: (f : Π₀ i, β i)
  证明: by
  ext i; by_cases h2 : f i != 0 <;> try simp at h2; simp [h2]

@[simp]
-/
theorem subtypeDomain_def (f : Π₀ i, β i) :
    f.subtypeDomain p = mk (f.support.subtype p) fun i => f i := by
  ext i; by_cases h2 : f i != 0 <;> try simp at h2; simp [h2]

@[simp]
/--
theorem `support_subtypeDomain` / 定理 `support_subtypeDomain`

English:
theorem support_subtypeDomain
  given: {f : Π₀ i, β i}
  proof: by
  ext
  simp

中文:
定理 support_subtypeDomain
  条件: {f : Π₀ i, β i}
  证明: by
  ext
  simp
-/
theorem support_subtypeDomain {f : Π₀ i, β i} :
    (subtypeDomain p f).support = f.support.subtype p := by
  ext
  simp

end FilterAndSubtypeDomain

end SupportBasic

/--
theorem `support_add` / 定理 `support_add`

English:
theorem support_add
  statement: [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: support_zipWith

@[simp]

中文:
定理 support_add
  结论: [对任意 i, 加法零类 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)]
  证明: support_zipWith

@[simp]

Depends on / 依赖: support_zipWith
-/
theorem support_add [forall i, AddZeroClass (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    {g₁ g₂ : Π₀ i, β i} : (g₁ + g₂).support subseteq g₁.support union g₂.support :=
  support_zipWith

@[simp]
/--
theorem `support_neg` / 定理 `support_neg`

English:
theorem support_neg
  given: [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i}
  proof: by ext; simp

中文:
定理 support_neg
  条件: [对任意 i, 加法群 (β i)] [对任意 (i) (x : β i), 可判定 (x != 0)] {f : Π₀ i, β i}
  证明: by ext; simp
-/
theorem support_neg [forall i, AddGroup (β i)] [forall (i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i} :
    support (-f) = support f := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Zero (β i)] [forall i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i)
  body: fun f g =>
  decidable_of_iff (f.support = g.support ∧ forall i in f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i in f.support then h₂ i h else by
      have hf : f i = 0 := by rwa [mem_support_iff, not_not] at h
      have hg : g i = 0 := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf]; rw [hg],
     by rintro rfl; simp⟩

中文:
实例 [对任意
  签名: i, 零 (β i)] [对任意 i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i)
  定义体: fun f g =>
  decidable_of_iff (f.support = g.support ∧ forall i in f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i in f.support then h₂ i h else by
      have hf : f i = 0 := by rwa [mem_support_iff, not_not] at h
      have hg : g i = 0 := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf]; rw [hg],
     by rintro rfl; simp⟩
-/
instance [forall i, Zero (β i)] [forall i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ forall i in f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i in f.support then h₂ i h else by
      have hf : f i = 0 := by rwa [mem_support_iff, not_not] at h
      have hg : g i = 0 := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf]; rw [hg],
     by rintro rfl; simp⟩

end DecidableEq

section Equiv

open Finset

variable {κ : Type*}

/--
Definition of `comapDomain` / `comapDomain` 的定义

English:
definition comapDomain
  signature: [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injective h)
  body: f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨(s.1.finite_toSet.preimage hh.injOn).toFinset.val, fun x =>
(s.prop (h x)).imp_left fun hx => (Set.Finite.mem_toFinset _).mpr hx⟩

@[simp]

中文:
定义 comapDomain
  签名: [对任意 i, 零 (β i)] (h : κ -> ι) (hh : 函数.单射 h)
  定义体: f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨(s.1.finite_toSet.preimage hh.injOn).toFinset.val, fun x =>
(s.prop (h x)).imp_left fun hx => (Set.Finite.mem_toFinset _).mpr hx⟩

@[simp]
-/
noncomputable def comapDomain [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injective h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨(s.1.finite_toSet.preimage hh.injOn).toFinset.val, fun x =>
(s.prop (h x)).imp_left fun hx => (Set.Finite.mem_toFinset _).mpr hx⟩

@[simp]
/--
theorem `comapDomain_apply` / 定理 `comapDomain_apply`

English:
theorem comapDomain_apply
  statement: [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injective h) (f : Π₀ i, β i)
  proof: rfl

@[simp]

中文:
定理 comapDomain_apply
  结论: [对任意 i, 零 (β i)] (h : κ -> ι) (hh : 函数.单射 h) (f : Π₀ i, β i)
  证明: rfl

@[simp]
-/
theorem comapDomain_apply [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injective h) (f : Π₀ i, β i)
    (k : κ) : comapDomain h hh f k = f (h k) :=
  rfl

@[simp]
/--
theorem `comapDomain_zero` / 定理 `comapDomain_zero`

English:
theorem comapDomain_zero
  given: [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injective h)
  proof: by
  ext
  rw [zero_apply]; rw [comapDomain_apply]; rw [zero_apply]

@[simp]

中文:
定理 comapDomain_zero
  条件: [对任意 i, 零 (β i)] (h : κ -> ι) (hh : 函数.单射 h)
  证明: by
  ext
  rw [zero_apply]; rw [comapDomain_apply]; rw [zero_apply]

@[simp]

Depends on / 依赖: comapDomain_apply, zero_apply
-/
theorem comapDomain_zero [forall i, Zero (β i)] (h : κ -> ι) (hh : Function.Injective h) :
    comapDomain h hh (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply]; rw [comapDomain_apply]; rw [zero_apply]

@[simp]
/--
theorem `comapDomain_add` / 定理 `comapDomain_add`

English:
theorem comapDomain_add
  statement: [forall i, AddZeroClass (β i)] (h : κ -> ι) (hh : Function.Injective h)
  proof: by
  ext
  rw [add_apply]; rw [comapDomain_apply]; rw [comapDomain_apply]; rw [comapDomain_apply]; rw [add_apply]

@[simp]

中文:
定理 comapDomain_add
  结论: [对任意 i, 加法零类 (β i)] (h : κ -> ι) (hh : 函数.单射 h)
  证明: by
  ext
  rw [add_apply]; rw [comapDomain_apply]; rw [comapDomain_apply]; rw [comapDomain_apply]; rw [add_apply]

@[simp]

Depends on / 依赖: add_apply, comapDomain_apply
-/
theorem comapDomain_add [forall i, AddZeroClass (β i)] (h : κ -> ι) (hh : Function.Injective h)
    (f g : Π₀ i, β i) : comapDomain h hh (f + g) = comapDomain h hh f + comapDomain h hh g := by
  ext
  rw [add_apply]; rw [comapDomain_apply]; rw [comapDomain_apply]; rw [comapDomain_apply]; rw [add_apply]

@[simp]
/--
theorem `comapDomain_single` / 定理 `comapDomain_single`

English:
theorem comapDomain_single
  statement: [DecidableEq ι] [DecidableEq κ] [forall i, Zero (β i)] (h : κ -> ι)
  proof: by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik, single_eq_of_ne (hh.ne hik)]

中文:
定理 comapDomain_single
  结论: [DecidableEq ι] [DecidableEq κ] [对任意 i, 零 (β i)] (h : κ -> ι)
  证明: by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik, single_eq_of_ne (hh.ne hik)]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, comapDomain_apply, eq_or_ne, hh.ne, single_eq_of_ne, single_eq_same
-/
theorem comapDomain_single [DecidableEq ι] [DecidableEq κ] [forall i, Zero (β i)] (h : κ -> ι)
    (hh : Function.Injective h) (k : κ) (x : β (h k)) :
    comapDomain h hh (single (h k) x) = single k x := by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik, single_eq_of_ne (hh.ne hik)]

/--
Definition of `comapDomain'` / `comapDomain'` 的定义

English:
definition comapDomain'
  signature: [forall i, Zero (β i)] (h : κ -> ι) {h' : ι -> κ} (hh' : Function.LeftInverse h' h)
  body: f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩

@[simp, grind =]

中文:
定义 comapDomain'
  签名: [对任意 i, 零 (β i)] (h : κ -> ι) {h' : ι -> κ} (hh' : 函数.左逆 h' h)
  定义体: f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩

@[simp, grind =]
-/
def comapDomain' [forall i, Zero (β i)] (h : κ -> ι) {h' : ι -> κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩

@[simp, grind =]
/--
theorem `comapDomain'_apply` / 定理 `comapDomain'_apply`

English:
theorem comapDomain'_apply
  statement: [forall i, Zero (β i)] (h : κ -> ι) {h' : ι -> κ}
  proof: rfl

@[simp]

中文:
定理 comapDomain'_apply
  结论: [对任意 i, 零 (β i)] (h : κ -> ι) {h' : ι -> κ}
  证明: rfl

@[simp]
-/
theorem comapDomain'_apply [forall i, Zero (β i)] (h : κ -> ι) {h' : ι -> κ}
    (hh' : Function.LeftInverse h' h) (f : Π₀ i, β i) (k : κ) : comapDomain' h hh' f k = f (h k) :=
  rfl

@[simp]
/--
theorem `comapDomain'_zero` / 定理 `comapDomain'_zero`

English:
theorem comapDomain'_zero
  statement: [forall i, Zero (β i)] (h : κ -> ι) {h' : ι -> κ}
  proof: by
  ext
  rw [zero_apply]; rw [comapDomain'_apply]; rw [zero_apply]

@[simp]

中文:
定理 comapDomain'_zero
  结论: [对任意 i, 零 (β i)] (h : κ -> ι) {h' : ι -> κ}
  证明: by
  ext
  rw [zero_apply]; rw [comapDomain'_apply]; rw [zero_apply]

@[simp]
-/
theorem comapDomain'_zero [forall i, Zero (β i)] (h : κ -> ι) {h' : ι -> κ}
    (hh' : Function.LeftInverse h' h) : comapDomain' h hh' (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply]; rw [comapDomain'_apply]; rw [zero_apply]

@[simp]
/--
theorem `comapDomain'_add` / 定理 `comapDomain'_add`

English:
theorem comapDomain'_add
  statement: [forall i, AddZeroClass (β i)] (h : κ -> ι) {h' : ι -> κ}
  proof: by
  ext
  rw [add_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [add_apply]

@[simp]

中文:
定理 comapDomain'_add
  结论: [对任意 i, 加法零类 (β i)] (h : κ -> ι) {h' : ι -> κ}
  证明: by
  ext
  rw [add_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [add_apply]

@[simp]
-/
theorem comapDomain'_add [forall i, AddZeroClass (β i)] (h : κ -> ι) {h' : ι -> κ}
    (hh' : Function.LeftInverse h' h) (f g : Π₀ i, β i) :
    comapDomain' h hh' (f + g) = comapDomain' h hh' f + comapDomain' h hh' g := by
  ext
  rw [add_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [add_apply]

@[simp]
/--
theorem `comapDomain'_single` / 定理 `comapDomain'_single`

English:
theorem comapDomain'_single
  statement: [DecidableEq ι] [DecidableEq κ] [forall i, Zero (β i)] (h : κ -> ι)
  proof: by
  grind

中文:
定理 comapDomain'_single
  结论: [DecidableEq ι] [DecidableEq κ] [对任意 i, 零 (β i)] (h : κ -> ι)
  证明: by
  grind
-/
theorem comapDomain'_single [DecidableEq ι] [DecidableEq κ] [forall i, Zero (β i)] (h : κ -> ι)
    {h' : ι -> κ} (hh' : Function.LeftInverse h' h) (k : κ) (x : β (h k)) :
    comapDomain' h hh' (single (h k) x) = single k x := by
  grind

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing terms of a dfinsupp.

This is the dfinsupp version of `Equiv.piCongrLeft'`. -/
@[simps apply]
/--
Definition of `equivCongrLeft` / `equivCongrLeft` 的定义

English:
definition equivCongrLeft
  signature: [forall i, Zero (β i)] (h : ι ≃ κ)
  body: comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i => (Equiv.cast_eq_iff_heq _).mpr <| by rw [Equiv.symm_apply_apply])
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [Equiv.cast_eq_iff_heq]; rw [h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply]; rw [mapRange_apply]; rw [comapDomain'_apply]; rw [Equiv.cast_eq_iff_heq]; rw [h.apply_symm_apply]

中文:
定义 equivCongrLeft
  签名: [对任意 i, 零 (β i)] (h : ι ≃ κ)
  定义体: comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i => (Equiv.cast_eq_iff_heq _).mpr <| by rw [Equiv.symm_apply_apply])
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [Equiv.cast_eq_iff_heq]; rw [h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply]; rw [mapRange_apply]; rw [comapDomain'_apply]; rw [Equiv.cast_eq_iff_heq]; rw [h.apply_symm_apply]

Depends on / 依赖: comapDomain, h.right_inv, h.symm, right_inv
-/
def equivCongrLeft [forall i, Zero (β i)] (h : ι ≃ κ) : (Π₀ i, β i) ≃ Π₀ k, β (h.symm k) where
  toFun := comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i => (Equiv.cast_eq_iff_heq _).mpr <| by rw [Equiv.symm_apply_apply])
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply]; rw [comapDomain'_apply]; rw [comapDomain'_apply]; rw [Equiv.cast_eq_iff_heq]; rw [h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply]; rw [mapRange_apply]; rw [comapDomain'_apply]; rw [Equiv.cast_eq_iff_heq]; rw [h.apply_symm_apply]

variable {α : Option ι -> Type v}

/--
Definition of `extendWith` / `extendWith` 的定义

English:
definition extendWith
  signature: [forall i, Zero (α i)] (a : α none) (f : Π₀ i, α (some i))
  body: fun i => match i with | none => a | some _ => f _
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s.1, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
(s.prop i).imp_left fun h => Multiset.mem_cons_of_mem Multiset.mem_map_of_mem _ h)
          i⟩

@[simp]

中文:
定义 extendWith
  签名: [对任意 i, 零 (α i)] (a : α none) (f : Π₀ i, α (some i))
  定义体: fun i => match i with | none => a | some _ => f _
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s.1, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
(s.prop i).imp_left fun h => Multiset.mem_cons_of_mem Multiset.mem_map_of_mem _ h)
          i⟩

@[simp]
-/
def extendWith [forall i, Zero (α i)] (a : α none) (f : Π₀ i, α (some i)) : Π₀ i, α i where
  toFun := fun i => match i with | none => a | some _ => f _
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s.1, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
(s.prop i).imp_left fun h => Multiset.mem_cons_of_mem Multiset.mem_map_of_mem _ h)
          i⟩

@[simp]
/--
theorem `extendWith_none` / 定理 `extendWith_none`

English:
theorem extendWith_none
  given: [forall i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none)
  proof: rfl

@[simp]

中文:
定理 extendWith_none
  条件: [对任意 i, 零 (α i)] (f : Π₀ i, α (some i)) (a : α none)
  证明: rfl

@[simp]
-/
theorem extendWith_none [forall i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) :
    f.extendWith a none = a :=
  rfl

@[simp]
/--
theorem `extendWith_some` / 定理 `extendWith_some`

English:
theorem extendWith_some
  given: [forall i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι)
  proof: rfl

@[simp]

中文:
定理 extendWith_some
  条件: [对任意 i, 零 (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι)
  证明: rfl

@[simp]
-/
theorem extendWith_some [forall i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i :=
  rfl

@[simp]
/--
theorem `extendWith_single_zero` / 定理 `extendWith_single_zero`

English:
theorem extendWith_single_zero
  given: [DecidableEq ι] [forall i, Zero (α i)] (i : ι) (x : α (some i))
  proof: by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _).symm]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne j i
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]

@[simp]

中文:
定理 extendWith_single_zero
  条件: [DecidableEq ι] [对任意 i, 零 (α i)] (i : ι) (x : α (some i))
  证明: by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _).symm]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne j i
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]

@[simp]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Option.some_injective, Option.some_ne_none, eq_or_ne, extendWith_none, extendWith_some, single_eq_of_ne, single_eq_same, some_injective, some_ne_none
-/
theorem extendWith_single_zero [DecidableEq ι] [forall i, Zero (α i)] (i : ι) (x : α (some i)) :
    (single i x).extendWith 0 = single (some i) x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _).symm]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne j i
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]

@[simp]
/--
theorem `extendWith_zero` / 定理 `extendWith_zero`

English:
theorem extendWith_zero
  given: [DecidableEq ι] [forall i, Zero (α i)] (x : α none)
  proof: by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _), zero_apply]

中文:
定理 extendWith_zero
  条件: [DecidableEq ι] [对任意 i, 零 (α i)] (x : α none)
  证明: by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _), zero_apply]

Depends on / 依赖: Option.some_ne_none, extendWith_none, extendWith_some, single_eq_of_ne, single_eq_same, some_ne_none, zero_apply
-/
theorem extendWith_zero [DecidableEq ι] [forall i, Zero (α i)] (x : α none) :
    (0 : Π₀ i, α (some i)).extendWith x = single none x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _), zero_apply]

/-- Bijection obtained by separating the term of index `none` of a dfinsupp over `Option ι`.

This is the dfinsupp version of `Equiv.piOptionEquivProd`. -/
@[simps]
/--
Definition of `equivProdDFinsupp` / `equivProdDFinsupp` 的定义

English:
definition equivProdDFinsupp
  signature: [forall i, Zero (α i)]
  body: (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; obtain - | i := i
    · rw [extendWith_none]
    · rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]

中文:
定义 equivProdDFinsupp
  签名: [对任意 i, 零 (α i)]
  定义体: (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; obtain - | i := i
    · rw [extendWith_none]
    · rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]

Depends on / 依赖: List.Lex, List.cons_head, Option.some_injective, _tail, comapDomain, cons_head, head_le_of_lt, replace, some_injective
-/
noncomputable def equivProdDFinsupp [forall i, Zero (α i)] :
    (Π₀ i, α i) ≃ α none × Π₀ i, α (some i) where
  toFun f := (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; obtain - | i := i
    · rw [extendWith_none]
    · rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]

/--
theorem `equivProdDFinsupp_add` / 定理 `equivProdDFinsupp_add`

English:
theorem equivProdDFinsupp_add
  given: [forall i, AddZeroClass (α i)] (f g : Π₀ i, α i)
  proof: Prod.ext (add_apply _ _ _) (comapDomain_add _ (Option.some_injective _) _ _)

中文:
定理 equivProdDFinsupp_add
  条件: [对任意 i, 加法零类 (α i)] (f g : Π₀ i, α i)
  证明: Prod.ext (add_apply _ _ _) (comapDomain_add _ (Option.some_injective _) _ _)

Depends on / 依赖: Option.some_injective, Prod.ext, add_apply, comapDomain_add, some_injective
-/
theorem equivProdDFinsupp_add [forall i, AddZeroClass (α i)] (f g : Π₀ i, α i) :
    equivProdDFinsupp (f + g) = equivProdDFinsupp f + equivProdDFinsupp g :=
  Prod.ext (add_apply _ _ _) (comapDomain_add _ (Option.some_injective _) _ _)

end Equiv

/-! ### Bundled versions of `DFinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/


section MapRange

variable [forall i, AddZeroClass (β i)] [forall i, AddZeroClass (β₁ i)] [forall i, AddZeroClass (β₂ i)]

/--
theorem `mapRange_add` / 定理 `mapRange_add`

English:
theorem mapRange_add
  statement: (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0)
  proof: by
  ext
  simp only [mapRange_apply f, coe_add, Pi.add_apply, hf']

中文:
定理 mapRange_add
  结论: (f : 对任意 i, β₁ i -> β₂ i) (hf : 对任意 i, f i 0 = 0)
  证明: by
  ext
  simp only [mapRange_apply f, coe_add, Pi.add_apply, hf']

Depends on / 依赖: Pi.add_apply, add_apply, coe_add, mapRange_apply
-/
theorem mapRange_add (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0)
    (hf' : forall i x y, f i (x + y) = f i x + f i y) (g₁ g₂ : Π₀ i, β₁ i) :
    mapRange f hf (g₁ + g₂) = mapRange f hf g₁ + mapRange f hf g₂ := by
  ext
  simp only [mapRange_apply f, coe_add, Pi.add_apply, hf']

/-- `DFinsupp.mapRange` as an `AddMonoidHom`. -/
@[simps apply]
/--
Definition of `mapRange.addMonoidHom` / `mapRange.addMonoidHom` 的定义

English:
definition mapRange.addMonoidHom
  signature: (f : forall i, β₁ i ->+ β₂ i)
  body: mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := mapRange_zero _ _
  map_add' := mapRange_add _ (fun i => (f i).map_zero) fun i => (f i).map_add

@[simp]

中文:
定义 mapRange.addMonoidHom
  签名: (f : 对任意 i, β₁ i ->+ β₂ i)
  定义体: mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := mapRange_zero _ _
  map_add' := mapRange_add _ (fun i => (f i).map_zero) fun i => (f i).map_add

@[simp]
-/
def mapRange.addMonoidHom (f : forall i, β₁ i ->+ β₂ i) : (Π₀ i, β₁ i) ->+ Π₀ i, β₂ i where
  toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := mapRange_zero _ _
  map_add' := mapRange_add _ (fun i => (f i).map_zero) fun i => (f i).map_add

@[simp]
/--
theorem `mapRange.addMonoidHom_id` / 定理 `mapRange.addMonoidHom_id`

English:
theorem mapRange.addMonoidHom_id
  proof: AddMonoidHom.ext mapRange_id

中文:
定理 mapRange.addMonoidHom_id
  证明: AddMonoidHom.ext mapRange_id
-/
theorem mapRange.addMonoidHom_id :
    (mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHom.id _ :=
  AddMonoidHom.ext mapRange_id

/--
theorem `mapRange.addMonoidHom_comp` / 定理 `mapRange.addMonoidHom_comp`

English:
theorem mapRange.addMonoidHom_comp
  given: (f : forall i, β₁ i ->+ β₂ i) (f₂ : forall i, β i ->+ β₁ i)
  proof: by
  ext
  simp

中文:
定理 mapRange.addMonoidHom_comp
  条件: (f : 对任意 i, β₁ i ->+ β₂ i) (f₂ : 对任意 i, β i ->+ β₁ i)
  证明: by
  ext
  simp
-/
theorem mapRange.addMonoidHom_comp (f : forall i, β₁ i ->+ β₂ i) (f₂ : forall i, β i ->+ β₁ i) :
    (mapRange.addMonoidHom fun i => (f i).comp (f₂ i)) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) := by
  ext
  simp

/-- `DFinsupp.mapRange.addMonoidHom` as an `AddEquiv`. -/
@[simps apply]
/--
Definition of `mapRange.addEquiv` / `mapRange.addEquiv` 的定义

English:
definition mapRange.addEquiv
  signature: (e : forall i, β₁ i ≃+ β₂ i)
  body: { mapRange.addMonoidHom fun i =>
      (e i).toAddMonoidHom with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero
    left_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.symm_comp_self]
          simp
    right_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.self_comp_symm]
          simp }

@[simp]

中文:
定义 mapRange.addEquiv
  签名: (e : 对任意 i, β₁ i ≃+ β₂ i)
  定义体: { mapRange.addMonoidHom fun i =>
      (e i).toAddMonoidHom with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero
    left_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.symm_comp_self]
          simp
    right_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.self_comp_symm]
          simp }

@[simp]
-/
def mapRange.addEquiv (e : forall i, β₁ i ≃+ β₂ i) : (Π₀ i, β₁ i) ≃+ Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i =>
      (e i).toAddMonoidHom with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero
    left_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.symm_comp_self]
          simp
    right_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.self_comp_symm]
          simp }

@[simp]
/--
theorem `mapRange.addEquiv_refl` / 定理 `mapRange.addEquiv_refl`

English:
theorem mapRange.addEquiv_refl
  proof: AddEquiv.ext mapRange_id

中文:
定理 mapRange.addEquiv_refl
  证明: AddEquiv.ext mapRange_id
-/
theorem mapRange.addEquiv_refl :
    (mapRange.addEquiv fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl _ :=
  AddEquiv.ext mapRange_id

/--
theorem `mapRange.addEquiv_trans` / 定理 `mapRange.addEquiv_trans`

English:
theorem mapRange.addEquiv_trans
  given: (f : forall i, β i ≃+ β₁ i) (f₂ : forall i, β₁ i ≃+ β₂ i)
  proof: by
  ext
  simp

@[simp]

中文:
定理 mapRange.addEquiv_trans
  条件: (f : 对任意 i, β i ≃+ β₁ i) (f₂ : 对任意 i, β₁ i ≃+ β₂ i)
  证明: by
  ext
  simp

@[simp]
-/
theorem mapRange.addEquiv_trans (f : forall i, β i ≃+ β₁ i) (f₂ : forall i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) := by
  ext
  simp

@[simp]
/--
theorem `mapRange.addEquiv_symm` / 定理 `mapRange.addEquiv_symm`

English:
theorem mapRange.addEquiv_symm
  given: (e : forall i, β₁ i ≃+ β₂ i)
  proof: rfl

中文:
定理 mapRange.addEquiv_symm
  条件: (e : 对任意 i, β₁ i ≃+ β₂ i)
  证明: rfl
-/
theorem mapRange.addEquiv_symm (e : forall i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv e).symm = mapRange.addEquiv fun i => (e i).symm :=
  rfl

end MapRange

end DFinsupp
