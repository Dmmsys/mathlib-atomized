/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.SetTheory.ZFC.PSet

/-!
# A model of ZFC

In this file, we model Zermelo-Fraenkel set theory (+ choice) using Lean's underlying type theory,
building on the pre-sets defined in `Mathlib/SetTheory/ZFC/PSet.lean`.

The theory of classes is developed in `Mathlib/SetTheory/ZFC/Class.lean`.

## Main definitions

* `ZFSet`: ZFC set. Defined as `PSet` quotiented by `PSet.Equiv`, the extensional equivalence.
* `ZFSet.choice`: Axiom of choice. Proved from Lean's axiom of choice.
* `ZFSet.omega`: The von Neumann ordinal `ω` as a `Set`.
* `Classical.allZFSetDefinable`: All functions are classically definable.
* `ZFSet.IsFunc` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `ZFSet.funs`: ZFC set of ZFC functions `x → y`.
* `ZFSet.Hereditarily p x`: Predicate that every set in the transitive closure of `x` has property
  `p`.

## Notes

To avoid confusion between the Lean `Set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`Set`" and "ZFC set".
-/

@[expose] public section


universe u

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
@[pp_with_univ, use_set_notation_for_order]
/--
Definition of `ZFSet` / `ZFSet` 的定义

English:
definition ZFSet
  signature: : Type (u + 1)
  body: Quotient PSet.setoid.{u}

中文:
定义 ZFSet
  签名: : Type (u + 1)
  定义体: Quotient PSet.setoid.{u}

Depends on / 依赖: PSet.setoid, Quotient, setoid
-/
def ZFSet : Type (u + 1) :=
  Quotient PSet.setoid.{u}

namespace ZFSet

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : PSet -> ZFSet
  body: Quotient.mk''

@[simp]

中文:
定义 mk
  签名: : PSet -> ZFSet
  定义体: Quotient.mk''

@[simp]

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk : PSet -> ZFSet :=
  Quotient.mk''

@[simp]
/--
theorem `mk_eq` / 定理 `mk_eq`

English:
theorem mk_eq
  given: (x : PSet)
  statement: @Eq ZFSet ⟦x⟧ (mk x)
  proof: rfl

@[simp]

中文:
定理 mk_eq
  条件: (x : PSet)
  结论: @Eq ZFSet ⟦x⟧ (mk x)
  证明: rfl

@[simp]
-/
theorem mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x) :=
  rfl

@[simp]
/--
theorem `mk_out` / 定理 `mk_out`

English:
theorem mk_out
  statement: forall x : ZFSet, mk x.out = x
  proof: Quotient.out_eq

中文:
定理 mk_out
  结论: 对任意 x : ZFSet, mk x.out = x
  证明: Quotient.out_eq

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem mk_out : forall x : ZFSet, mk x.out = x :=
  Quotient.out_eq

/--
Definition of `Definable` / `Definable` 的定义

English:
class Definable
  parameters: (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u})
  axioms and operations (2):
    - out : (Fin n -> PSet.{u}) -> PSet.{u}
    - mk_out(xs) : mk (out xs) = f (mk <| xs ·)  [default: by simp]

中文:
类 Definable
  参数: (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u})
  公理与运算 (2 个):
    - out : (Fin n -> PSet.{u}) -> PSet.{u}
    - mk_out(xs) : mk (out xs) = f (mk <| xs ·)  [默认: by simp]
-/
class Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where
  /-- Turns a definable function into an n-ary `PSet` function. -/
  out : (Fin n -> PSet.{u}) -> PSet.{u}
  /-- A set function `f` is the image of `Definable.out f`. -/
  mk_out xs : mk (out xs) = f (mk <| xs ·) := by simp

attribute [simp] Definable.mk_out

/--
Definition of `Definable₁` / `Definable₁` 的定义

English:
abbreviation Definable₁
  signature: (f : ZFSet.{u} -> ZFSet.{u})
  body: Definable 1 (fun s => f (s 0))

中文:
缩写 Definable₁
  签名: (f : ZFSet.{u} -> ZFSet.{u})
  定义体: Definable 1 (fun s => f (s 0))

Depends on / 依赖: Definable
-/
abbrev Definable₁ (f : ZFSet.{u} -> ZFSet.{u}) := Definable 1 (fun s => f (s 0))

/--
Definition of `Definable₁.mk` / `Definable₁.mk` 的定义

English:
abbreviation Definable₁.mk
  signature: {f : ZFSet.{u} -> ZFSet.{u}}
  body: out (xs 0)
  mk_out xs := mk_out (xs 0)

中文:
缩写 Definable₁.mk
  签名: {f : ZFSet.{u} -> ZFSet.{u}}
  定义体: out (xs 0)
  mk_out xs := mk_out (xs 0)
-/
abbrev Definable₁.mk {f : ZFSet.{u} -> ZFSet.{u}}
    (out : PSet.{u} -> PSet.{u}) (mk_out : forall x, ⟦out x⟧ = f ⟦x⟧) :
    Definable₁ f where
  out xs := out (xs 0)
  mk_out xs := mk_out (xs 0)

/--
Definition of `Definable₁.out` / `Definable₁.out` 的定义

English:
abbreviation Definable₁.out
  signature: (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f]
  body: fun x => Definable.out (fun s => f (s 0)) ![x]

中文:
缩写 Definable₁.out
  签名: (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f]
  定义体: fun x => Definable.out (fun s => f (s 0)) ![x]

Depends on / 依赖: Definable, Definable.out
-/
abbrev Definable₁.out (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f] :
    PSet.{u} -> PSet.{u} :=
  fun x => Definable.out (fun s => f (s 0)) ![x]

/--
lemma `Definable₁.mk_out` / 引理 `Definable₁.mk_out`

English:
lemma Definable₁.mk_out
  statement: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f]
  proof: Definable.mk_out ![x]

中文:
引理 Definable₁.mk_out
  结论: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f]
  证明: Definable.mk_out ![x]

Depends on / 依赖: Definable, Definable.mk_out, mk_out
-/
lemma Definable₁.mk_out {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f]
    {x : PSet} :
    .mk (out f x) = f (.mk x) :=
  Definable.mk_out ![x]

/--
Definition of `Definable₂` / `Definable₂` 的定义

English:
abbreviation Definable₂
  signature: (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
  body: Definable 2 (fun s => f (s 0) (s 1))

中文:
缩写 Definable₂
  签名: (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
  定义体: Definable 2 (fun s => f (s 0) (s 1))

Depends on / 依赖: Definable
-/
abbrev Definable₂ (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) := Definable 2 (fun s => f (s 0) (s 1))

/--
Definition of `Definable₂.mk` / `Definable₂.mk` 的定义

English:
abbreviation Definable₂.mk
  signature: {f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
  body: out (xs 0) (xs 1)
  mk_out xs := mk_out (xs 0) (xs 1)

中文:
缩写 Definable₂.mk
  签名: {f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
  定义体: out (xs 0) (xs 1)
  mk_out xs := mk_out (xs 0) (xs 1)
-/
abbrev Definable₂.mk {f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    (out : PSet.{u} -> PSet.{u} -> PSet.{u}) (mk_out : forall x y, ⟦out x y⟧ = f ⟦x⟧ ⟦y⟧) :
    Definable₂ f where
  out xs := out (xs 0) (xs 1)
  mk_out xs := mk_out (xs 0) (xs 1)

/--
Definition of `Definable₂.out` / `Definable₂.out` 的定义

English:
abbreviation Definable₂.out
  signature: (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) [Definable₂ f]
  body: fun x y => Definable.out (fun s => f (s 0) (s 1)) ![x, y]

中文:
缩写 Definable₂.out
  签名: (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) [Definable₂ f]
  定义体: fun x y => Definable.out (fun s => f (s 0) (s 1)) ![x, y]

Depends on / 依赖: Definable, Definable.out
-/
abbrev Definable₂.out (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) [Definable₂ f] :
    PSet.{u} -> PSet.{u} -> PSet.{u} :=
  fun x y => Definable.out (fun s => f (s 0) (s 1)) ![x, y]

/--
lemma `Definable₂.mk_out` / 引理 `Definable₂.mk_out`

English:
lemma Definable₂.mk_out
  statement: {f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}} [Definable₂ f]
  proof: Definable.mk_out ![x, y]

中文:
引理 Definable₂.mk_out
  结论: {f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}} [Definable₂ f]
  证明: Definable.mk_out ![x, y]

Depends on / 依赖: Definable, Definable.mk_out, mk_out
-/
lemma Definable₂.mk_out {f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}} [Definable₂ f]
    {x y : PSet} :
    .mk (out f x y) = f (.mk x) (.mk y) :=
  Definable.mk_out ![x, y]

instance (f) [Definable₁ f] (n g) [Definable n g] :
    Definable n (fun s => f (g s)) where
  out xs := Definable₁.out f (Definable.out g xs)

instance (f) [Definable₂ f] (n g₁ g₂) [Definable n g₁] [Definable n g₂] :
    Definable n (fun s => f (g₁ s) (g₂ s)) where
  out xs := Definable₂.out f (Definable.out g₁ xs) (Definable.out g₂ xs)

instance (n) (i) : Definable n (fun s => s i) where
  out s := s i

/--
lemma `Definable.out_equiv` / 引理 `Definable.out_equiv`

English:
lemma Definable.out_equiv
  statement: {n} (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) [Definable n f]
  proof: by
  rw [← Quotient.eq_iff_equiv]; rw [mk_eq]; rw [mk_eq]; rw [mk_out]; rw [mk_out]
  exact congrArg _ (funext fun i => Quotient.sound (h i))

中文:
引理 Definable.out_equiv
  结论: {n} (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) [Definable n f]
  证明: by
  rw [← Quotient.eq_iff_equiv]; rw [mk_eq]; rw [mk_eq]; rw [mk_out]; rw [mk_out]
  exact congrArg _ (funext fun i => Quotient.sound (h i))

Depends on / 依赖: Quotient, Quotient.eq_iff_equiv, Quotient.sound, eq_iff_equiv, mk_eq, mk_out
-/
lemma Definable.out_equiv {n} (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) [Definable n f]
    {xs ys : Fin n -> PSet} (h : forall i, xs i ≈ ys i) :
    out f xs ≈ out f ys := by
  rw [← Quotient.eq_iff_equiv]; rw [mk_eq]; rw [mk_eq]; rw [mk_out]; rw [mk_out]
  exact congrArg _ (funext fun i => Quotient.sound (h i))

/--
lemma `Definable₁.out_equiv` / 引理 `Definable₁.out_equiv`

English:
lemma Definable₁.out_equiv
  statement: (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f]
  proof: Definable.out_equiv _ (by simp [h])

中文:
引理 Definable₁.out_equiv
  结论: (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f]
  证明: Definable.out_equiv _ (by simp [h])

Depends on / 依赖: Definable, Definable.out_equiv, out_equiv
-/
lemma Definable₁.out_equiv (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f]
    {x y : PSet} (h : x ≈ y) :
    out f x ≈ out f y :=
  Definable.out_equiv _ (by simp [h])

/--
lemma `Definable₂.out_equiv` / 引理 `Definable₂.out_equiv`

English:
lemma Definable₂.out_equiv
  statement: (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) [Definable₂ f]
  proof: Definable.out_equiv _ (by simp [Fin.forall_fin_succ, h₁, h₂])

中文:
引理 Definable₂.out_equiv
  结论: (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) [Definable₂ f]
  证明: Definable.out_equiv _ (by simp [Fin.forall_fin_succ, h₁, h₂])

Depends on / 依赖: Definable, Definable.out_equiv, Fin.forall_fin_succ, forall_fin_succ, out_equiv
-/
lemma Definable₂.out_equiv (f : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) [Definable₂ f]
    {x₁ y₁ x₂ y₂ : PSet} (h₁ : x₁ ≈ y₁) (h₂ : x₂ ≈ y₂) :
    out f x₁ x₂ ≈ out f y₁ y₂ :=
  Definable.out_equiv _ (by simp [Fin.forall_fin_succ, h₁, h₂])

end ZFSet

namespace Classical

open PSet ZFSet

/-- All functions are classically definable. -/
@[instance_reducible]
/--
Definition of `allZFSetDefinable` / `allZFSetDefinable` 的定义

English:
definition allZFSetDefinable
  signature: {n} (F : (Fin n -> ZFSet.{u}) -> ZFSet.{u})
  body: (F (mk <| xs ·)).out

中文:
定义 allZFSetDefinable
  签名: {n} (F : (Fin n -> ZFSet.{u}) -> ZFSet.{u})
  定义体: (F (mk <| xs ·)).out
-/
noncomputable def allZFSetDefinable {n} (F : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) : Definable n F where
  out xs := (F (mk <| xs ·)).out

end Classical

namespace ZFSet
variable {x y z : ZFSet.{u}}

open PSet

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {x y : PSet}
  statement: mk x = mk y ↔ Equiv x y
  proof: Quotient.eq

中文:
定理 eq
  条件: {x y : PSet}
  结论: mk x = mk y ↔ Equiv x y
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem eq {x y : PSet} : mk x = mk y ↔ Equiv x y :=
  Quotient.eq

/--
theorem `sound` / 定理 `sound`

English:
theorem sound
  given: {x y : PSet} (h : PSet.Equiv x y)
  statement: mk x = mk y
  proof: Quotient.sound h

中文:
定理 sound
  条件: {x y : PSet} (h : PSet.Equiv x y)
  结论: mk x = mk y
  证明: Quotient.sound h

Depends on / 依赖: Quotient, Quotient.sound
-/
theorem sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y :=
  Quotient.sound h

/--
theorem `exact` / 定理 `exact`

English:
theorem exact
  given: {x y : PSet}
  statement: mk x = mk y -> PSet.Equiv x y
  proof: Quotient.exact

中文:
定理 exact
  条件: {x y : PSet}
  结论: mk x = mk y -> PSet.Equiv x y
  证明: Quotient.exact

Depends on / 依赖: Quotient, Quotient.exact
-/
theorem exact {x y : PSet} : mk x = mk y -> PSet.Equiv x y :=
  Quotient.exact

/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: (x : ZFSet)
  body: {y | Quotient.lift₂ (· in ·) (fun _ _ _ _ hx hy =>
    propext ((Mem.congr_left hx).trans (Mem.congr_right hy))) y x}

中文:
定义 toSet
  签名: (x : ZFSet)
  定义体: {y | Quotient.lift₂ (· in ·) (fun _ _ _ _ hx hy =>
    propext ((Mem.congr_left hx).trans (Mem.congr_right hy))) y x}

Depends on / 依赖: Mem.congr_left, Mem.congr_right, Quotient, Quotient.lift, congr_left, congr_right, propext
-/
def toSet (x : ZFSet) : Set ZFSet :=
  {y | Quotient.lift₂ (· in ·) (fun _ _ _ _ hx hy =>
    propext ((Mem.congr_left hx).trans (Mem.congr_right hy))) y x}

/--
lemma `ext_aux` / 引理 `ext_aux`

English:
lemma ext_aux
  statement: (forall z : ZFSet.{u}, z in x.toSet ↔ z in y.toSet) -> x = y
  proof: Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (Mem.ext fun w => h ⟦w⟧)

中文:
引理 ext_aux
  结论: (对任意 z : ZFSet.{u}, z in x.toSet ↔ z in y.toSet) -> x = y
  证明: Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (Mem.ext fun w => h ⟦w⟧)
-/
private lemma ext_aux : (forall z : ZFSet.{u}, z in x.toSet ↔ z in y.toSet) -> x = y :=
  Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (Mem.ext fun w => h ⟦w⟧)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike ZFSet.{u} ZFSet.{u}
  body: toSet
  coe_injective x y hxy := by apply ext_aux; intro z; exact congr(z in $hxy)

中文:
实例 :
  签名: SetLike ZFSet.{u} ZFSet.{u}
  定义体: toSet
  coe_injective x y hxy := by apply ext_aux; intro z; exact congr(z in $hxy)
-/
instance : SetLike ZFSet.{u} ZFSet.{u} where
  coe := toSet
  coe_injective x y hxy := by apply ext_aux; intro z; exact congr(z in $hxy)

/-- The membership relation for ZFC sets is inherited from the membership relation for pre-sets. -/
@[deprecated "use `in` notation" (since := "2026-03-16")]
/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: : ZFSet -> ZFSet -> Prop
  body: (· in ·)

@[simp]

中文:
定义 Mem
  签名: : ZFSet -> ZFSet -> 命题
  定义体: (· in ·)

@[simp]
-/
protected def Mem : ZFSet -> ZFSet -> Prop := (· in ·)

@[simp]
/--
theorem `mk_mem_iff` / 定理 `mk_mem_iff`

English:
theorem mk_mem_iff
  given: {x y : PSet}
  statement: mk x in mk y ↔ x in y
  proof: Iff.rfl

中文:
定理 mk_mem_iff
  条件: {x y : PSet}
  结论: mk x in mk y ↔ x in y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_mem_iff {x y : PSet} : mk x in mk y ↔ x in y :=
  Iff.rfl

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (forall z : ZFSet.{u}, z in x ↔ z in y) -> x = y
  proof: ext_aux

中文:
引理 ext
  结论: (对任意 z : ZFSet.{u}, z in x ↔ z in y) -> x = y
  证明: ext_aux
-/
@[ext] lemma ext : (forall z : ZFSet.{u}, z in x ↔ z in y) -> x = y := ext_aux

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder ZFSet.{u}
  body: .ofSetLike ZFSet.{u} ZFSet.{u}

中文:
实例 :
  签名: PartialOrder ZFSet.{u}
  定义体: .ofSetLike ZFSet.{u} ZFSet.{u}

Depends on / 依赖: ofSetLike
-/
instance : PartialOrder ZFSet.{u} := .ofSetLike ZFSet.{u} ZFSet.{u}

/--
Instance `small_coe` / 实例 `small_coe`

English:
instance small_coe
  signature: (x : ZFSet.{u})
  body: Quotient.inductionOn x fun a => by
let f (i : a.Type) : mk a := ⟨mk a.Func i, func_mem a i⟩
    suffices Function.Surjective f by exact small_of_surjective this
    rintro ⟨y, hb⟩
    induction y using Quotient.inductionOn
    obtain ⟨i, h⟩ := hb
    exact ⟨i, Subtype.coe_injective (Quotient.sound h

中文:
实例 small_coe
  签名: (x : ZFSet.{u})
  定义体: Quotient.inductionOn x fun a => by
let f (i : a.Type) : mk a := ⟨mk a.Func i, func_mem a i⟩
    suffices Function.Surjective f by exact small_of_surjective this
    rintro ⟨y, hb⟩
    induction y using Quotient.inductionOn
    obtain ⟨i, h⟩ := hb
    exact ⟨i, Subtype.coe_injective (Quotient.sound h

Depends on / 依赖: Function, Function.Surjective, Quotient, Quotient.inductionOn, Quotient.sound, Subtype, Subtype.coe_injective, Surjective, a.Func, a.Type, coe_injective, func_mem, h.symm, inductionOn, small_of_surjective
-/
instance small_coe (x : ZFSet.{u}) : Small.{u} x :=
  Quotient.inductionOn x fun a => by
let f (i : a.Type) : mk a := ⟨mk a.Func i, func_mem a i⟩
    suffices Function.Surjective f by exact small_of_surjective this
    rintro ⟨y, hb⟩
    induction y using Quotient.inductionOn
    obtain ⟨i, h⟩ := hb
    exact ⟨i, Subtype.coe_injective (Quotient.sound h.symm)⟩

/--
Definition of `Nonempty` / `Nonempty` 的定义

English:
definition Nonempty
  signature: (u : ZFSet.{u})
  body: (u : Set ZFSet.{u}).Nonempty

中文:
定义 Nonempty
  签名: (u : ZFSet.{u})
  定义体: (u : Set ZFSet.{u}).Nonempty
-/
protected def Nonempty (u : ZFSet.{u}) : Prop := (u : Set ZFSet.{u}).Nonempty

/--
theorem `nonempty_def` / 定理 `nonempty_def`

English:
theorem nonempty_def
  given: (u : ZFSet)
  statement: u.Nonempty ↔ exists x, x in u
  proof: Iff.rfl

中文:
定理 nonempty_def
  条件: (u : ZFSet)
  结论: u.Nonempty ↔ 存在 x, x in u
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem nonempty_def (u : ZFSet) : u.Nonempty ↔ exists x, x in u :=
  Iff.rfl

/--
theorem `nonempty_of_mem` / 定理 `nonempty_of_mem`

English:
theorem nonempty_of_mem
  given: {x u : ZFSet} (h : x in u)
  statement: u.Nonempty
  proof: ⟨x, h⟩

中文:
定理 nonempty_of_mem
  条件: {x u : ZFSet} (h : x in u)
  结论: u.Nonempty
  证明: ⟨x, h⟩
-/
theorem nonempty_of_mem {x u : ZFSet} (h : x in u) : u.Nonempty :=
  ⟨x, h⟩

/--
lemma `nonempty_coe` / 引理 `nonempty_coe`

English:
lemma nonempty_coe
  statement: (x : Set ZFSet.{u}).Nonempty ↔ x.Nonempty
  proof: .rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]

中文:
引理 nonempty_coe
  结论: (x : Set ZFSet.{u}).Nonempty ↔ x.Nonempty
  证明: .rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
-/
@[simp, norm_cast] lemma nonempty_coe : (x : Set ZFSet.{u}).Nonempty ↔ x.Nonempty := .rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  statement: x <= y ↔ x subseteq y
  proof: .rfl
@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]

中文:
引理 le_def
  结论: x <= y ↔ x subseteq y
  证明: .rfl
@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
-/
lemma le_def : x <= y ↔ x subseteq y := .rfl
@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/--
lemma `lt_def` / 引理 `lt_def`

English:
lemma lt_def
  statement: x < y ↔ x ⊂ y
  proof: .rfl

中文:
引理 lt_def
  结论: x < y ↔ x ⊂ y
  证明: .rfl
-/
lemma lt_def : x < y ↔ x ⊂ y := .rfl

/--
theorem `subset_def` / 定理 `subset_def`

English:
theorem subset_def
  given: {x y : ZFSet.{u}}
  statement: x subseteq y ↔ forall ⦃z⦄, z in x -> z in y
  proof: Iff.rfl

中文:
定理 subset_def
  条件: {x y : ZFSet.{u}}
  结论: x subseteq y ↔ 对任意 ⦃z⦄, z in x -> z in y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subset_def {x y : ZFSet.{u}} : x subseteq y ↔ forall ⦃z⦄, z in x -> z in y :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Refl ZFSet (· subseteq ·)
  body: ⟨fun _ _ => id⟩

中文:
实例 :
  签名: @Std.Refl ZFSet (· subseteq ·)
  定义体: ⟨fun _ _ => id⟩
-/
instance : @Std.Refl ZFSet (· subseteq ·) :=
  ⟨fun _ _ => id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrans ZFSet (· subseteq ·)
  body: ⟨fun _ _ _ hxy hyz _ ha => hyz (hxy ha)⟩

@[simp]

中文:
实例 :
  签名: IsTrans ZFSet (· subseteq ·)
  定义体: ⟨fun _ _ _ hxy hyz _ ha => hyz (hxy ha)⟩

@[simp]
-/
instance : IsTrans ZFSet (· subseteq ·) :=
  ⟨fun _ _ _ hxy hyz _ ha => hyz (hxy ha)⟩

@[simp]
/--
theorem `subset_iff` / 定理 `subset_iff`

English:
theorem subset_iff
  statement: forall {x y : PSet}, mk x subseteq mk y ↔ x subseteq y
  proof: h a
        ⟨b, za.trans ab⟩⟩

中文:
定理 subset_iff
  结论: 对任意 {x y : PSet}, mk x subseteq mk y ↔ x subseteq y
  证明: h a
        ⟨b, za.trans ab⟩⟩
-/
theorem subset_iff : forall {x y : PSet}, mk x subseteq mk y ↔ x subseteq y
  | ⟨_, A⟩, ⟨_, _⟩ =>
    ⟨fun h a => @h ⟦A a⟧ (Mem.mk A a), fun h z =>
      Quotient.inductionOn z fun _ ⟨a, za⟩ =>
        let ⟨b, ab⟩ := h a
        ⟨b, za.trans ab⟩⟩

/--
lemma `coe_subset_coe` / 引理 `coe_subset_coe`

English:
lemma coe_subset_coe
  statement: (x : Set ZFSet.{u}) subseteq y ↔ x subseteq y
  proof: SetLike.coe_subset_coe

中文:
引理 coe_subset_coe
  结论: (x : Set ZFSet.{u}) subseteq y ↔ x subseteq y
  证明: SetLike.coe_subset_coe

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, coe_subset_coe
-/
lemma coe_subset_coe : (x : Set ZFSet.{u}) subseteq y ↔ x subseteq y := SetLike.coe_subset_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Antisymm ZFSet (· subseteq ·)
  body: ⟨@le_antisymm ZFSet _⟩

中文:
实例 :
  签名: @Std.Antisymm ZFSet (· subseteq ·)
  定义体: ⟨@le_antisymm ZFSet _⟩

Depends on / 依赖: le_antisymm
-/
instance : @Std.Antisymm ZFSet (· subseteq ·) :=
  ⟨@le_antisymm ZFSet _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNonstrictStrictOrder ZFSet (· subseteq ·) (· ⊂ ·)
  body: ⟨fun _ _ => Iff.rfl⟩

中文:
实例 :
  签名: IsNonstrictStrictOrder ZFSet (· subseteq ·) (· ⊂ ·)
  定义体: ⟨fun _ _ => Iff.rfl⟩

Depends on / 依赖: Iff.rfl
-/
instance : IsNonstrictStrictOrder ZFSet (· subseteq ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : ZFSet
  body: mk ∅

中文:
定义 empty
  签名: : ZFSet
  定义体: mk ∅
-/
protected def empty : ZFSet :=
  mk ∅

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection ZFSet
  body: ⟨ZFSet.empty⟩

中文:
实例 :
  签名: EmptyCollection ZFSet
  定义体: ⟨ZFSet.empty⟩

Depends on / 依赖: ZFSet.empty
-/
instance : EmptyCollection ZFSet :=
  ⟨ZFSet.empty⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited ZFSet
  body: ⟨∅⟩

@[simp]

中文:
实例 :
  签名: Inhabited ZFSet
  定义体: ⟨∅⟩

@[simp]
-/
instance : Inhabited ZFSet :=
  ⟨∅⟩

@[simp]
/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: (x)
  statement: x ∉ (∅ : ZFSet.{u})
  proof: Quotient.inductionOn x PSet.notMem_empty

中文:
定理 notMem_empty
  条件: (x)
  结论: x ∉ (∅ : ZFSet.{u})
  证明: Quotient.inductionOn x PSet.notMem_empty

Depends on / 依赖: PSet.notMem_empty, Quotient, Quotient.inductionOn, inductionOn, notMem_empty
-/
theorem notMem_empty (x) : x ∉ (∅ : ZFSet.{u}) :=
  Quotient.inductionOn x PSet.notMem_empty

/--
lemma `coe_empty` / 引理 `coe_empty`

English:
lemma coe_empty
  statement: ((∅ : ZFSet.{u}) : Set ZFSet.{u}) = ∅
  proof: by ext; simp

@[simp]

中文:
引理 coe_empty
  结论: ((∅ : ZFSet.{u}) : Set ZFSet.{u}) = ∅
  证明: by ext; simp

@[simp]
-/
@[simp, norm_cast] lemma coe_empty : ((∅ : ZFSet.{u}) : Set ZFSet.{u}) = ∅ := by ext; simp

@[simp]
/--
theorem `empty_subset` / 定理 `empty_subset`

English:
theorem empty_subset
  given: (x : ZFSet.{u})
  statement: (∅ : ZFSet) subseteq x
  proof: Quotient.inductionOn x fun y => subset_iff.2 PSet.empty_subset y

@[simp]

中文:
定理 empty_subset
  条件: (x : ZFSet.{u})
  结论: (∅ : ZFSet) subseteq x
  证明: Quotient.inductionOn x fun y => subset_iff.2 PSet.empty_subset y

@[simp]

Depends on / 依赖: PSet.empty_subset, Quotient, Quotient.inductionOn, empty_subset, inductionOn, subset_iff
-/
theorem empty_subset (x : ZFSet.{u}) : (∅ : ZFSet) subseteq x :=
Quotient.inductionOn x fun y => subset_iff.2 PSet.empty_subset y

@[simp]
/--
theorem `not_nonempty_empty` / 定理 `not_nonempty_empty`

English:
theorem not_nonempty_empty
  statement: ¬ZFSet.Nonempty ∅
  proof: by simp [ZFSet.Nonempty]

@[simp]

中文:
定理 not_nonempty_empty
  结论: ¬ZFSet.Nonempty ∅
  证明: by simp [ZFSet.Nonempty]

@[simp]

Depends on / 依赖: Nonempty, ZFSet.Nonempty
-/
theorem not_nonempty_empty : ¬ZFSet.Nonempty ∅ := by simp [ZFSet.Nonempty]

@[simp]
/--
theorem `nonempty_mk_iff` / 定理 `nonempty_mk_iff`

English:
theorem nonempty_mk_iff
  given: {x : PSet}
  statement: (mk x).Nonempty ↔ x.Nonempty
  proof: by
  refine ⟨?_, fun ⟨a, h⟩ => ⟨mk a, h⟩⟩
  rintro ⟨a, h⟩
  induction a using Quotient.inductionOn
  exact ⟨_, h⟩

中文:
定理 nonempty_mk_iff
  条件: {x : PSet}
  结论: (mk x).Nonempty ↔ x.Nonempty
  证明: by
  refine ⟨?_, fun ⟨a, h⟩ => ⟨mk a, h⟩⟩
  rintro ⟨a, h⟩
  induction a using Quotient.inductionOn
  exact ⟨_, h⟩

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem nonempty_mk_iff {x : PSet} : (mk x).Nonempty ↔ x.Nonempty := by
  refine ⟨?_, fun ⟨a, h⟩ => ⟨mk a, h⟩⟩
  rintro ⟨a, h⟩
  induction a using Quotient.inductionOn
  exact ⟨_, h⟩

/--
theorem `eq_empty` / 定理 `eq_empty`

English:
theorem eq_empty
  given: (x : ZFSet.{u})
  statement: x = ∅ ↔ forall y : ZFSet.{u}, y ∉ x
  proof: by
  simp [ZFSet.ext_iff]

中文:
定理 eq_empty
  条件: (x : ZFSet.{u})
  结论: x = ∅ ↔ 对任意 y : ZFSet.{u}, y ∉ x
  证明: by
  simp [ZFSet.ext_iff]

Depends on / 依赖: ZFSet.ext_iff, ext_iff
-/
theorem eq_empty (x : ZFSet.{u}) : x = ∅ ↔ forall y : ZFSet.{u}, y ∉ x := by
  simp [ZFSet.ext_iff]

/--
theorem `eq_empty_or_nonempty` / 定理 `eq_empty_or_nonempty`

English:
theorem eq_empty_or_nonempty
  given: (u : ZFSet)
  statement: u = ∅ ∨ u.Nonempty
  proof: by
  rw [eq_empty]; rw [← not_exists]
  apply em'

中文:
定理 eq_empty_or_nonempty
  条件: (u : ZFSet)
  结论: u = ∅ ∨ u.Nonempty
  证明: by
  rw [eq_empty]; rw [← not_exists]
  apply em'

Depends on / 依赖: eq_empty, not_exists
-/
theorem eq_empty_or_nonempty (u : ZFSet) : u = ∅ ∨ u.Nonempty := by
  rw [eq_empty]; rw [← not_exists]
  apply em'

/--
Definition of `Insert` / `Insert` 的定义

English:
definition Insert
  signature: : ZFSet -> ZFSet -> ZFSet
  body: Quotient.map₂ PSet.insert
    fun _ _ uv ⟨_, _⟩ ⟨_, _⟩ ⟨αβ, βα⟩ =>
      ⟨fun o =>
        match o with
        | some a =>
          let ⟨b, hb⟩ := αβ a
          ⟨some b, hb⟩
        | none => ⟨none, uv⟩,
        fun o =>
        match o with
        | some b =>
          let ⟨a, ha⟩ := βα b
     

中文:
定义 Insert
  签名: : ZFSet -> ZFSet -> ZFSet
  定义体: Quotient.map₂ PSet.insert
    fun _ _ uv ⟨_, _⟩ ⟨_, _⟩ ⟨αβ, βα⟩ =>
      ⟨fun o =>
        match o with
        | some a =>
          let ⟨b, hb⟩ := αβ a
          ⟨some b, hb⟩
        | none => ⟨none, uv⟩,
        fun o =>
        match o with
        | some b =>
          let ⟨a, ha⟩ := βα b
     
-/
protected def Insert : ZFSet -> ZFSet -> ZFSet :=
  Quotient.map₂ PSet.insert
    fun _ _ uv ⟨_, _⟩ ⟨_, _⟩ ⟨αβ, βα⟩ =>
      ⟨fun o =>
        match o with
        | some a =>
          let ⟨b, hb⟩ := αβ a
          ⟨some b, hb⟩
        | none => ⟨none, uv⟩,
        fun o =>
        match o with
        | some b =>
          let ⟨a, ha⟩ := βα b
          ⟨some a, ha⟩
        | none => ⟨none, uv⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert ZFSet ZFSet
  body: ⟨ZFSet.Insert⟩

中文:
实例 :
  签名: Insert ZFSet ZFSet
  定义体: ⟨ZFSet.Insert⟩

Depends on / 依赖: Insert, ZFSet.Insert
-/
instance : Insert ZFSet ZFSet :=
  ⟨ZFSet.Insert⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton ZFSet ZFSet
  body: ⟨fun x => insert x ∅⟩

中文:
实例 :
  签名: Singleton ZFSet ZFSet
  定义体: ⟨fun x => insert x ∅⟩

Depends on / 依赖: insert
-/
instance : Singleton ZFSet ZFSet :=
  ⟨fun x => insert x ∅⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulSingleton ZFSet ZFSet
  body: ⟨fun _ => rfl⟩

@[simp]

中文:
实例 :
  签名: LawfulSingleton ZFSet ZFSet
  定义体: ⟨fun _ => rfl⟩

@[simp]
-/
instance : LawfulSingleton ZFSet ZFSet :=
  ⟨fun _ => rfl⟩

@[simp]
/--
theorem `mem_insert_iff` / 定理 `mem_insert_iff`

English:
theorem mem_insert_iff
  given: {x y z : ZFSet.{u}}
  statement: x in insert y z ↔ x = y ∨ x in z
  proof: Quotient.inductionOn₃ x y z fun _ _ _ => PSet.mem_insert_iff.trans (or_congr_left eq.symm)

中文:
定理 mem_insert_iff
  条件: {x y z : ZFSet.{u}}
  结论: x in insert y z ↔ x = y ∨ x in z
  证明: Quotient.inductionOn₃ x y z fun _ _ _ => PSet.mem_insert_iff.trans (or_congr_left eq.symm)

Depends on / 依赖: PSet.mem_insert_iff.trans, Quotient, Quotient.inductionOn, eq.symm, mem_insert_iff, or_congr_left
-/
theorem mem_insert_iff {x y z : ZFSet.{u}} : x in insert y z ↔ x = y ∨ x in z :=
  Quotient.inductionOn₃ x y z fun _ _ _ => PSet.mem_insert_iff.trans (or_congr_left eq.symm)

/--
theorem `mem_insert` / 定理 `mem_insert`

English:
theorem mem_insert
  given: (x y : ZFSet)
  statement: x in insert x y
  proof: mem_insert_iff.2 Or.inl rfl

中文:
定理 mem_insert
  条件: (x y : ZFSet)
  结论: x in insert x y
  证明: mem_insert_iff.2 Or.inl rfl

Depends on / 依赖: Or.inl, mem_insert_iff
-/
theorem mem_insert (x y : ZFSet) : x in insert x y :=
mem_insert_iff.2 Or.inl rfl

/--
theorem `mem_insert_of_mem` / 定理 `mem_insert_of_mem`

English:
theorem mem_insert_of_mem
  given: {y z : ZFSet} (x) (h : z in y)
  statement: z in insert x y
  proof: mem_insert_iff.2 Or.inr h

@[simp, norm_cast]

中文:
定理 mem_insert_of_mem
  条件: {y z : ZFSet} (x) (h : z in y)
  结论: z in insert x y
  证明: mem_insert_iff.2 Or.inr h

@[simp, norm_cast]

Depends on / 依赖: Or.inr, mem_insert_iff
-/
theorem mem_insert_of_mem {y z : ZFSet} (x) (h : z in y) : z in insert x y :=
mem_insert_iff.2 Or.inr h

@[simp, norm_cast]
/--
lemma `coe_insert` / 引理 `coe_insert`

English:
lemma coe_insert
  given: (x y : ZFSet)
  statement: ↑(insert x y) = (insert x ↑y : Set ZFSet)
  proof: by ext; simp

@[simp]

中文:
引理 coe_insert
  条件: (x y : ZFSet)
  结论: ↑(insert x y) = (insert x ↑y : Set ZFSet)
  证明: by ext; simp

@[simp]

Depends on / 依赖: ofT0PseudoEMetricSpace
-/
lemma coe_insert (x y : ZFSet) : ↑(insert x y) = (insert x ↑y : Set ZFSet) := by ext; simp

@[simp]
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: {x y : ZFSet.{u}}
  statement: x in ({y} : ZFSet.{u}) ↔ x = y
  proof: Quotient.inductionOn₂ x y fun _ _ => PSet.mem_singleton.trans eq.symm

中文:
定理 mem_singleton
  条件: {x y : ZFSet.{u}}
  结论: x in ({y} : ZFSet.{u}) ↔ x = y
  证明: Quotient.inductionOn₂ x y fun _ _ => PSet.mem_singleton.trans eq.symm

Depends on / 依赖: PSet.mem_singleton.trans, Quotient, Quotient.inductionOn, eq.symm, mem_singleton
-/
theorem mem_singleton {x y : ZFSet.{u}} : x in ({y} : ZFSet.{u}) ↔ x = y :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_singleton.trans eq.symm

/--
theorem `notMem_singleton` / 定理 `notMem_singleton`

English:
theorem notMem_singleton
  given: {x y : ZFSet.{u}}
  statement: x ∉ ({y} : ZFSet.{u}) ↔ x != y
  proof: mem_singleton.not

@[simp, norm_cast]

中文:
定理 notMem_singleton
  条件: {x y : ZFSet.{u}}
  结论: x ∉ ({y} : ZFSet.{u}) ↔ x != y
  证明: mem_singleton.not

@[simp, norm_cast]

Depends on / 依赖: mem_singleton, mem_singleton.not
-/
theorem notMem_singleton {x y : ZFSet.{u}} : x ∉ ({y} : ZFSet.{u}) ↔ x != y :=
  mem_singleton.not

@[simp, norm_cast]
/--
lemma `coe_singleton` / 引理 `coe_singleton`

English:
lemma coe_singleton
  given: (x : ZFSet)
  statement: (({x} : ZFSet) : Set ZFSet) = {x}
  proof: by ext; simp

中文:
引理 coe_singleton
  条件: (x : ZFSet)
  结论: (({x} : ZFSet) : Set ZFSet) = {x}
  证明: by ext; simp
-/
lemma coe_singleton (x : ZFSet) : (({x} : ZFSet) : Set ZFSet) = {x} := by ext; simp

/--
theorem `insert_nonempty` / 定理 `insert_nonempty`

English:
theorem insert_nonempty
  given: (u v : ZFSet)
  statement: (insert u v).Nonempty
  proof: ⟨u, mem_insert u v⟩

中文:
定理 insert_nonempty
  条件: (u v : ZFSet)
  结论: (insert u v).Nonempty
  证明: ⟨u, mem_insert u v⟩

Depends on / 依赖: mem_insert
-/
theorem insert_nonempty (u v : ZFSet) : (insert u v).Nonempty :=
  ⟨u, mem_insert u v⟩

/--
theorem `singleton_nonempty` / 定理 `singleton_nonempty`

English:
theorem singleton_nonempty
  given: (u : ZFSet)
  statement: ZFSet.Nonempty {u}
  proof: insert_nonempty u ∅

中文:
定理 singleton_nonempty
  条件: (u : ZFSet)
  结论: ZFSet.Nonempty {u}
  证明: insert_nonempty u ∅

Depends on / 依赖: insert_nonempty
-/
theorem singleton_nonempty (u : ZFSet) : ZFSet.Nonempty {u} :=
  insert_nonempty u ∅

/--
theorem `mem_pair` / 定理 `mem_pair`

English:
theorem mem_pair
  given: {x y z : ZFSet.{u}}
  statement: x in ({y, z} : ZFSet) ↔ x = y ∨ x = z
  proof: by
  simp

@[simp]

中文:
定理 mem_pair
  条件: {x y z : ZFSet.{u}}
  结论: x in ({y, z} : ZFSet) ↔ x = y ∨ x = z
  证明: by
  simp

@[simp]
-/
theorem mem_pair {x y z : ZFSet.{u}} : x in ({y, z} : ZFSet) ↔ x = y ∨ x = z := by
  simp

@[simp]
/--
theorem `pair_eq_singleton` / 定理 `pair_eq_singleton`

English:
theorem pair_eq_singleton
  given: (x : ZFSet)
  statement: {x, x} = ({x} : ZFSet)
  proof: by
  ext
  simp

@[simp]

中文:
定理 pair_eq_singleton
  条件: (x : ZFSet)
  结论: {x, x} = ({x} : ZFSet)
  证明: by
  ext
  simp

@[simp]
-/
theorem pair_eq_singleton (x : ZFSet) : {x, x} = ({x} : ZFSet) := by
  ext
  simp

@[simp]
/--
theorem `pair_eq_singleton_iff` / 定理 `pair_eq_singleton_iff`

English:
theorem pair_eq_singleton_iff
  given: {x y z : ZFSet}
  statement: ({x, y} : ZFSet) = {z} ↔ x = z ∧ y = z
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← mem_singleton, ← mem_singleton]
    simp [← h]
  · rintro ⟨rfl, rfl⟩
    exact pair_eq_singleton y

@[simp]

中文:
定理 pair_eq_singleton_iff
  条件: {x y z : ZFSet}
  结论: ({x, y} : ZFSet) = {z} ↔ x = z ∧ y = z
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← mem_singleton, ← mem_singleton]
    simp [← h]
  · rintro ⟨rfl, rfl⟩
    exact pair_eq_singleton y

@[simp]

Depends on / 依赖: mem_singleton, pair_eq_singleton
-/
theorem pair_eq_singleton_iff {x y z : ZFSet} : ({x, y} : ZFSet) = {z} ↔ x = z ∧ y = z := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← mem_singleton, ← mem_singleton]
    simp [← h]
  · rintro ⟨rfl, rfl⟩
    exact pair_eq_singleton y

@[simp]
/--
theorem `singleton_eq_pair_iff` / 定理 `singleton_eq_pair_iff`

English:
theorem singleton_eq_pair_iff
  given: {x y z : ZFSet}
  statement: ({x} : ZFSet) = {y, z} ↔ x = y ∧ x = z
  proof: by
  rw [eq_comm]; rw [pair_eq_singleton_iff]
  simp_rw [eq_comm]

中文:
定理 singleton_eq_pair_iff
  条件: {x y z : ZFSet}
  结论: ({x} : ZFSet) = {y, z} ↔ x = y ∧ x = z
  证明: by
  rw [eq_comm]; rw [pair_eq_singleton_iff]
  simp_rw [eq_comm]

Depends on / 依赖: eq_comm, pair_eq_singleton_iff, simp_rw
-/
theorem singleton_eq_pair_iff {x y z : ZFSet} : ({x} : ZFSet) = {y, z} ↔ x = y ∧ x = z := by
  rw [eq_comm]; rw [pair_eq_singleton_iff]
  simp_rw [eq_comm]

/--
Definition of `omega` / `omega` 的定义

English:
definition omega
  signature: : ZFSet
  body: mk PSet.omega

@[simp]

中文:
定义 omega
  签名: : ZFSet
  定义体: mk PSet.omega

@[simp]

Depends on / 依赖: PSet.omega
-/
def omega : ZFSet :=
  mk PSet.omega

@[simp]
/--
theorem `omega_zero` / 定理 `omega_zero`

English:
theorem omega_zero
  statement: ∅ in omega
  proof: ⟨⟨0⟩, Equiv.rfl⟩

@[simp]

中文:
定理 omega_zero
  结论: ∅ in omega
  证明: ⟨⟨0⟩, Equiv.rfl⟩

@[simp]

Depends on / 依赖: Equiv.rfl
-/
theorem omega_zero : ∅ in omega :=
  ⟨⟨0⟩, Equiv.rfl⟩

@[simp]
/--
theorem `omega_succ` / 定理 `omega_succ`

English:
theorem omega_succ
  given: {n}
  statement: n in omega.{u} -> insert n n in omega.{u}
  proof: Quotient.inductionOn n fun x ⟨⟨n⟩, h⟩ =>
    ⟨⟨n + 1⟩,
ZFSet.exact
        show insert (mk x) (mk x) = insert (mk <| ofNat n) (mk <| ofNat n) by
          rw [ZFSet.sound h]
          rfl⟩

中文:
定理 omega_succ
  条件: {n}
  结论: n in omega.{u} -> insert n n in omega.{u}
  证明: Quotient.inductionOn n fun x ⟨⟨n⟩, h⟩ =>
    ⟨⟨n + 1⟩,
ZFSet.exact
        show insert (mk x) (mk x) = insert (mk <| ofNat n) (mk <| ofNat n) by
          rw [ZFSet.sound h]
          rfl⟩

Depends on / 依赖: Quotient, Quotient.inductionOn, ZFSet.exact, ZFSet.sound, inductionOn, insert
-/
theorem omega_succ {n} : n in omega.{u} -> insert n n in omega.{u} :=
  Quotient.inductionOn n fun x ⟨⟨n⟩, h⟩ =>
    ⟨⟨n + 1⟩,
ZFSet.exact
        show insert (mk x) (mk x) = insert (mk <| ofNat n) (mk <| ofNat n) by
          rw [ZFSet.sound h]
          rfl⟩

/--
Definition of `sep` / `sep` 的定义

English:
definition sep
  signature: (p : ZFSet -> Prop)
  body: Quotient.map (PSet.sep fun y => p (mk y))
    fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by simpa only [mk_func, ← ZFSet.sound hb]⟩, hb⟩,
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by simpa only [mk_func, ZFSet.sound ha]⟩, ha⟩⟩

中文:
定义 sep
  签名: (p : ZFSet -> 命题)
  定义体: Quotient.map (PSet.sep fun y => p (mk y))
    fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by simpa only [mk_func, ← ZFSet.sound hb]⟩, hb⟩,
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by simpa only [mk_func, ZFSet.sound ha]⟩, ha⟩⟩

Depends on / 依赖: ofT0PseudoMetricSpace
-/
protected def sep (p : ZFSet -> Prop) : ZFSet -> ZFSet :=
  Quotient.map (PSet.sep fun y => p (mk y))
    fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by simpa only [mk_func, ← ZFSet.sound hb]⟩, hb⟩,
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by simpa only [mk_func, ZFSet.sound ha]⟩, ha⟩⟩

-- Porting note: the { x | p x } notation appears to be disabled in Lean 4.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sep ZFSet ZFSet
  body: ⟨ZFSet.sep⟩

@[simp]

中文:
实例 :
  签名: Sep ZFSet ZFSet
  定义体: ⟨ZFSet.sep⟩

@[simp]

Depends on / 依赖: ZFSet.sep
-/
instance : Sep ZFSet ZFSet :=
  ⟨ZFSet.sep⟩

@[simp]
/--
theorem `mem_sep` / 定理 `mem_sep`

English:
theorem mem_sep
  given: {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}}
  proof: Quotient.inductionOn₂ x y fun _ _ =>
    PSet.mem_sep (p := p ∘ mk) fun _ _ h => (Quotient.sound h).subst

@[simp]

中文:
定理 mem_sep
  条件: {p : ZFSet.{u} -> 命题} {x y : ZFSet.{u}}
  证明: Quotient.inductionOn₂ x y fun _ _ =>
    PSet.mem_sep (p := p ∘ mk) fun _ _ h => (Quotient.sound h).subst

@[simp]

Depends on / 依赖: PSet.mem_sep, Quotient, Quotient.inductionOn, Quotient.sound, mem_sep
-/
theorem mem_sep {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}} :
    y in ZFSet.sep p x ↔ y in x ∧ p y :=
  Quotient.inductionOn₂ x y fun _ _ =>
    PSet.mem_sep (p := p ∘ mk) fun _ _ h => (Quotient.sound h).subst

@[simp]
/--
theorem `sep_empty` / 定理 `sep_empty`

English:
theorem sep_empty
  given: (p : ZFSet -> Prop)
  statement: (∅ : ZFSet).sep p = ∅
  proof: (eq_empty _).mpr fun _ h => notMem_empty _ (mem_sep.mp h).1

中文:
定理 sep_empty
  条件: (p : ZFSet -> 命题)
  结论: (∅ : ZFSet).sep p = ∅
  证明: (eq_empty _).mpr fun _ h => notMem_empty _ (mem_sep.mp h).1

Depends on / 依赖: eq_empty, mem_sep, mem_sep.mp, notMem_empty
-/
theorem sep_empty (p : ZFSet -> Prop) : (∅ : ZFSet).sep p = ∅ :=
  (eq_empty _).mpr fun _ h => notMem_empty _ (mem_sep.mp h).1

/--
theorem `sep_subset` / 定理 `sep_subset`

English:
theorem sep_subset
  given: {x p}
  statement: ZFSet.sep p x subseteq x
  proof: fun _ h => (mem_sep.1 h).1

@[simp, norm_cast]

中文:
定理 sep_subset
  条件: {x p}
  结论: ZFSet.sep p x subseteq x
  证明: fun _ h => (mem_sep.1 h).1

@[simp, norm_cast]

Depends on / 依赖: mem_sep
-/
theorem sep_subset {x p} : ZFSet.sep p x subseteq x :=
  fun _ h => (mem_sep.1 h).1

@[simp, norm_cast]
/--
lemma `coe_sep` / 引理 `coe_sep`

English:
lemma coe_sep
  given: (a : ZFSet) (p : ZFSet -> Prop)
  statement: (ZFSet.sep p a : Set ZFSet) = {x in a | p x}
  proof: by
  ext
  simp

中文:
引理 coe_sep
  条件: (a : ZFSet) (p : ZFSet -> 命题)
  结论: (ZFSet.sep p a : Set ZFSet) = {x in a | p x}
  证明: by
  ext
  simp
-/
lemma coe_sep (a : ZFSet) (p : ZFSet -> Prop) : (ZFSet.sep p a : Set ZFSet) = {x in a | p x} := by
  ext
  simp

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: : ZFSet -> ZFSet
  body: Quotient.map PSet.powerset
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | exists a, a in p ∧ Equiv (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨_, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | exists b, b

中文:
定义 powerset
  签名: : ZFSet -> ZFSet
  定义体: Quotient.map PSet.powerset
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | exists a, a in p ∧ Equiv (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨_, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | exists b, b

Depends on / 依赖: PSet.powerset, Quotient, Quotient.map, powerset
-/
def powerset : ZFSet -> ZFSet :=
  Quotient.map PSet.powerset
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | exists a, a in p ∧ Equiv (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨_, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | exists b, b in q ∧ Equiv (A a) (B b) }, fun ⟨_, b, qb, ab⟩ => ⟨⟨b, qb⟩, ab⟩, fun ⟨b, qb⟩ =>
          let ⟨a, ab⟩ := βα b
          ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩

@[simp]
/--
theorem `mem_powerset` / 定理 `mem_powerset`

English:
theorem mem_powerset
  given: {x y : ZFSet.{u}}
  statement: y in powerset x ↔ y subseteq x
  proof: Quotient.inductionOn₂ x y fun _ _ => PSet.mem_powerset.trans subset_iff.symm

中文:
定理 mem_powerset
  条件: {x y : ZFSet.{u}}
  结论: y in powerset x ↔ y subseteq x
  证明: Quotient.inductionOn₂ x y fun _ _ => PSet.mem_powerset.trans subset_iff.symm

Depends on / 依赖: PSet.mem_powerset.trans, Quotient, Quotient.inductionOn, mem_powerset, subset_iff, subset_iff.symm
-/
theorem mem_powerset {x y : ZFSet.{u}} : y in powerset x ↔ y subseteq x :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_powerset.trans subset_iff.symm

/--
theorem `sUnion_lem` / 定理 `sUnion_lem`

English:
theorem sUnion_lem
  given: {α β : Type u} (A : α -> PSet) (B : β -> PSet) (αβ : forall a, exists b, Equiv (A a) (B b))
  proof: αβ a
    induction ea : A a with | _ γ Γ
    induction eb : B b with | _ δ Δ
    rw [ea]; rw [eb] at hb
    obtain ⟨γδ, δγ⟩ := hb
    let c : (A a).Type := c
    let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
    use ⟨b, Eq.ndrec d (Eq.symm eb)⟩
    change PSet.Equiv ((A a).Func c) ((B b).Func (Eq.ndrec d eb.

中文:
定理 sUnion_lem
  条件: {α β : 类型u} (A : α -> PSet) (B : β -> PSet) (αβ : 对任意 a, 存在 b, Equiv (A a) (B b))
  证明: αβ a
    induction ea : A a with | _ γ Γ
    induction eb : B b with | _ δ Δ
    rw [ea]; rw [eb] at hb
    obtain ⟨γδ, δγ⟩ := hb
    let c : (A a).Type := c
    let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
    use ⟨b, Eq.ndrec d (Eq.symm eb)⟩
    change PSet.Equiv ((A a).Func c) ((B b).Func (Eq.ndrec d eb.
-/
theorem sUnion_lem {α β : Type u} (A : α -> PSet) (B : β -> PSet) (αβ : forall a, exists b, Equiv (A a) (B b)) :
    forall a, exists b, Equiv ((sUnion ⟨α, A⟩).Func a) ((sUnion ⟨β, B⟩).Func b)
  | ⟨a, c⟩ => by
    let ⟨b, hb⟩ := αβ a
    induction ea : A a with | _ γ Γ
    induction eb : B b with | _ δ Δ
    rw [ea]; rw [eb] at hb
    obtain ⟨γδ, δγ⟩ := hb
    let c : (A a).Type := c
    let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
    use ⟨b, Eq.ndrec d (Eq.symm eb)⟩
    change PSet.Equiv ((A a).Func c) ((B b).Func (Eq.ndrec d eb.symm))
    match A a, B b, ea, eb, c, d, hd with
    | _, _, rfl, rfl, _, _, hd => exact hd

/--
Definition of `sUnion` / `sUnion` 的定义

English:
definition sUnion
  signature: : ZFSet -> ZFSet
  body: Quotient.map PSet.sUnion
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Z

中文:
定义 sUnion
  签名: : ZFSet -> ZFSet
  定义体: Quotient.map PSet.sUnion
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Z

Depends on / 依赖: Exists, Exists.elim, PSet.Equiv.symm, PSet.sUnion, Quotient, Quotient.map, sUnion, sUnion_lem
-/
def sUnion : ZFSet -> ZFSet :=
  Quotient.map PSet.sUnion
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩

@[inherit_doc]
scoped prefix:110 "⋃₀ " => ZFSet.sUnion

/--
Definition of `sInter` / `sInter` 的定义

English:
definition sInter
  signature: (x : ZFSet)
  body: (⋃₀ x).sep (fun y => forall z in x, y in z)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => ZFSet.sInter

@[simp]

中文:
定义 sInter
  签名: (x : ZFSet)
  定义体: (⋃₀ x).sep (fun y => forall z in x, y in z)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => ZFSet.sInter

@[simp]
-/
def sInter (x : ZFSet) : ZFSet := (⋃₀ x).sep (fun y => forall z in x, y in z)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => ZFSet.sInter

@[simp]
/--
theorem `mem_sUnion` / 定理 `mem_sUnion`

English:
theorem mem_sUnion
  given: {x y : ZFSet.{u}}
  statement: y in ⋃₀ x ↔ exists z in x, y in z
  proof: Quotient.inductionOn₂ x y fun _ _ => PSet.mem_sUnion.trans
    ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotient.inductionOn z (fun z h => ⟨z, h⟩) h⟩

中文:
定理 mem_sUnion
  条件: {x y : ZFSet.{u}}
  结论: y in ⋃₀ x ↔ 存在 z in x, y in z
  证明: Quotient.inductionOn₂ x y fun _ _ => PSet.mem_sUnion.trans
    ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotient.inductionOn z (fun z h => ⟨z, h⟩) h⟩

Depends on / 依赖: PSet.mem_sUnion.trans, Quotient, Quotient.inductionOn, inductionOn, mem_sUnion
-/
theorem mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in x, y in z :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_sUnion.trans
    ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotient.inductionOn z (fun z h => ⟨z, h⟩) h⟩

/--
theorem `mem_sInter` / 定理 `mem_sInter`

English:
theorem mem_sInter
  given: {x y : ZFSet} (h : x.Nonempty)
  statement: y in ⋂₀ x ↔ forall z in x, y in z
  proof: by
  unfold sInter
  simp only [and_iff_right_iff_imp, mem_sep]
  intro mem
  apply mem_sUnion.mpr
  replace ⟨s, h⟩ := h
  exact ⟨_, h, mem _ h⟩

@[simp]

中文:
定理 mem_sInter
  条件: {x y : ZFSet} (h : x.Nonempty)
  结论: y in ⋂₀ x ↔ 对任意 z in x, y in z
  证明: by
  unfold sInter
  simp only [and_iff_right_iff_imp, mem_sep]
  intro mem
  apply mem_sUnion.mpr
  replace ⟨s, h⟩ := h
  exact ⟨_, h, mem _ h⟩

@[simp]

Depends on / 依赖: and_iff_right_iff_imp, mem_sUnion, mem_sUnion.mpr, mem_sep, replace, sInter
-/
theorem mem_sInter {x y : ZFSet} (h : x.Nonempty) : y in ⋂₀ x ↔ forall z in x, y in z := by
  unfold sInter
  simp only [and_iff_right_iff_imp, mem_sep]
  intro mem
  apply mem_sUnion.mpr
  replace ⟨s, h⟩ := h
  exact ⟨_, h, mem _ h⟩

@[simp]
/--
theorem `sUnion_empty` / 定理 `sUnion_empty`

English:
theorem sUnion_empty
  statement: ⋃₀ (∅ : ZFSet.{u}) = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 sUnion_empty
  结论: ⋃₀ (∅ : ZFSet.{u}) = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem sUnion_empty : ⋃₀ (∅ : ZFSet.{u}) = ∅ := by
  ext
  simp

@[simp]
/--
theorem `sInter_empty` / 定理 `sInter_empty`

English:
theorem sInter_empty
  statement: ⋂₀ (∅ : ZFSet) = ∅
  proof: by simp [sInter]

中文:
定理 sInter_empty
  结论: ⋂₀ (∅ : ZFSet) = ∅
  证明: by simp [sInter]

Depends on / 依赖: sInter
-/
theorem sInter_empty : ⋂₀ (∅ : ZFSet) = ∅ := by simp [sInter]

/--
theorem `mem_of_mem_sInter` / 定理 `mem_of_mem_sInter`

English:
theorem mem_of_mem_sInter
  given: {x y z : ZFSet} (hy : y in ⋂₀ x) (hz : z in x)
  statement: y in z
  proof: by
  rcases eq_empty_or_nonempty x with (rfl | hx)
  · exact (notMem_empty z hz).elim
  · exact (mem_sInter hx).1 hy z hz

中文:
定理 mem_of_mem_sInter
  条件: {x y z : ZFSet} (hy : y in ⋂₀ x) (hz : z in x)
  结论: y in z
  证明: by
  rcases eq_empty_or_nonempty x with (rfl | hx)
  · exact (notMem_empty z hz).elim
  · exact (mem_sInter hx).1 hy z hz

Depends on / 依赖: eq_empty_or_nonempty, mem_sInter, notMem_empty
-/
theorem mem_of_mem_sInter {x y z : ZFSet} (hy : y in ⋂₀ x) (hz : z in x) : y in z := by
  rcases eq_empty_or_nonempty x with (rfl | hx)
  · exact (notMem_empty z hz).elim
  · exact (mem_sInter hx).1 hy z hz

/--
theorem `mem_sUnion_of_mem` / 定理 `mem_sUnion_of_mem`

English:
theorem mem_sUnion_of_mem
  given: {x y z : ZFSet} (hy : y in z) (hz : z in x)
  statement: y in ⋃₀ x
  proof: mem_sUnion.2 ⟨z, hz, hy⟩

中文:
定理 mem_sUnion_of_mem
  条件: {x y z : ZFSet} (hy : y in z) (hz : z in x)
  结论: y in ⋃₀ x
  证明: mem_sUnion.2 ⟨z, hz, hy⟩

Depends on / 依赖: mem_sUnion
-/
theorem mem_sUnion_of_mem {x y z : ZFSet} (hy : y in z) (hz : z in x) : y in ⋃₀ x :=
  mem_sUnion.2 ⟨z, hz, hy⟩

/--
theorem `notMem_sInter_of_notMem` / 定理 `notMem_sInter_of_notMem`

English:
theorem notMem_sInter_of_notMem
  given: {x y z : ZFSet} (hy : y ∉ z) (hz : z in x)
  statement: y ∉ ⋂₀ x
  proof: fun hx => hy mem_of_mem_sInter hx hz

@[simp]

中文:
定理 notMem_sInter_of_notMem
  条件: {x y z : ZFSet} (hy : y ∉ z) (hz : z in x)
  结论: y ∉ ⋂₀ x
  证明: fun hx => hy mem_of_mem_sInter hx hz

@[simp]

Depends on / 依赖: mem_of_mem_sInter
-/
theorem notMem_sInter_of_notMem {x y z : ZFSet} (hy : y ∉ z) (hz : z in x) : y ∉ ⋂₀ x :=
fun hx => hy mem_of_mem_sInter hx hz

@[simp]
/--
theorem `sUnion_singleton` / 定理 `sUnion_singleton`

English:
theorem sUnion_singleton
  given: {x : ZFSet.{u}}
  statement: ⋃₀ ({x} : ZFSet) = x
  proof: ext fun y => by simp_rw [mem_sUnion, mem_singleton, exists_eq_left]

@[simp]

中文:
定理 sUnion_singleton
  条件: {x : ZFSet.{u}}
  结论: ⋃₀ ({x} : ZFSet) = x
  证明: ext fun y => by simp_rw [mem_sUnion, mem_singleton, exists_eq_left]

@[simp]

Depends on / 依赖: exists_eq_left, mem_sUnion, mem_singleton, simp_rw
-/
theorem sUnion_singleton {x : ZFSet.{u}} : ⋃₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sUnion, mem_singleton, exists_eq_left]

@[simp]
/--
theorem `sInter_singleton` / 定理 `sInter_singleton`

English:
theorem sInter_singleton
  given: {x : ZFSet.{u}}
  statement: ⋂₀ ({x} : ZFSet) = x
  proof: ext fun y => by simp_rw [mem_sInter (singleton_nonempty x), mem_singleton, forall_eq]

@[simp, norm_cast]

中文:
定理 sInter_singleton
  条件: {x : ZFSet.{u}}
  结论: ⋂₀ ({x} : ZFSet) = x
  证明: ext fun y => by simp_rw [mem_sInter (singleton_nonempty x), mem_singleton, forall_eq]

@[simp, norm_cast]

Depends on / 依赖: forall_eq, mem_sInter, mem_singleton, simp_rw, singleton_nonempty
-/
theorem sInter_singleton {x : ZFSet.{u}} : ⋂₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sInter (singleton_nonempty x), mem_singleton, forall_eq]

@[simp, norm_cast]
/--
lemma `coe_sUnion` / 引理 `coe_sUnion`

English:
lemma coe_sUnion
  given: (x : ZFSet.{u})
  statement: (⋃₀ x : Set ZFSet) = ⋃₀ (SetLike.coe '' (x : Set ZFSet))
  proof: by
  ext
  simp

@[simp, norm_cast]

中文:
引理 coe_sUnion
  条件: (x : ZFSet.{u})
  结论: (⋃₀ x : Set ZFSet) = ⋃₀ (SetLike.coe '' (x : Set ZFSet))
  证明: by
  ext
  simp

@[simp, norm_cast]
-/
lemma coe_sUnion (x : ZFSet.{u}) : (⋃₀ x : Set ZFSet) = ⋃₀ (SetLike.coe '' (x : Set ZFSet)) := by
  ext
  simp

@[simp, norm_cast]
/--
lemma `coe_sInter` / 引理 `coe_sInter`

English:
lemma coe_sInter
  given: (h : x.Nonempty)
  statement: (⋂₀ x : Set ZFSet) = ⋂₀ (SetLike.coe '' (x : Set ZFSet))
  proof: by
  ext
  simp [mem_sInter h]

中文:
引理 coe_sInter
  条件: (h : x.Nonempty)
  结论: (⋂₀ x : Set ZFSet) = ⋂₀ (SetLike.coe '' (x : Set ZFSet))
  证明: by
  ext
  simp [mem_sInter h]

Depends on / 依赖: mem_sInter
-/
lemma coe_sInter (h : x.Nonempty) : (⋂₀ x : Set ZFSet) = ⋂₀ (SetLike.coe '' (x : Set ZFSet)) := by
  ext
  simp [mem_sInter h]

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  statement: Function.Injective (@singleton ZFSet ZFSet _)
  proof: fun x y H => by
  let := congr_arg sUnion H
  rwa [sUnion_singleton, sUnion_singleton] at this

@[simp]

中文:
定理 singleton_injective
  结论: Function.Injective (@singleton ZFSet ZFSet _)
  证明: fun x y H => by
  let := congr_arg sUnion H
  rwa [sUnion_singleton, sUnion_singleton] at this

@[simp]

Depends on / 依赖: congr_arg, sUnion, sUnion_singleton
-/
theorem singleton_injective : Function.Injective (@singleton ZFSet ZFSet _) := fun x y H => by
  let := congr_arg sUnion H
  rwa [sUnion_singleton, sUnion_singleton] at this

@[simp]
/--
theorem `singleton_inj` / 定理 `singleton_inj`

English:
theorem singleton_inj
  given: {x y : ZFSet}
  statement: ({x} : ZFSet) = {y} ↔ x = y
  proof: singleton_injective.eq_iff

中文:
定理 singleton_inj
  条件: {x y : ZFSet}
  结论: ({x} : ZFSet) = {y} ↔ x = y
  证明: singleton_injective.eq_iff

Depends on / 依赖: eq_iff, singleton_injective, singleton_injective.eq_iff
-/
theorem singleton_inj {x y : ZFSet} : ({x} : ZFSet) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (x y : ZFSet.{u})
  body: ⋃₀ {x, y}

中文:
定义 union
  签名: (x y : ZFSet.{u})
  定义体: ⋃₀ {x, y}
-/
protected def union (x y : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ {x, y}

/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: (x y : ZFSet.{u})
  body: ZFSet.sep (fun z => z in y) x -- { z ∈ x | z ∈ y }

中文:
定义 inter
  签名: (x y : ZFSet.{u})
  定义体: ZFSet.sep (fun z => z in y) x -- { z ∈ x | z ∈ y }
-/
protected def inter (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z in y) x -- { z ∈ x | z ∈ y }

/--
Definition of `diff` / `diff` 的定义

English:
definition diff
  signature: (x y : ZFSet.{u})
  body: ZFSet.sep (fun z => z ∉ y) x -- { z ∈ x | z ∉ y }

中文:
定义 diff
  签名: (x y : ZFSet.{u})
  定义体: ZFSet.sep (fun z => z ∉ y) x -- { z ∈ x | z ∉ y }
-/
protected def diff (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∉ y) x -- { z ∈ x | z ∉ y }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Union ZFSet
  body: ⟨ZFSet.union⟩

中文:
实例 :
  签名: Union ZFSet
  定义体: ⟨ZFSet.union⟩

Depends on / 依赖: ZFSet.union
-/
instance : Union ZFSet :=
  ⟨ZFSet.union⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inter ZFSet
  body: ⟨ZFSet.inter⟩

中文:
实例 :
  签名: 整数er ZFSet
  定义体: ⟨ZFSet.inter⟩

Depends on / 依赖: ZFSet.inter
-/
instance : Inter ZFSet :=
  ⟨ZFSet.inter⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SDiff ZFSet
  body: ⟨ZFSet.diff⟩

中文:
实例 :
  签名: SDiff ZFSet
  定义体: ⟨ZFSet.diff⟩

Depends on / 依赖: ZFSet.diff
-/
instance : SDiff ZFSet :=
  ⟨ZFSet.diff⟩

/--
lemma `sUnion_pair` / 引理 `sUnion_pair`

English:
lemma sUnion_pair
  given: (x y : ZFSet.{u})
  statement: ⋃₀ ({x, y} : ZFSet.{u}) = x union y
  proof: rfl

中文:
引理 sUnion_pair
  条件: (x y : ZFSet.{u})
  结论: ⋃₀ ({x, y} : ZFSet.{u}) = x union y
  证明: rfl
-/
@[simp] lemma sUnion_pair (x y : ZFSet.{u}) : ⋃₀ ({x, y} : ZFSet.{u}) = x union y := rfl

/--
lemma `sep_mem` / 引理 `sep_mem`

English:
lemma sep_mem
  given: (x y : ZFSet.{u})
  statement: x.sep (· in y) = x inter y
  proof: rfl

中文:
引理 sep_mem
  条件: (x y : ZFSet.{u})
  结论: x.sep (· in y) = x inter y
  证明: rfl
-/
@[simp] lemma sep_mem (x y : ZFSet.{u}) : x.sep (· in y) = x inter y := rfl
/--
lemma `sep_notMem` / 引理 `sep_notMem`

English:
lemma sep_notMem
  given: (x y : ZFSet.{u})
  statement: x.sep (· ∉ y) = x \ y
  proof: rfl

中文:
引理 sep_notMem
  条件: (x y : ZFSet.{u})
  结论: x.sep (· ∉ y) = x \ y
  证明: rfl
-/
@[simp] lemma sep_notMem (x y : ZFSet.{u}) : x.sep (· ∉ y) = x \ y := rfl

/--
lemma `mem_union` / 引理 `mem_union`

English:
lemma mem_union
  statement: z in x union y ↔ z in x ∨ z in y
  proof: by simp [← sUnion_pair]

中文:
引理 mem_union
  结论: z in x union y ↔ z in x ∨ z in y
  证明: by simp [← sUnion_pair]
-/
@[simp] lemma mem_union : z in x union y ↔ z in x ∨ z in y := by simp [← sUnion_pair]
/--
lemma `mem_inter` / 引理 `mem_inter`

English:
lemma mem_inter
  statement: z in x inter y ↔ z in x ∧ z in y
  proof: by simp [← sep_mem]

中文:
引理 mem_inter
  结论: z in x inter y ↔ z in x ∧ z in y
  证明: by simp [← sep_mem]
-/
@[simp] lemma mem_inter : z in x inter y ↔ z in x ∧ z in y := by simp [← sep_mem]
/--
lemma `mem_sdiff` / 引理 `mem_sdiff`

English:
lemma mem_sdiff
  statement: z in x \ y ↔ z in x ∧ z ∉ y
  proof: by simp [← sep_notMem]

@[simp, norm_cast]

中文:
引理 mem_sdiff
  结论: z in x \ y ↔ z in x ∧ z ∉ y
  证明: by simp [← sep_notMem]

@[simp, norm_cast]
-/
@[simp] lemma mem_sdiff : z in x \ y ↔ z in x ∧ z ∉ y := by simp [← sep_notMem]

@[simp, norm_cast]
/--
lemma `coe_union` / 引理 `coe_union`

English:
lemma coe_union
  given: (x y : ZFSet.{u})
  statement: ↑(x union y) = (↑x union ↑y : Set ZFSet)
  proof: by ext; simp

@[simp, norm_cast]

中文:
引理 coe_union
  条件: (x y : ZFSet.{u})
  结论: ↑(x union y) = (↑x union ↑y : Set ZFSet)
  证明: by ext; simp

@[simp, norm_cast]
-/
lemma coe_union (x y : ZFSet.{u}) : ↑(x union y) = (↑x union ↑y : Set ZFSet) := by ext; simp

@[simp, norm_cast]
/--
lemma `coe_inter` / 引理 `coe_inter`

English:
lemma coe_inter
  given: (x y : ZFSet.{u})
  statement: ↑(x inter y) = (↑x inter ↑y : Set ZFSet)
  proof: by ext; simp

@[simp, norm_cast]

中文:
引理 coe_inter
  条件: (x y : ZFSet.{u})
  结论: ↑(x inter y) = (↑x inter ↑y : Set ZFSet)
  证明: by ext; simp

@[simp, norm_cast]
-/
lemma coe_inter (x y : ZFSet.{u}) : ↑(x inter y) = (↑x inter ↑y : Set ZFSet) := by ext; simp

@[simp, norm_cast]
/--
lemma `coe_sdiff` / 引理 `coe_sdiff`

English:
lemma coe_sdiff
  given: (x y : ZFSet.{u})
  statement: ↑(x \ y) = (↑x \ ↑y : Set ZFSet)
  proof: by ext; simp

中文:
引理 coe_sdiff
  条件: (x y : ZFSet.{u})
  结论: ↑(x \ y) = (↑x \ ↑y : Set ZFSet)
  证明: by ext; simp
-/
lemma coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (↑x \ ↑y : Set ZFSet) := by ext; simp

/--
lemma `inter_eq_left_of_subset` / 引理 `inter_eq_left_of_subset`

English:
lemma inter_eq_left_of_subset
  given: (hxy : x subseteq y)
  statement: x inter y = x
  proof: by ext; simpa using @hxy _

中文:
引理 inter_eq_left_of_subset
  条件: (hxy : x subseteq y)
  结论: x inter y = x
  证明: by ext; simpa using @hxy _
-/
@[simp] lemma inter_eq_left_of_subset (hxy : x subseteq y) : x inter y = x := by ext; simpa using @hxy _
/--
lemma `inter_eq_right_of_subset` / 引理 `inter_eq_right_of_subset`

English:
lemma inter_eq_right_of_subset
  given: (hyx : y subseteq x)
  statement: x inter y = y
  proof: by ext; simpa using @hyx _

中文:
引理 inter_eq_right_of_subset
  条件: (hyx : y subseteq x)
  结论: x inter y = y
  证明: by ext; simpa using @hyx _
-/
@[simp] lemma inter_eq_right_of_subset (hyx : y subseteq x) : x inter y = y := by ext; simpa using @hyx _

/--
Definition of `powersetEquiv` / `powersetEquiv` 的定义

English:
definition powersetEquiv
  signature: (x : ZFSet.{u})
  body: ⟨y.1, Set.mem_powerset (mem_powerset.1 y.2)⟩
  invFun s := ⟨x.sep (· in s.1), mem_powerset.2 sep_subset⟩
  left_inv := by simp +contextual [Function.LeftInverse]
  right_inv := by simp +contextual [Function.LeftInverse, Function.RightInverse, Set.ofPred_and]

中文:
定义 powersetEquiv
  签名: (x : ZFSet.{u})
  定义体: ⟨y.1, Set.mem_powerset (mem_powerset.1 y.2)⟩
  invFun s := ⟨x.sep (· in s.1), mem_powerset.2 sep_subset⟩
  left_inv := by simp +contextual [Function.LeftInverse]
  right_inv := by simp +contextual [Function.LeftInverse, Function.RightInverse, Set.ofPred_and]

Depends on / 依赖: Set.mem_powerset, mem_powerset
-/
def powersetEquiv (x : ZFSet.{u}) : x.powerset ≃ 𝒫 (x : Set ZFSet) where
  toFun y := ⟨y.1, Set.mem_powerset (mem_powerset.1 y.2)⟩
  invFun s := ⟨x.sep (· in s.1), mem_powerset.2 sep_subset⟩
  left_inv := by simp +contextual [Function.LeftInverse]
  right_inv := by simp +contextual [Function.LeftInverse, Function.RightInverse, Set.ofPred_and]

/--
theorem `insert_eq` / 定理 `insert_eq`

English:
theorem insert_eq
  given: (x y : ZFSet)
  statement: insert x y = {x} union y
  proof: by
  ext; simp

中文:
定理 insert_eq
  条件: (x y : ZFSet)
  结论: insert x y = {x} union y
  证明: by
  ext; simp
-/
theorem insert_eq (x y : ZFSet) : insert x y = {x} union y := by
  ext; simp

/--
theorem `mem_wf` / 定理 `mem_wf`

English:
theorem mem_wf
  statement: @WellFounded ZFSet (· in ·)
  proof: (wellFounded_lift₂_iff (H := fun a b c d hx hy =>
    propext ((@Mem.congr_left a c hx).trans (@Mem.congr_right b d hy _)))).mpr PSet.mem_wf

中文:
定理 mem_wf
  结论: @WellFounded ZFSet (· in ·)
  证明: (wellFounded_lift₂_iff (H := fun a b c d hx hy =>
    propext ((@Mem.congr_left a c hx).trans (@Mem.congr_right b d hy _)))).mpr PSet.mem_wf

Depends on / 依赖: Mem.congr_left, Mem.congr_right, PSet.mem_wf, congr_left, congr_right, mem_wf, propext
-/
theorem mem_wf : @WellFounded ZFSet (· in ·) :=
  (wellFounded_lift₂_iff (H := fun a b c d hx hy =>
    propext ((@Mem.congr_left a c hx).trans (@Mem.congr_right b d hy _)))).mpr PSet.mem_wf

/-- Induction on the `∈` relation. -/
@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  given: {p : ZFSet -> Prop} (x) (h : forall x, (forall y in x, p y) -> p x)
  statement: p x
  proof: mem_wf.induction x h

中文:
定理 inductionOn
  条件: {p : ZFSet -> 命题} (x) (h : 对任意 x, (对任意 y in x, p y) -> p x)
  结论: p x
  证明: mem_wf.induction x h

Depends on / 依赖: mem_wf, mem_wf.induction
-/
theorem inductionOn {p : ZFSet -> Prop} (x) (h : forall x, (forall y in x, p y) -> p x) : p x :=
  mem_wf.induction x h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsWellFounded ZFSet (· in ·)
  body: ⟨mem_wf⟩

中文:
实例 :
  签名: IsWellFounded ZFSet (· in ·)
  定义体: ⟨mem_wf⟩

Depends on / 依赖: mem_wf
-/
instance : IsWellFounded ZFSet (· in ·) :=
  ⟨mem_wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation ZFSet
  body: ⟨_, mem_wf⟩

中文:
实例 :
  签名: WellFoundedRelation ZFSet
  定义体: ⟨_, mem_wf⟩

Depends on / 依赖: mem_wf
-/
instance : WellFoundedRelation ZFSet :=
  ⟨_, mem_wf⟩

/--
theorem `mem_asymm` / 定理 `mem_asymm`

English:
theorem mem_asymm
  given: {x y : ZFSet}
  statement: x in y -> y ∉ x
  proof: asymm_of (· in ·)

中文:
定理 mem_asymm
  条件: {x y : ZFSet}
  结论: x in y -> y ∉ x
  证明: asymm_of (· in ·)

Depends on / 依赖: asymm_of
-/
theorem mem_asymm {x y : ZFSet} : x in y -> y ∉ x :=
  asymm_of (· in ·)

/--
theorem `mem_irrefl` / 定理 `mem_irrefl`

English:
theorem mem_irrefl
  given: (x : ZFSet)
  statement: x ∉ x
  proof: irrefl_of (· in ·) x

中文:
定理 mem_irrefl
  条件: (x : ZFSet)
  结论: x ∉ x
  证明: irrefl_of (· in ·) x

Depends on / 依赖: irrefl_of
-/
theorem mem_irrefl (x : ZFSet) : x ∉ x :=
  irrefl_of (· in ·) x

/--
theorem `not_subset_of_mem` / 定理 `not_subset_of_mem`

English:
theorem not_subset_of_mem
  given: {x y : ZFSet} (h : x in y)
  statement: ¬ y subseteq x
  proof: fun h' => mem_irrefl _ (h' h)

中文:
定理 not_subset_of_mem
  条件: {x y : ZFSet} (h : x in y)
  结论: ¬ y subseteq x
  证明: fun h' => mem_irrefl _ (h' h)

Depends on / 依赖: mem_irrefl
-/
theorem not_subset_of_mem {x y : ZFSet} (h : x in y) : ¬ y subseteq x :=
  fun h' => mem_irrefl _ (h' h)

/--
theorem `notMem_of_subset` / 定理 `notMem_of_subset`

English:
theorem notMem_of_subset
  given: {x y : ZFSet} (h : x subseteq y)
  statement: y ∉ x
  proof: imp_not_comm.2 not_subset_of_mem h

中文:
定理 notMem_of_subset
  条件: {x y : ZFSet} (h : x subseteq y)
  结论: y ∉ x
  证明: imp_not_comm.2 not_subset_of_mem h

Depends on / 依赖: imp_not_comm, not_subset_of_mem
-/
theorem notMem_of_subset {x y : ZFSet} (h : x subseteq y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h

/--
theorem `regularity` / 定理 `regularity`

English:
theorem regularity
  given: (x : ZFSet.{u}) (h : x != ∅)
  statement: exists y in x, x inter y = ∅
  proof: by_contradiction fun ne =>
h (eq_empty x).2 fun y =>
      @inductionOn (fun z => z ∉ x) y fun z IH zx =>
        ne ⟨z, zx, (eq_empty _).2 fun w wxz =>
          let ⟨wx, wz⟩ := mem_inter.1 wxz
          IH w wz wx⟩

中文:
定理 regularity
  条件: (x : ZFSet.{u}) (h : x != ∅)
  结论: 存在 y in x, x inter y = ∅
  证明: by_contradiction fun ne =>
h (eq_empty x).2 fun y =>
      @inductionOn (fun z => z ∉ x) y fun z IH zx =>
        ne ⟨z, zx, (eq_empty _).2 fun w wxz =>
          let ⟨wx, wz⟩ := mem_inter.1 wxz
          IH w wz wx⟩

Depends on / 依赖: by_contradiction, eq_empty, inductionOn, mem_inter
-/
theorem regularity (x : ZFSet.{u}) (h : x != ∅) : exists y in x, x inter y = ∅ :=
  by_contradiction fun ne =>
h (eq_empty x).2 fun y =>
      @inductionOn (fun z => z ∉ x) y fun z IH zx =>
        ne ⟨z, zx, (eq_empty _).2 fun w wxz =>
          let ⟨wx, wz⟩ := mem_inter.1 wxz
          IH w wz wx⟩

/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (f : ZFSet -> ZFSet) [Definable₁ f]
  body: let r := Definable₁.out f
  Quotient.map (PSet.image r)
    fun _ _ e =>
      Mem.ext fun _ =>
(mem_image (fun _ _ => Definable₁.out_equiv _)).trans
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (Mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
⟨w, (Mem.congr_right e).2 h1, h2⟩⟩
       

中文:
定义 image
  签名: (f : ZFSet -> ZFSet) [Definable₁ f]
  定义体: let r := Definable₁.out f
  Quotient.map (PSet.image r)
    fun _ _ e =>
      Mem.ext fun _ =>
(mem_image (fun _ _ => Definable₁.out_equiv _)).trans
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (Mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
⟨w, (Mem.congr_right e).2 h1, h2⟩⟩
       

Depends on / 依赖: Iff.trans, Mem.congr_right, Mem.ext, PSet.image, Quotient, Quotient.map, congr_right, mem_image, out_equiv
-/
def image (f : ZFSet -> ZFSet) [Definable₁ f] : ZFSet -> ZFSet :=
  let r := Definable₁.out f
  Quotient.map (PSet.image r)
    fun _ _ e =>
      Mem.ext fun _ =>
(mem_image (fun _ _ => Definable₁.out_equiv _)).trans
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (Mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
⟨w, (Mem.congr_right e).2 h1, h2⟩⟩
            (mem_image (fun _ _ => Definable₁.out_equiv _)).symm

/--
theorem `image.mk` / 定理 `image.mk`

English:
theorem image.mk
  given: (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f] (x) {y}
  statement: y in x -> f y in image f x
  proof: Quotient.inductionOn₂ x y fun ⟨_, _⟩ _ ⟨a, ya⟩ => by
    simp only [mk_eq, ← Definable₁.mk_out (f := f)]
    exact ⟨a, Definable₁.out_equiv f ya⟩

@[simp]

中文:
定理 image.mk
  条件: (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f] (x) {y}
  结论: y in x -> f y in image f x
  证明: Quotient.inductionOn₂ x y fun ⟨_, _⟩ _ ⟨a, ya⟩ => by
    simp only [mk_eq, ← Definable₁.mk_out (f := f)]
    exact ⟨a, Definable₁.out_equiv f ya⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, mk_eq, mk_out, out_equiv
-/
theorem image.mk (f : ZFSet.{u} -> ZFSet.{u}) [Definable₁ f] (x) {y} : y in x -> f y in image f x :=
  Quotient.inductionOn₂ x y fun ⟨_, _⟩ _ ⟨a, ya⟩ => by
    simp only [mk_eq, ← Definable₁.mk_out (f := f)]
    exact ⟨a, Definable₁.out_equiv f ya⟩

@[simp]
/--
theorem `mem_image` / 定理 `mem_image`

English:
theorem mem_image
  given: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
  proof: Quotient.inductionOn₂ x y fun ⟨_, A⟩ _ =>
    ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, ((Quotient.sound ya).trans Definable₁.mk_out).symm⟩,
      fun ⟨_, hz, e⟩ => e ▸ image.mk _ _ hz⟩

@[simp, norm_cast]

中文:
定理 mem_image
  条件: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
  证明: Quotient.inductionOn₂ x y fun ⟨_, A⟩ _ =>
    ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, ((Quotient.sound ya).trans Definable₁.mk_out).symm⟩,
      fun ⟨_, hz, e⟩ => e ▸ image.mk _ _ hz⟩

@[simp, norm_cast]

Depends on / 依赖: Mem.mk, Quotient, Quotient.inductionOn, Quotient.sound, image.mk, mk_out
-/
theorem mem_image {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}} :
    y in image f x ↔ exists z in x, f z = y :=
  Quotient.inductionOn₂ x y fun ⟨_, A⟩ _ =>
    ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, ((Quotient.sound ya).trans Definable₁.mk_out).symm⟩,
      fun ⟨_, hz, e⟩ => e ▸ image.mk _ _ hz⟩

@[simp, norm_cast]
/--
lemma `coe_image` / 引理 `coe_image`

English:
lemma coe_image
  given: (f : ZFSet -> ZFSet) [Definable₁ f] (x : ZFSet)
  proof: by ext; simp

中文:
引理 coe_image
  条件: (f : ZFSet -> ZFSet) [Definable₁ f] (x : ZFSet)
  证明: by ext; simp
-/
lemma coe_image (f : ZFSet -> ZFSet) [Definable₁ f] (x : ZFSet) :
    (image f x : Set ZFSet) = f '' x := by ext; simp

section Small

variable {α : Type*} [Small.{u} α]

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : α -> ZFSet.{u})
  body: ⟦⟨_, Quotient.out ∘ f ∘ (equivShrink α).symm⟩⟧

中文:
定义 range
  签名: (f : α -> ZFSet.{u})
  定义体: ⟦⟨_, Quotient.out ∘ f ∘ (equivShrink α).symm⟩⟧

Depends on / 依赖: Quotient, Quotient.out, equivShrink
-/
noncomputable def range (f : α -> ZFSet.{u}) : ZFSet.{u} :=
  ⟦⟨_, Quotient.out ∘ f ∘ (equivShrink α).symm⟩⟧

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: {f : α -> ZFSet.{u}} {x : ZFSet.{u}}
  statement: x in range f ↔ exists i, f i = x
  proof: Quotient.inductionOn x fun y => by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(equivShrink α).symm z, Quotient.eq_mk_iff_out.2 hz.symm⟩
    · rintro ⟨z, hz⟩
      use equivShrink α z
      simpa [hz] using PSet.Equiv.symm (Quotient.mk_out y)

@[simp, norm_cast]

中文:
定理 mem_range
  条件: {f : α -> ZFSet.{u}} {x : ZFSet.{u}}
  结论: x in range f ↔ 存在 i, f i = x
  证明: Quotient.inductionOn x fun y => by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(equivShrink α).symm z, Quotient.eq_mk_iff_out.2 hz.symm⟩
    · rintro ⟨z, hz⟩
      use equivShrink α z
      simpa [hz] using PSet.Equiv.symm (Quotient.mk_out y)

@[simp, norm_cast]

Depends on / 依赖: PSet.Equiv.symm, Quotient, Quotient.eq_mk_iff_out, Quotient.inductionOn, Quotient.mk_out, eq_mk_iff_out, equivShrink, hz.symm, inductionOn, mk_out
-/
theorem mem_range {f : α -> ZFSet.{u}} {x : ZFSet.{u}} : x in range f ↔ exists i, f i = x :=
  Quotient.inductionOn x fun y => by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(equivShrink α).symm z, Quotient.eq_mk_iff_out.2 hz.symm⟩
    · rintro ⟨z, hz⟩
      use equivShrink α z
      simpa [hz] using PSet.Equiv.symm (Quotient.mk_out y)

@[simp, norm_cast]
/--
lemma `coe_range` / 引理 `coe_range`

English:
lemma coe_range
  given: (f : α -> ZFSet.{u})
  statement: (range f : Set ZFSet) = .range f
  proof: by ext; simp

中文:
引理 coe_range
  条件: (f : α -> ZFSet.{u})
  结论: (range f : Set ZFSet) = .range f
  证明: by ext; simp
-/
lemma coe_range (f : α -> ZFSet.{u}) : (range f : Set ZFSet) = .range f := by ext; simp

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: {f : α -> ZFSet.{u}} (a : α)
  statement: f a in range f
  proof: by simp

中文:
定理 mem_range_self
  条件: {f : α -> ZFSet.{u}} (a : α)
  结论: f a in range f
  证明: by simp
-/
theorem mem_range_self {f : α -> ZFSet.{u}} (a : α) : f a in range f := by simp

/--
Definition of `iUnion` / `iUnion` 的定义

English:
definition iUnion
  signature: (f : α -> ZFSet.{u})
  body: sUnion (range f)

@[inherit_doc iUnion] scoped notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

@[simp]

中文:
定义 iUnion
  签名: (f : α -> ZFSet.{u})
  定义体: sUnion (range f)

@[inherit_doc iUnion] scoped notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

@[simp]

Depends on / 依赖: sUnion
-/
noncomputable def iUnion (f : α -> ZFSet.{u}) : ZFSet.{u} :=
  sUnion (range f)

@[inherit_doc iUnion] scoped notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

@[simp]
/--
theorem `mem_iUnion` / 定理 `mem_iUnion`

English:
theorem mem_iUnion
  given: {f : α -> ZFSet.{u}} {x : ZFSet.{u}}
  statement: x in ⋃ i, f i ↔ exists i, x in f i
  proof: by
  simp [iUnion]

@[simp, norm_cast]

中文:
定理 mem_iUnion
  条件: {f : α -> ZFSet.{u}} {x : ZFSet.{u}}
  结论: x in ⋃ i, f i ↔ 存在 i, x in f i
  证明: by
  simp [iUnion]

@[simp, norm_cast]

Depends on / 依赖: iUnion
-/
theorem mem_iUnion {f : α -> ZFSet.{u}} {x : ZFSet.{u}} : x in ⋃ i, f i ↔ exists i, x in f i := by
  simp [iUnion]

@[simp, norm_cast]
/--
lemma `coe_iUnion` / 引理 `coe_iUnion`

English:
lemma coe_iUnion
  given: (f : α -> ZFSet.{u})
  statement: ↑(⋃ i, f i) = ⋃ i, (f i : Set ZFSet)
  proof: by
  ext
  simp

中文:
引理 coe_iUnion
  条件: (f : α -> ZFSet.{u})
  结论: ↑(⋃ i, f i) = ⋃ i, (f i : Set ZFSet)
  证明: by
  ext
  simp
-/
lemma coe_iUnion (f : α -> ZFSet.{u}) : ↑(⋃ i, f i) = ⋃ i, (f i : Set ZFSet) := by
  ext
  simp

/--
theorem `subset_iUnion` / 定理 `subset_iUnion`

English:
theorem subset_iUnion
  given: (f : α -> ZFSet.{u}) (i : α)
  statement: f i subseteq ⋃ i, f i
  proof: by
  intro x hx
  simpa using ⟨i, hx⟩

中文:
定理 subset_iUnion
  条件: (f : α -> ZFSet.{u}) (i : α)
  结论: f i subseteq ⋃ i, f i
  证明: by
  intro x hx
  simpa using ⟨i, hx⟩
-/
theorem subset_iUnion (f : α -> ZFSet.{u}) (i : α) : f i subseteq ⋃ i, f i := by
  intro x hx
  simpa using ⟨i, hx⟩

end Small

/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: (x y : ZFSet.{u})
  body: {{x}, {x, y}}

@[simp, norm_cast]

中文:
定义 pair
  签名: (x y : ZFSet.{u})
  定义体: {{x}, {x, y}}

@[simp, norm_cast]
-/
def pair (x y : ZFSet.{u}) : ZFSet.{u} :=
  {{x}, {x, y}}

@[simp, norm_cast]
/--
lemma `coe_pair` / 引理 `coe_pair`

English:
lemma coe_pair
  given: (x y : ZFSet.{u})
  statement: (pair x y : Set ZFSet) = {{x}, {x, y}}
  proof: by simp [pair]

中文:
引理 coe_pair
  条件: (x y : ZFSet.{u})
  结论: (pair x y : Set ZFSet) = {{x}, {x, y}}
  证明: by simp [pair]
-/
lemma coe_pair (x y : ZFSet.{u}) : (pair x y : Set ZFSet) = {{x}, {x, y}} := by simp [pair]

/--
Definition of `pairSep` / `pairSep` 的定义

English:
definition pairSep
  signature: (p : ZFSet.{u} -> ZFSet.{u} -> Prop) (x y : ZFSet.{u})
  body: (powerset (powerset (x union y))).sep fun z => exists a in x, exists b in y, z = pair a b ∧ p a b

@[simp]

中文:
定义 pairSep
  签名: (p : ZFSet.{u} -> ZFSet.{u} -> 命题) (x y : ZFSet.{u})
  定义体: (powerset (powerset (x union y))).sep fun z => exists a in x, exists b in y, z = pair a b ∧ p a b

@[simp]

Depends on / 依赖: powerset
-/
def pairSep (p : ZFSet.{u} -> ZFSet.{u} -> Prop) (x y : ZFSet.{u}) : ZFSet.{u} :=
  (powerset (powerset (x union y))).sep fun z => exists a in x, exists b in y, z = pair a b ∧ p a b

@[simp]
/--
theorem `mem_pairSep` / 定理 `mem_pairSep`

English:
theorem mem_pairSep
  given: {p} {x y z : ZFSet.{u}}
  proof: by
  refine mem_sep.trans ⟨And.right, fun e => ⟨?_, e⟩⟩
  grind [mem_pair, mem_powerset, mem_singleton, mem_union, pair, subset_def]

中文:
定理 mem_pairSep
  条件: {p} {x y z : ZFSet.{u}}
  证明: by
  refine mem_sep.trans ⟨And.right, fun e => ⟨?_, e⟩⟩
  grind [mem_pair, mem_powerset, mem_singleton, mem_union, pair, subset_def]

Depends on / 依赖: And.right, mem_pair, mem_powerset, mem_sep, mem_sep.trans, mem_singleton, mem_union, subset_def
-/
theorem mem_pairSep {p} {x y z : ZFSet.{u}} :
    z in pairSep p x y ↔ exists a in x, exists b in y, z = pair a b ∧ p a b := by
  refine mem_sep.trans ⟨And.right, fun e => ⟨?_, e⟩⟩
  grind [mem_pair, mem_powerset, mem_singleton, mem_union, pair, subset_def]

/--
theorem `pair_injective` / 定理 `pair_injective`

English:
theorem pair_injective
  statement: Function.Injective2 pair
  proof: by
  intro x x' y y' H
  simp_rw [ZFSet.ext_iff, pair, mem_pair] at H
obtain rfl : x = x' := And.left by simpa [or_and_left] using (H {x}).1 (Or.inl rfl)
  have he : y = x -> y = y' := by
    rintro rfl
    simpa [eq_comm] using H {y, y'}
  have hx := H {x, y}
  simp_rw [pair_eq_singleton_iff, true_

中文:
定理 pair_injective
  结论: Function.Injective2 pair
  证明: by
  intro x x' y y' H
  simp_rw [ZFSet.ext_iff, pair, mem_pair] at H
obtain rfl : x = x' := And.left by simpa [or_and_left] using (H {x}).1 (Or.inl rfl)
  have he : y = x -> y = y' := by
    rintro rfl
    simpa [eq_comm] using H {y, y'}
  have hx := H {x, y}
  simp_rw [pair_eq_singleton_iff, true_

Depends on / 依赖: And.left, Or.elim, Or.inl, ZFSet.ext_iff, eq_comm, ext_iff, hx.elim, mem_pair, or_and_left, or_true, pair_eq_singleton_iff, simp_rw, true_and, true_iff
-/
theorem pair_injective : Function.Injective2 pair := by
  intro x x' y y' H
  simp_rw [ZFSet.ext_iff, pair, mem_pair] at H
obtain rfl : x = x' := And.left by simpa [or_and_left] using (H {x}).1 (Or.inl rfl)
  have he : y = x -> y = y' := by
    rintro rfl
    simpa [eq_comm] using H {y, y'}
  have hx := H {x, y}
  simp_rw [pair_eq_singleton_iff, true_and, or_true, true_iff] at hx
  refine ⟨rfl, hx.elim he fun hy => Or.elim ?_ he id⟩
  simpa using ZFSet.ext_iff.1 hy y

@[simp]
/--
theorem `pair_inj` / 定理 `pair_inj`

English:
theorem pair_inj
  given: {x y x' y' : ZFSet}
  statement: pair x y = pair x' y' ↔ x = x' ∧ y = y'
  proof: pair_injective.eq_iff

中文:
定理 pair_inj
  条件: {x y x' y' : ZFSet}
  结论: pair x y = pair x' y' ↔ x = x' ∧ y = y'
  证明: pair_injective.eq_iff

Depends on / 依赖: eq_iff, pair_injective, pair_injective.eq_iff
-/
theorem pair_inj {x y x' y' : ZFSet} : pair x y = pair x' y' ↔ x = x' ∧ y = y' :=
  pair_injective.eq_iff

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}
  body: pairSep fun _ _ => True

@[simp]

中文:
定义 prod
  签名: : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}
  定义体: pairSep fun _ _ => True

@[simp]

Depends on / 依赖: pairSep
-/
def prod : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u} :=
  pairSep fun _ _ => True

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {x y z : ZFSet.{u}}
  statement: z in prod x y ↔ exists a in x, exists b in y, z = pair a b
  proof: by
  simp [prod]

中文:
定理 mem_prod
  条件: {x y z : ZFSet.{u}}
  结论: z in prod x y ↔ 存在 a in x, 存在 b in y, z = pair a b
  证明: by
  simp [prod]
-/
theorem mem_prod {x y z : ZFSet.{u}} : z in prod x y ↔ exists a in x, exists b in y, z = pair a b := by
  simp [prod]

/--
theorem `pair_mem_prod` / 定理 `pair_mem_prod`

English:
theorem pair_mem_prod
  given: {x y a b : ZFSet.{u}}
  statement: pair a b in prod x y ↔ a in x ∧ b in y
  proof: by
  simp

中文:
定理 pair_mem_prod
  条件: {x y a b : ZFSet.{u}}
  结论: pair a b in prod x y ↔ a in x ∧ b in y
  证明: by
  simp
-/
theorem pair_mem_prod {x y a b : ZFSet.{u}} : pair a b in prod x y ↔ a in x ∧ b in y := by
  simp

/--
Definition of `IsFunc` / `IsFunc` 的定义

English:
definition IsFunc
  signature: (x y f : ZFSet.{u})
  body: f subseteq prod x y ∧ forall z : ZFSet.{u}, z in x -> exists! w, pair z w in f

中文:
定义 IsFunc
  签名: (x y f : ZFSet.{u})
  定义体: f subseteq prod x y ∧ forall z : ZFSet.{u}, z in x -> exists! w, pair z w in f

Depends on / 依赖: subseteq
-/
def IsFunc (x y f : ZFSet.{u}) : Prop :=
  f subseteq prod x y ∧ forall z : ZFSet.{u}, z in x -> exists! w, pair z w in f

/--
Definition of `funs` / `funs` 的定义

English:
definition funs
  signature: (x y : ZFSet.{u})
  body: ZFSet.sep (IsFunc x y) (powerset (prod x y))

@[simp]

中文:
定义 funs
  签名: (x y : ZFSet.{u})
  定义体: ZFSet.sep (IsFunc x y) (powerset (prod x y))

@[simp]

Depends on / 依赖: IsFunc, ZFSet.sep, powerset
-/
def funs (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsFunc x y) (powerset (prod x y))

@[simp]
/--
theorem `mem_funs` / 定理 `mem_funs`

English:
theorem mem_funs
  given: {x y f : ZFSet.{u}}
  statement: f in funs x y ↔ IsFunc x y f
  proof: by simp [funs, IsFunc]

中文:
定理 mem_funs
  条件: {x y f : ZFSet.{u}}
  结论: f in funs x y ↔ IsFunc x y f
  证明: by simp [funs, IsFunc]

Depends on / 依赖: IsFunc
-/
theorem mem_funs {x y f : ZFSet.{u}} : f in funs x y ↔ IsFunc x y f := by simp [funs, IsFunc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Definable₁ ({·})
  body: .mk ({·}) (fun _ => rfl)

中文:
实例 :
  签名: Definable₁ ({·})
  定义体: .mk ({·}) (fun _ => rfl)
-/
instance : Definable₁ ({·}) := .mk ({·}) (fun _ => rfl)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Definable₂ insert
  body: .mk insert (fun _ _ => rfl)

中文:
实例 :
  签名: Definable₂ insert
  定义体: .mk insert (fun _ _ => rfl)

Depends on / 依赖: insert
-/
instance : Definable₂ insert := .mk insert (fun _ _ => rfl)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Definable₂ pair
  body: inferInstanceAs Definable₂ fun x y => {{x}, {x, y}}

中文:
实例 :
  签名: Definable₂ pair
  定义体: inferInstanceAs Definable₂ fun x y => {{x}, {x, y}}
-/
instance : Definable₂ pair := inferInstanceAs Definable₂ fun x y => {{x}, {x, y}}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : ZFSet -> ZFSet) [Definable₁ f]
  body: image fun y => pair y (f y)

@[simp]

中文:
定义 map
  签名: (f : ZFSet -> ZFSet) [Definable₁ f]
  定义体: image fun y => pair y (f y)

@[simp]
-/
def map (f : ZFSet -> ZFSet) [Definable₁ f] : ZFSet -> ZFSet :=
  image fun y => pair y (f y)

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet}
  proof: mem_image

中文:
定理 mem_map
  条件: {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet}
  证明: mem_image

Depends on / 依赖: mem_image
-/
theorem mem_map {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet} :
    y in map f x ↔ exists z in x, pair z (f z) = y :=
  mem_image

/--
theorem `map_unique` / 定理 `map_unique`

English:
theorem map_unique
  statement: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x z : ZFSet.{u}}
  proof: ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, _, we⟩ := mem_image.1 yx
    let ⟨wz, fy⟩ := pair_injective we
    rw [← fy]; rw [wz]⟩

@[simp]

中文:
定理 map_unique
  结论: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x z : ZFSet.{u}}
  证明: ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, _, we⟩ := mem_image.1 yx
    let ⟨wz, fy⟩ := pair_injective we
    rw [← fy]; rw [wz]⟩

@[simp]

Depends on / 依赖: image.mk, mem_image, pair_injective
-/
theorem map_unique {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x z : ZFSet.{u}}
    (zx : z in x) : exists! w, pair z w in map f x :=
  ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, _, we⟩ := mem_image.1 yx
    let ⟨wz, fy⟩ := pair_injective we
    rw [← fy]; rw [wz]⟩

@[simp]
/--
theorem `map_isFunc` / 定理 `map_isFunc`

English:
theorem map_isFunc
  given: {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet}
  proof: ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨_, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun _ yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun _ => map_unique⟩⟩

中文:
定理 map_isFunc
  条件: {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet}
  证明: ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨_, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun _ yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun _ => map_unique⟩⟩

Depends on / 依赖: image.mk, map_unique, mem_image, pair_mem_prod
-/
theorem map_isFunc {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet} :
    IsFunc x y (map f x) ↔ forall z in x, f z in y :=
  ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨_, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun _ yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun _ => map_unique⟩⟩

/--
Definition of `Hereditarily` / `Hereditarily` 的定义

English:
definition Hereditarily
  signature: (p : ZFSet -> Prop) (x : ZFSet)
  body: p x ∧ forall y in x, Hereditarily p y
termination_by x

中文:
定义 Hereditarily
  签名: (p : ZFSet -> 命题) (x : ZFSet)
  定义体: p x ∧ forall y in x, Hereditarily p y
termination_by x

Depends on / 依赖: Hereditarily, termination_by
-/
def Hereditarily (p : ZFSet -> Prop) (x : ZFSet) : Prop :=
  p x ∧ forall y in x, Hereditarily p y
termination_by x

section Hereditarily

variable {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}}

/--
theorem `hereditarily_iff` / 定理 `hereditarily_iff`

English:
theorem hereditarily_iff
  statement: Hereditarily p x ↔ p x ∧ forall y in x, Hereditarily p y
  proof: by
  rw [← Hereditarily]

alias ⟨Hereditarily.def, _⟩ := hereditarily_iff

中文:
定理 hereditarily_iff
  结论: Hereditarily p x ↔ p x ∧ 对任意 y in x, Hereditarily p y
  证明: by
  rw [← Hereditarily]

alias ⟨Hereditarily.def, _⟩ := hereditarily_iff

Depends on / 依赖: Hereditarily
-/
theorem hereditarily_iff : Hereditarily p x ↔ p x ∧ forall y in x, Hereditarily p y := by
  rw [← Hereditarily]

alias ⟨Hereditarily.def, _⟩ := hereditarily_iff

/--
theorem `Hereditarily.self` / 定理 `Hereditarily.self`

English:
theorem Hereditarily.self
  given: (h : x.Hereditarily p)
  statement: p x
  proof: h.def.1

中文:
定理 Hereditarily.self
  条件: (h : x.Hereditarily p)
  结论: p x
  证明: h.def.1

Depends on / 依赖: h.def
-/
theorem Hereditarily.self (h : x.Hereditarily p) : p x :=
  h.def.1

/--
theorem `Hereditarily.mem` / 定理 `Hereditarily.mem`

English:
theorem Hereditarily.mem
  given: (h : x.Hereditarily p) (hy : y in x)
  statement: y.Hereditarily p
  proof: h.def.2 _ hy

中文:
定理 Hereditarily.mem
  条件: (h : x.Hereditarily p) (hy : y in x)
  结论: y.Hereditarily p
  证明: h.def.2 _ hy

Depends on / 依赖: h.def
-/
theorem Hereditarily.mem (h : x.Hereditarily p) (hy : y in x) : y.Hereditarily p :=
  h.def.2 _ hy

/--
theorem `Hereditarily.empty` / 定理 `Hereditarily.empty`

English:
theorem Hereditarily.empty
  statement: Hereditarily p x -> p ∅
  proof: by
  apply @ZFSet.inductionOn _ x
  intro y IH h
  rcases ZFSet.eq_empty_or_nonempty y with (rfl | ⟨a, ha⟩)
  · exact h.self
  · exact IH a ha (h.mem ha)

中文:
定理 Hereditarily.empty
  结论: Hereditarily p x -> p ∅
  证明: by
  apply @ZFSet.inductionOn _ x
  intro y IH h
  rcases ZFSet.eq_empty_or_nonempty y with (rfl | ⟨a, ha⟩)
  · exact h.self
  · exact IH a ha (h.mem ha)

Depends on / 依赖: ZFSet.eq_empty_or_nonempty, ZFSet.inductionOn, eq_empty_or_nonempty, h.mem, h.self, inductionOn
-/
theorem Hereditarily.empty : Hereditarily p x -> p ∅ := by
  apply @ZFSet.inductionOn _ x
  intro y IH h
  rcases ZFSet.eq_empty_or_nonempty y with (rfl | ⟨a, ha⟩)
  · exact h.self
  · exact IH a ha (h.mem ha)

end Hereditarily

end ZFSet
