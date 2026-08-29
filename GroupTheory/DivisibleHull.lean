/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Order.Module.Archimedean
public import Mathlib.Algebra.Order.Monoid.PNat
public import Mathlib.Data.Sign.Defs
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Divisible Hull of an abelian group

This file constructs the divisible hull of an `AddCommMonoid` as a `ℕ`-module localized at
`ℕ+` (implemented using `nonZeroDivisors ℕ`), which is a `ℚ≥0`-module.

Furthermore, we show that

* when `M` is a group, so is `DivisibleHull M`, which is also a `ℚ`-module
* when `M` is linearly ordered and cancellative, so is `DivisibleHull M`, which is also an
  ordered `ℚ≥0`-module.
* when `M` is a linearly ordered group, `DivisibleHull M` is an ordered `ℚ`-module, and
  `ArchimedeanClass` is preserved.

Despite the name, this file doesn't implement a `DivisibleBy` instance on `DivisibleHull`. This
should be implemented on `LocalizedModule` in a more general setting (TODO: implement this).
This file mainly focuses on the specialization to `ℕ` and the linear order property introduced by
it.

## Main declarations

* `DivisibleHull M` is the divisible hull of an abelian group.
* `DivisibleHull.archimedeanClassOrderIso M` is the equivalence between `ArchimedeanClass M` and
  `ArchimedeanClass (DivisibleHull M)`.

-/

@[expose] public section

variable {M : Type*} [AddCommMonoid M]

local notation "↑ⁿ" => PNat.equivNonZeroDivisorsNat

variable (M) in
/--
Definition of `DivisibleHull` / `DivisibleHull` 的定义

English:
abbreviation DivisibleHull
  body: LocalizedModule (nonZeroDivisors Nat) M

中文:
缩写 DivisibleHull
  定义体: LocalizedModule (nonZeroDivisors Nat) M

Depends on / 依赖: LocalizedModule, nonZeroDivisors
-/
abbrev DivisibleHull := LocalizedModule (nonZeroDivisors Nat) M

namespace DivisibleHull

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (m : M) (s : Nat+)
  body: LocalizedModule.mk m (↑ⁿ s)

中文:
定义 mk
  签名: (m : M) (s : 自然数+)
  定义体: LocalizedModule.mk m (↑ⁿ s)

Depends on / 依赖: LocalizedModule, LocalizedModule.mk
-/
def mk (m : M) (s : Nat+) : DivisibleHull M := LocalizedModule.mk m (↑ⁿ s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Rat>=0 (DivisibleHull M)
  body: LocalizedModule.moduleOfIsLocalization ..

中文:
实例 :
  签名: Module Rat>=0 (DivisibleHull M)
  定义体: LocalizedModule.moduleOfIsLocalization ..

Depends on / 依赖: LocalizedModule, LocalizedModule.moduleOfIsLocalization, moduleOfIsLocalization
-/
noncomputable instance : Module Rat>=0 (DivisibleHull M) := LocalizedModule.moduleOfIsLocalization ..

/-- Define coercion as `m ↦ m / 1`. -/
@[coe]
/--
Definition of `coe` / `coe` 的定义

English:
abbreviation coe
  signature: (m : M)
  body: mk m 1

中文:
缩写 coe
  签名: (m : M)
  定义体: mk m 1
-/
abbrev coe (m : M) := mk m 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe M (DivisibleHull M)
  body: coe

@[simp]

中文:
实例 :
  签名: Coe M (DivisibleHull M)
  定义体: coe

@[simp]
-/
instance : Coe M (DivisibleHull M) where
  coe := coe

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: (s : Nat+)
  statement: mk (0 : M) s = 0
  proof: by simp [mk]

@[elab_as_elim, induction_eliminator]

中文:
定理 mk_zero
  条件: (s : 自然数+)
  结论: mk (0 : M) s = 0
  证明: by simp [mk]

@[elab_as_elim, induction_eliminator]
-/
theorem mk_zero (s : Nat+) : mk (0 : M) s = 0 := by simp [mk]

@[elab_as_elim, induction_eliminator]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  given: {motive : DivisibleHull M -> Prop} (mk : forall num den, motive (.mk num den))
  proof: LocalizedModule.induction_on fun m s => mk m (↑ⁿ.symm s)

中文:
定理 ind
  条件: {motive : DivisibleHull M -> 命题} (mk : 对任意 num den, motive (.mk num den))
  证明: LocalizedModule.induction_on fun m s => mk m (↑ⁿ.symm s)

Depends on / 依赖: LocalizedModule, LocalizedModule.induction_on, induction_on
-/
theorem ind {motive : DivisibleHull M -> Prop} (mk : forall num den, motive (.mk num den)) :
    forall x, motive x :=
  LocalizedModule.induction_on fun m s => mk m (↑ⁿ.symm s)

/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {m m' : M} {s s' : Nat+}
  proof: by
  unfold mk
  rw [LocalizedModule.mk_eq]; rw [↑ⁿ.exists_congr_left]
  rfl

中文:
定理 mk_eq_mk
  条件: {m m' : M} {s s' : 自然数+}
  证明: by
  unfold mk
  rw [LocalizedModule.mk_eq]; rw [↑ⁿ.exists_congr_left]
  rfl

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_eq, exists_congr_left, mk_eq
-/
theorem mk_eq_mk {m m' : M} {s s' : Nat+} :
    mk m s = mk m' s' ↔ exists u : Nat+, u.val • s'.val • m = u.val • s.val • m' := by
  unfold mk
  rw [LocalizedModule.mk_eq]; rw [↑ⁿ.exists_congr_left]
  rfl

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: {α : Type*} (x : DivisibleHull M)
  body: LocalizedModule.liftOn x (fun p => f p.1 (↑ⁿ.symm p.2)) fun p p' heq =>
h p.1 p'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm p'.2) by
      obtain ⟨u, hu⟩ := heq
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩

@[simp]

中文:
定义 liftOn
  签名: {α : 类型} (x : DivisibleHull M)
  定义体: LocalizedModule.liftOn x (fun p => f p.1 (↑ⁿ.symm p.2)) fun p p' heq =>
h p.1 p'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm p'.2) by
      obtain ⟨u, hu⟩ := heq
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩

@[simp]

Depends on / 依赖: LocalizedModule, LocalizedModule.liftOn, liftOn, mk_eq_mk, mk_eq_mk.mpr
-/
def liftOn {α : Type*} (x : DivisibleHull M)
    (f : M -> Nat+ -> α)
    (h : forall (m m' : M) (s s' : Nat+), mk m s = mk m' s' -> f m s = f m' s') : α :=
  LocalizedModule.liftOn x (fun p => f p.1 (↑ⁿ.symm p.2)) fun p p' heq =>
h p.1 p'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm p'.2) by
      obtain ⟨u, hu⟩ := heq
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩

@[simp]
/--
theorem `liftOn_mk` / 定理 `liftOn_mk`

English:
theorem liftOn_mk
  statement: {α : Type*} (m : M) (s : Nat+)
  proof: rfl

中文:
定理 liftOn_mk
  结论: {α : 类型} (m : M) (s : 自然数+)
  证明: rfl
-/
theorem liftOn_mk {α : Type*} (m : M) (s : Nat+)
    (f : M -> Nat+ -> α)
    (h : forall (m m' : M) (s s' : Nat+), mk m s = mk m' s' -> f m s = f m' s') :
    liftOn (mk m s) f h = f m s := rfl

/--
Definition of `liftOn₂` / `liftOn₂` 的定义

English:
definition liftOn₂
  signature: {α : Type*} (x y : DivisibleHull M)
  body: LocalizedModule.liftOn₂ x y (fun p q => f p.1 (↑ⁿ.symm p.2) q.1 (↑ⁿ.symm q.2))
    fun p q p' q' heq heq' =>
    h p.1 q.1 p'.1 q'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm q.2) (↑ⁿ.symm p'.2) (↑ⁿ.symm q'.2)
      (by
        obtain ⟨u, hu⟩ := heq
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)
      (by
        obtain 

中文:
定义 liftOn₂
  签名: {α : 类型} (x y : DivisibleHull M)
  定义体: LocalizedModule.liftOn₂ x y (fun p q => f p.1 (↑ⁿ.symm p.2) q.1 (↑ⁿ.symm q.2))
    fun p q p' q' heq heq' =>
    h p.1 q.1 p'.1 q'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm q.2) (↑ⁿ.symm p'.2) (↑ⁿ.symm q'.2)
      (by
        obtain ⟨u, hu⟩ := heq
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)
      (by
        obtain 

Depends on / 依赖: LocalizedModule, LocalizedModule.liftOn, mk_eq_mk, mk_eq_mk.mpr
-/
def liftOn₂ {α : Type*} (x y : DivisibleHull M)
    (f : M -> Nat+ -> M -> Nat+ -> α)
    (h : forall (m n m' n' : M) (s t s' t' : Nat+),
      mk m s = mk m' s' -> mk n t = mk n' t' -> f m s n t = f m' s' n' t') : α :=
  LocalizedModule.liftOn₂ x y (fun p q => f p.1 (↑ⁿ.symm p.2) q.1 (↑ⁿ.symm q.2))
    fun p q p' q' heq heq' =>
    h p.1 q.1 p'.1 q'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm q.2) (↑ⁿ.symm p'.2) (↑ⁿ.symm q'.2)
      (by
        obtain ⟨u, hu⟩ := heq
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)
      (by
        obtain ⟨u, hu⟩ := heq'
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)

@[simp]
/--
theorem `liftOn₂_mk` / 定理 `liftOn₂_mk`

English:
theorem liftOn₂_mk
  statement: {α : Type*} (m m' : M) (s s' : Nat+)
  proof: rfl

中文:
定理 liftOn₂_mk
  结论: {α : 类型} (m m' : M) (s s' : 自然数+)
  证明: rfl
-/
theorem liftOn₂_mk {α : Type*} (m m' : M) (s s' : Nat+)
    (f : M -> Nat+ -> M -> Nat+ -> α)
    (h : forall (m n m' n' : M) (s t s' t' : Nat+),
      mk m s = mk m' s' -> mk n t = mk n' t' -> f m s n t = f m' s' n' t') :
    liftOn₂ (mk m s) (mk m' s') f h = f m s m' s' := rfl

/--
theorem `mk_add_mk` / 定理 `mk_add_mk`

English:
theorem mk_add_mk
  given: {m1 m2 : M} {s1 s2 : Nat+}
  proof: LocalizedModule.mk_add_mk

中文:
定理 mk_add_mk
  条件: {m1 m2 : M} {s1 s2 : 自然数+}
  证明: LocalizedModule.mk_add_mk

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_add_mk, mk_add_mk
-/
theorem mk_add_mk {m1 m2 : M} {s1 s2 : Nat+} :
    mk m1 s1 + mk m2 s2 = mk (s2.val • m1 + s1.val • m2) (s1 * s2) := LocalizedModule.mk_add_mk

/--
theorem `mk_add_mk_left` / 定理 `mk_add_mk_left`

English:
theorem mk_add_mk_left
  given: {m1 m2 : M} {s : Nat+}
  proof: by
  rw [mk_add_mk]; rw [mk_eq_mk]
  exact ⟨1, by simp [smul_smul]⟩

@[simp, norm_cast]

中文:
定理 mk_add_mk_left
  条件: {m1 m2 : M} {s : 自然数+}
  证明: by
  rw [mk_add_mk]; rw [mk_eq_mk]
  exact ⟨1, by simp [smul_smul]⟩

@[simp, norm_cast]

Depends on / 依赖: mk_add_mk, mk_eq_mk, smul_smul
-/
theorem mk_add_mk_left {m1 m2 : M} {s : Nat+} :
    mk m1 s + mk m2 s = mk (m1 + m2) s := by
  rw [mk_add_mk]; rw [mk_eq_mk]
  exact ⟨1, by simp [smul_smul]⟩

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: {m1 m2 : M}
  statement: ↑(m1 + m2) = (↑m1 + ↑m2 : DivisibleHull M)
  proof: by simp [mk_add_mk_left]

中文:
定理 coe_add
  条件: {m1 m2 : M}
  结论: ↑(m1 + m2) = (↑m1 + ↑m2 : DivisibleHull M)
  证明: by simp [mk_add_mk_left]

Depends on / 依赖: mk_add_mk_left
-/
theorem coe_add {m1 m2 : M} : ↑(m1 + m2) = (↑m1 + ↑m2 : DivisibleHull M) := by simp [mk_add_mk_left]

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `coeAddMonoidHom` / `coeAddMonoidHom` 的定义

English:
definition coeAddMonoidHom
  signature: : M ->+ DivisibleHull M where
  body: (↑)
  map_zero' := by simp
  map_add' := by simp

中文:
定义 coeAddMonoidHom
  签名: : M ->+ DivisibleHull M where
  定义体: (↑)
  map_zero' := by simp
  map_add' := by simp
-/
def coeAddMonoidHom : M ->+ DivisibleHull M where
  toFun := (↑)
  map_zero' := by simp
  map_add' := by simp

/--
theorem `nsmul_mk` / 定理 `nsmul_mk`

English:
theorem nsmul_mk
  given: (a : Nat) (m : M) (s : Nat+)
  statement: a • mk m s = mk (a • m) s
  proof: by
  induction a with
  | zero => simp
  | succ n h => simp [add_nsmul, mk_add_mk_left, h]

中文:
定理 nsmul_mk
  条件: (a : 自然数) (m : M) (s : 自然数+)
  结论: a • mk m s = mk (a • m) s
  证明: by
  induction a with
  | zero => simp
  | succ n h => simp [add_nsmul, mk_add_mk_left, h]

Depends on / 依赖: add_nsmul, mk_add_mk_left
-/
theorem nsmul_mk (a : Nat) (m : M) (s : Nat+) : a • mk m s = mk (a • m) s := by
  induction a with
  | zero => simp
  | succ n h => simp [add_nsmul, mk_add_mk_left, h]

/--
theorem `nnqsmul_mk` / 定理 `nnqsmul_mk`

English:
theorem nnqsmul_mk
  given: (a : Rat>=0) (m : M) (s : Nat+)
  proof: by
  convert! LocalizedModule.mk'_smul_mk Rat>=0 a.num m ⟨a.den, by simp⟩ (↑ⁿ s)
  simp [IsLocalization.eq_mk'_iff_mul_eq]

中文:
定理 nnqsmul_mk
  条件: (a : Rat>=0) (m : M) (s : 自然数+)
  证明: by
  convert! LocalizedModule.mk'_smul_mk Rat>=0 a.num m ⟨a.den, by simp⟩ (↑ⁿ s)
  simp [IsLocalization.eq_mk'_iff_mul_eq]

Depends on / 依赖: IsLocalization, IsLocalization.eq_mk, LocalizedModule, LocalizedModule.mk, _iff_mul_eq, _smul_mk, a.den, a.num, convert, eq_mk
-/
theorem nnqsmul_mk (a : Rat>=0) (m : M) (s : Nat+) :
    a • mk m s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s) := by
  convert! LocalizedModule.mk'_smul_mk Rat>=0 a.num m ⟨a.den, by simp⟩ (↑ⁿ s)
  simp [IsLocalization.eq_mk'_iff_mul_eq]

section TorsionFree
variable [IsAddTorsionFree M]

/--
theorem `mk_eq_mk_iff_smul_eq_smul` / 定理 `mk_eq_mk_iff_smul_eq_smul`

English:
theorem mk_eq_mk_iff_smul_eq_smul
  given: {m m' : M} {s s' : Nat+}
  proof: by
  aesop (add simp [mk_eq_mk, nsmul_right_inj])

中文:
定理 mk_eq_mk_iff_smul_eq_smul
  条件: {m m' : M} {s s' : 自然数+}
  证明: by
  aesop (add simp [mk_eq_mk, nsmul_right_inj])

Depends on / 依赖: mk_eq_mk, nsmul_right_inj
-/
theorem mk_eq_mk_iff_smul_eq_smul {m m' : M} {s s' : Nat+} :
    mk m s = mk m' s' ↔ s'.val • m = s.val • m' := by
  aesop (add simp [mk_eq_mk, nsmul_right_inj])

/--
theorem `mk_left_injective` / 定理 `mk_left_injective`

English:
theorem mk_left_injective
  given: (s : Nat+)
  statement: Function.Injective (fun (m : M) => mk m s)
  proof: by
  intro m n h
  simp_rw [mk_eq_mk_iff_smul_eq_smul] at h
  exact nsmul_right_injective (by simp) h

中文:
定理 mk_left_injective
  条件: (s : 自然数+)
  结论: Function.Injective (fun (m : M) => mk m s)
  证明: by
  intro m n h
  simp_rw [mk_eq_mk_iff_smul_eq_smul] at h
  exact nsmul_right_injective (by simp) h

Depends on / 依赖: mk_eq_mk_iff_smul_eq_smul, nsmul_right_injective, simp_rw
-/
theorem mk_left_injective (s : Nat+) : Function.Injective (fun (m : M) => mk m s) := by
  intro m n h
  simp_rw [mk_eq_mk_iff_smul_eq_smul] at h
  exact nsmul_right_injective (by simp) h

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : M -> DivisibleHull M)
  proof: mk_left_injective 1

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: Function.Injective ((↑) : M -> DivisibleHull M)
  证明: mk_left_injective 1

@[simp, norm_cast]

Depends on / 依赖: mk_left_injective
-/
theorem coe_injective : Function.Injective ((↑) : M -> DivisibleHull M) :=
  mk_left_injective 1

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {m m' : M}
  statement: (m : DivisibleHull M) = ↑m' ↔ m = m'
  proof: coe_injective.eq_iff

中文:
定理 coe_inj
  条件: {m m' : M}
  结论: (m : DivisibleHull M) = ↑m' ↔ m = m'
  证明: coe_injective.eq_iff

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {m m' : M} : (m : DivisibleHull M) = ↑m' ↔ m = m' :=
  coe_injective.eq_iff

end TorsionFree

section Group
variable {M : Type*} [AddCommGroup M]

/--
theorem `neg_mk` / 定理 `neg_mk`

English:
theorem neg_mk
  given: (m : M) (s : Nat+)
  statement: -mk m s = mk (-m) s
  proof: (eq_neg_of_add_eq_zero_left (by simp [mk_add_mk_left])).symm

noncomputable

中文:
定理 neg_mk
  条件: (m : M) (s : 自然数+)
  结论: -mk m s = mk (-m) s
  证明: (eq_neg_of_add_eq_zero_left (by simp [mk_add_mk_left])).symm

noncomputable

Depends on / 依赖: eq_neg_of_add_eq_zero_left, mk_add_mk_left
-/
theorem neg_mk (m : M) (s : Nat+) : -mk m s = mk (-m) s :=
  (eq_neg_of_add_eq_zero_left (by simp [mk_add_mk_left])).symm

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Rat (DivisibleHull M)
  body: (SignType.sign a : Int) • (show Rat>=0 from ⟨|a|, abs_nonneg _⟩) • x

中文:
实例 :
  签名: SMul Rat (DivisibleHull M)
  定义体: (SignType.sign a : Int) • (show Rat>=0 from ⟨|a|, abs_nonneg _⟩) • x

Depends on / 依赖: SignType, SignType.sign, abs_nonneg
-/
instance : SMul Rat (DivisibleHull M) where
  smul a x := (SignType.sign a : Int) • (show Rat>=0 from ⟨|a|, abs_nonneg _⟩) • x

/--
theorem `qsmul_def` / 定理 `qsmul_def`

English:
theorem qsmul_def
  given: (a : Rat) (x : DivisibleHull M)
  proof: rfl

中文:
定理 qsmul_def
  条件: (a : Rat) (x : DivisibleHull M)
  证明: rfl
-/
theorem qsmul_def (a : Rat) (x : DivisibleHull M) :
    a • x = (SignType.sign a : Int) • (show Rat>=0 from ⟨|a|, abs_nonneg _⟩) • x :=
  rfl

/--
theorem `zero_qsmul` / 定理 `zero_qsmul`

English:
theorem zero_qsmul
  given: (x : DivisibleHull M)
  statement: (0 : Rat) • x = 0
  proof: by
  simp [qsmul_def]

中文:
定理 zero_qsmul
  条件: (x : DivisibleHull M)
  结论: (0 : Rat) • x = 0
  证明: by
  simp [qsmul_def]

Depends on / 依赖: qsmul_def
-/
theorem zero_qsmul (x : DivisibleHull M) : (0 : Rat) • x = 0 := by
  simp [qsmul_def]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `qsmul_of_nonneg` / 定理 `qsmul_of_nonneg`

English:
theorem qsmul_of_nonneg
  given: {a : Rat} (h : 0 <= a) (x : DivisibleHull M)
  proof: by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_pos])

中文:
定理 qsmul_of_nonneg
  条件: {a : Rat} (h : 0 <= a) (x : DivisibleHull M)
  证明: by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_pos])

Depends on / 依赖: abs_of_pos, eq_or_lt, h.eq_or_lt, qsmul_def
-/
theorem qsmul_of_nonneg {a : Rat} (h : 0 <= a) (x : DivisibleHull M) :
    a • x = (show Rat>=0 from ⟨a, h⟩) • x := by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_pos])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `qsmul_of_nonpos` / 定理 `qsmul_of_nonpos`

English:
theorem qsmul_of_nonpos
  given: {a : Rat} (h : a <= 0) (x : DivisibleHull M)
  proof: by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_neg])

中文:
定理 qsmul_of_nonpos
  条件: {a : Rat} (h : a <= 0) (x : DivisibleHull M)
  证明: by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_neg])

Depends on / 依赖: abs_of_neg, eq_or_lt, h.eq_or_lt, qsmul_def
-/
theorem qsmul_of_nonpos {a : Rat} (h : a <= 0) (x : DivisibleHull M) :
    a • x = -((show Rat>=0 from ⟨-a, Left.nonneg_neg_iff.mpr h⟩) • x) := by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_neg])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `qsmul_mk` / 定理 `qsmul_mk`

English:
theorem qsmul_mk
  given: (a : Rat) (m : M) (s : Nat+)
  proof: by
  obtain h | h := le_total 0 a
  · rw [qsmul_of_nonneg h, nnqsmul_mk, ← natCast_zsmul]
    congr
    simpa using h
  · rw [qsmul_of_nonpos h]
    have : a.num.natAbs • m = -a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this, ← neg_mk]

中文:
定理 qsmul_mk
  条件: (a : Rat) (m : M) (s : 自然数+)
  证明: by
  obtain h | h := le_total 0 a
  · rw [qsmul_of_nonneg h, nnqsmul_mk, ← natCast_zsmul]
    congr
    simpa using h
  · rw [qsmul_of_nonpos h]
    have : a.num.natAbs • m = -a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this, ← neg_mk]

Depends on / 依赖: a.num, a.num.natAbs, le_total, natAbs, natCast_zsmul, neg_mk, nnqsmul_mk, qsmul_of_nonneg, qsmul_of_nonpos
-/
theorem qsmul_mk (a : Rat) (m : M) (s : Nat+) :
    a • mk m s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s) := by
  obtain h | h := le_total 0 a
  · rw [qsmul_of_nonneg h, nnqsmul_mk, ← natCast_zsmul]
    congr
    simpa using h
  · rw [qsmul_of_nonpos h]
    have : a.num.natAbs • m = -a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this, ← neg_mk]

set_option backward.isDefEq.respectTransparency false in
noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Rat (DivisibleHull M)
  body: by
    induction x with | mk m s
    simp [qsmul_of_nonneg zero_le_one, nnqsmul_mk]
  zero_smul := zero_qsmul
  smul_zero a := by simp [qsmul_def]
  smul_add a x y := by simp [qsmul_def, smul_add]
  add_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_add_mk, mk_eq_mk]
    us

中文:
实例 :
  签名: Module Rat (DivisibleHull M)
  定义体: by
    induction x with | mk m s
    simp [qsmul_of_nonneg zero_le_one, nnqsmul_mk]
  zero_smul := zero_qsmul
  smul_zero a := by simp [qsmul_def]
  smul_add a x y := by simp [qsmul_def, smul_add]
  add_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_add_mk, mk_eq_mk]
    us

Depends on / 依赖: Rat.add_num_de, a.den, a.num, add_num_de, add_smul, all_goals, b.den, b.num, convert, mk_add_mk, mk_eq_mk, natCast_zsmul, nnqsmul_mk, qsmul_def, qsmul_mk, qsmul_of_nonneg, ring_nf, simp_rw, smul_add, smul_smul
-/
instance : Module Rat (DivisibleHull M) where
  one_smul x := by
    induction x with | mk m s
    simp [qsmul_of_nonneg zero_le_one, nnqsmul_mk]
  zero_smul := zero_qsmul
  smul_zero a := by simp [qsmul_def]
  smul_add a x y := by simp [qsmul_def, smul_add]
  add_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_add_mk, mk_eq_mk]
    use 1
    suffices ((a + b).num * a.den * b.den * (s * s)) • m =
        ((a.num * b.den + b.num * a.den) * (a + b).den * (s * s)) • m by
      convert! this using 1
      all_goals
      simp [← natCast_zsmul, smul_smul, ← add_smul]
      ring_nf
    rw [Rat.add_num_den']
  mul_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_eq_mk]
    use 1
    suffices ((a * b).num * a.den * b.den * s) • m = (a.num * b.num * (a * b).den * s) • m by
      convert! this using 1
      all_goals
      simp [← natCast_zsmul, smul_smul]
      ring_nf
    rw [Rat.mul_num_den']

/--
theorem `zsmul_mk` / 定理 `zsmul_mk`

English:
theorem zsmul_mk
  given: (a : Int) (m : M) (s : Nat+)
  statement: a • mk m s = mk (a • m) s
  proof: by
  simp [← Int.cast_smul_eq_zsmul Rat a, qsmul_mk]

中文:
定理 zsmul_mk
  条件: (a : 整数) (m : M) (s : 自然数+)
  结论: a • mk m s = mk (a • m) s
  证明: by
  simp [← Int.cast_smul_eq_zsmul Rat a, qsmul_mk]

Depends on / 依赖: Int.cast_smul_eq_zsmul, cast_smul_eq_zsmul, qsmul_mk
-/
theorem zsmul_mk (a : Int) (m : M) (s : Nat+) : a • mk m s = mk (a • m) s := by
  simp [← Int.cast_smul_eq_zsmul Rat a, qsmul_mk]

end Group

section LinearOrder
variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

set_option backward.privateInPublic true in
/--
theorem `lift_aux` / 定理 `lift_aux`

English:
theorem lift_aux
  statement: (m n m' n' : M) (s t s' t' : Nat+)
  proof: by
  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  rw [propext_iff]; rw [← nsmul_le_nsmul_iff_right (mul_ne_zero s'.ne_zero t'.ne_zero)]
  convert! (nsmul_le_nsmul_iff_right (M := M) (mul_ne_zero s.ne_zero t.ne_zero)) using 2
  · simp_rw [smul_smul, mul_rotate s'.val, ← smul_smul, h, smul_smul]
    ring_

中文:
定理 lift_aux
  结论: (m n m' n' : M) (s t s' t' : 自然数+)
  证明: by
  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  rw [propext_iff]; rw [← nsmul_le_nsmul_iff_right (mul_ne_zero s'.ne_zero t'.ne_zero)]
  convert! (nsmul_le_nsmul_iff_right (M := M) (mul_ne_zero s.ne_zero t.ne_zero)) using 2
  · simp_rw [smul_smul, mul_rotate s'.val, ← smul_smul, h, smul_smul]
    ring_
-/
private theorem lift_aux (m n m' n' : M) (s t s' t' : Nat+)
    (h : mk m s = mk m' s') (h' : mk n t = mk n' t') :
    (t.val • m <= s.val • n) = (t'.val • m' <= s'.val • n') := by
  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  rw [propext_iff]; rw [← nsmul_le_nsmul_iff_right (mul_ne_zero s'.ne_zero t'.ne_zero)]
  convert! (nsmul_le_nsmul_iff_right (M := M) (mul_ne_zero s.ne_zero t.ne_zero)) using 2
  · simp_rw [smul_smul, mul_rotate s'.val, ← smul_smul, h, smul_smul]
    ring_nf
  · simp_rw [smul_smul, ← mul_rotate s'.val, ← smul_smul, ← h', smul_smul]
    ring_nf

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (DivisibleHull M)
  body: liftOn₂ x y (fun m s n t => t.val • m <= s.val • n) lift_aux

@[simp]

中文:
实例 :
  签名: LE (DivisibleHull M)
  定义体: liftOn₂ x y (fun m s n t => t.val • m <= s.val • n) lift_aux

@[simp]

Depends on / 依赖: lift_aux, s.val, t.val
-/
instance : LE (DivisibleHull M) where
  le x y := liftOn₂ x y (fun m s n t => t.val • m <= s.val • n) lift_aux

@[simp]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {m m' : M} {s s' : Nat+}
  proof: by rfl

中文:
定理 mk_le_mk
  条件: {m m' : M} {s s' : 自然数+}
  证明: by rfl
-/
theorem mk_le_mk {m m' : M} {s s' : Nat+} :
    mk m s <= mk m' s' ↔ s'.val • m <= s.val • m' := by rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (DivisibleHull M)
  body: by
    induction a with | mk m s
    simp
  le_trans a b c hab hbc := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    rw [mk_le_mk] at ⊢ hab hbc
    rw [← nsmul_le_nsmul_iff_right (show sb.val != 0 by simp)]; rw [smul_comm _ _ ma]; rw [smul_comm

中文:
实例 :
  签名: LinearOrder (DivisibleHull M)
  定义体: by
    induction a with | mk m s
    simp
  le_trans a b c hab hbc := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    rw [mk_le_mk] at ⊢ hab hbc
    rw [← nsmul_le_nsmul_iff_right (show sb.val != 0 by simp)]; rw [smul_comm _ _ ma]; rw [smul_comm

Depends on / 依赖: hab.trans, le_antisymm, le_trans, mk_le_mk, nsmul_le_nsmul_iff_right, sa.val, sb.val, sc.val, smul_comm
-/
instance : LinearOrder (DivisibleHull M) where
  le_refl a := by
    induction a with | mk m s
    simp
  le_trans a b c hab hbc := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    rw [mk_le_mk] at ⊢ hab hbc
    rw [← nsmul_le_nsmul_iff_right (show sb.val != 0 by simp)]; rw [smul_comm _ _ ma]; rw [smul_comm _ _ mc]
    rw [← nsmul_le_nsmul_iff_right (show sc.val != 0 by simp)]; rw [smul_comm _ _ mb] at hab
    rw [← nsmul_le_nsmul_iff_right (show sa.val != 0 by simp)] at hbc
    exact hab.trans hbc
  le_antisymm a b h h' := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    rw [mk_le_mk] at h h'
    rw [mk_eq_mk_iff_smul_eq_smul]
    exact le_antisymm h h'
  le_total a b := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    simp_rw [mk_le_mk]
    exact le_total _ _
  toDecidableLE := by
    unfold DecidableLE LE.le instLE liftOn₂ LocalizedModule.liftOn₂
    infer_instance

@[simp]
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  given: {m m' : M} {s s' : Nat+}
  statement: mk m s < mk m' s' ↔ s'.val • m < s.val • m'
  proof: by
  simp_rw [lt_iff_not_ge, mk_le_mk]

中文:
定理 mk_lt_mk
  条件: {m m' : M} {s s' : 自然数+}
  结论: mk m s < mk m' s' ↔ s'.val • m < s.val • m'
  证明: by
  simp_rw [lt_iff_not_ge, mk_le_mk]

Depends on / 依赖: lt_iff_not_ge, mk_le_mk, simp_rw
-/
theorem mk_lt_mk {m m' : M} {s s' : Nat+} : mk m s < mk m' s' ↔ s'.val • m < s.val • m' := by
  simp_rw [lt_iff_not_ge, mk_le_mk]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedCancelAddMonoid (DivisibleHull M)
  body: .of_add_lt_add_left (fun a b c h => by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_add_mk]
    rw [mk_lt_mk] at ⊢ h
    simp_rw [PNat.mul_coe, mul_smul, smul_add, smul_smul]
    have := add_lt_add_right (nsmul_lt_nsmul_right (sa * s

中文:
实例 :
  签名: IsOrderedCancelAddMonoid (DivisibleHull M)
  定义体: .of_add_lt_add_left (fun a b c h => by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_add_mk]
    rw [mk_lt_mk] at ⊢ h
    simp_rw [PNat.mul_coe, mul_smul, smul_add, smul_smul]
    have := add_lt_add_right (nsmul_lt_nsmul_right (sa * s

Depends on / 依赖: PNat.mul_coe, add_lt_add_right, convert, mk_add_mk, mk_lt_mk, mul_coe, mul_smul, ne_zero, nsmul_lt_nsmul_right, of_add_lt_add_left, sc.val, simp_rw, smul_add, smul_smul
-/
instance : IsOrderedCancelAddMonoid (DivisibleHull M) :=
  .of_add_lt_add_left (fun a b c h => by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_add_mk]
    rw [mk_lt_mk] at ⊢ h
    simp_rw [PNat.mul_coe, mul_smul, smul_add, smul_smul]
    have := add_lt_add_right (nsmul_lt_nsmul_right (sa * sa).ne_zero h) ((sa * sb * sc.val) • ma)
    simp_rw [PNat.mul_coe, smul_smul] at this
    convert! this using 3 <;> ring)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStrictOrderedModule Rat>=0 (DivisibleHull M)
  body: by
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_lt_mk] at h
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    exact (nsmul_right_strictMono (by simpa using ha.ne.symm)).lt_iff_lt

中文:
实例 :
  签名: IsStrictOrderedModule Rat>=0 (DivisibleHull M)
  定义体: by
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_lt_mk] at h
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    exact (nsmul_right_strictMono (by simpa using ha.ne.symm)).lt_iff_lt

Depends on / 依赖: PNat.mk_coe, PNat.mul_coe, a.num, convert, ha.ne.symm, lt_iff_lt, lt_iff_lt.mpr, mk_coe, mk_lt_mk, mul_coe, mul_lt_mul_of_pos_right, mul_right_comm, mul_smul, nnqsmul_mk, nsmul_right_strictMono, simp_rw, smul_lt_smul_of_pos_right, smul_smul
-/
instance : IsStrictOrderedModule Rat>=0 (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_lt_mk] at h
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    exact (nsmul_right_strictMono (by simpa using ha.ne.symm)).lt_iff_lt.mpr h
  smul_lt_smul_of_pos_right a ha b c h := by
    induction a with | mk m s
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe, PNat.mk_coe]
    refine smul_lt_smul_of_pos_right ?_ ?_
    · convert! mul_lt_mul_of_pos_right (NNRat.lt_def.mp h) (show 0 < s.val by simp) using 1 <;> ring
    · rw [← mk_zero 1, mk_lt_mk] at ha
      simpa using ha

end LinearOrder

section OrderedGroup
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStrictOrderedModule Rat (DivisibleHull M)
  body: by
    simp_rw [qsmul_of_nonneg ha.le]
    apply smul_lt_smul_of_pos_left h (by simpa using! ha)
  smul_lt_smul_of_pos_right a ha b c h := by
    apply lt_of_sub_pos
    rw [← sub_smul]
    simp_rw [qsmul_of_nonneg (sub_pos_of_lt h).le]
    apply smul_pos (by simpa [← NNRat.coe_pos] using! h) ha

中文:
实例 :
  签名: IsStrictOrderedModule Rat (DivisibleHull M)
  定义体: by
    simp_rw [qsmul_of_nonneg ha.le]
    apply smul_lt_smul_of_pos_left h (by simpa using! ha)
  smul_lt_smul_of_pos_right a ha b c h := by
    apply lt_of_sub_pos
    rw [← sub_smul]
    simp_rw [qsmul_of_nonneg (sub_pos_of_lt h).le]
    apply smul_pos (by simpa [← NNRat.coe_pos] using! h) ha

Depends on / 依赖: NNRat.coe_pos, coe_pos, ha.le, lt_of_sub_pos, qsmul_of_nonneg, simp_rw, smul_lt_smul_of_pos_left, smul_lt_smul_of_pos_right, smul_pos, sub_pos_of_lt, sub_smul
-/
instance : IsStrictOrderedModule Rat (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    simp_rw [qsmul_of_nonneg ha.le]
    apply smul_lt_smul_of_pos_left h (by simpa using! ha)
  smul_lt_smul_of_pos_right a ha b c h := by
    apply lt_of_sub_pos
    rw [← sub_smul]
    simp_rw [qsmul_of_nonneg (sub_pos_of_lt h).le]
    apply smul_pos (by simpa [← NNRat.coe_pos] using! h) ha

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as an `OrderAddMonoidHom`. -/
@[simps!]
/--
Definition of `coeOrderAddMonoidHom` / `coeOrderAddMonoidHom` 的定义

English:
definition coeOrderAddMonoidHom
  signature: : M ->+o DivisibleHull M where
  body: coeAddMonoidHom M
  monotone' a b h := by simpa using h

中文:
定义 coeOrderAddMonoidHom
  签名: : M ->+o DivisibleHull M where
  定义体: coeAddMonoidHom M
  monotone' a b h := by simpa using h

Depends on / 依赖: coeAddMonoidHom
-/
def coeOrderAddMonoidHom : M ->+o DivisibleHull M where
  __ := coeAddMonoidHom M
  monotone' a b h := by simpa using h

/--
theorem `archimedeanClassMk_mk_eq` / 定理 `archimedeanClassMk_mk_eq`

English:
theorem archimedeanClassMk_mk_eq
  given: (m : M) (s s' : Nat+)
  proof: by
  suffices (s : Int) • mk m s = (s' : Int) • mk m s' by
    apply_fun ArchimedeanClass.mk at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    exact this
  simp_rw [zsmul_mk, mk_eq_mk_iff_smul_eq_smul, natCast_zsmul, smul_smul, mu

中文:
定理 archimedeanClassMk_mk_eq
  条件: (m : M) (s s' : 自然数+)
  证明: by
  suffices (s : Int) • mk m s = (s' : Int) • mk m s' by
    apply_fun ArchimedeanClass.mk at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    exact this
  simp_rw [zsmul_mk, mk_eq_mk_iff_smul_eq_smul, natCast_zsmul, smul_smul, mu

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk, ArchimedeanClass.mk_smul, apply_fun, mk_eq_mk_iff_smul_eq_smul, mk_smul, mul_comm, natCast_zsmul, simp_rw, smul_smul, zsmul_mk
-/
theorem archimedeanClassMk_mk_eq (m : M) (s s' : Nat+) :
    ArchimedeanClass.mk (mk m s) = ArchimedeanClass.mk (mk m s') := by
  suffices (s : Int) • mk m s = (s' : Int) • mk m s' by
    apply_fun ArchimedeanClass.mk at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    exact this
  simp_rw [zsmul_mk, mk_eq_mk_iff_smul_eq_smul, natCast_zsmul, smul_smul, mul_comm s'.val]

set_option backward.privateInPublic true in
variable (M) in
/-- Forward direction of `archimedeanClassOrderIso`. -/
private noncomputable
/--
Definition of `archimedeanClassOrderHom` / `archimedeanClassOrderHom` 的定义

English:
definition archimedeanClassOrderHom
  signature: : ArchimedeanClass M ->o ArchimedeanClass (DivisibleHull M)
  body: ArchimedeanClass.orderHom (coeOrderAddMonoidHom M)

中文:
定义 archimedeanClassOrderHom
  签名: : ArchimedeanClass M ->o ArchimedeanClass (DivisibleHull M)
  定义体: ArchimedeanClass.orderHom (coeOrderAddMonoidHom M)

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.orderHom, coeOrderAddMonoidHom, orderHom
-/
def archimedeanClassOrderHom : ArchimedeanClass M ->o ArchimedeanClass (DivisibleHull M) :=
  ArchimedeanClass.orderHom (coeOrderAddMonoidHom M)

set_option backward.privateInPublic true in
/--
theorem `aux_archimedeanClassMk_mk` / 定理 `aux_archimedeanClassMk_mk`

English:
theorem aux_archimedeanClassMk_mk
  given: (m : M) (s : Nat+)
  proof: by
  rw [archimedeanClassOrderHom]; rw [ArchimedeanClass.orderHom_mk]; rw [coeOrderAddMonoidHom_apply]
  apply archimedeanClassMk_mk_eq

中文:
定理 aux_archimedeanClassMk_mk
  条件: (m : M) (s : 自然数+)
  证明: by
  rw [archimedeanClassOrderHom]; rw [ArchimedeanClass.orderHom_mk]; rw [coeOrderAddMonoidHom_apply]
  apply archimedeanClassMk_mk_eq
-/
private theorem aux_archimedeanClassMk_mk (m : M) (s : Nat+) :
    ArchimedeanClass.mk (mk m s) = archimedeanClassOrderHom M (ArchimedeanClass.mk m) := by
  rw [archimedeanClassOrderHom]; rw [ArchimedeanClass.orderHom_mk]; rw [coeOrderAddMonoidHom_apply]
  apply archimedeanClassMk_mk_eq

/--
theorem `aux_archimedeanClassOrderHom_injective` / 定理 `aux_archimedeanClassOrderHom_injective`

English:
theorem aux_archimedeanClassOrderHom_injective
  proof: ArchimedeanClass.orderHom_injective coe_injective

中文:
定理 aux_archimedeanClassOrderHom_injective
  证明: ArchimedeanClass.orderHom_injective coe_injective
-/
private theorem aux_archimedeanClassOrderHom_injective :
    Function.Injective (archimedeanClassOrderHom M) :=
  ArchimedeanClass.orderHom_injective coe_injective

set_option backward.privateInPublic true in
variable (M) in
/-- Backward direction of `archimedeanClassOrderIso`. -/
private noncomputable
/--
Definition of `archimedeanClassOrderHomInv` / `archimedeanClassOrderHomInv` 的定义

English:
definition archimedeanClassOrderHomInv
  signature: : ArchimedeanClass (DivisibleHull M) ->o ArchimedeanClass M
  body: ArchimedeanClass.liftOrderHom (fun x => x.liftOn (fun m s => ArchimedeanClass.mk m)
    (fun _ _ _ _ h => by
      apply aux_archimedeanClassOrderHom_injective
      apply_fun ArchimedeanClass.mk at h
      simpa [aux_archimedeanClassMk_mk] using h))
    (fun a b h => by
      induction a with | mk 

中文:
定义 archimedeanClassOrderHomInv
  签名: : ArchimedeanClass (DivisibleHull M) ->o ArchimedeanClass M
  定义体: ArchimedeanClass.liftOrderHom (fun x => x.liftOn (fun m s => ArchimedeanClass.mk m)
    (fun _ _ _ _ h => by
      apply aux_archimedeanClassOrderHom_injective
      apply_fun ArchimedeanClass.mk at h
      simpa [aux_archimedeanClassMk_mk] using h))
    (fun a b h => by
      induction a with | mk 

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.liftOrderHom, ArchimedeanClass.mk, apply_fun, archimedeanClassOrderHom, aux_archimedeanClassMk_mk, aux_archimedeanClassOrderHom_injective, le_iff_le, le_iff_le.mp, liftOn, liftOrderHom, monotone, monotone.strictMono_of_injective, simp_rw, strictMono_of_injective, x.liftOn
-/
def archimedeanClassOrderHomInv : ArchimedeanClass (DivisibleHull M) ->o ArchimedeanClass M :=
  ArchimedeanClass.liftOrderHom (fun x => x.liftOn (fun m s => ArchimedeanClass.mk m)
    (fun _ _ _ _ h => by
      apply aux_archimedeanClassOrderHom_injective
      apply_fun ArchimedeanClass.mk at h
      simpa [aux_archimedeanClassMk_mk] using h))
    (fun a b h => by
      induction a with | mk _ _
      induction b with | mk _ _
      simp_rw [aux_archimedeanClassMk_mk] at h
      simpa using ((archimedeanClassOrderHom M).monotone.strictMono_of_injective
        aux_archimedeanClassOrderHom_injective).le_iff_le.mp h)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (M) in
/-- The Archimedean classes of `DivisibleHull M` are the same as those of `M`. -/
noncomputable
/--
Definition of `archimedeanClassOrderIso` / `archimedeanClassOrderIso` 的定义

English:
definition archimedeanClassOrderIso
  signature: : ArchimedeanClass M ≃o ArchimedeanClass (DivisibleHull M)
  body: by
  apply OrderIso.ofHomInv (archimedeanClassOrderHom M) (archimedeanClassOrderHomInv M)
  · ext a
    induction a with | mk a
    induction a with | mk m s
    suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
      simpa [archimedeanClassOrderHom, archimedeanClassOrderHomInv

中文:
定义 archimedeanClassOrderIso
  签名: : ArchimedeanClass M ≃o ArchimedeanClass (DivisibleHull M)
  定义体: by
  apply OrderIso.ofHomInv (archimedeanClassOrderHom M) (archimedeanClassOrderHomInv M)
  · ext a
    induction a with | mk a
    induction a with | mk m s
    suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
      simpa [archimedeanClassOrderHom, archimedeanClassOrderHomInv

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk, OrderIso, OrderIso.ofHomInv, archimedeanClassOrderHom, archimedeanClassOrderHomInv, aux_archimedeanClassMk_mk, ofHomInv, simp_rw
-/
def archimedeanClassOrderIso : ArchimedeanClass M ≃o ArchimedeanClass (DivisibleHull M) := by
  apply OrderIso.ofHomInv (archimedeanClassOrderHom M) (archimedeanClassOrderHomInv M)
  · ext a
    induction a with | mk a
    induction a with | mk m s
    suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
      simpa [archimedeanClassOrderHom, archimedeanClassOrderHomInv]
    simp_rw [aux_archimedeanClassMk_mk]
  · ext a
    induction a with | mk _
    simp [archimedeanClassOrderHom, archimedeanClassOrderHomInv]

@[simp]
/--
theorem `archimedeanClassOrderIso_apply` / 定理 `archimedeanClassOrderIso_apply`

English:
theorem archimedeanClassOrderIso_apply
  given: (a : ArchimedeanClass M)
  proof: rfl

@[simp]

中文:
定理 archimedeanClassOrderIso_apply
  条件: (a : ArchimedeanClass M)
  证明: rfl

@[simp]
-/
theorem archimedeanClassOrderIso_apply (a : ArchimedeanClass M) :
    archimedeanClassOrderIso M a = ArchimedeanClass.orderHom (coeOrderAddMonoidHom M) a := rfl

@[simp]
/--
theorem `archimedeanClassOrderIso_symm_apply` / 定理 `archimedeanClassOrderIso_symm_apply`

English:
theorem archimedeanClassOrderIso_symm_apply
  given: (m : M) (s : Nat+)
  proof: rfl

中文:
定理 archimedeanClassOrderIso_symm_apply
  条件: (m : M) (s : 自然数+)
  证明: rfl
-/
theorem archimedeanClassOrderIso_symm_apply (m : M) (s : Nat+) :
    (archimedeanClassOrderIso M).symm (ArchimedeanClass.mk (mk m s)) = ArchimedeanClass.mk m := rfl

end OrderedGroup

end DivisibleHull
