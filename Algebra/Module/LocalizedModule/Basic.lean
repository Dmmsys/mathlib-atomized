/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definitions

* `LocalizedModule.r`: the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `LocalizedModule M S`: the localized module by `S`.
* `LocalizedModule.mk`: the canonical map sending `(m, s) : M × S ↦ m/s : LocalizedModule M S`
* `LocalizedModule.liftOn`: any well-defined function `f : M × S → α` respecting `r` descents to
  a function `LocalizedModule M S → α`
* `LocalizedModule.liftOn₂`: any well-defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `LocalizedModule M S → LocalizedModule M S`
* `LocalizedModule.mk_add_mk`: in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `LocalizedModule.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : Localization S` is localized ring
  by `S`.
* `LocalizedModule.isModule` : `LocalizedModule M S` is a `Localization S`-module.

## Future work

* Redefine `Localization` for monoids and rings to coincide with `LocalizedModule`.
-/

@[expose] public section

open Module

namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable (M : Type v) [AddCommMonoid M] [Module R M]
variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]
variable (T' : Type*) [CommSemiring T'] [Algebra R T'] [IsLocalization S T']

/--
Definition of `r` / `r` 的定义

English:
definition r
  signature: (a b : M × S)
  body: exists u : S, u • b.2 • a.1 = u • a.2 • b.1

中文:
定义 r
  签名: (a b : M × S)
  定义体: exists u : S, u • b.2 • a.1 = u • a.2 • b.1
-/
def r (a b : M × S) : Prop :=
  exists u : S, u • b.2 • a.1 = u • a.2 • b.1

/--
lemma `oreEqv_eq_r` / 引理 `oreEqv_eq_r`

English:
lemma oreEqv_eq_r
  statement: (OreLocalization.oreEqv S M).r = r S M
  proof: by
  ext a b
  constructor
  · rintro ⟨u, v, h₁, h₂⟩
    use u
    simp only [Submonoid.smul_def, smul_smul, h₂]
    rw [mul_comm]; rw [mul_smul]; rw [← h₁]; rw [mul_comm]; rw [mul_smul]; rw [Submonoid.smul_def]
  · rintro ⟨u, hu⟩
    use u * a.2, u * b.2
    rw [mul_smul]; rw [← hu]; rw [mul_smul]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_comm (a.2 : R)]
    simp [Submonoid.smul_def]

中文:
引理 oreEqv_eq_r
  结论: (OreLocalization.oreEqv S M).r = r S M
  证明: by
  ext a b
  constructor
  · rintro ⟨u, v, h₁, h₂⟩
    use u
    simp only [Submonoid.smul_def, smul_smul, h₂]
    rw [mul_comm]; rw [mul_smul]; rw [← h₁]; rw [mul_comm]; rw [mul_smul]; rw [Submonoid.smul_def]
  · rintro ⟨u, hu⟩
    use u * a.2, u * b.2
    rw [mul_smul]; rw [← hu]; rw [mul_smul]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_comm (a.2 : R)]
    simp [Submonoid.smul_def]

Depends on / 依赖: Submonoid, Submonoid.coe_mul, Submonoid.smul_def, coe_mul, mul_assoc, mul_comm, mul_smul, smul_def, smul_smul
-/
lemma oreEqv_eq_r : (OreLocalization.oreEqv S M).r = r S M := by
  ext a b
  constructor
  · rintro ⟨u, v, h₁, h₂⟩
    use u
    simp only [Submonoid.smul_def, smul_smul, h₂]
    rw [mul_comm]; rw [mul_smul]; rw [← h₁]; rw [mul_comm]; rw [mul_smul]; rw [Submonoid.smul_def]
  · rintro ⟨u, hu⟩
    use u * a.2, u * b.2
    rw [mul_smul]; rw [← hu]; rw [mul_smul]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_comm (a.2 : R)]
    simp [Submonoid.smul_def]

/--
theorem `r.isEquiv` / 定理 `r.isEquiv`

English:
theorem r.isEquiv
  statement: IsEquiv _ (r S M)
  proof: { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2']; rw [hu1']
    symm := fun ⟨_, _⟩ ⟨_, _⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

中文:
定理 r.isEquiv
  结论: Is等价 _ (r S M)
  证明: { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2']; rw [hu1']
    symm := fun ⟨_, _⟩ ⟨_, _⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

Depends on / 依赖: one_smul
-/
theorem r.isEquiv : IsEquiv _ (r S M) :=
  { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2']; rw [hu1']
    symm := fun ⟨_, _⟩ ⟨_, _⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

/--
Instance `r.setoid` / 实例 `r.setoid`

English:
instance r.setoid
  signature: : Setoid (M × S) where
  body: r S M
  iseqv := ⟨(r.isEquiv S M).refl, (r.isEquiv S M).symm _ _, (r.isEquiv S M).trans _ _ _⟩

中文:
实例 r.setoid
  签名: : 集合等价关系 (M × S) where
  定义体: r S M
  iseqv := ⟨(r.isEquiv S M).refl, (r.isEquiv S M).symm _ _, (r.isEquiv S M).trans _ _ _⟩
-/
instance r.setoid : Setoid (M × S) where
  r := r S M
  iseqv := ⟨(r.isEquiv S M).refl, (r.isEquiv S M).symm _ _, (r.isEquiv S M).trans _ _ _⟩

/--
Definition of `_root_.LocalizedModule` / `_root_.LocalizedModule` 的定义

English:
abbreviation _root_.LocalizedModule
  signature: : Type max u v
  body: OreLocalization S M

中文:
缩写 _root_.LocalizedModule
  签名: : 类型 最大值 u v
  定义体: OreLocalization S M

Depends on / 依赖: OreLocalization
-/
abbrev _root_.LocalizedModule : Type max u v :=
  OreLocalization S M

/--
lemma `example_localization_eq_localizedModule` / 引理 `example_localization_eq_localizedModule`

English:
lemma example_localization_eq_localizedModule
  proof: by
  with_reducible rfl

中文:
引理 example_localization_eq_localizedModule
  证明: by
  with_reducible rfl
-/
private lemma example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl

section

variable {M S}

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (m : M) (s : S)
  body: m /ₒ s

中文:
缩写 mk
  签名: (m : M) (s : S)
  定义体: m /ₒ s
-/
abbrev mk (m : M) (s : S) : LocalizedModule S M := m /ₒ s

/--
theorem `mk_eq` / 定理 `mk_eq`

English:
theorem mk_eq
  given: {m m' : M} {s s' : S}
  statement: mk m s = mk m' s' ↔ exists u : S, u • s' • m = u • s • m'
  proof: by
  rw [mk]; rw [mk]; rw [OreLocalization.oreDiv_eq_iff]
  exact congr($(oreEqv_eq_r S M) ⟨m, s⟩ ⟨m', s'⟩)

@[elab_as_elim, induction_eliminator, cases_eliminator]

中文:
定理 mk_eq
  条件: {m m' : M} {s s' : S}
  结论: mk m s = mk m' s' ↔ 存在 u : S, u • s' • m = u • s • m'
  证明: by
  rw [mk]; rw [mk]; rw [OreLocalization.oreDiv_eq_iff]
  exact congr($(oreEqv_eq_r S M) ⟨m, s⟩ ⟨m', s'⟩)

@[elab_as_elim, induction_eliminator, cases_eliminator]

Depends on / 依赖: OreLocalization, OreLocalization.oreDiv_eq_iff, oreDiv_eq_iff, oreEqv_eq_r
-/
theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ exists u : S, u • s' • m = u • s • m' := by
  rw [mk]; rw [mk]; rw [OreLocalization.oreDiv_eq_iff]
  exact congr($(oreEqv_eq_r S M) ⟨m, s⟩ ⟨m', s'⟩)

@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {β : LocalizedModule S M -> Prop} (h : forall (m : M) (s : S), β (mk m s))
  proof: by
  rintro ⟨⟨m, s⟩⟩
  exact h m s

@[elab_as_elim]

中文:
定理 induction_on
  条件: {β : LocalizedModule S M -> 命题} (h : 对任意 (m : M) (s : S), β (mk m s))
  证明: by
  rintro ⟨⟨m, s⟩⟩
  exact h m s

@[elab_as_elim]
-/
theorem induction_on {β : LocalizedModule S M -> Prop} (h : forall (m : M) (s : S), β (mk m s)) :
    forall x : LocalizedModule S M, β x := by
  rintro ⟨⟨m, s⟩⟩
  exact h m s

@[elab_as_elim]
/--
theorem `induction_on₂` / 定理 `induction_on₂`

English:
theorem induction_on₂
  statement: {β : LocalizedModule S M -> LocalizedModule S M -> Prop}
  proof: by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'

中文:
定理 induction_on₂
  结论: {β : LocalizedModule S M -> LocalizedModule S M -> 命题}
  证明: by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'
-/
theorem induction_on₂ {β : LocalizedModule S M -> LocalizedModule S M -> Prop}
    (h : forall (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : forall x y, β x y := by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: {α : Type*} (x : LocalizedModule S M) (f : M × S -> α)
  body: Quotient.liftOn x f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)

中文:
定义 liftOn
  签名: {α : 类型} (x : LocalizedModule S M) (f : M × S -> α)
  定义体: Quotient.liftOn x f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)

Depends on / 依赖: Quotient, Quotient.liftOn, instances, liftOn, oreEqv_eq_r, r.setoid, setoid
-/
def liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S -> α)
    (wd : forall (p p' : M × S), p ≈ p' -> f p = f p') : α :=
  Quotient.liftOn x f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)

/--
theorem `liftOn_mk` / 定理 `liftOn_mk`

English:
theorem liftOn_mk
  statement: {α : Type*} {f : M × S -> α} (wd : forall (p p' : M × S), p ≈ p' -> f p = f p')
  proof: by convert! Quotient.liftOn_mk f wd ⟨m, s⟩

中文:
定理 liftOn_mk
  结论: {α : 类型} {f : M × S -> α} (wd : 对任意 (p p' : M × S), p ≈ p' -> f p = f p')
  证明: by convert! Quotient.liftOn_mk f wd ⟨m, s⟩

Depends on / 依赖: Quotient, Quotient.liftOn_mk, convert, liftOn_mk
-/
theorem liftOn_mk {α : Type*} {f : M × S -> α} (wd : forall (p p' : M × S), p ≈ p' -> f p = f p')
    (m : M) (s : S) : liftOn (mk m s) f wd = f ⟨m, s⟩ := by convert! Quotient.liftOn_mk f wd ⟨m, s⟩

/--
Definition of `liftOn₂` / `liftOn₂` 的定义

English:
definition liftOn₂
  signature: {α : Type*} (x y : LocalizedModule S M) (f : M × S -> M × S -> α)
  body: Quotient.liftOn₂ x y f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)

中文:
定义 liftOn₂
  签名: {α : 类型} (x y : LocalizedModule S M) (f : M × S -> M × S -> α)
  定义体: Quotient.liftOn₂ x y f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)

Depends on / 依赖: Quotient, Quotient.liftOn, instances, oreEqv_eq_r, r.setoid, setoid
-/
def liftOn₂ {α : Type*} (x y : LocalizedModule S M) (f : M × S -> M × S -> α)
    (wd : forall (p q p' q' : M × S), p ≈ p' -> q ≈ q' -> f p q = f p' q') : α :=
  Quotient.liftOn₂ x y f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)

/--
theorem `liftOn₂_mk` / 定理 `liftOn₂_mk`

English:
theorem liftOn₂_mk
  statement: {α : Type*} (f : M × S -> M × S -> α)
  proof: by
  convert! Quotient.liftOn₂_mk f wd _ _

中文:
定理 liftOn₂_mk
  结论: {α : 类型} (f : M × S -> M × S -> α)
  证明: by
  convert! Quotient.liftOn₂_mk f wd _ _

Depends on / 依赖: Quotient, Quotient.liftOn, convert
-/
theorem liftOn₂_mk {α : Type*} (f : M × S -> M × S -> α)
    (wd : forall (p q p' q' : M × S), p ≈ p' -> q ≈ q' -> f p q = f p' q') (m m' : M)
    (s s' : S) : liftOn₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ := by
  convert! Quotient.liftOn₂_mk f wd _ _

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (h : 0 in S)
  statement: Subsingleton (LocalizedModule S M)
  proof: by
  refine ⟨fun a b => ?_⟩
  induction a, b using LocalizedModule.induction_on₂
  exact mk_eq.mpr ⟨⟨0, h⟩, by simp only [Submonoid.mk_smul, zero_smul]⟩

中文:
定理 subsingleton
  条件: (h : 0 in S)
  结论: 子单例 (LocalizedModule S M)
  证明: by
  refine ⟨fun a b => ?_⟩
  induction a, b using LocalizedModule.induction_on₂
  exact mk_eq.mpr ⟨⟨0, h⟩, by simp only [Submonoid.mk_smul, zero_smul]⟩

Depends on / 依赖: LocalizedModule, LocalizedModule.induction_on, Submonoid, Submonoid.mk_smul, mk_eq, mk_eq.mpr, mk_smul, zero_smul
-/
theorem subsingleton (h : 0 in S) : Subsingleton (LocalizedModule S M) := by
  refine ⟨fun a b => ?_⟩
  induction a, b using LocalizedModule.induction_on₂
  exact mk_eq.mpr ⟨⟨0, h⟩, by simp only [Submonoid.mk_smul, zero_smul]⟩

/--
theorem `zero_mk` / 定理 `zero_mk`

English:
theorem zero_mk
  given: (s : S)
  statement: mk (0 : M) s = 0
  proof: by simp [mk]

中文:
定理 zero_mk
  条件: (s : S)
  结论: mk (0 : M) s = 0
  证明: by simp [mk]
-/
theorem zero_mk (s : S) : mk (0 : M) s = 0 := by simp [mk]

/--
theorem `mk_add_mk` / 定理 `mk_add_mk`

English:
theorem mk_add_mk
  given: {m1 m2 : M} {s1 s2 : S}
  proof: by
  simp [mk, OreLocalization.oreDiv_add_oreDiv, mul_comm s1 s2, Submonoid.smul_def]

中文:
定理 mk_add_mk
  条件: {m1 m2 : M} {s1 s2 : S}
  证明: by
  simp [mk, OreLocalization.oreDiv_add_oreDiv, mul_comm s1 s2, Submonoid.smul_def]

Depends on / 依赖: OreLocalization, OreLocalization.oreDiv_add_oreDiv, Submonoid, Submonoid.smul_def, mul_comm, oreDiv_add_oreDiv, smul_def
-/
theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) := by
  simp [mk, OreLocalization.oreDiv_add_oreDiv, mul_comm s1 s2, Submonoid.smul_def]

/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  given: {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S}
  proof: by simp [mk]

中文:
定理 mk_neg
  条件: {M : 类型} [加法交换群 M] [模 R M] {m : M} {s : S}
  证明: by simp [mk]
-/
theorem mk_neg {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S} :
    mk (-m) s = -mk m s := by simp [mk]

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R}
  body: liftOn₂ m₁ m₂ (fun x₁ x₂ => LocalizedModule.mk (x₁.1 * x₂.1) (x₂.2 * x₁.2)) (by
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
    simp only [mul_comm s₂ s₁, mul_comm t₂ t₁]
    rw [mk_eq]
    use u₁ * u₂
    dsimp [Submonoid.smul_def] at *
    simp only [mul_smul_mul_comm, e₁, e₂])

中文:
定义 mul
  签名: {A : 类型} [半环 A] [代数 R A] {S : 子幺半群 R}
  定义体: liftOn₂ m₁ m₂ (fun x₁ x₂ => LocalizedModule.mk (x₁.1 * x₂.1) (x₂.2 * x₁.2)) (by
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
    simp only [mul_comm s₂ s₁, mul_comm t₂ t₁]
    rw [mk_eq]
    use u₁ * u₂
    dsimp [Submonoid.smul_def] at *
    simp only [mul_smul_mul_comm, e₁, e₂])
-/
protected def mul {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R}
    (m₁ m₂ : LocalizedModule S A) : LocalizedModule S A :=
  liftOn₂ m₁ m₂ (fun x₁ x₂ => LocalizedModule.mk (x₁.1 * x₂.1) (x₂.2 * x₁.2)) (by
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
    simp only [mul_comm s₂ s₁, mul_comm t₂ t₁]
    rw [mk_eq]
    use u₁ * u₂
    dsimp [Submonoid.smul_def] at *
    simp only [mul_smul_mul_comm, e₁, e₂])

instance (priority := 900) {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Monoid (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : One (LocalizedModule S A))
    mul := LocalizedModule.mul
    one_mul := by
      rintro ⟨a, s⟩
      with_unfolding_all exact mk_eq.mpr ⟨1, by simp only [one_mul, mul_one, one_smul]⟩
    mul_one := by
      rintro ⟨a, s⟩
      with_unfolding_all exact mk_eq.mpr ⟨1, by simp only [mul_one, one_smul, one_mul]⟩
    mul_assoc := by with_unfolding_all
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      apply mk_eq.mpr _
      use 1
      simp only [one_mul, smul_smul, ← mul_assoc, mul_right_comm] }

set_option backward.isDefEq.respectTransparency false in
/--
lemma `example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid` / 引理 `example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid`

English:
lemma example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid
  proof: by
  with_reducible_and_instances rfl

中文:
引理 example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid
  证明: by
  with_reducible_and_instances rfl
-/
private lemma example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid :
    OreLocalization.instMonoid = LocalizedModule.instMonoid (A := R) (S := S) := by
  with_reducible_and_instances rfl

/--
theorem `mk_mul_mk'` / 定理 `mk_mul_mk'`

English:
theorem mk_mul_mk'
  given: {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S}
  proof: rfl

中文:
定理 mk_mul_mk'
  条件: {A : 类型} [半环 A] [代数 R A] {a₁ a₂ : A} {s₁ s₂ : S}
  证明: rfl
-/
theorem mk_mul_mk' {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₂ * s₁) := rfl

/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S}
  proof: by rw [mk_mul_mk', mul_comm s₁ s₂]

中文:
定理 mk_mul_mk
  条件: {A : 类型} [半环 A] [代数 R A] {a₁ a₂ : A} {s₁ s₂ : S}
  证明: by rw [mk_mul_mk', mul_comm s₁ s₂]

Depends on / 依赖: mk_mul_mk, mul_comm
-/
theorem mk_mul_mk {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂) := by rw [mk_mul_mk', mul_comm s₁ s₂]

/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} (n : Nat) (a : A) (s : S)
  proof: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [pow_zero]; rw [OreLocalization.one_def]
  | succ n ih =>
    simp only [pow_succ', ih, LocalizedModule.mk_mul_mk]

中文:
定理 mk_pow
  条件: {A : 类型} [半环 A] [代数 R A] {S : 子幺半群 R} (n : 自然数) (a : A) (s : S)
  证明: by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [pow_zero]; rw [OreLocalization.one_def]
  | succ n ih =>
    simp only [pow_succ', ih, LocalizedModule.mk_mul_mk]

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_mul_mk, OreLocalization, OreLocalization.one_def, mk_mul_mk, one_def, pow_succ, pow_zero
-/
theorem mk_pow {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} (n : Nat) (a : A) (s : S) :
    mk a s ^ n = mk (a ^ n) (s ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]; rw [pow_zero]; rw [pow_zero]; rw [OreLocalization.one_def]
  | succ n ih =>
    simp only [pow_succ', ih, LocalizedModule.mk_mul_mk]

-- For the instance on `Localization S`, we prefer `OreLocalization.instSemiring`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
instance (priority := 900) {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Semiring (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : AddCommMonoid (LocalizedModule S A))
    __ := (inferInstance : Monoid (LocalizedModule S A))
    left_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      change a₁ /ₒ s₁ * (a₂ /ₒ s₂ + a₃ /ₒ s₃) = a₁ /ₒ s₁ * (a₂ /ₒ s₂) + a₁ /ₒ s₁ * (a₃ /ₒ s₃)
      rw [← mk]; rw [← mk]; rw [← mk]; rw [mk_mul_mk]; rw [mk_mul_mk]; rw [mk_add_mk]; rw [mk_mul_mk]; rw [mk_add_mk]
      apply mk_eq.mpr _
      use 1
      simp only [← mul_assoc, mul_right_comm, mul_add, mul_smul_comm, smul_add, smul_smul, one_mul]
    right_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      change (a₁ /ₒ s₁ + a₂ /ₒ s₂) * (a₃ /ₒ s₃) = a₁ /ₒ s₁ * (a₃ /ₒ s₃) + a₂ /ₒ s₂ * (a₃ /ₒ s₃)
      rw [← mk]; rw [← mk]; rw [← mk]; rw [mk_mul_mk]; rw [mk_mul_mk]; rw [mk_add_mk]; rw [mk_mul_mk]; rw [mk_add_mk]
      apply mk_eq.mpr _
      use 1
      simp only [one_mul, smul_add, add_mul, smul_smul, ← mul_assoc, smul_mul_assoc,
        mul_right_comm]
    zero_mul := by with_unfolding_all
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [zero_mul, smul_zero]⟩
    mul_zero := by with_unfolding_all
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [mul_zero, smul_zero]⟩ }

-- For the instance on `Localization S`, we prefer `OreLocalization.instCommSemiring`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
instance (priority := 900) {A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R} :
    CommSemiring (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : Semiring (LocalizedModule S A))
    mul_comm := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩
      exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩ }

-- For the instance on `Localization S`, we prefer `OreLocalization.instRing`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
instance (priority := 900) {A : Type*} [Ring A] [Algebra R A] {S : Submonoid R} :
    Ring (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : AddCommGroup (LocalizedModule S A))
    __ := (inferInstance : Semiring (LocalizedModule S A)) }

-- For the instance on `Localization S`, we prefer `OreLocalization.instCommRing`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
instance (priority := 900) {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R} :
    CommRing (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : Ring (LocalizedModule S A))
    __ := (inferInstance : CommSemiring (LocalizedModule S A)) }

set_option backward.isDefEq.respectTransparency false in
/--
lemma `example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing` / 引理 `example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing`

English:
lemma example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing
  proof: by
  with_reducible_and_instances rfl

中文:
引理 example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing
  证明: by
  with_reducible_and_instances rfl
-/
private lemma example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing
    {R : Type*} [CommRing R] {S : Submonoid R} :
    OreLocalization.instCommRing = (LocalizedModule.instCommRing : CommRing R[S⁻¹]) := by
  with_reducible_and_instances rfl

/--
theorem `smul'_mk` / 定理 `smul'_mk`

English:
theorem smul'_mk
  proof: by
  rw [OreLocalization.smul_oreDiv]
  simp

中文:
定理 smul'_mk
  证明: by
  rw [OreLocalization.smul_oreDiv]
  simp

Depends on / 依赖: OreLocalization, OreLocalization.smul_oreDiv, smul_oreDiv
-/
theorem smul'_mk
    {R₀ : Type*} [SMul R₀ R] [SMul R₀ M] [IsScalarTower R₀ R R] [IsScalarTower R₀ R M]
    (r : R₀) (m : M) (s : S) :
    r • LocalizedModule.mk m s = LocalizedModule.mk (r • m) s := by
  rw [OreLocalization.smul_oreDiv]
  simp

/--
theorem `prod_mk` / 定理 `prod_mk`

English:
theorem prod_mk
  statement: {ι A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R}
  proof: by
  induction t using Finset.cons_induction <;> simp [OreLocalization.one_def, *, mk_mul_mk]

中文:
定理 prod_mk
  结论: {ι A : 类型} [交换半环 A] [代数 R A] {S : 子幺半群 R}
  证明: by
  induction t using Finset.cons_induction <;> simp [OreLocalization.one_def, *, mk_mul_mk]

Depends on / 依赖: Finset, Finset.cons_induction, OreLocalization, OreLocalization.one_def, cons_induction, mk_mul_mk, one_def
-/
theorem prod_mk {ι A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R}
    (t : Finset ι) (a : ι -> A) (s : ι -> S) :
    ∏ i in t, mk (a i) (s i) = mk (∏ i in t, a i) (∏ i in t, s i) := by
  induction t using Finset.cons_induction <;> simp [OreLocalization.one_def, *, mk_mul_mk]

/--
Definition of `smulOfIsLocalization` / `smulOfIsLocalization` 的定义

English:
abbreviation smulOfIsLocalization
  signature: : SMul T (LocalizedModule S M) where
  body: let a := IsLocalization.sec S x
    liftOn p (fun p => mk (a.1 • p.1) (a.2 * p.2))
      (by
        rintro p p' ⟨s, h⟩
        refine mk_eq.mpr ⟨s, ?_⟩
        calc
          _ = a.2 • a.1 • s • p'.2 • p.1 := by
            simp_rw [Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul]; ring_nf
          _ = a.2 • a.1 • s • p.2 • p'.1 := by rw [h]
          _ = s • (a.2 * p.2) • a.1 • p'.1 := by
            simp_rw [Submonoid.smul_def, ← mul_smul, Submonoid.coe_mul]; ring_nf)

中文:
缩写 smulOfIsLocalization
  签名: : 标量乘法 T (LocalizedModule S M) where
  定义体: let a := IsLocalization.sec S x
    liftOn p (fun p => mk (a.1 • p.1) (a.2 * p.2))
      (by
        rintro p p' ⟨s, h⟩
        refine mk_eq.mpr ⟨s, ?_⟩
        calc
          _ = a.2 • a.1 • s • p'.2 • p.1 := by
            simp_rw [Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul]; ring_nf
          _ = a.2 • a.1 • s • p.2 • p'.1 := by rw [h]
          _ = s • (a.2 * p.2) • a.1 • p'.1 := by
            simp_rw [Submonoid.smul_def, ← mul_smul, Submonoid.coe_mul]; ring_nf)

Depends on / 依赖: IsLocalization, IsLocalization.sec, Submonoid, Submonoid.coe_mul, Submonoid.smul_def, coe_mul, liftOn, mk_eq, mk_eq.mpr, mul_smul, ring_nf, simp_rw, smul_def
-/
noncomputable abbrev smulOfIsLocalization : SMul T (LocalizedModule S M) where
  smul x p :=
    let a := IsLocalization.sec S x
    liftOn p (fun p => mk (a.1 • p.1) (a.2 * p.2))
      (by
        rintro p p' ⟨s, h⟩
        refine mk_eq.mpr ⟨s, ?_⟩
        calc
          _ = a.2 • a.1 • s • p'.2 • p.1 := by
            simp_rw [Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul]; ring_nf
          _ = a.2 • a.1 • s • p.2 • p'.1 := by rw [h]
          _ = s • (a.2 * p.2) • a.1 • p'.1 := by
            simp_rw [Submonoid.smul_def, ← mul_smul, Submonoid.coe_mul]; ring_nf)

attribute [local instance] smulOfIsLocalization

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (x : T) (m : M) (s : S)
  proof: rfl

中文:
定理 smul_def
  条件: (x : T) (m : M) (s : S)
  证明: rfl
-/
theorem smul_def (x : T) (m : M) (s : S) :
    x • mk m s = mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s) := rfl

/--
theorem `mk'_smul_mk` / 定理 `mk'_smul_mk`

English:
theorem mk'_smul_mk
  given: (r : R) (m : M) (s s' : S)
  proof: by
  rw [smul_def]; rw [mk_eq]
obtain ⟨c, hc⟩ := IsLocalization.eq.mp IsLocalization.mk'_sec T (IsLocalization.mk' T r s)
  use c
  simp_rw [← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, ← mul_assoc,
    mul_comm _ (s' : R), mul_assoc, hc]

中文:
定理 mk'_smul_mk
  条件: (r : R) (m : M) (s s' : S)
  证明: by
  rw [smul_def]; rw [mk_eq]
obtain ⟨c, hc⟩ := IsLocalization.eq.mp IsLocalization.mk'_sec T (IsLocalization.mk' T r s)
  use c
  simp_rw [← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, ← mul_assoc,
    mul_comm _ (s' : R), mul_assoc, hc]

Depends on / 依赖: IsLocalization, IsLocalization.eq.mp, IsLocalization.mk, Submonoid, Submonoid.coe_mul, Submonoid.smul_def, _sec, coe_mul, mk_eq, mul_assoc, mul_comm, mul_smul, simp_rw, smul_def
-/
theorem mk'_smul_mk (r : R) (m : M) (s s' : S) :
    IsLocalization.mk' T r s • mk m s' = mk (r • m) (s * s') := by
  rw [smul_def]; rw [mk_eq]
obtain ⟨c, hc⟩ := IsLocalization.eq.mp IsLocalization.mk'_sec T (IsLocalization.mk' T r s)
  use c
  simp_rw [← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, ← mul_assoc,
    mul_comm _ (s' : R), mul_assoc, hc]

/--
theorem `mk_smul_mk` / 定理 `mk_smul_mk`

English:
theorem mk_smul_mk
  given: (r : R) (m : M) (s t : S)
  proof: (OreLocalization.oreDiv_smul_char _ _ _ _ _ _ (mul_comm _ _)).trans (by rw [mul_comm])

中文:
定理 mk_smul_mk
  条件: (r : R) (m : M) (s t : S)
  证明: (OreLocalization.oreDiv_smul_char _ _ _ _ _ _ (mul_comm _ _)).trans (by rw [mul_comm])

Depends on / 依赖: OreLocalization, OreLocalization.oreDiv_smul_char, mul_comm, oreDiv_smul_char
-/
theorem mk_smul_mk (r : R) (m : M) (s t : S) :
    Localization.mk r s • mk m t = mk (r • m) (s * t) :=
  (OreLocalization.oreDiv_smul_char _ _ _ _ _ _ (mul_comm _ _)).trans (by rw [mul_comm])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass T T' (LocalizedModule S M)
  body: by
    induction p with | _ m s
    simp_rw [smul_def, smul_smul, mul_left_comm, mul_comm]

中文:
实例 :
  签名: 标量交换类 T T' (LocalizedModule S M)
  定义体: by
    induction p with | _ m s
    simp_rw [smul_def, smul_smul, mul_left_comm, mul_comm]

Depends on / 依赖: mul_comm, mul_left_comm, simp_rw, smul_def, smul_smul
-/
instance : SMulCommClass T T' (LocalizedModule S M) where
  smul_comm t t' p := by
    induction p with | _ m s
    simp_rw [smul_def, smul_smul, mul_left_comm, mul_comm]

variable {T}

set_option backward.privateInPublic true in
/--
theorem `one_smul_aux` / 定理 `one_smul_aux`

English:
theorem one_smul_aux
  given: (p : LocalizedModule S M)
  statement: (1 : T) • p = p
  proof: by
  induction p with | _ m s
  rw [show (1 : T) = IsLocalization.mk' T (1 : R) (1 : S) by rw [IsLocalization.mk'_one]; rw [map_one]]
  rw [mk'_smul_mk]; rw [one_smul]; rw [one_mul]

中文:
定理 one_smul_aux
  条件: (p : LocalizedModule S M)
  结论: (1 : T) • p = p
  证明: by
  induction p with | _ m s
  rw [show (1 : T) = IsLocalization.mk' T (1 : R) (1 : S) by rw [IsLocalization.mk'_one]; rw [map_one]]
  rw [mk'_smul_mk]; rw [one_smul]; rw [one_mul]
-/
private theorem one_smul_aux (p : LocalizedModule S M) : (1 : T) • p = p := by
  induction p with | _ m s
  rw [show (1 : T) = IsLocalization.mk' T (1 : R) (1 : S) by rw [IsLocalization.mk'_one]; rw [map_one]]
  rw [mk'_smul_mk]; rw [one_smul]; rw [one_mul]

set_option backward.privateInPublic true in
/--
theorem `mul_smul_aux` / 定理 `mul_smul_aux`

English:
theorem mul_smul_aux
  given: (x y : T) (p : LocalizedModule S M)
  proof: by
  induction p with | _ m s
  rw [← IsLocalization.mk'_sec (M := S) T x]; rw [← IsLocalization.mk'_sec (M := S) T y]
  simp_rw [← IsLocalization.mk'_mul, mk'_smul_mk, ← mul_smul, mul_assoc]

中文:
定理 mul_smul_aux
  条件: (x y : T) (p : LocalizedModule S M)
  证明: by
  induction p with | _ m s
  rw [← IsLocalization.mk'_sec (M := S) T x]; rw [← IsLocalization.mk'_sec (M := S) T y]
  simp_rw [← IsLocalization.mk'_mul, mk'_smul_mk, ← mul_smul, mul_assoc]
-/
private theorem mul_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x * y) • p = x • y • p := by
  induction p with | _ m s
  rw [← IsLocalization.mk'_sec (M := S) T x]; rw [← IsLocalization.mk'_sec (M := S) T y]
  simp_rw [← IsLocalization.mk'_mul, mk'_smul_mk, ← mul_smul, mul_assoc]

set_option backward.privateInPublic true in
/--
theorem `smul_add_aux` / 定理 `smul_add_aux`

English:
theorem smul_add_aux
  given: (x : T) (p q : LocalizedModule S M)
  proof: by
  induction p with | _ m s
  induction q with | _ n t
  rw [smul_def]; rw [smul_def]; rw [mk_add_mk]; rw [mk_add_mk]
  rw [show x • _ = IsLocalization.mk' T _ _ • _ by rw [IsLocalization.mk'_sec (M := S) T]]
  rw [← IsLocalization.mk'_cancel _ _ (IsLocalization.sec S x).2]; rw [mk'_smul_mk]
  congr 1
  · simp only [Submonoid.smul_def, smul_add, ← mul_smul, Submonoid.coe_mul]; ring_nf
  · rw [mul_mul_mul_comm] -- ring does not work here

中文:
定理 smul_add_aux
  条件: (x : T) (p q : LocalizedModule S M)
  证明: by
  induction p with | _ m s
  induction q with | _ n t
  rw [smul_def]; rw [smul_def]; rw [mk_add_mk]; rw [mk_add_mk]
  rw [show x • _ = IsLocalization.mk' T _ _ • _ by rw [IsLocalization.mk'_sec (M := S) T]]
  rw [← IsLocalization.mk'_cancel _ _ (IsLocalization.sec S x).2]; rw [mk'_smul_mk]
  congr 1
  · simp only [Submonoid.smul_def, smul_add, ← mul_smul, Submonoid.coe_mul]; ring_nf
  · rw [mul_mul_mul_comm] -- ring does not work here
-/
private theorem smul_add_aux (x : T) (p q : LocalizedModule S M) :
    x • (p + q) = x • p + x • q := by
  induction p with | _ m s
  induction q with | _ n t
  rw [smul_def]; rw [smul_def]; rw [mk_add_mk]; rw [mk_add_mk]
  rw [show x • _ = IsLocalization.mk' T _ _ • _ by rw [IsLocalization.mk'_sec (M := S) T]]
  rw [← IsLocalization.mk'_cancel _ _ (IsLocalization.sec S x).2]; rw [mk'_smul_mk]
  congr 1
  · simp only [Submonoid.smul_def, smul_add, ← mul_smul, Submonoid.coe_mul]; ring_nf
  · rw [mul_mul_mul_comm] -- ring does not work here

set_option backward.privateInPublic true in
/--
theorem `smul_zero_aux` / 定理 `smul_zero_aux`

English:
theorem smul_zero_aux
  given: (x : T)
  statement: x • (0 : LocalizedModule S M) = 0
  proof: by
  conv => lhs; rw [← zero_mk 1, smul_def, smul_zero, zero_mk]

中文:
定理 smul_zero_aux
  条件: (x : T)
  结论: x • (0 : LocalizedModule S M) = 0
  证明: by
  conv => lhs; rw [← zero_mk 1, smul_def, smul_zero, zero_mk]
-/
private theorem smul_zero_aux (x : T) : x • (0 : LocalizedModule S M) = 0 := by
  conv => lhs; rw [← zero_mk 1, smul_def, smul_zero, zero_mk]

set_option backward.privateInPublic true in
/--
theorem `add_smul_aux` / 定理 `add_smul_aux`

English:
theorem add_smul_aux
  given: (x y : T) (p : LocalizedModule S M)
  proof: by
  induction p with | _ m s
  rw [smul_def T x]; rw [smul_def T y]; rw [mk_add_mk]; rw [show (x + y) • _ = IsLocalization.mk' T _ _ • _ by
    rw [← IsLocalization.mk'_sec (M := S) T x]; rw [← IsLocalization.mk'_sec (M := S) T y]; rw [← IsLocalization.mk'_add]; rw [IsLocalization.mk'_cancel _ _ s], mk'_smul_mk, ← smul_assoc,
    ← smul_assoc, ← add_smul]
  congr 1
  · simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_eq_mul]; ring_nf
  · rw [mul_mul_mul_comm, mul_assoc] -- ring does not work here

中文:
定理 add_smul_aux
  条件: (x y : T) (p : LocalizedModule S M)
  证明: by
  induction p with | _ m s
  rw [smul_def T x]; rw [smul_def T y]; rw [mk_add_mk]; rw [show (x + y) • _ = IsLocalization.mk' T _ _ • _ by
    rw [← IsLocalization.mk'_sec (M := S) T x]; rw [← IsLocalization.mk'_sec (M := S) T y]; rw [← IsLocalization.mk'_add]; rw [IsLocalization.mk'_cancel _ _ s], mk'_smul_mk, ← smul_assoc,
    ← smul_assoc, ← add_smul]
  congr 1
  · simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_eq_mul]; ring_nf
  · rw [mul_mul_mul_comm, mul_assoc] -- ring does not work here
-/
private theorem add_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x + y) • p = x • p + y • p := by
  induction p with | _ m s
  rw [smul_def T x]; rw [smul_def T y]; rw [mk_add_mk]; rw [show (x + y) • _ = IsLocalization.mk' T _ _ • _ by
    rw [← IsLocalization.mk'_sec (M := S) T x]; rw [← IsLocalization.mk'_sec (M := S) T y]; rw [← IsLocalization.mk'_add]; rw [IsLocalization.mk'_cancel _ _ s], mk'_smul_mk, ← smul_assoc,
    ← smul_assoc, ← add_smul]
  congr 1
  · simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_eq_mul]; ring_nf
  · rw [mul_mul_mul_comm, mul_assoc] -- ring does not work here

set_option backward.privateInPublic true in
/--
theorem `zero_smul_aux` / 定理 `zero_smul_aux`

English:
theorem zero_smul_aux
  given: (p : LocalizedModule S M)
  statement: (0 : T) • p = 0
  proof: by
  induction p with | _ m s
  rw [show (0 : T) = IsLocalization.mk' T (0 : R) (1 : S) by rw [IsLocalization.mk'_zero],
    mk'_smul_mk, zero_smul, zero_mk]

中文:
定理 zero_smul_aux
  条件: (p : LocalizedModule S M)
  结论: (0 : T) • p = 0
  证明: by
  induction p with | _ m s
  rw [show (0 : T) = IsLocalization.mk' T (0 : R) (1 : S) by rw [IsLocalization.mk'_zero],
    mk'_smul_mk, zero_smul, zero_mk]
-/
private theorem zero_smul_aux (p : LocalizedModule S M) : (0 : T) • p = 0 := by
  induction p with | _ m s
  rw [show (0 : T) = IsLocalization.mk' T (0 : R) (1 : S) by rw [IsLocalization.mk'_zero],
    mk'_smul_mk, zero_smul, zero_mk]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `moduleOfIsLocalization` / `moduleOfIsLocalization` 的定义

English:
abbreviation moduleOfIsLocalization
  signature: : Module T (LocalizedModule S M) where
  body: one_smul_aux
  mul_smul := mul_smul_aux
  smul_add := smul_add_aux
  smul_zero := smul_zero_aux
  add_smul := add_smul_aux
  zero_smul := zero_smul_aux

@[simp]

中文:
缩写 moduleOfIsLocalization
  签名: : 模 T (LocalizedModule S M) where
  定义体: one_smul_aux
  mul_smul := mul_smul_aux
  smul_add := smul_add_aux
  smul_zero := smul_zero_aux
  add_smul := add_smul_aux
  zero_smul := zero_smul_aux

@[simp]

Depends on / 依赖: one_smul_aux
-/
noncomputable abbrev moduleOfIsLocalization : Module T (LocalizedModule S M) where
  one_smul := one_smul_aux
  mul_smul := mul_smul_aux
  smul_add := smul_add_aux
  smul_zero := smul_zero_aux
  add_smul := add_smul_aux
  zero_smul := zero_smul_aux

@[simp]
/--
theorem `mk_cancel_common_left` / 定理 `mk_cancel_common_left`

English:
theorem mk_cancel_common_left
  given: (s' s : S) (m : M)
  statement: mk (s' • m) (s' * s) = mk m s
  proof: mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      rw [smul_comm]⟩

@[simp]

中文:
定理 mk_cancel_common_left
  条件: (s' s : S) (m : M)
  结论: mk (s' • m) (s' * s) = mk m s
  证明: mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      rw [smul_comm]⟩

@[simp]

Depends on / 依赖: mk_eq, mk_eq.mpr, mul_smul, one_smul, smul_comm
-/
theorem mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s :=
  mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      rw [smul_comm]⟩

@[simp]
/--
theorem `mk_cancel` / 定理 `mk_cancel`

English:
theorem mk_cancel
  given: (s : S) (m : M)
  statement: mk (s • m) s = mk m 1
  proof: mk_eq.mpr ⟨1, by simp⟩

@[simp]

中文:
定理 mk_cancel
  条件: (s : S) (m : M)
  结论: mk (s • m) s = mk m 1
  证明: mk_eq.mpr ⟨1, by simp⟩

@[simp]

Depends on / 依赖: mk_eq, mk_eq.mpr
-/
theorem mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1 :=
  mk_eq.mpr ⟨1, by simp⟩

@[simp]
/--
theorem `mk_cancel_common_right` / 定理 `mk_cancel_common_right`

English:
theorem mk_cancel_common_right
  given: (s s' : S) (m : M)
  statement: mk (s' • m) (s * s') = mk m s
  proof: mk_eq.mpr ⟨1, by simp [mul_smul]⟩

中文:
定理 mk_cancel_common_right
  条件: (s s' : S) (m : M)
  结论: mk (s' • m) (s * s') = mk m s
  证明: mk_eq.mpr ⟨1, by simp [mul_smul]⟩

Depends on / 依赖: mk_eq, mk_eq.mpr, mul_smul
-/
theorem mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s :=
  mk_eq.mpr ⟨1, by simp [mul_smul]⟩

/--
lemma `smul_eq_iff_of_mem` / 引理 `smul_eq_iff_of_mem`

English:
lemma smul_eq_iff_of_mem
  proof: by
  induction x using induction_on with
  | h m s =>
    induction y using induction_on with
    | h n t =>
      rw [smul'_mk]; rw [mk_smul_mk]; rw [one_smul]; rw [mk_eq]; rw [mk_eq]
      simp only [Subtype.exists, Submonoid.mk_smul, exists_prop]
      fconstructor
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [mul_smul]; rw [← eq1]; rw [Submonoid.mk_smul]; rw [smul_comm r t]
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [← eq1]; rw [mul_comm]; rw [mul_smul]; rw [Submonoid.mk_smul]; rw [Submonoid.smul_def]; rw [Submonoid.mk_smul]

中文:
引理 smul_eq_iff_of_mem
  证明: by
  induction x using induction_on with
  | h m s =>
    induction y using induction_on with
    | h n t =>
      rw [smul'_mk]; rw [mk_smul_mk]; rw [one_smul]; rw [mk_eq]; rw [mk_eq]
      simp only [Subtype.exists, Submonoid.mk_smul, exists_prop]
      fconstructor
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [mul_smul]; rw [← eq1]; rw [Submonoid.mk_smul]; rw [smul_comm r t]
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [← eq1]; rw [mul_comm]; rw [mul_smul]; rw [Submonoid.mk_smul]; rw [Submonoid.smul_def]; rw [Submonoid.mk_smul]

Depends on / 依赖: Submonoid, Submonoid.mk_s, Submonoid.mk_smul, Submonoid.smul_def, Subtype, Subtype.exists, exists_prop, fconstructor, induction_on, mk_eq, mk_s, mk_smul, mk_smul_mk, mul_comm, mul_smul, one_smul, smul_comm, smul_def
-/
lemma smul_eq_iff_of_mem
    (r : R) (hr : r in S) (x y : LocalizedModule S M) :
    r • x = y ↔ x = Localization.mk 1 ⟨r, hr⟩ • y := by
  induction x using induction_on with
  | h m s =>
    induction y using induction_on with
    | h n t =>
      rw [smul'_mk]; rw [mk_smul_mk]; rw [one_smul]; rw [mk_eq]; rw [mk_eq]
      simp only [Subtype.exists, Submonoid.mk_smul, exists_prop]
      fconstructor
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [mul_smul]; rw [← eq1]; rw [Submonoid.mk_smul]; rw [smul_comm r t]
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [← eq1]; rw [mul_comm]; rw [mul_smul]; rw [Submonoid.mk_smul]; rw [Submonoid.smul_def]; rw [Submonoid.mk_smul]

/--
lemma `eq_zero_of_smul_eq_zero` / 引理 `eq_zero_of_smul_eq_zero`

English:
lemma eq_zero_of_smul_eq_zero
  proof: by
  rw [smul_eq_iff_of_mem (hr := hr)] at hx
  rw [hx]; rw [smul_zero]

中文:
引理 eq_zero_of_smul_eq_zero
  证明: by
  rw [smul_eq_iff_of_mem (hr := hr)] at hx
  rw [hx]; rw [smul_zero]

Depends on / 依赖: smul_eq_iff_of_mem, smul_zero
-/
lemma eq_zero_of_smul_eq_zero
    (r : R) (hr : r in S) (x : LocalizedModule S M) (hx : r • x = 0) : x = 0 := by
  rw [smul_eq_iff_of_mem (hr := hr)] at hx
  rw [hx]; rw [smul_zero]

/--
theorem `smul'_mul` / 定理 `smul'_mul`

English:
theorem smul'_mul
  given: {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A)
  proof: by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [mk_mul_mk]; rw [smul_def]; rw [smul_def]; rw [mk_mul_mk]; rw [mul_assoc]; rw [smul_mul_assoc]

中文:
定理 smul'_mul
  条件: {A : 类型} [半环 A] [代数 R A] (x : T) (p₁ p₂ : LocalizedModule S A)
  证明: by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [mk_mul_mk]; rw [smul_def]; rw [smul_def]; rw [mk_mul_mk]; rw [mul_assoc]; rw [smul_mul_assoc]
-/
theorem smul'_mul {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A) :
    x • p₁ * p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [mk_mul_mk]; rw [smul_def]; rw [smul_def]; rw [mk_mul_mk]; rw [mul_assoc]; rw [smul_mul_assoc]

/--
theorem `mul_smul'` / 定理 `mul_smul'`

English:
theorem mul_smul'
  given: {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A)
  proof: by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [smul_def]; rw [mk_mul_mk]; rw [mk_mul_mk]; rw [smul_def]; rw [mul_left_comm]; rw [mul_smul_comm]

中文:
定理 mul_smul'
  条件: {A : 类型} [半环 A] [代数 R A] (x : T) (p₁ p₂ : LocalizedModule S A)
  证明: by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [smul_def]; rw [mk_mul_mk]; rw [mk_mul_mk]; rw [smul_def]; rw [mul_left_comm]; rw [mul_smul_comm]

Depends on / 依赖: mk_mul_mk, mul_left_comm, mul_smul_comm, smul_def
-/
theorem mul_smul' {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A) :
    p₁ * x • p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [smul_def]; rw [mk_mul_mk]; rw [mk_mul_mk]; rw [smul_def]; rw [mul_left_comm]; rw [mul_smul_comm]

variable (T)

attribute [local instance] moduleOfIsLocalization in
/--
Definition of `algebraOfIsLocalization` / `algebraOfIsLocalization` 的定义

English:
abbreviation algebraOfIsLocalization
  signature: {A : Type*} [Semiring A] [Algebra R A]
  body: Algebra.ofModule smul'_mul mul_smul'

中文:
缩写 algebraOfIsLocalization
  签名: {A : 类型} [半环 A] [代数 R A]
  定义体: Algebra.ofModule smul'_mul mul_smul'

Depends on / 依赖: Algebra, Algebra.ofModule, _mul, mul_smul, ofModule
-/
noncomputable abbrev algebraOfIsLocalization {A : Type*} [Semiring A] [Algebra R A] :
    Algebra T (LocalizedModule S A) :=
  Algebra.ofModule smul'_mul mul_smul'

attribute [local instance] algebraOfIsLocalization

/--
theorem `algebraMap_mk'` / 定理 `algebraMap_mk'`

English:
theorem algebraMap_mk'
  given: {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S)
  proof: by
  with_unfolding_all
  rw [Algebra.algebraMap_eq_smul_one]
  change _ • mk _ _ = _
  rw [mk'_smul_mk]; rw [Algebra.algebraMap_eq_smul_one]; rw [mul_one]

中文:
定理 algebraMap_mk'
  条件: {A : 类型} [半环 A] [代数 R A] (a : R) (s : S)
  证明: by
  with_unfolding_all
  rw [Algebra.algebraMap_eq_smul_one]
  change _ • mk _ _ = _
  rw [mk'_smul_mk]; rw [Algebra.algebraMap_eq_smul_one]; rw [mul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, _smul_mk, algebraMap_eq_smul_one, mul_one, with_unfolding_all
-/
theorem algebraMap_mk' {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (IsLocalization.mk' T a s) = mk (algebraMap R A a) s := by
  with_unfolding_all
  rw [Algebra.algebraMap_eq_smul_one]
  change _ • mk _ _ = _
  rw [mk'_smul_mk]; rw [Algebra.algebraMap_eq_smul_one]; rw [mul_one]

/--
theorem `algebraMap_mk` / 定理 `algebraMap_mk`

English:
theorem algebraMap_mk
  given: {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S)
  proof: by
  rw [Localization.mk_eq_mk']
  exact algebraMap_mk' ..

中文:
定理 algebraMap_mk
  条件: {A : 类型} [半环 A] [代数 R A] (a : R) (s : S)
  证明: by
  rw [Localization.mk_eq_mk']
  exact algebraMap_mk' ..

Depends on / 依赖: Localization, Localization.mk_eq_mk, algebraMap_mk, mk_eq_mk
-/
theorem algebraMap_mk {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (Localization.mk a s) = mk (algebraMap R A a) s := by
  rw [Localization.mk_eq_mk']
  exact algebraMap_mk' ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R T (LocalizedModule S M)
  body: by
    induction p with | _ m s
    rw [← IsLocalization.mk'_sec (M := S) T x]; rw [IsLocalization.smul_mk']; rw [mk'_smul_mk]; rw [mk'_smul_mk]; rw [smul'_mk]; rw [mul_smul]

中文:
实例 :
  签名: 标量塔 R T (LocalizedModule S M)
  定义体: by
    induction p with | _ m s
    rw [← IsLocalization.mk'_sec (M := S) T x]; rw [IsLocalization.smul_mk']; rw [mk'_smul_mk]; rw [mk'_smul_mk]; rw [smul'_mk]; rw [mul_smul]

Depends on / 依赖: IsLocalization, IsLocalization.mk, IsLocalization.smul_mk, _sec, _smul_mk, mul_smul, smul_mk
-/
instance : IsScalarTower R T (LocalizedModule S M) where
  smul_assoc r x p := by
    induction p with | _ m s
    rw [← IsLocalization.mk'_sec (M := S) T x]; rw [IsLocalization.smul_mk']; rw [mk'_smul_mk]; rw [mk'_smul_mk]; rw [smul'_mk]; rw [mul_smul]

/--
Definition of `numeratorRingHom` / `numeratorRingHom` 的定义

English:
abbreviation numeratorRingHom
  signature: {A : Type*} [Semiring A] [Algebra R A]
  body: mk r 1
  map_one' := by simp [OreLocalization.one_def]
  map_mul' := by simp [mk_mul_mk]
  map_zero' := by simp
  map_add' := by simp

中文:
缩写 numeratorRingHom
  签名: {A : 类型} [半环 A] [代数 R A]
  定义体: mk r 1
  map_one' := by simp [OreLocalization.one_def]
  map_mul' := by simp [mk_mul_mk]
  map_zero' := by simp
  map_add' := by simp
-/
abbrev numeratorRingHom {A : Type*} [Semiring A] [Algebra R A] : A ->+* A[S⁻¹] where
  toFun r := mk r 1
  map_one' := by simp [OreLocalization.one_def]
  map_mul' := by simp [mk_mul_mk]
  map_zero' := by simp
  map_add' := by simp

noncomputable instance (priority := 900) algebra' {A : Type*} [Semiring A] [Algebra R A] :
    Algebra R (LocalizedModule S A) where
  algebraMap := numeratorRingHom.comp (algebraMap R A)
  commutes' r x := by
    induction x using induction_on with | _ a s => _
    simp only [RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply]
    rw [mk_mul_mk]; rw [mk_mul_mk]; rw [mul_comm]; rw [Algebra.commutes]
  smul_def' r x := by
    induction x using induction_on with | _ a s => _
    simp only [RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply]
    rw [mk_mul_mk]; rw [smul'_mk]; rw [Algebra.smul_def]; rw [one_mul]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra'` / 引理 `example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra'`

English:
lemma example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra'
  proof: by
  with_reducible_and_instances rfl

中文:
引理 example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra'
  证明: by
  with_reducible_and_instances rfl
-/
private lemma example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra' :
    OreLocalization.instAlgebra = (algebra' : Algebra R (LocalizedModule S R)) := by
  with_reducible_and_instances rfl

section

variable (S M)

/-- The function `m ↦ m / 1` as an `R`-linear map.
-/
@[simps]
/--
Definition of `mkLinearMap` / `mkLinearMap` 的定义

English:
definition mkLinearMap
  signature: : M ->ₗ[R] LocalizedModule S M where
  body: mk m 1
  map_add' x y := by simp
  map_smul' _ _ := by simp [mk, OreLocalization.smul_oreDiv]

中文:
定义 mkLinearMap
  签名: : M ->ₗ[R] LocalizedModule S M where
  定义体: mk m 1
  map_add' x y := by simp
  map_smul' _ _ := by simp [mk, OreLocalization.smul_oreDiv]
-/
noncomputable def mkLinearMap : M ->ₗ[R] LocalizedModule S M where
  toFun m := mk m 1
  map_add' x y := by simp
  map_smul' _ _ := by simp [mk, OreLocalization.smul_oreDiv]

end

/-- For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
@[simps]
/--
Definition of `divBy` / `divBy` 的定义

English:
definition divBy
  signature: (s : S)
  body: p.liftOn (fun p => mk p.1 (p.2 * s)) fun ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩ =>
      mk_eq.mpr ⟨c, by rw [mul_smul, mul_smul, smul_comm _ s, smul_comm _ s, eq1, smul_comm _ s,
        smul_comm _ s]⟩
  map_add' x y := by
    refine x.induction_on₂ ?_ y
    intro m₁ m₂ t₁ t₂
    simp_rw [mk_add_mk, LocalizedModule.liftOn_mk, mk_add_mk, mul_smul, mul_comm _ s, mul_assoc,
      smul_comm _ s, ← smul_add, mul_left_comm s t₁ t₂, mk_cancel_common_left s]
  map_smul' r x := by
    refine x.induction_on (fun _ _ => ?_)
    simp_rw [smul'_mk, liftOn_mk, smul'_mk]
    congr!

中文:
定义 divBy
  签名: (s : S)
  定义体: p.liftOn (fun p => mk p.1 (p.2 * s)) fun ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩ =>
      mk_eq.mpr ⟨c, by rw [mul_smul, mul_smul, smul_comm _ s, smul_comm _ s, eq1, smul_comm _ s,
        smul_comm _ s]⟩
  map_add' x y := by
    refine x.induction_on₂ ?_ y
    intro m₁ m₂ t₁ t₂
    simp_rw [mk_add_mk, LocalizedModule.liftOn_mk, mk_add_mk, mul_smul, mul_comm _ s, mul_assoc,
      smul_comm _ s, ← smul_add, mul_left_comm s t₁ t₂, mk_cancel_common_left s]
  map_smul' r x := by
    refine x.induction_on (fun _ _ => ?_)
    simp_rw [smul'_mk, liftOn_mk, smul'_mk]
    congr!

Depends on / 依赖: LocalizedModule, LocalizedModule.liftOn_mk, induction_on, liftOn, liftOn_mk, map_add, map_smul, mk_add_mk, mk_cancel_common_left, mk_eq, mk_eq.mpr, mul_assoc, mul_comm, mul_left_comm, mul_smul, p.liftOn, simp_rw, smul_add, smul_comm, x.induction_on
-/
noncomputable def divBy (s : S) : LocalizedModule S M ->ₗ[R] LocalizedModule S M where
  toFun p :=
    p.liftOn (fun p => mk p.1 (p.2 * s)) fun ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩ =>
      mk_eq.mpr ⟨c, by rw [mul_smul, mul_smul, smul_comm _ s, smul_comm _ s, eq1, smul_comm _ s,
        smul_comm _ s]⟩
  map_add' x y := by
    refine x.induction_on₂ ?_ y
    intro m₁ m₂ t₁ t₂
    simp_rw [mk_add_mk, LocalizedModule.liftOn_mk, mk_add_mk, mul_smul, mul_comm _ s, mul_assoc,
      smul_comm _ s, ← smul_add, mul_left_comm s t₁ t₂, mk_cancel_common_left s]
  map_smul' r x := by
    refine x.induction_on (fun _ _ => ?_)
    simp_rw [smul'_mk, liftOn_mk, smul'_mk]
    congr!

/--
theorem `divBy_mul_by` / 定理 `divBy_mul_by`

English:
theorem divBy_mul_by
  given: (s : S) (p : LocalizedModule S M)
  proof: p.induction_on fun m t => by
    rw [Module.algebraMap_end_apply]; rw [divBy_apply]; rw [smul'_mk]; rw [liftOn_mk]; rw [← Submonoid.smul_def]; rw [mk_cancel_common_right _ s]

中文:
定理 divBy_mul_by
  条件: (s : S) (p : LocalizedModule S M)
  证明: p.induction_on fun m t => by
    rw [Module.algebraMap_end_apply]; rw [divBy_apply]; rw [smul'_mk]; rw [liftOn_mk]; rw [← Submonoid.smul_def]; rw [mk_cancel_common_right _ s]

Depends on / 依赖: Module, Module.algebraMap_end_apply, Submonoid, Submonoid.smul_def, algebraMap_end_apply, divBy_apply, induction_on, liftOn_mk, mk_cancel_common_right, p.induction_on, smul_def
-/
theorem divBy_mul_by (s : S) (p : LocalizedModule S M) :
    divBy s (algebraMap R (Module.End R (LocalizedModule S M)) s p) = p :=
  p.induction_on fun m t => by
    rw [Module.algebraMap_end_apply]; rw [divBy_apply]; rw [smul'_mk]; rw [liftOn_mk]; rw [← Submonoid.smul_def]; rw [mk_cancel_common_right _ s]

/--
theorem `mul_by_divBy` / 定理 `mul_by_divBy`

English:
theorem mul_by_divBy
  given: (s : S) (p : LocalizedModule S M)
  proof: p.induction_on fun m t => by
    rw [divBy_apply]; rw [Module.algebraMap_end_apply]; rw [LocalizedModule.liftOn_mk]; rw [smul'_mk]; rw [← Submonoid.smul_def]; rw [mk_cancel_common_right _ s]

中文:
定理 mul_by_divBy
  条件: (s : S) (p : LocalizedModule S M)
  证明: p.induction_on fun m t => by
    rw [divBy_apply]; rw [Module.algebraMap_end_apply]; rw [LocalizedModule.liftOn_mk]; rw [smul'_mk]; rw [← Submonoid.smul_def]; rw [mk_cancel_common_right _ s]

Depends on / 依赖: LocalizedModule, LocalizedModule.liftOn_mk, Module, Module.algebraMap_end_apply, Submonoid, Submonoid.smul_def, _apply, algebraMap_end_apply, coeff_divOf, coeff_single_mul_add, divBy_apply, induction_on, liftOn_mk, mk_cancel_common_right, one_mul, p.induction_on, smul_def
-/
theorem mul_by_divBy (s : S) (p : LocalizedModule S M) :
    algebraMap R (Module.End R (LocalizedModule S M)) s (divBy s p) = p :=
  p.induction_on fun m t => by
    rw [divBy_apply]; rw [Module.algebraMap_end_apply]; rw [LocalizedModule.liftOn_mk]; rw [smul'_mk]; rw [← Submonoid.smul_def]; rw [mk_cancel_common_right _ s]

end

end LocalizedModule

section IsLocalizedModule

universe u v

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
variable {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]
variable [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']
variable (f : M ->ₗ[R] M') (g : M ->ₗ[R] M'')

/--
Definition of `IsLocalizedModule` / `IsLocalizedModule` 的定义

English:
class IsLocalizedModule
  parameters: (S : Submonoid R) (f : M ->ₗ[R] M')
  axioms and operations (3):
    - map_units : forall x : S, IsUnit (algebraMap R (Module.End R M') x)
    - surj((S f)) : forall y : M', exists x : M × S, x.2 • y = f x.1
    - exists_of_eq : forall {x₁ x₂}, f x₁ = f x₂ -> exists c : S, c • x₁ = c • x₂

中文:
类 是Localized模
  参数: (S : 子幺半群 R) (f : M ->ₗ[R] M')
  公理与运算 (3 个):
    - map_units : 对任意 x : S, 是单位 (algebraMap R (模.End R M') x)
    - surj((S f)) : 对任意 y : M', 存在 x : M × S, x.2 • y = f x.1
    - exists_of_eq : 对任意 {x₁ x₂}, f x₁ = f x₂ -> 存在 c : S, c • x₁ = c • x₂
-/
@[mk_iff] class IsLocalizedModule (S : Submonoid R) (f : M ->ₗ[R] M') : Prop where
  map_units : forall x : S, IsUnit (algebraMap R (Module.End R M') x)
  surj (S f) : forall y : M', exists x : M × S, x.2 • y = f x.1
  exists_of_eq : forall {x₁ x₂}, f x₁ = f x₂ -> exists c : S, c • x₁ = c • x₂

attribute [nolint docBlame] IsLocalizedModule.map_units IsLocalizedModule.surj
  IsLocalizedModule.exists_of_eq

/--
lemma `IsLocalizedModule.eq_iff_exists` / 引理 `IsLocalizedModule.eq_iff_exists`

English:
lemma IsLocalizedModule.eq_iff_exists
  given: [IsLocalizedModule S f] {x₁ x₂}
  proof: Iff.intro exists_of_eq fun ⟨c, h⟩ => by
    apply_fun f at h
    simp_rw [f.map_smul_of_tower, Submonoid.smul_def, ← Module.algebraMap_end_apply R R] at h
    exact ((Module.End.isUnit_iff _).mp <| map_units f c).1 h

中文:
引理 是Localized模.eq_iff_存在
  条件: [是Localized模 S f] {x₁ x₂}
  证明: Iff.intro exists_of_eq fun ⟨c, h⟩ => by
    apply_fun f at h
    simp_rw [f.map_smul_of_tower, Submonoid.smul_def, ← Module.algebraMap_end_apply R R] at h
    exact ((Module.End.isUnit_iff _).mp <| map_units f c).1 h

Depends on / 依赖: Iff.intro, Module, Module.End.isUnit_iff, Module.algebraMap_end_apply, Submonoid, Submonoid.smul_def, _divOf, algebraMap_end_apply, apply_fun, exists_of_eq, f.map_smul_of_tower, isUnit_iff, map_smul_of_tower, map_units, mul_of, one_mul, simp_rw, smul_def
-/
lemma IsLocalizedModule.eq_iff_exists [IsLocalizedModule S f] {x₁ x₂} :
    f x₁ = f x₂ ↔ exists c : S, c • x₁ = c • x₂ :=
  Iff.intro exists_of_eq fun ⟨c, h⟩ => by
    apply_fun f at h
    simp_rw [f.map_smul_of_tower, Submonoid.smul_def, ← Module.algebraMap_end_apply R R] at h
    exact ((Module.End.isUnit_iff _).mp <| map_units f c).1 h

/--
lemma `IsLocalizedModule.injective_iff_isRegular` / 引理 `IsLocalizedModule.injective_iff_isRegular`

English:
lemma IsLocalizedModule.injective_iff_isRegular
  given: [IsLocalizedModule S f]
  proof: by
  simp_rw [IsSMulRegular, Function.Injective, eq_iff_exists S, exists_imp, forall_comm (α := S)]

中文:
引理 是Localized模.injective_iff_isRegular
  条件: [是Localized模 S f]
  证明: by
  simp_rw [IsSMulRegular, Function.Injective, eq_iff_exists S, exists_imp, forall_comm (α := S)]

Depends on / 依赖: Function, Function.Injective, Injective, IsSMulRegular, eq_iff_exists, exists_imp, forall_comm, simp_rw
-/
lemma IsLocalizedModule.injective_iff_isRegular [IsLocalizedModule S f] :
    Function.Injective f ↔ forall c : S, IsSMulRegular M c := by
  simp_rw [IsSMulRegular, Function.Injective, eq_iff_exists S, exists_imp, forall_comm (α := S)]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `IsLocalizedModule.of_linearEquiv` / 实例 `IsLocalizedModule.of_linearEquiv`

English:
instance IsLocalizedModule.of_linearEquiv
  signature: (e : M' ≃ₗ[R] M'') [hf : IsLocalizedModule S f]
  body: by
    rw [show algebraMap R (Module.End R M'') s = e ∘ₗ (algebraMap R (Module.End R M') s) ∘ₗ e.symm
      by ext; simp]; rw [Module.End.isUnit_iff]; rw [LinearMap.coe_comp]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [LinearEquiv.coe_coe]; rw [EquivLike.comp_bijective]; rw [EquivLike.bijective_comp]
exact (Module.End.isUnit_iff _).mp hf.map_units s
  surj x := by
    obtain ⟨p, h⟩ := hf.surj (e.symm x)
    exact ⟨p, by rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← e.congr_arg h,
      Submonoid.smul_def, Submonoid.smul_def, map_smul, LinearEquiv.apply_symm_apply]⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact hf.exists_of_eq h

中文:
实例 是Localized模.of_linearEquiv
  签名: (e : M' ≃ₗ[R] M'') [hf : 是Localized模 S f]
  定义体: by
    rw [show algebraMap R (Module.End R M'') s = e ∘ₗ (algebraMap R (Module.End R M') s) ∘ₗ e.symm
      by ext; simp]; rw [Module.End.isUnit_iff]; rw [LinearMap.coe_comp]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [LinearEquiv.coe_coe]; rw [EquivLike.comp_bijective]; rw [EquivLike.bijective_comp]
exact (Module.End.isUnit_iff _).mp hf.map_units s
  surj x := by
    obtain ⟨p, h⟩ := hf.surj (e.symm x)
    exact ⟨p, by rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← e.congr_arg h,
      Submonoid.smul_def, Submonoid.smul_def, map_smul, LinearEquiv.apply_symm_apply]⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact hf.exists_of_eq h

Depends on / 依赖: EquivLike, EquivLike.bijective_comp, EquivLike.comp_bijective, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, Module, Module.End, Module.End.isUnit_iff, algebraMap, bijective_comp, coe_coe, coe_comp, comp_apply, comp_bijective, congr_arg, e.congr_arg
-/
instance IsLocalizedModule.of_linearEquiv (e : M' ≃ₗ[R] M'') [hf : IsLocalizedModule S f] :
    IsLocalizedModule S (e ∘ₗ f : M ->ₗ[R] M'') where
  map_units s := by
    rw [show algebraMap R (Module.End R M'') s = e ∘ₗ (algebraMap R (Module.End R M') s) ∘ₗ e.symm
      by ext; simp]; rw [Module.End.isUnit_iff]; rw [LinearMap.coe_comp]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [LinearEquiv.coe_coe]; rw [EquivLike.comp_bijective]; rw [EquivLike.bijective_comp]
exact (Module.End.isUnit_iff _).mp hf.map_units s
  surj x := by
    obtain ⟨p, h⟩ := hf.surj (e.symm x)
    exact ⟨p, by rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← e.congr_arg h,
      Submonoid.smul_def, Submonoid.smul_def, map_smul, LinearEquiv.apply_symm_apply]⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact hf.exists_of_eq h

set_option backward.isDefEq.respectTransparency false in
/--
Instance `IsLocalizedModule.of_linearEquiv_right` / 实例 `IsLocalizedModule.of_linearEquiv_right`

English:
instance IsLocalizedModule.of_linearEquiv_right
  signature: (e : M'' ≃ₗ[R] M) [hf : IsLocalizedModule S f]
  body: hf.map_units s
  surj x := by
    obtain ⟨⟨p, s⟩, h⟩ := hf.surj x
    exact ⟨⟨e.symm p, s⟩, by simpa using h⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    obtain ⟨c, hc⟩ := hf.exists_of_eq h
    exact ⟨c, by simpa only [Submonoid.smul_def, map_smul, e.symm_apply_apply]
      using congr(e.symm $hc)⟩

中文:
实例 是Localized模.of_linearEquiv_right
  签名: (e : M'' ≃ₗ[R] M) [hf : 是Localized模 S f]
  定义体: hf.map_units s
  surj x := by
    obtain ⟨⟨p, s⟩, h⟩ := hf.surj x
    exact ⟨⟨e.symm p, s⟩, by simpa using h⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    obtain ⟨c, hc⟩ := hf.exists_of_eq h
    exact ⟨c, by simpa only [Submonoid.smul_def, map_smul, e.symm_apply_apply]
      using congr(e.symm $hc)⟩

Depends on / 依赖: hf.map_units, map_units
-/
instance IsLocalizedModule.of_linearEquiv_right (e : M'' ≃ₗ[R] M) [hf : IsLocalizedModule S f] :
    IsLocalizedModule S (f ∘ₗ e : M'' ->ₗ[R] M') where
  map_units s := hf.map_units s
  surj x := by
    obtain ⟨⟨p, s⟩, h⟩ := hf.surj x
    exact ⟨⟨e.symm p, s⟩, by simpa using h⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    obtain ⟨c, hc⟩ := hf.exists_of_eq h
    exact ⟨c, by simpa only [Submonoid.smul_def, map_smul, e.symm_apply_apply]
      using congr(e.symm $hc)⟩

/--
lemma `IsLocalizedModule.comp_iff_of_bijective_left` / 引理 `IsLocalizedModule.comp_iff_of_bijective_left`

English:
lemma IsLocalizedModule.comp_iff_of_bijective_left
  statement: {f : M ->ₗ[R] M'} (e : M' ->ₗ[R] M'')
  proof: by
  refine ⟨fun h => ?_, fun h => .of_linearEquiv _ _ (.ofBijective _ he)⟩
  have : (LinearEquiv.ofBijective _ he).symm.toLinearMap ∘ₗ e ∘ₗ f = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv _ _ _

中文:
引理 是Localized模.comp_iff_of_bijective_left
  结论: {f : M ->ₗ[R] M'} (e : M' ->ₗ[R] M'')
  证明: by
  refine ⟨fun h => ?_, fun h => .of_linearEquiv _ _ (.ofBijective _ he)⟩
  have : (LinearEquiv.ofBijective _ he).symm.toLinearMap ∘ₗ e ∘ₗ f = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv _ _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, ofBijective, of_linearEquiv, symm.toLinearMap, toLinearMap
-/
lemma IsLocalizedModule.comp_iff_of_bijective_left {f : M ->ₗ[R] M'} (e : M' ->ₗ[R] M'')
    (he : Function.Bijective e) :
    IsLocalizedModule S (e ∘ₗ f) ↔ IsLocalizedModule S f := by
  refine ⟨fun h => ?_, fun h => .of_linearEquiv _ _ (.ofBijective _ he)⟩
  have : (LinearEquiv.ofBijective _ he).symm.toLinearMap ∘ₗ e ∘ₗ f = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv _ _ _

/--
lemma `IsLocalizedModule.comp_iff_of_bijective_right` / 引理 `IsLocalizedModule.comp_iff_of_bijective_right`

English:
lemma IsLocalizedModule.comp_iff_of_bijective_right
  statement: (e : M ->ₗ[R] M') {f : M' ->ₗ[R] M''}
  proof: by
  refine ⟨fun h => ?_, fun h => .of_linearEquiv_right _ _ (.ofBijective _ he)⟩
  have : (f ∘ₗ e) ∘ₗ (LinearEquiv.ofBijective _ he).symm.toLinearMap = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv_right _ _ _

中文:
引理 是Localized模.comp_iff_of_bijective_right
  结论: (e : M ->ₗ[R] M') {f : M' ->ₗ[R] M''}
  证明: by
  refine ⟨fun h => ?_, fun h => .of_linearEquiv_right _ _ (.ofBijective _ he)⟩
  have : (f ∘ₗ e) ∘ₗ (LinearEquiv.ofBijective _ he).symm.toLinearMap = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv_right _ _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, ofBijective, of_linearEquiv_right, symm.toLinearMap, toLinearMap
-/
lemma IsLocalizedModule.comp_iff_of_bijective_right (e : M ->ₗ[R] M') {f : M' ->ₗ[R] M''}
    (he : Function.Bijective e) :
    IsLocalizedModule S (f ∘ₗ e) ↔ IsLocalizedModule S f := by
  refine ⟨fun h => ?_, fun h => .of_linearEquiv_right _ _ (.ofBijective _ he)⟩
  have : (f ∘ₗ e) ∘ₗ (LinearEquiv.ofBijective _ he).symm.toLinearMap = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv_right _ _ _

variable (M) in
/--
lemma `isLocalizedModule_id` / 引理 `isLocalizedModule_id`

English:
lemma isLocalizedModule_id
  statement: (R') [CommSemiring R'] [Algebra R R'] [IsLocalization S R'] [Module R' M]
  proof: by
    rw [← (Algebra.lsmul R (A := R') R M).commutes]; exact (IsLocalization.map_units R' s).map _
  surj m := ⟨(m, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congr_arg _ h⟩

中文:
引理 isLocalizedModule_id
  结论: (R') [交换半环 R'] [代数 R R'] [是Localization S R'] [模 R' M]
  证明: by
    rw [← (Algebra.lsmul R (A := R') R M).commutes]; exact (IsLocalization.map_units R' s).map _
  surj m := ⟨(m, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congr_arg _ h⟩

Depends on / 依赖: Algebra, Algebra.lsmul, Finsupp, Finsupp.coe_zero, IsLocalization, IsLocalization.map_units, Pi.zero_apply, _apply, coe_zero, coeff_modOf_of_not_exists_add, coeff_modOf_self_add, coeff_single_mul_of_forall_add_ne, coeff_zero, commutes, congr_arg, eq_comm, exists_of_eq, map_units, one_smul, zero_apply
-/
lemma isLocalizedModule_id (R') [CommSemiring R'] [Algebra R R'] [IsLocalization S R'] [Module R' M]
    [IsScalarTower R R' M] : IsLocalizedModule S (.id : M ->ₗ[R] M) where
  map_units s := by
    rw [← (Algebra.lsmul R (A := R') R M).commutes]; exact (IsLocalization.map_units R' s).map _
  surj m := ⟨(m, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congr_arg _ h⟩

namespace LocalizedModule

/--
Definition of `lift'` / `lift'` 的定义

English:
definition lift'
  signature: (g : M ->ₗ[R] M'')
  body: fun m =>
  m.liftOn (fun p => (h p.2).unit⁻¹.val <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    dsimp only
    simp only [Submonoid.smul_def] at eq1
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [eq_comm]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
    have : c • s • g m' = c • s' • g m := by
      simp only [Submonoid.smul_def, ← g.map_smul, eq1]
    have : Function.Injective (h c).unit.inv := ((Module.End.isUnit_iff _).1 (by simp)).1
    apply_fun (h c).unit.inv
    rw [Units.inv_eq_val_inv]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [←
      (h c).unit⁻¹.val.map_smul]
    symm
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← g.map_smul]; rw [← g.map_smul]; rw [← g.map_smul]; rw [←
      g.map_smul]; rw [eq1]

中文:
定义 lift'
  签名: (g : M ->ₗ[R] M'')
  定义体: fun m =>
  m.liftOn (fun p => (h p.2).unit⁻¹.val <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    dsimp only
    simp only [Submonoid.smul_def] at eq1
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [eq_comm]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
    have : c • s • g m' = c • s' • g m := by
      simp only [Submonoid.smul_def, ← g.map_smul, eq1]
    have : Function.Injective (h c).unit.inv := ((Module.End.isUnit_iff _).1 (by simp)).1
    apply_fun (h c).unit.inv
    rw [Units.inv_eq_val_inv]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [←
      (h c).unit⁻¹.val.map_smul]
    symm
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← g.map_smul]; rw [← g.map_smul]; rw [← g.map_smul]; rw [←
      g.map_smul]; rw [eq1]

Depends on / 依赖: Finsupp, Finsupp.zero_apply, Function, Function.Injective, Injective, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Module.End.isUnit_iff, Submonoid, Submonoid.smul_def, Units.inv_eq_val_in, _apply, add_comm, algebraMap_isUnit_inv_apply_eq_iff, apply_fun, coeff_modOf_of_not_exists_add, coeff_modOf_self_add, coeff_mul_single_of_forall_add_ne, coeff_zero, eq_comm
-/
noncomputable def lift' (g : M ->ₗ[R] M'')
    (h : forall x : S, IsUnit (algebraMap R (Module.End R M'') x)) : LocalizedModule S M -> M'' :=
  fun m =>
  m.liftOn (fun p => (h p.2).unit⁻¹.val <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    dsimp only
    simp only [Submonoid.smul_def] at eq1
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [eq_comm]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
    have : c • s • g m' = c • s' • g m := by
      simp only [Submonoid.smul_def, ← g.map_smul, eq1]
    have : Function.Injective (h c).unit.inv := ((Module.End.isUnit_iff _).1 (by simp)).1
    apply_fun (h c).unit.inv
    rw [Units.inv_eq_val_inv]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [←
      (h c).unit⁻¹.val.map_smul]
    symm
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← g.map_smul]; rw [← g.map_smul]; rw [← g.map_smul]; rw [←
      g.map_smul]; rw [eq1]

/--
theorem `lift'_mk` / 定理 `lift'_mk`

English:
theorem lift'_mk
  statement: (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: rfl

中文:
定理 lift'_mk
  结论: (g : M ->ₗ[R] M'') (h : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: rfl

Depends on / 依赖: _modOf, mul_of, one_mul
-/
theorem lift'_mk (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (m : M) (s : S) :
    LocalizedModule.lift' S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl

/--
theorem `lift'_add` / 定理 `lift'_add`

English:
theorem lift'_add
  statement: (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      rw [mk_add_mk]; rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.lift'_mk]
      rw [map_add]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [smul_add]; rw [← map_smul]; rw [← map_smul]; rw [← map_smul]
      congr 1 <;> symm
      · rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
        simp only [Submonoid.coe_mul, LinearMap.map_smul_of_tower]
        rw [mul_smul]; rw [Submonoid.smul_def]
      · dsimp
        rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [mul_comm]; rw [mul_smul]; rw [← map_smul]
        rfl)
    x y

中文:
定理 lift'_add
  结论: (g : M ->ₗ[R] M'') (h : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      rw [mk_add_mk]; rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.lift'_mk]
      rw [map_add]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [smul_add]; rw [← map_smul]; rw [← map_smul]; rw [← map_smul]
      congr 1 <;> symm
      · rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
        simp only [Submonoid.coe_mul, LinearMap.map_smul_of_tower]
        rw [mul_smul]; rw [Submonoid.smul_def]
      · dsimp
        rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [mul_comm]; rw [mul_smul]; rw [← map_smul]
        rfl)
    x y
-/
theorem lift'_add (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (x y) :
    LocalizedModule.lift' S g h (x + y) =
      LocalizedModule.lift' S g h x + LocalizedModule.lift' S g h y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      rw [mk_add_mk]; rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.lift'_mk]
      rw [map_add]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [smul_add]; rw [← map_smul]; rw [← map_smul]; rw [← map_smul]
      congr 1 <;> symm
      · rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
        simp only [Submonoid.coe_mul, LinearMap.map_smul_of_tower]
        rw [mul_smul]; rw [Submonoid.smul_def]
      · dsimp
        rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [mul_comm]; rw [mul_smul]; rw [← map_smul]
        rfl)
    x y

/--
theorem `lift'_smul` / 定理 `lift'_smul`

English:
theorem lift'_smul
  statement: (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: m.induction_on fun a b => by
    rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.smul'_mk]; rw [LocalizedModule.lift'_mk]; rw [← map_smul]; rw [← g.map_smul]

中文:
定理 lift'_smul
  结论: (g : M ->ₗ[R] M'') (h : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: m.induction_on fun a b => by
    rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.smul'_mk]; rw [LocalizedModule.lift'_mk]; rw [← map_smul]; rw [← g.map_smul]
-/
theorem lift'_smul (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (r : R) (m) : r • LocalizedModule.lift' S g h m = LocalizedModule.lift' S g h (r • m) :=
  m.induction_on fun a b => by
    rw [LocalizedModule.lift'_mk]; rw [LocalizedModule.smul'_mk]; rw [LocalizedModule.lift'_mk]; rw [← map_smul]; rw [← g.map_smul]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : M ->ₗ[R] M'')
  body: LocalizedModule.lift' S g h
  map_add' := LocalizedModule.lift'_add S g h
  map_smul' r x := by rw [LocalizedModule.lift'_smul, RingHom.id_apply]

中文:
定义 lift
  签名: (g : M ->ₗ[R] M'')
  定义体: LocalizedModule.lift' S g h
  map_add' := LocalizedModule.lift'_add S g h
  map_smul' r x := by rw [LocalizedModule.lift'_smul, RingHom.id_apply]

Depends on / 依赖: LocalizedModule, LocalizedModule.lift, _mul_modOf, add_zero, divOf_add_modOf, dvd_mul_right
-/
noncomputable def lift (g : M ->ₗ[R] M'')
    (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    LocalizedModule S M ->ₗ[R] M'' where
  toFun := LocalizedModule.lift' S g h
  map_add' := LocalizedModule.lift'_add S g h
  map_smul' r x := by rw [LocalizedModule.lift'_smul, RingHom.id_apply]

/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  proof: rfl

@[simp]

中文:
定理 lift_mk
  证明: rfl

@[simp]
-/
theorem lift_mk
    (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit (algebraMap R (Module.End R M'') x)) (m : M) (s : S) :
    LocalizedModule.lift S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl

@[simp]
/--
lemma `lift_mk_one` / 引理 `lift_mk_one`

English:
lemma lift_mk_one
  given: (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) (m : M)
  proof: by
  simp [lift_mk]

中文:
引理 lift_mk_one
  条件: (h : 对任意 (x : S), 是单位 ((algebraMap R (模.End R M'')) x)) (m : M)
  证明: by
  simp [lift_mk]

Depends on / 依赖: lift_mk
-/
lemma lift_mk_one (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) (m : M) :
    (LocalizedModule.lift S g h) (LocalizedModule.mk m 1) = g m := by
  simp [lift_mk]

/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  given: (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: by
  ext x
  simp [LocalizedModule.lift_mk]

中文:
定理 lift_comp
  条件: (g : M ->ₗ[R] M'') (h : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: by
  ext x
  simp [LocalizedModule.lift_mk]

Depends on / 依赖: LocalizedModule, LocalizedModule.lift_mk, lift_mk
-/
theorem lift_comp (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S g h).comp (mkLinearMap S M) = g := by
  ext x
  simp [LocalizedModule.lift_mk]

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: by
  ext x; induction x with | _ m s
  rw [LocalizedModule.lift_mk]
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← hl]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LocalizedModule.mkLinearMap_apply]; rw [← l.map_smul]; rw [LocalizedModule.smul'_mk]
  congr 1; rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩; simp only [one_smul, Submonoid.smul_def]

中文:
定理 lift_unique
  结论: (g : M ->ₗ[R] M'') (h : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: by
  ext x; induction x with | _ m s
  rw [LocalizedModule.lift_mk]
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← hl]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LocalizedModule.mkLinearMap_apply]; rw [← l.map_smul]; rw [LocalizedModule.smul'_mk]
  congr 1; rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩; simp only [one_smul, Submonoid.smul_def]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LocalizedModule, LocalizedModule.lift_mk, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq, LocalizedModule.smul, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submonoid, Submonoid.smul_def, algebraMap_isUnit_inv_apply_eq_iff, coe_comp, comp_apply, l.map_smul, lift_mk, map_smul, mkLinearMap_apply
-/
theorem lift_unique (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : LocalizedModule S M ->ₗ[R] M'') (hl : l.comp (LocalizedModule.mkLinearMap S M) = g) :
    LocalizedModule.lift S g h = l := by
  ext x; induction x with | _ m s
  rw [LocalizedModule.lift_mk]
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← hl]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LocalizedModule.mkLinearMap_apply]; rw [← l.map_smul]; rw [LocalizedModule.smul'_mk]
  congr 1; rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩; simp only [one_smul, Submonoid.smul_def]

end LocalizedModule

/--
Instance `localizedModuleIsLocalizedModule` / 实例 `localizedModuleIsLocalizedModule`

English:
instance localizedModuleIsLocalizedModule
  signature: :
  body: ⟨⟨algebraMap R (Module.End R (LocalizedModule S M)) s, LocalizedModule.divBy s,
DFunLike.ext _ _ LocalizedModule.mul_by_divBy s,
DFunLike.ext _ _ LocalizedModule.divBy_mul_by s⟩,
      DFunLike.ext _ _ fun p =>
p.induction_on by
          intros
          rfl⟩
  surj p :=
    p.induction_on fun m t => by
      refine ⟨⟨m, t⟩, ?_⟩
      rw [Submonoid.smul_def]; rw [LocalizedModule.smul'_mk]; rw [LocalizedModule.mkLinearMap_apply]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel t]
  exists_of_eq eq1 := by simpa only [eq_comm, one_smul] using LocalizedModule.mk_eq.mp eq1

中文:
实例 localizedModuleIsLocalizedModule
  签名: :
  定义体: ⟨⟨algebraMap R (Module.End R (LocalizedModule S M)) s, LocalizedModule.divBy s,
DFunLike.ext _ _ LocalizedModule.mul_by_divBy s,
DFunLike.ext _ _ LocalizedModule.divBy_mul_by s⟩,
      DFunLike.ext _ _ fun p =>
p.induction_on by
          intros
          rfl⟩
  surj p :=
    p.induction_on fun m t => by
      refine ⟨⟨m, t⟩, ?_⟩
      rw [Submonoid.smul_def]; rw [LocalizedModule.smul'_mk]; rw [LocalizedModule.mkLinearMap_apply]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel t]
  exists_of_eq eq1 := by simpa only [eq_comm, one_smul] using LocalizedModule.mk_eq.mp eq1

Depends on / 依赖: DFunLike, DFunLike.ext, LocalizedModule, LocalizedModule.divBy, LocalizedModule.divBy_mul_by, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_cancel, LocalizedModule.mul_by_divBy, LocalizedModule.smul, Module, Module.End, Submonoid, Submonoid.smul_def, algebraMap, divBy_mul_by, eq_comm, exists_of_eq, induction_on, intros, mkLinearMap_apply
-/
instance localizedModuleIsLocalizedModule :
    IsLocalizedModule S (LocalizedModule.mkLinearMap S M) where
  map_units s :=
    ⟨⟨algebraMap R (Module.End R (LocalizedModule S M)) s, LocalizedModule.divBy s,
DFunLike.ext _ _ LocalizedModule.mul_by_divBy s,
DFunLike.ext _ _ LocalizedModule.divBy_mul_by s⟩,
      DFunLike.ext _ _ fun p =>
p.induction_on by
          intros
          rfl⟩
  surj p :=
    p.induction_on fun m t => by
      refine ⟨⟨m, t⟩, ?_⟩
      rw [Submonoid.smul_def]; rw [LocalizedModule.smul'_mk]; rw [LocalizedModule.mkLinearMap_apply]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel t]
  exists_of_eq eq1 := by simpa only [eq_comm, one_smul] using LocalizedModule.mk_eq.mp eq1

/--
lemma `IsLocalizedModule.restrictScalars` / 引理 `IsLocalizedModule.restrictScalars`

English:
lemma IsLocalizedModule.restrictScalars
  statement: (S : Submonoid R) [Module A M]
  proof: by
    have := h.1 ⟨algebraMap R A s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, ⟨_, ⟨r, ⟨hr₁, rfl⟩⟩⟩⟩, hx⟩ := h.2 y
    exact ⟨⟨x, ⟨r, hr₁⟩⟩, by simpa [Submonoid.smul_def] using hx⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩, hc⟩ := h.3 e
    exact ⟨⟨r, hr⟩, by simpa [Submonoid.smul_def] using hc⟩

中文:
引理 是Localized模.restrictScalars
  结论: (S : 子幺半群 R) [模 A M]
  证明: by
    have := h.1 ⟨algebraMap R A s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, ⟨_, ⟨r, ⟨hr₁, rfl⟩⟩⟩⟩, hx⟩ := h.2 y
    exact ⟨⟨x, ⟨r, hr₁⟩⟩, by simpa [Submonoid.smul_def] using hx⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩, hc⟩ := h.3 e
    exact ⟨⟨r, hr⟩, by simpa [Submonoid.smul_def] using hc⟩

Depends on / 依赖: Algebra, Algebra.mem_algebraMapSubmonoid_of_mem, IsScalarTower, IsScalarTower.algebraMap_apply, Module, Module.End.isUnit_iff, Submonoid, Submonoid.smul_def, algebraMap, algebraMap_apply, exists_of_eq, isUnit_iff, mem_algebraMapSubmonoid_of_mem, smul_def
-/
lemma IsLocalizedModule.restrictScalars (S : Submonoid R) [Module A M]
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M ->ₗ[A] N) [h : IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f] :
    IsLocalizedModule S (f.restrictScalars R) where
  map_units s := by
    have := h.1 ⟨algebraMap R A s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, ⟨_, ⟨r, ⟨hr₁, rfl⟩⟩⟩⟩, hx⟩ := h.2 y
    exact ⟨⟨x, ⟨r, hr₁⟩⟩, by simpa [Submonoid.smul_def] using hx⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩, hc⟩ := h.3 e
    exact ⟨⟨r, hr⟩, by simpa [Submonoid.smul_def] using hc⟩

/--
lemma `IsLocalizedModule.restrictScalars_powers` / 引理 `IsLocalizedModule.restrictScalars_powers`

English:
lemma IsLocalizedModule.restrictScalars_powers
  statement: [Module A M]
  proof: by
  rw [← Algebra.algebraMapSubmonoid_powers] at h
  exact IsLocalizedModule.restrictScalars _ f

中文:
引理 是Localized模.restrictScalars_powers
  结论: [模 A M]
  证明: by
  rw [← Algebra.algebraMapSubmonoid_powers] at h
  exact IsLocalizedModule.restrictScalars _ f

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_powers, IsLocalizedModule, IsLocalizedModule.restrictScalars, algebraMapSubmonoid_powers, restrictScalars
-/
lemma IsLocalizedModule.restrictScalars_powers [Module A M]
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (r : R) (f : M ->ₗ[A] N) [h : IsLocalizedModule (.powers (algebraMap R A r)) f] :
    IsLocalizedModule (.powers r) (f.restrictScalars R) := by
  rw [← Algebra.algebraMapSubmonoid_powers] at h
  exact IsLocalizedModule.restrictScalars _ f

/--
lemma `IsLocalizedModule.of_restrictScalars` / 引理 `IsLocalizedModule.of_restrictScalars`

English:
lemma IsLocalizedModule.of_restrictScalars
  statement: (S : Submonoid R)
  proof: by
    obtain ⟨_, x, hx, rfl⟩ := x
    have := IsLocalizedModule.map_units (f.restrictScalars R) ⟨x, hx⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S (f.restrictScalars R) y
    exact ⟨⟨x, ⟨_, t, t.2, rfl⟩⟩, by simpa [Submonoid.smul_def] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f.restrictScalars R) e
    refine ⟨⟨_, c, c.2, rfl⟩, by simpa [Submonoid.smul_def]⟩

中文:
引理 是Localized模.of_restrictScalars
  结论: (S : 子幺半群 R)
  证明: by
    obtain ⟨_, x, hx, rfl⟩ := x
    have := IsLocalizedModule.map_units (f.restrictScalars R) ⟨x, hx⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S (f.restrictScalars R) y
    exact ⟨⟨x, ⟨_, t, t.2, rfl⟩⟩, by simpa [Submonoid.smul_def] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f.restrictScalars R) e
    refine ⟨⟨_, c, c.2, rfl⟩, by simpa [Submonoid.smul_def]⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.exists_of_eq, IsLocalizedModule.map_units, IsLocalizedModule.surj, IsScalarTower, IsScalarTower.algebraMap_apply, Module, Module.End.isUnit_iff, Submonoid, Submonoid.smul_def, algebraMap_apply, exists_of_eq, f.restrictScalars, isUnit_iff, map_units, restrictScalars, smul_def
-/
lemma IsLocalizedModule.of_restrictScalars (S : Submonoid R)
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M ->ₗ[A] N) [IsLocalizedModule S (f.restrictScalars R)] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f where
  map_units x := by
    obtain ⟨_, x, hx, rfl⟩ := x
    have := IsLocalizedModule.map_units (f.restrictScalars R) ⟨x, hx⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S (f.restrictScalars R) y
    exact ⟨⟨x, ⟨_, t, t.2, rfl⟩⟩, by simpa [Submonoid.smul_def] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f.restrictScalars R) e
    refine ⟨⟨_, c, c.2, rfl⟩, by simpa [Submonoid.smul_def]⟩

/--
lemma `IsLocalizedModule.restrictScalars_iff` / 引理 `IsLocalizedModule.restrictScalars_iff`

English:
lemma IsLocalizedModule.restrictScalars_iff
  statement: (S : Submonoid R)
  proof: ⟨fun _ => restrictScalars _ _, fun _ => of_restrictScalars _ _⟩

中文:
引理 是Localized模.restrictScalars_iff
  结论: (S : 子幺半群 R)
  证明: ⟨fun _ => restrictScalars _ _, fun _ => of_restrictScalars _ _⟩

Depends on / 依赖: of_restrictScalars, restrictScalars
-/
lemma IsLocalizedModule.restrictScalars_iff (S : Submonoid R)
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N] (f : M ->ₗ[A] N) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f ↔
    IsLocalizedModule S (f.restrictScalars R) :=
  ⟨fun _ => restrictScalars _ _, fun _ => of_restrictScalars _ _⟩

/--
lemma `IsLocalizedModule.of_exists_mul_mem` / 引理 `IsLocalizedModule.of_exists_mul_mem`

English:
lemma IsLocalizedModule.of_exists_mul_mem
  statement: {N : Type*} [AddCommMonoid N] [Module R N]
  proof: by
    obtain ⟨m, mx⟩ := h' x
    have := IsLocalizedModule.map_units f ⟨_, mx⟩
    rw [map_mul]; rw [(Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at this
    exact this.2
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S f y
    exact ⟨⟨x, ⟨t, h t.2⟩⟩, e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) e
    exact ⟨⟨c, h c.2⟩, hc⟩

中文:
引理 是Localized模.of_存在_mul_mem
  结论: {N : 类型} [加法交换幺半群 N] [模 R N]
  证明: by
    obtain ⟨m, mx⟩ := h' x
    have := IsLocalizedModule.map_units f ⟨_, mx⟩
    rw [map_mul]; rw [(Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at this
    exact this.2
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S f y
    exact ⟨⟨x, ⟨t, h t.2⟩⟩, e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) e
    exact ⟨⟨c, h c.2⟩, hc⟩

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_left, IsLocalizedModule, IsLocalizedModule.exists_of_eq, IsLocalizedModule.map_units, IsLocalizedModule.surj, commute_algebraMap_left, exists_of_eq, isUnit_mul_iff, map_mul, map_units
-/
lemma IsLocalizedModule.of_exists_mul_mem {N : Type*} [AddCommMonoid N] [Module R N]
    (S T : Submonoid R) (h : S <= T) (h' : forall x : T, exists m : R, m * x in S)
    (f : M ->ₗ[R] N) [IsLocalizedModule S f] :
    IsLocalizedModule T f where
  map_units x := by
    obtain ⟨m, mx⟩ := h' x
    have := IsLocalizedModule.map_units f ⟨_, mx⟩
    rw [map_mul]; rw [(Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at this
    exact this.2
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S f y
    exact ⟨⟨x, ⟨t, h t.2⟩⟩, e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) e
    exact ⟨⟨c, h c.2⟩, hc⟩

namespace IsLocalizedModule

variable [IsLocalizedModule S f]

/--
Definition of `fromLocalizedModule'` / `fromLocalizedModule'` 的定义

English:
definition fromLocalizedModule'
  signature: : LocalizedModule S M -> M'
  body: fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).unit⁻¹.val (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      dsimp
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [← map_smul]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']; rw [← map_smul]
      exact (IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1.symm⟩)

@[simp]

中文:
定义 fromLocalizedModule'
  签名: : LocalizedModule S M -> M'
  定义体: fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).unit⁻¹.val (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      dsimp
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [← map_smul]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']; rw [← map_smul]
      exact (IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1.symm⟩)

@[simp]
-/
noncomputable def fromLocalizedModule' : LocalizedModule S M -> M' := fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).unit⁻¹.val (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      dsimp
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [← map_smul]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']; rw [← map_smul]
      exact (IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1.symm⟩)

@[simp]
/--
theorem `fromLocalizedModule'_mk` / 定理 `fromLocalizedModule'_mk`

English:
theorem fromLocalizedModule'_mk
  given: (m : M) (s : S)
  proof: rfl

中文:
定理 fromLocalizedModule'_mk
  条件: (m : M) (s : S)
  证明: rfl
-/
theorem fromLocalizedModule'_mk (m : M) (s : S) :
    fromLocalizedModule' S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

/--
theorem `fromLocalizedModule'_add` / 定理 `fromLocalizedModule'_add`

English:
theorem fromLocalizedModule'_add
  given: (x y : LocalizedModule S M)
  proof: LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      simp only [LocalizedModule.mk_add_mk, fromLocalizedModule'_mk]
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [smul_add]; rw [← map_smul]; rw [← map_smul]; rw [← map_smul]; rw [map_add]
      congr 1
      all_goals rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']
      · simp [mul_smul, Submonoid.smul_def]
      · rw [Submonoid.coe_mul, LinearMap.map_smul_of_tower, mul_comm, mul_smul, Submonoid.smul_def])
    x y

中文:
定理 fromLocalizedModule'_add
  条件: (x y : LocalizedModule S M)
  证明: LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      simp only [LocalizedModule.mk_add_mk, fromLocalizedModule'_mk]
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [smul_add]; rw [← map_smul]; rw [← map_smul]; rw [← map_smul]; rw [map_add]
      congr 1
      all_goals rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']
      · simp [mul_smul, Submonoid.smul_def]
      · rw [Submonoid.coe_mul, LinearMap.map_smul_of_tower, mul_comm, mul_smul, Submonoid.smul_def])
    x y
-/
theorem fromLocalizedModule'_add (x y : LocalizedModule S M) :
    fromLocalizedModule' S f (x + y) = fromLocalizedModule' S f x + fromLocalizedModule' S f y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      simp only [LocalizedModule.mk_add_mk, fromLocalizedModule'_mk]
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [smul_add]; rw [← map_smul]; rw [← map_smul]; rw [← map_smul]; rw [map_add]
      congr 1
      all_goals rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']
      · simp [mul_smul, Submonoid.smul_def]
      · rw [Submonoid.coe_mul, LinearMap.map_smul_of_tower, mul_comm, mul_smul, Submonoid.smul_def])
    x y

/--
theorem `fromLocalizedModule'_smul` / 定理 `fromLocalizedModule'_smul`

English:
theorem fromLocalizedModule'_smul
  given: (r : R) (x : LocalizedModule S M)
  proof: LocalizedModule.induction_on
    (by
      intro a b
      rw [fromLocalizedModule'_mk]; rw [LocalizedModule.smul'_mk]; rw [fromLocalizedModule'_mk]; rw [f.map_smul]; rw [map_smul])
    x

中文:
定理 fromLocalizedModule'_smul
  条件: (r : R) (x : LocalizedModule S M)
  证明: LocalizedModule.induction_on
    (by
      intro a b
      rw [fromLocalizedModule'_mk]; rw [LocalizedModule.smul'_mk]; rw [fromLocalizedModule'_mk]; rw [f.map_smul]; rw [map_smul])
    x
-/
theorem fromLocalizedModule'_smul (r : R) (x : LocalizedModule S M) :
    r • fromLocalizedModule' S f x = fromLocalizedModule' S f (r • x) :=
  LocalizedModule.induction_on
    (by
      intro a b
      rw [fromLocalizedModule'_mk]; rw [LocalizedModule.smul'_mk]; rw [fromLocalizedModule'_mk]; rw [f.map_smul]; rw [map_smul])
    x

/--
Definition of `fromLocalizedModule` / `fromLocalizedModule` 的定义

English:
definition fromLocalizedModule
  signature: : LocalizedModule S M ->ₗ[R] M' where
  body: fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]

中文:
定义 fromLocalizedModule
  签名: : LocalizedModule S M ->ₗ[R] M' where
  定义体: fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]

Depends on / 依赖: fromLocalizedModule
-/
noncomputable def fromLocalizedModule : LocalizedModule S M ->ₗ[R] M' where
  toFun := fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]

/--
theorem `fromLocalizedModule_mk` / 定理 `fromLocalizedModule_mk`

English:
theorem fromLocalizedModule_mk
  given: (m : M) (s : S)
  proof: rfl

中文:
定理 fromLocalizedModule_mk
  条件: (m : M) (s : S)
  证明: rfl
-/
theorem fromLocalizedModule_mk (m : M) (s : S) :
    fromLocalizedModule S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

/--
theorem `fromLocalizedModule.inj` / 定理 `fromLocalizedModule.inj`

English:
theorem fromLocalizedModule.inj
  statement: Function.Injective fromLocalizedModule S f
  proof: fun x y eq1 => by
  induction x with | _ a b
  induction y with | _ a' b'
  simp only [fromLocalizedModule_mk] at eq1
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  rw [LocalizedModule.mk_eq]; rw [← IsLocalizedModule.eq_iff_exists S f]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [f.map_smul]; rw [f.map_smul]; rw [eq1]

中文:
定理 fromLocalizedModule.inj
  结论: 函数.单射 fromLocalizedModule S f
  证明: fun x y eq1 => by
  induction x with | _ a b
  induction y with | _ a' b'
  simp only [fromLocalizedModule_mk] at eq1
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  rw [LocalizedModule.mk_eq]; rw [← IsLocalizedModule.eq_iff_exists S f]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [f.map_smul]; rw [f.map_smul]; rw [eq1]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.eq_iff_exists, LocalizedModule, LocalizedModule.mk_eq, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submonoid, Submonoid.smul_def, algebraMap_isUnit_inv_apply_eq_iff, eq_iff_exists, f.map_smul, fromLocalizedModule_mk, map_smul, mk_eq, smul_def
-/
theorem fromLocalizedModule.inj : Function.Injective fromLocalizedModule S f := fun x y eq1 => by
  induction x with | _ a b
  induction y with | _ a' b'
  simp only [fromLocalizedModule_mk] at eq1
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← map_smul]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  rw [LocalizedModule.mk_eq]; rw [← IsLocalizedModule.eq_iff_exists S f]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [f.map_smul]; rw [f.map_smul]; rw [eq1]

/--
theorem `fromLocalizedModule.surj` / 定理 `fromLocalizedModule.surj`

English:
theorem fromLocalizedModule.surj
  statement: Function.Surjective fromLocalizedModule S f
  proof: fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← eq1]; rw [Submonoid.smul_def]⟩

中文:
定理 fromLocalizedModule.surj
  结论: 函数.满射 fromLocalizedModule S f
  证明: fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← eq1]; rw [Submonoid.smul_def]⟩
-/
theorem fromLocalizedModule.surj : Function.Surjective fromLocalizedModule S f := fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [← eq1]; rw [Submonoid.smul_def]⟩

/--
theorem `fromLocalizedModule.bij` / 定理 `fromLocalizedModule.bij`

English:
theorem fromLocalizedModule.bij
  statement: Function.Bijective fromLocalizedModule S f
  proof: ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩

中文:
定理 fromLocalizedModule.bij
  结论: 函数.双射 fromLocalizedModule S f
  证明: ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩

Depends on / 依赖: fromLocalizedModule, fromLocalizedModule.inj, fromLocalizedModule.surj
-/
theorem fromLocalizedModule.bij : Function.Bijective fromLocalizedModule S f :=
  ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: : LocalizedModule S M ≃ₗ[R] M'
  body: { fromLocalizedModule S f,
Equiv.ofBijective (fromLocalizedModule S f) fromLocalizedModule.bij _ _ with }

中文:
定义 iso
  签名: : LocalizedModule S M ≃ₗ[R] M'
  定义体: { fromLocalizedModule S f,
Equiv.ofBijective (fromLocalizedModule S f) fromLocalizedModule.bij _ _ with }

Depends on / 依赖: Equiv.ofBijective, fromLocalizedModule, fromLocalizedModule.bij, ofBijective
-/
noncomputable def iso : LocalizedModule S M ≃ₗ[R] M' :=
  { fromLocalizedModule S f,
Equiv.ofBijective (fromLocalizedModule S f) fromLocalizedModule.bij _ _ with }

/--
theorem `iso_apply_mk` / 定理 `iso_apply_mk`

English:
theorem iso_apply_mk
  given: (m : M) (s : S)
  proof: rfl

@[simp]

中文:
定理 iso_apply_mk
  条件: (m : M) (s : S)
  证明: rfl

@[simp]
-/
theorem iso_apply_mk (m : M) (s : S) :
    iso S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

@[simp]
/--
lemma `iso_mk_one` / 引理 `iso_mk_one`

English:
lemma iso_mk_one
  given: (x : M)
  statement: (iso S f) (LocalizedModule.mk x 1) = f x
  proof: by
  simp [iso_apply_mk]

中文:
引理 iso_mk_one
  条件: (x : M)
  结论: (iso S f) (LocalizedModule.mk x 1) = f x
  证明: by
  simp [iso_apply_mk]

Depends on / 依赖: iso_apply_mk
-/
lemma iso_mk_one (x : M) : (iso S f) (LocalizedModule.mk x 1) = f x := by
  simp [iso_apply_mk]

/--
theorem `iso_symm_apply_aux` / 定理 `iso_symm_apply_aux`

English:
theorem iso_symm_apply_aux
  given: (m : M')
  proof: by
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  rw [LinearEquiv.apply_symm_apply]
  simp [iso, fromLocalizedModule, Module.End.algebraMap_isUnit_inv_apply_eq_iff',
    ← Submonoid.smul_def, (surj _ _ _).choose_spec]

中文:
定理 iso_symm_apply_aux
  条件: (m : M')
  证明: by
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  rw [LinearEquiv.apply_symm_apply]
  simp [iso, fromLocalizedModule, Module.End.algebraMap_isUnit_inv_apply_eq_iff',
    ← Submonoid.smul_def, (surj _ _ _).choose_spec]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.injective, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submonoid, Submonoid.smul_def, algebraMap_isUnit_inv_apply_eq_iff, apply_fun, apply_symm_apply, choose_spec, fromLocalizedModule, injective, smul_def
-/
theorem iso_symm_apply_aux (m : M') :
    (iso S f).symm m =
      LocalizedModule.mk (IsLocalizedModule.surj S f m).choose.1
        (IsLocalizedModule.surj S f m).choose.2 := by
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  rw [LinearEquiv.apply_symm_apply]
  simp [iso, fromLocalizedModule, Module.End.algebraMap_isUnit_inv_apply_eq_iff',
    ← Submonoid.smul_def, (surj _ _ _).choose_spec]

/--
theorem `iso_symm_apply'` / 定理 `iso_symm_apply'`

English:
theorem iso_symm_apply'
  given: (m : M') (a : M) (b : S) (eq1 : b • m = f a)
  proof: (iso_symm_apply_aux S f m).trans
LocalizedModule.mk_eq.mpr by
      rw [← IsLocalizedModule.eq_iff_exists S f]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [f.map_smul]; rw [f.map_smul]; rw [← (surj _ _ _).choose_spec]; rw [← Submonoid.smul_def]; rw [← Submonoid.smul_def]; rw [← mul_smul]; rw [mul_comm]; rw [mul_smul]; rw [eq1]

中文:
定理 iso_symm_apply'
  条件: (m : M') (a : M) (b : S) (eq1 : b • m = f a)
  证明: (iso_symm_apply_aux S f m).trans
LocalizedModule.mk_eq.mpr by
      rw [← IsLocalizedModule.eq_iff_exists S f]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [f.map_smul]; rw [f.map_smul]; rw [← (surj _ _ _).choose_spec]; rw [← Submonoid.smul_def]; rw [← Submonoid.smul_def]; rw [← mul_smul]; rw [mul_comm]; rw [mul_smul]; rw [eq1]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.eq_iff_exists, LocalizedModule, LocalizedModule.mk_eq.mpr, Submonoid, Submonoid.smul_def, choose_spec, eq_iff_exists, f.map_smul, iso_symm_apply_aux, map_smul, mk_eq, mul_comm, mul_smul, smul_def
-/
theorem iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) :
    (iso S f).symm m = LocalizedModule.mk a b :=
(iso_symm_apply_aux S f m).trans
LocalizedModule.mk_eq.mpr by
      rw [← IsLocalizedModule.eq_iff_exists S f]; rw [Submonoid.smul_def]; rw [Submonoid.smul_def]; rw [f.map_smul]; rw [f.map_smul]; rw [← (surj _ _ _).choose_spec]; rw [← Submonoid.smul_def]; rw [← Submonoid.smul_def]; rw [← mul_smul]; rw [mul_comm]; rw [mul_smul]; rw [eq1]

/--
theorem `iso_symm_comp` / 定理 `iso_symm_comp`

English:
theorem iso_symm_comp
  statement: (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M
  proof: by
  ext m
  rw [LinearMap.comp_apply]; rw [LocalizedModule.mkLinearMap_apply]; rw [LinearEquiv.coe_coe]; rw [iso_symm_apply']
  exact one_smul _ _

@[simp]

中文:
定理 iso_symm_comp
  结论: (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M
  证明: by
  ext m
  rw [LinearMap.comp_apply]; rw [LocalizedModule.mkLinearMap_apply]; rw [LinearEquiv.coe_coe]; rw [iso_symm_apply']
  exact one_smul _ _

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.comp_apply, LocalizedModule, LocalizedModule.mkLinearMap_apply, coe_coe, comp_apply, iso_symm_apply, mkLinearMap_apply, one_smul
-/
theorem iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M := by
  ext m
  rw [LinearMap.comp_apply]; rw [LocalizedModule.mkLinearMap_apply]; rw [LinearEquiv.coe_coe]; rw [iso_symm_apply']
  exact one_smul _ _

@[simp]
/--
lemma `iso_symm_apply` / 引理 `iso_symm_apply`

English:
lemma iso_symm_apply
  given: (x)
  statement: (iso S f).symm (f x) = LocalizedModule.mk x 1
  proof: DFunLike.congr_fun (iso_symm_comp S f) x

中文:
引理 iso_symm_apply
  条件: (x)
  结论: (iso S f).symm (f x) = LocalizedModule.mk x 1
  证明: DFunLike.congr_fun (iso_symm_comp S f) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, iso_symm_comp
-/
lemma iso_symm_apply (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1 :=
  DFunLike.congr_fun (iso_symm_comp S f) x

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : M ->ₗ[R] M'')
  body: (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap

中文:
定义 lift
  签名: (g : M ->ₗ[R] M'')
  定义体: (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap

Depends on / 依赖: LocalizedModule, LocalizedModule.lift, symm.toLinearMap, toLinearMap
-/
noncomputable def lift (g : M ->ₗ[R] M'')
    (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) : M' ->ₗ[R] M'' :=
  (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap

/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  given: (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc]; rw [iso_symm_comp]; rw [LocalizedModule.lift_comp S g h]

@[simp]

中文:
定理 lift_comp
  条件: (g : M ->ₗ[R] M'') (h : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc]; rw [iso_symm_comp]; rw [LocalizedModule.lift_comp S g h]

@[simp]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift, LinearMap, LinearMap.comp_assoc, LocalizedModule, LocalizedModule.lift_comp, comp_assoc, iso_symm_comp, lift_comp
-/
theorem lift_comp (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S f g h).comp f = g := by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc]; rw [iso_symm_comp]; rw [LocalizedModule.lift_comp S g h]

@[simp]
/--
lemma `lift_iso` / 引理 `lift_iso`

English:
lemma lift_iso
  statement: (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: by
  simp [lift]

@[simp]

中文:
引理 lift_iso
  结论: (h : 对任意 (x : S), 是单位 ((algebraMap R (模.End R M'')) x))
  证明: by
  simp [lift]

@[simp]
-/
lemma lift_iso (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
    (x : LocalizedModule S M) :
    IsLocalizedModule.lift S f g h ((iso S f) x) = LocalizedModule.lift S g h x := by
  simp [lift]

@[simp]
/--
lemma `lift_comp_iso` / 引理 `lift_comp_iso`

English:
lemma lift_comp_iso
  given: (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: LinearMap.ext fun x => lift_iso S f g h x

@[simp]

中文:
引理 lift_comp_iso
  条件: (h : 对任意 (x : S), 是单位 ((algebraMap R (模.End R M'')) x))
  证明: LinearMap.ext fun x => lift_iso S f g h x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, lift_iso
-/
lemma lift_comp_iso (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) :
    IsLocalizedModule.lift S f g h ∘ₗ iso S f = LocalizedModule.lift S g h :=
  LinearMap.ext fun x => lift_iso S f g h x

@[simp]
/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (g : M ->ₗ[R] M'') (h) (x)
  proof: LinearMap.congr_fun (lift_comp S f g h) x

中文:
定理 lift_apply
  条件: (g : M ->ₗ[R] M'') (h) (x)
  证明: LinearMap.congr_fun (lift_comp S f g h) x

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, lift_comp
-/
theorem lift_apply (g : M ->ₗ[R] M'') (h) (x) :
    lift S f g h (f x) = g x := LinearMap.congr_fun (lift_comp S f g h) x

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: by
  dsimp only [IsLocalizedModule.lift]
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap)]; rw [LinearMap.comp_assoc]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.symm_trans_self]; rw [LinearEquiv.refl_toLinearMap]; rw [LinearMap.comp_id]
  rw [LinearMap.comp_assoc]; rw [← hl]
  ext x
  simp

中文:
定理 lift_unique
  结论: (g : M ->ₗ[R] M'') (h : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: by
  dsimp only [IsLocalizedModule.lift]
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap)]; rw [LinearMap.comp_assoc]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.symm_trans_self]; rw [LinearEquiv.refl_toLinearMap]; rw [LinearMap.comp_id]
  rw [LinearMap.comp_assoc]; rw [← hl]
  ext x
  simp

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.lift, LinearEquiv, LinearEquiv.comp_coe, LinearEquiv.refl_toLinearMap, LinearEquiv.symm_trans_self, LinearMap, LinearMap.comp_assoc, LinearMap.comp_id, LocalizedModule, LocalizedModule.lift_unique, comp_assoc, comp_coe, comp_id, l.comp, lift_unique, refl_toLinearMap, symm_trans_self, toLinearMap
-/
theorem lift_unique (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : M' ->ₗ[R] M'') (hl : l.comp f = g) : lift S f g h = l := by
  dsimp only [IsLocalizedModule.lift]
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap)]; rw [LinearMap.comp_assoc]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.symm_trans_self]; rw [LinearEquiv.refl_toLinearMap]; rw [LinearMap.comp_id]
  rw [LinearMap.comp_assoc]; rw [← hl]
  ext x
  simp

/--
theorem `is_universal` / 定理 `is_universal`

English:
theorem is_universal
  proof: fun g h => ⟨lift S f g h, lift_comp S f g h, fun l hl => (lift_unique S f g h l hl).symm⟩

中文:
定理 is_universal
  证明: fun g h => ⟨lift S f g h, lift_comp S f g h, fun l hl => (lift_unique S f g h l hl).symm⟩

Depends on / 依赖: lift_comp, lift_unique
-/
theorem is_universal :
    forall (g : M ->ₗ[R] M'') (_ : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)),
      exists! l : M' ->ₗ[R] M'', l.comp f = g :=
  fun g h => ⟨lift S f g h, lift_comp S f g h, fun l hl => (lift_unique S f g h l hl).symm⟩

/--
theorem `linearMap_ext` / 定理 `linearMap_ext`

English:
theorem linearMap_ext
  statement: {N N'} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']
  proof: (is_universal S f _ <| map_units f').unique h rfl

中文:
定理 linearMap_ext
  结论: {N N'} [加法交换幺半群 N] [模 R N] [加法交换幺半群 N'] [模 R N']
  证明: (is_universal S f _ <| map_units f').unique h rfl

Depends on / 依赖: is_universal, map_units, unique
-/
theorem linearMap_ext {N N'} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']
    (f' : N ->ₗ[R] N') [IsLocalizedModule S f'] ⦃g g' : M' ->ₗ[R] N'⦄
    (h : g ∘ₗ f = g' ∘ₗ f) : g = g' :=
  (is_universal S f _ <| map_units f').unique h rfl

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (map_unit : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
  proof: by
  rw [← lift_unique S f (k.comp f) map_unit j h]; rw [lift_unique]
  rfl

中文:
定理 ext
  结论: (map_unit : 对任意 x : S, 是单位 ((algebraMap R (模.End R M'')) x))
  证明: by
  rw [← lift_unique S f (k.comp f) map_unit j h]; rw [lift_unique]
  rfl

Depends on / 依赖: k.comp, lift_unique, map_unit
-/
theorem ext (map_unit : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    ⦃j k : M' ->ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k := by
  rw [← lift_unique S f (k.comp f) map_unit j h]; rw [lift_unique]
  rfl

/--
Definition of `linearEquiv` / `linearEquiv` 的定义

English:
definition linearEquiv
  signature: [IsLocalizedModule S g]
  body: (iso S f).symm.trans (iso S g)

@[simp]

中文:
定义 linearEquiv
  签名: [是Localized模 S g]
  定义体: (iso S f).symm.trans (iso S g)

@[simp]

Depends on / 依赖: symm.trans
-/
noncomputable def linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M'' :=
  (iso S f).symm.trans (iso S g)

@[simp]
/--
lemma `linearEquiv_apply` / 引理 `linearEquiv_apply`

English:
lemma linearEquiv_apply
  given: [IsLocalizedModule S g] (x : M)
  proof: by
  simp [linearEquiv]

@[simp]

中文:
引理 linearEquiv_apply
  条件: [是Localized模 S g] (x : M)
  证明: by
  simp [linearEquiv]

@[simp]

Depends on / 依赖: linearEquiv
-/
lemma linearEquiv_apply [IsLocalizedModule S g] (x : M) :
    (linearEquiv S f g) (f x) = g x := by
  simp [linearEquiv]

@[simp]
/--
lemma `linearEquiv_symm_apply` / 引理 `linearEquiv_symm_apply`

English:
lemma linearEquiv_symm_apply
  given: [IsLocalizedModule S g] (x : M)
  proof: by
  simp [linearEquiv]

中文:
引理 linearEquiv_symm_apply
  条件: [是Localized模 S g] (x : M)
  证明: by
  simp [linearEquiv]

Depends on / 依赖: linearEquiv
-/
lemma linearEquiv_symm_apply [IsLocalizedModule S g] (x : M) :
    (linearEquiv S f g).symm (g x) = f x := by
  simp [linearEquiv]

/--
lemma `linearEquiv_of_isLocalizedModule_comp` / 引理 `linearEquiv_of_isLocalizedModule_comp`

English:
lemma linearEquiv_of_isLocalizedModule_comp
  given: (g : M' ->ₗ[R] M'') [IsLocalizedModule S (g ∘ₗ f)]
  proof: by
  refine ext S f (IsLocalizedModule.map_units (g ∘ₗ f)) ?_
  ext
  simp

中文:
引理 linearEquiv_of_isLocalizedModule_comp
  条件: (g : M' ->ₗ[R] M'') [是Localized模 S (g ∘ₗ f)]
  证明: by
  refine ext S f (IsLocalizedModule.map_units (g ∘ₗ f)) ?_
  ext
  simp

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.map_units, map_units
-/
lemma linearEquiv_of_isLocalizedModule_comp (g : M' ->ₗ[R] M'') [IsLocalizedModule S (g ∘ₗ f)] :
    linearEquiv S f (g ∘ₗ f) = g := by
  refine ext S f (IsLocalizedModule.map_units (g ∘ₗ f)) ?_
  ext
  simp

variable {S}

include f in
/--
theorem `smul_injective` / 定理 `smul_injective`

English:
theorem smul_injective
  given: (s : S)
  statement: Function.Injective fun m : M' => s • m
  proof: ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective

include f in

中文:
定理 smul_injective
  条件: (s : S)
  结论: 函数.单射 fun m : M' => s • m
  证明: ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective

include f in

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.map_units, Module, Module.End.isUnit_iff, injective, isUnit_iff, map_units
-/
theorem smul_injective (s : S) : Function.Injective fun m : M' => s • m :=
  ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective

include f in
/--
theorem `smul_inj` / 定理 `smul_inj`

English:
theorem smul_inj
  given: (s : S) (m₁ m₂ : M')
  statement: s • m₁ = s • m₂ ↔ m₁ = m₂
  proof: (smul_injective f s).eq_iff

include f in

中文:
定理 smul_inj
  条件: (s : S) (m₁ m₂ : M')
  结论: s • m₁ = s • m₂ ↔ m₁ = m₂
  证明: (smul_injective f s).eq_iff

include f in

Depends on / 依赖: eq_iff, smul_injective
-/
theorem smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂ :=
  (smul_injective f s).eq_iff

include f in
/--
lemma `isRegular_of_smul_left_injective` / 引理 `isRegular_of_smul_left_injective`

English:
lemma isRegular_of_smul_left_injective
  statement: {m : M'} (inj : Function.Injective fun r : R => r • m)
  proof: (Commute.isRegular_iff (Commute.all _)).mpr fun r r' eq => by
    have := congr_arg (· • m) eq
    simp_rw [mul_smul, ← Submonoid.smul_def, smul_inj f] at this
    exact inj this

中文:
引理 isRegular_of_smul_left_injective
  结论: {m : M'} (inj : 函数.单射 fun r : R => r • m)
  证明: (Commute.isRegular_iff (Commute.all _)).mpr fun r r' eq => by
    have := congr_arg (· • m) eq
    simp_rw [mul_smul, ← Submonoid.smul_def, smul_inj f] at this
    exact inj this

Depends on / 依赖: Commute, Commute.all, Commute.isRegular_iff, Submonoid, Submonoid.smul_def, congr_arg, isRegular_iff, mul_smul, simp_rw, smul_def, smul_inj
-/
lemma isRegular_of_smul_left_injective {m : M'} (inj : Function.Injective fun r : R => r • m)
    (s : S) : IsRegular (s : R) :=
  (Commute.isRegular_iff (Commute.all _)).mpr fun r r' eq => by
    have := congr_arg (· • m) eq
    simp_rw [mul_smul, ← Submonoid.smul_def, smul_inj f] at this
    exact inj this

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (m : M) (s : S)
  body: fromLocalizedModule S f (LocalizedModule.mk m s)

中文:
定义 mk'
  签名: (m : M) (s : S)
  定义体: fromLocalizedModule S f (LocalizedModule.mk m s)

Depends on / 依赖: LocalizedModule, LocalizedModule.mk, fromLocalizedModule
-/
noncomputable def mk' (m : M) (s : S) : M' :=
  fromLocalizedModule S f (LocalizedModule.mk m s)

/--
theorem `mk'_smul` / 定理 `mk'_smul`

English:
theorem mk'_smul
  statement: {R₀ : Type*} [SMul R₀ R] [SMul R₀ M] [SMul R₀ M']
  proof: by
  delta mk'
  rw [← LocalizedModule.smul'_mk]; rw [LinearMap.map_smul_of_tower]

中文:
定理 mk'_smul
  结论: {R₀ : 类型} [标量乘法 R₀ R] [标量乘法 R₀ M] [标量乘法 R₀ M']
  证明: by
  delta mk'
  rw [← LocalizedModule.smul'_mk]; rw [LinearMap.map_smul_of_tower]
-/
theorem mk'_smul {R₀ : Type*} [SMul R₀ R] [SMul R₀ M] [SMul R₀ M']
    [IsScalarTower R₀ R R] [IsScalarTower R₀ R M] [IsScalarTower R₀ R M']
    (r : R₀) (m : M) (s : S) : mk' f (r • m) s = r • mk' f m s := by
  delta mk'
  rw [← LocalizedModule.smul'_mk]; rw [LinearMap.map_smul_of_tower]

/--
theorem `mk'_add_mk'` / 定理 `mk'_add_mk'`

English:
theorem mk'_add_mk'
  given: (m₁ m₂ : M) (s₁ s₂ : S)
  proof: by
  delta mk'
  rw [← map_add]; rw [LocalizedModule.mk_add_mk]

@[simp]

中文:
定理 mk'_add_mk'
  条件: (m₁ m₂ : M) (s₁ s₂ : S)
  证明: by
  delta mk'
  rw [← map_add]; rw [LocalizedModule.mk_add_mk]

@[simp]
-/
theorem mk'_add_mk' (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ + mk' f m₂ s₂ = mk' f (s₂ • m₁ + s₁ • m₂) (s₁ * s₂) := by
  delta mk'
  rw [← map_add]; rw [LocalizedModule.mk_add_mk]

@[simp]
/--
theorem `mk'_zero` / 定理 `mk'_zero`

English:
theorem mk'_zero
  given: (s : S)
  statement: mk' f 0 s = 0
  proof: by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]

中文:
定理 mk'_zero
  条件: (s : S)
  结论: mk' f 0 s = 0
  证明: by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]
-/
theorem mk'_zero (s : S) : mk' f 0 s = 0 := by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]

variable (S) in
@[simp]
/--
theorem `mk'_one` / 定理 `mk'_one`

English:
theorem mk'_one
  given: (m : M)
  statement: mk' f m (1 : S) = f m
  proof: by
  delta mk'
  rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [Submonoid.coe_one]; rw [one_smul]

@[simp]

中文:
定理 mk'_one
  条件: (m : M)
  结论: mk' f m (1 : S) = f m
  证明: by
  delta mk'
  rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [Submonoid.coe_one]; rw [one_smul]

@[simp]
-/
theorem mk'_one (m : M) : mk' f m (1 : S) = f m := by
  delta mk'
  rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [Submonoid.coe_one]; rw [one_smul]

@[simp]
/--
theorem `mk'_cancel` / 定理 `mk'_cancel`

English:
theorem mk'_cancel
  given: (m : M) (s : S)
  statement: mk' f (s • m) s = f m
  proof: by
  delta mk'
  rw [LocalizedModule.mk_cancel]; rw [← mk'_one S f]; rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [OneMemClass.coe_one]; rw [mk'_one]; rw [one_smul]

@[simp]

中文:
定理 mk'_cancel
  条件: (m : M) (s : S)
  结论: mk' f (s • m) s = f m
  证明: by
  delta mk'
  rw [LocalizedModule.mk_cancel]; rw [← mk'_one S f]; rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [OneMemClass.coe_one]; rw [mk'_one]; rw [one_smul]

@[simp]
-/
theorem mk'_cancel (m : M) (s : S) : mk' f (s • m) s = f m := by
  delta mk'
  rw [LocalizedModule.mk_cancel]; rw [← mk'_one S f]; rw [fromLocalizedModule_mk]; rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]; rw [OneMemClass.coe_one]; rw [mk'_one]; rw [one_smul]

@[simp]
/--
theorem `mk'_cancel'` / 定理 `mk'_cancel'`

English:
theorem mk'_cancel'
  given: (m : M) (s : S)
  statement: s • mk' f m s = f m
  proof: by
  rw [Submonoid.smul_def]; rw [← mk'_smul]; rw [← Submonoid.smul_def]; rw [mk'_cancel]

@[simp]

中文:
定理 mk'_cancel'
  条件: (m : M) (s : S)
  结论: s • mk' f m s = f m
  证明: by
  rw [Submonoid.smul_def]; rw [← mk'_smul]; rw [← Submonoid.smul_def]; rw [mk'_cancel]

@[simp]
-/
theorem mk'_cancel' (m : M) (s : S) : s • mk' f m s = f m := by
  rw [Submonoid.smul_def]; rw [← mk'_smul]; rw [← Submonoid.smul_def]; rw [mk'_cancel]

@[simp]
/--
theorem `mk'_cancel_left` / 定理 `mk'_cancel_left`

English:
theorem mk'_cancel_left
  given: (m : M) (s₁ s₂ : S)
  statement: mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂
  proof: by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_left]

@[simp]

中文:
定理 mk'_cancel_left
  条件: (m : M) (s₁ s₂ : S)
  结论: mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂
  证明: by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_left]

@[simp]
-/
theorem mk'_cancel_left (m : M) (s₁ s₂ : S) : mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_left]

@[simp]
/--
theorem `mk'_cancel_right` / 定理 `mk'_cancel_right`

English:
theorem mk'_cancel_right
  given: (m : M) (s₁ s₂ : S)
  statement: mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁
  proof: by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_right]

中文:
定理 mk'_cancel_right
  条件: (m : M) (s₁ s₂ : S)
  结论: mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁
  证明: by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_right]
-/
theorem mk'_cancel_right (m : M) (s₁ s₂ : S) : mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_right]

/--
theorem `mk'_add` / 定理 `mk'_add`

English:
theorem mk'_add
  given: (m₁ m₂ : M) (s : S)
  statement: mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s
  proof: by
  rw [mk'_add_mk']; rw [← smul_add]; rw [mk'_cancel_left]

中文:
定理 mk'_add
  条件: (m₁ m₂ : M) (s : S)
  结论: mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s
  证明: by
  rw [mk'_add_mk']; rw [← smul_add]; rw [mk'_cancel_left]
-/
theorem mk'_add (m₁ m₂ : M) (s : S) : mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s := by
  rw [mk'_add_mk']; rw [← smul_add]; rw [mk'_cancel_left]

/--
theorem `mk'_eq_mk'_iff` / 定理 `mk'_eq_mk'_iff`

English:
theorem mk'_eq_mk'_iff
  given: (m₁ m₂ : M) (s₁ s₂ : S)
  proof: by
  delta mk'
  rw [(fromLocalizedModule.inj S f).eq_iff]; rw [LocalizedModule.mk_eq]
  simp_rw [eq_comm]

中文:
定理 mk'_eq_mk'_iff
  条件: (m₁ m₂ : M) (s₁ s₂ : S)
  证明: by
  delta mk'
  rw [(fromLocalizedModule.inj S f).eq_iff]; rw [LocalizedModule.mk_eq]
  simp_rw [eq_comm]
-/
theorem mk'_eq_mk'_iff (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ = mk' f m₂ s₂ ↔ exists s : S, s • s₁ • m₂ = s • s₂ • m₁ := by
  delta mk'
  rw [(fromLocalizedModule.inj S f).eq_iff]; rw [LocalizedModule.mk_eq]
  simp_rw [eq_comm]

/--
theorem `mk'_neg` / 定理 `mk'_neg`

English:
theorem mk'_neg
  statement: {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
  proof: by
  delta mk'
  rw [LocalizedModule.mk_neg]; rw [map_neg]

中文:
定理 mk'_neg
  结论: {M M' : 类型} [加法交换群 M] [SubtractionComm幺半群 M'] [模 R M]
  证明: by
  delta mk'
  rw [LocalizedModule.mk_neg]; rw [map_neg]
-/
theorem mk'_neg {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M ->ₗ[R] M') [IsLocalizedModule S f] (m : M) (s : S) :
    mk' f (-m) s = -mk' f m s := by
  delta mk'
  rw [LocalizedModule.mk_neg]; rw [map_neg]

/--
theorem `mk'_sub` / 定理 `mk'_sub`

English:
theorem mk'_sub
  statement: {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [mk'_add]; rw [mk'_neg]

中文:
定理 mk'_sub
  结论: {M M' : 类型} [加法交换群 M] [SubtractionComm幺半群 M'] [模 R M]
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [mk'_add]; rw [mk'_neg]
-/
theorem mk'_sub {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M ->ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s : S) :
    mk' f (m₁ - m₂) s = mk' f m₁ s - mk' f m₂ s := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [mk'_add]; rw [mk'_neg]

/--
theorem `mk'_sub_mk'` / 定理 `mk'_sub_mk'`

English:
theorem mk'_sub_mk'
  statement: {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
  proof: by
  rw [sub_eq_add_neg]; rw [← mk'_neg]; rw [mk'_add_mk']; rw [smul_neg]; rw [← sub_eq_add_neg]

中文:
定理 mk'_sub_mk'
  结论: {M M' : 类型} [加法交换群 M] [SubtractionComm幺半群 M'] [模 R M]
  证明: by
  rw [sub_eq_add_neg]; rw [← mk'_neg]; rw [mk'_add_mk']; rw [smul_neg]; rw [← sub_eq_add_neg]
-/
theorem mk'_sub_mk' {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M ->ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ - mk' f m₂ s₂ = mk' f (s₂ • m₁ - s₁ • m₂) (s₁ * s₂) := by
  rw [sub_eq_add_neg]; rw [← mk'_neg]; rw [mk'_add_mk']; rw [smul_neg]; rw [← sub_eq_add_neg]

/--
theorem `mk'_mul_mk'_of_map_mul` / 定理 `mk'_mul_mk'_of_map_mul`

English:
theorem mk'_mul_mk'_of_map_mul
  statement: {M M' : Type*} [NonUnitalNonAssocSemiring M] [Semiring M']
  proof: by
  symm
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  rw [smul_smul_smul_comm]; rw [← mk'_smul]; rw [← mk'_smul]
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]

中文:
定理 mk'_mul_mk'_of_map_mul
  结论: {M M' : 类型} [非幺非结合半环 M] [半环 M']
  证明: by
  symm
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  rw [smul_smul_smul_comm]; rw [← mk'_smul]; rw [← mk'_smul]
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]
-/
theorem mk'_mul_mk'_of_map_mul {M M' : Type*} [NonUnitalNonAssocSemiring M] [Semiring M']
    [Module R M] [Algebra R M'] (f : M ->ₗ[R] M') (hf : forall m₁ m₂, f (m₁ * m₂) = f m₁ * f m₂)
    [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ * mk' f m₂ s₂ = mk' f (m₁ * m₂) (s₁ * s₂) := by
  symm
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  rw [smul_smul_smul_comm]; rw [← mk'_smul]; rw [← mk'_smul]
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]

/--
theorem `mk'_mul_mk'` / 定理 `mk'_mul_mk'`

English:
theorem mk'_mul_mk'
  statement: {M M' : Type*} [Semiring M] [Semiring M'] [Algebra R M] [Algebra R M']
  proof: mk'_mul_mk'_of_map_mul f.toLinearMap (map_mul f) m₁ m₂ s₁ s₂

中文:
定理 mk'_mul_mk'
  结论: {M M' : 类型} [半环 M] [半环 M'] [代数 R M] [代数 R M']
  证明: mk'_mul_mk'_of_map_mul f.toLinearMap (map_mul f) m₁ m₂ s₁ s₂
-/
theorem mk'_mul_mk' {M M' : Type*} [Semiring M] [Semiring M'] [Algebra R M] [Algebra R M']
    (f : M ->ₐ[R] M') [IsLocalizedModule S f.toLinearMap] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f.toLinearMap m₁ s₁ * mk' f.toLinearMap m₂ s₂ = mk' f.toLinearMap (m₁ * m₂) (s₁ * s₂) :=
  mk'_mul_mk'_of_map_mul f.toLinearMap (map_mul f) m₁ m₂ s₁ s₂

variable {f}

/--
theorem `mk'_eq_iff` / 定理 `mk'_eq_iff`

English:
theorem mk'_eq_iff
  given: {m : M} {s : S} {m' : M'}
  statement: mk' f m s = m' ↔ f m = s • m'
  proof: by
  rw [← smul_inj f s]; rw [Submonoid.smul_def]; rw [← mk'_smul]; rw [← Submonoid.smul_def]; rw [mk'_cancel]

@[simp]

中文:
定理 mk'_eq_iff
  条件: {m : M} {s : S} {m' : M'}
  结论: mk' f m s = m' ↔ f m = s • m'
  证明: by
  rw [← smul_inj f s]; rw [Submonoid.smul_def]; rw [← mk'_smul]; rw [← Submonoid.smul_def]; rw [mk'_cancel]

@[simp]
-/
theorem mk'_eq_iff {m : M} {s : S} {m' : M'} : mk' f m s = m' ↔ f m = s • m' := by
  rw [← smul_inj f s]; rw [Submonoid.smul_def]; rw [← mk'_smul]; rw [← Submonoid.smul_def]; rw [mk'_cancel]

@[simp]
/--
theorem `mk'_eq_zero` / 定理 `mk'_eq_zero`

English:
theorem mk'_eq_zero
  given: {m : M} (s : S)
  statement: mk' f m s = 0 ↔ f m = 0
  proof: by rw [mk'_eq_iff, smul_zero]

中文:
定理 mk'_eq_zero
  条件: {m : M} (s : S)
  结论: mk' f m s = 0 ↔ f m = 0
  证明: by rw [mk'_eq_iff, smul_zero]
-/
theorem mk'_eq_zero {m : M} (s : S) : mk' f m s = 0 ↔ f m = 0 := by rw [mk'_eq_iff, smul_zero]

variable (f)

/--
theorem `mk'_eq_zero'` / 定理 `mk'_eq_zero'`

English:
theorem mk'_eq_zero'
  given: {m : M} (s : S)
  statement: mk' f m s = 0 ↔ exists s' : S, s' • m = 0
  proof: by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]

中文:
定理 mk'_eq_zero'
  条件: {m : M} (s : S)
  结论: mk' f m s = 0 ↔ 存在 s' : S, s' • m = 0
  证明: by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]
-/
theorem mk'_eq_zero' {m : M} (s : S) : mk' f m s = 0 ↔ exists s' : S, s' • m = 0 := by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]

/--
theorem `mk_eq_mk'` / 定理 `mk_eq_mk'`

English:
theorem mk_eq_mk'
  given: (s : S) (m : M)
  proof: by
  rw [eq_comm]; rw [mk'_eq_iff]; rw [Submonoid.smul_def]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel]; rw [LocalizedModule.mkLinearMap_apply]

中文:
定理 mk_eq_mk'
  条件: (s : S) (m : M)
  证明: by
  rw [eq_comm]; rw [mk'_eq_iff]; rw [Submonoid.smul_def]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel]; rw [LocalizedModule.mkLinearMap_apply]

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_cancel, LocalizedModule.smul, Submonoid, Submonoid.smul_def, _eq_iff, eq_comm, mkLinearMap_apply, mk_cancel, smul_def
-/
theorem mk_eq_mk' (s : S) (m : M) :
    LocalizedModule.mk m s = mk' (LocalizedModule.mkLinearMap S M) m s := by
  rw [eq_comm]; rw [mk'_eq_iff]; rw [Submonoid.smul_def]; rw [LocalizedModule.smul'_mk]; rw [← Submonoid.smul_def]; rw [LocalizedModule.mk_cancel]; rw [LocalizedModule.mkLinearMap_apply]

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/--
lemma `mk'_smul_mk'` / 引理 `mk'_smul_mk'`

English:
lemma mk'_smul_mk'
  given: (x : R) (m : M) (s t : S)
  proof: by
  apply smul_injective f (s * t)
  conv_lhs => simp only [smul_assoc, mul_smul, smul_comm t]
  simp only [mk'_cancel', map_smul, Submonoid.smul_def s]
  rw [← smul_assoc]; rw [IsLocalization.smul_mk'_self]; rw [algebraMap_smul]

中文:
引理 mk'_smul_mk'
  条件: (x : R) (m : M) (s t : S)
  证明: by
  apply smul_injective f (s * t)
  conv_lhs => simp only [smul_assoc, mul_smul, smul_comm t]
  simp only [mk'_cancel', map_smul, Submonoid.smul_def s]
  rw [← smul_assoc]; rw [IsLocalization.smul_mk'_self]; rw [algebraMap_smul]
-/
lemma mk'_smul_mk' (x : R) (m : M) (s t : S) :
    IsLocalization.mk' A x s • mk' f m t = mk' f (x • m) (s * t) := by
  apply smul_injective f (s * t)
  conv_lhs => simp only [smul_assoc, mul_smul, smul_comm t]
  simp only [mk'_cancel', map_smul, Submonoid.smul_def s]
  rw [← smul_assoc]; rw [IsLocalization.smul_mk'_self]; rw [algebraMap_smul]

variable (S)

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {m : M}
  statement: f m = 0 ↔ exists s' : S, s' • m = 0
  proof: (mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)

中文:
定理 eq_zero_iff
  条件: {m : M}
  结论: f m = 0 ↔ 存在 s' : S, s' • m = 0
  证明: (mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)

Depends on / 依赖: _eq_zero, symm.trans
-/
theorem eq_zero_iff {m : M} : f m = 0 ↔ exists s' : S, s' • m = 0 :=
  (mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)

/--
theorem `mk'_surjective` / 定理 `mk'_surjective`

English:
theorem mk'_surjective
  statement: Function.Surjective (Function.uncurry <| mk' f : M × S -> M')
  proof: by
  intro x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩

中文:
定理 mk'_surjective
  结论: 函数.满射 (函数.uncurry <| mk' f : M × S -> M')
  证明: by
  intro x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩
-/
theorem mk'_surjective : Function.Surjective (Function.uncurry <| mk' f : M × S -> M') := by
  intro x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩

section liftOfLE

variable {M₁ M₂} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (S₁ S₂ : Submonoid R) (h : S₁ <= S₂) (f₁ : M ->ₗ[R] M₁) (f₂ : M ->ₗ[R] M₂)
variable [IsLocalizedModule S₁ f₁] [IsLocalizedModule S₂ f₂]

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
/--
Definition of `liftOfLE` / `liftOfLE` 的定义

English:
definition liftOfLE
  signature: : M₁ ->ₗ[R] M₂
  body: lift S₁ f₁ f₂ fun x => map_units f₂ ⟨x.1, h x.2⟩

中文:
定义 liftOfLE
  签名: : M₁ ->ₗ[R] M₂
  定义体: lift S₁ f₁ f₂ fun x => map_units f₂ ⟨x.1, h x.2⟩

Depends on / 依赖: map_units
-/
def liftOfLE : M₁ ->ₗ[R] M₂ :=
  lift S₁ f₁ f₂ fun x => map_units f₂ ⟨x.1, h x.2⟩

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
/--
Definition of `_root_.LocalizedModule.liftOfLE` / `_root_.LocalizedModule.liftOfLE` 的定义

English:
abbreviation _root_.LocalizedModule.liftOfLE
  signature: : LocalizedModule S₁ M ->ₗ[R] LocalizedModule S₂ M
  body: IsLocalizedModule.liftOfLE S₁ S₂ h
    (LocalizedModule.mkLinearMap S₁ M) (LocalizedModule.mkLinearMap S₂ M)

中文:
缩写 _root_.LocalizedModule.liftOfLE
  签名: : LocalizedModule S₁ M ->ₗ[R] LocalizedModule S₂ M
  定义体: IsLocalizedModule.liftOfLE S₁ S₂ h
    (LocalizedModule.mkLinearMap S₁ M) (LocalizedModule.mkLinearMap S₂ M)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.liftOfLE, LocalizedModule, LocalizedModule.mkLinearMap, liftOfLE, mkLinearMap
-/
abbrev _root_.LocalizedModule.liftOfLE : LocalizedModule S₁ M ->ₗ[R] LocalizedModule S₂ M :=
  IsLocalizedModule.liftOfLE S₁ S₂ h
    (LocalizedModule.mkLinearMap S₁ M) (LocalizedModule.mkLinearMap S₂ M)

/--
lemma `liftOfLE_comp` / 引理 `liftOfLE_comp`

English:
lemma liftOfLE_comp
  statement: (liftOfLE S₁ S₂ h f₁ f₂).comp f₁ = f₂
  proof: lift_comp ..

中文:
引理 liftOfLE_comp
  结论: (liftOfLE S₁ S₂ h f₁ f₂).comp f₁ = f₂
  证明: lift_comp ..

Depends on / 依赖: lift_comp
-/
lemma liftOfLE_comp : (liftOfLE S₁ S₂ h f₁ f₂).comp f₁ = f₂ := lift_comp ..

/--
lemma `liftOfLE_apply` / 引理 `liftOfLE_apply`

English:
lemma liftOfLE_apply
  given: (x)
  statement: liftOfLE S₁ S₂ h f₁ f₂ (f₁ x) = f₂ x
  proof: lift_apply ..

中文:
引理 liftOfLE_apply
  条件: (x)
  结论: liftOfLE S₁ S₂ h f₁ f₂ (f₁ x) = f₂ x
  证明: lift_apply ..
-/
@[simp] lemma liftOfLE_apply (x) : liftOfLE S₁ S₂ h f₁ f₂ (f₁ x) = f₂ x := lift_apply ..

set_option backward.isDefEq.respectTransparency false in
/-- The image of `m/s` under `liftOfLE` is `m/s`. -/
@[simp]
/--
lemma `liftOfLE_mk'` / 引理 `liftOfLE_mk'`

English:
lemma liftOfLE_mk'
  given: (m : M) (s : S₁)
  proof: by
  apply ((Module.End.isUnit_iff _).mp (map_units f₂ ⟨s, h s.2⟩)).1
  simp only [Module.algebraMap_end_apply, ← map_smul, ← Submonoid.smul_def, mk'_cancel']
  rw [liftOfLE]; rw [lift_apply]
  exact (mk'_cancel' (S := S₂) f₂ m ⟨s.1, h s.2⟩).symm

中文:
引理 liftOfLE_mk'
  条件: (m : M) (s : S₁)
  证明: by
  apply ((Module.End.isUnit_iff _).mp (map_units f₂ ⟨s, h s.2⟩)).1
  simp only [Module.algebraMap_end_apply, ← map_smul, ← Submonoid.smul_def, mk'_cancel']
  rw [liftOfLE]; rw [lift_apply]
  exact (mk'_cancel' (S := S₂) f₂ m ⟨s.1, h s.2⟩).symm

Depends on / 依赖: Module, Module.End.isUnit_iff, Module.algebraMap_end_apply, Submonoid, Submonoid.smul_def, _cancel, algebraMap_end_apply, isUnit_iff, liftOfLE, lift_apply, map_smul, map_units, smul_def
-/
lemma liftOfLE_mk' (m : M) (s : S₁) :
    liftOfLE S₁ S₂ h f₁ f₂ (mk' f₁ m s) = mk' f₂ m ⟨s.1, h s.2⟩ := by
  apply ((Module.End.isUnit_iff _).mp (map_units f₂ ⟨s, h s.2⟩)).1
  simp only [Module.algebraMap_end_apply, ← map_smul, ← Submonoid.smul_def, mk'_cancel']
  rw [liftOfLE]; rw [lift_apply]
  exact (mk'_cancel' (S := S₂) f₂ m ⟨s.1, h s.2⟩).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalizedModule S₂ (liftOfLE S₁ S₂ h f₁ f₂)
  body: map_units f₂
  surj y := by
    obtain ⟨⟨y', s⟩, e⟩ := IsLocalizedModule.surj S₂ f₂ y
    exact ⟨⟨f₁ y', s⟩, by simpa⟩
  exists_of_eq := by
    intro x₁ x₂ e
    obtain ⟨x₁, s₁, rfl⟩ := mk'_surjective S₁ f₁ x₁
    obtain ⟨x₂, s₂, rfl⟩ := mk'_surjective S₁ f₁ x₂
    simp only [Function.uncurry, liftOfLE_mk', mk'_eq_mk'_iff,
      Submonoid.smul_def, ← mk'_smul] at e ⊢
    obtain ⟨c, e⟩ := e
    exact ⟨c, 1, by simpa [← smul_comm c.1]⟩

中文:
实例 :
  签名: 是Localized模 S₂ (liftOfLE S₁ S₂ h f₁ f₂)
  定义体: map_units f₂
  surj y := by
    obtain ⟨⟨y', s⟩, e⟩ := IsLocalizedModule.surj S₂ f₂ y
    exact ⟨⟨f₁ y', s⟩, by simpa⟩
  exists_of_eq := by
    intro x₁ x₂ e
    obtain ⟨x₁, s₁, rfl⟩ := mk'_surjective S₁ f₁ x₁
    obtain ⟨x₂, s₂, rfl⟩ := mk'_surjective S₁ f₁ x₂
    simp only [Function.uncurry, liftOfLE_mk', mk'_eq_mk'_iff,
      Submonoid.smul_def, ← mk'_smul] at e ⊢
    obtain ⟨c, e⟩ := e
    exact ⟨c, 1, by simpa [← smul_comm c.1]⟩

Depends on / 依赖: map_units
-/
instance : IsLocalizedModule S₂ (liftOfLE S₁ S₂ h f₁ f₂) where
  map_units := map_units f₂
  surj y := by
    obtain ⟨⟨y', s⟩, e⟩ := IsLocalizedModule.surj S₂ f₂ y
    exact ⟨⟨f₁ y', s⟩, by simpa⟩
  exists_of_eq := by
    intro x₁ x₂ e
    obtain ⟨x₁, s₁, rfl⟩ := mk'_surjective S₁ f₁ x₁
    obtain ⟨x₂, s₂, rfl⟩ := mk'_surjective S₁ f₁ x₂
    simp only [Function.uncurry, liftOfLE_mk', mk'_eq_mk'_iff,
      Submonoid.smul_def, ← mk'_smul] at e ⊢
    obtain ⟨c, e⟩ := e
    exact ⟨c, 1, by simpa [← smul_comm c.1]⟩

end liftOfLE

include S in
/--
lemma `injective_of_map_eq` / 引理 `injective_of_map_eq`

English:
lemma injective_of_map_eq
  statement: {N : Type*} [AddCommMonoid N] [Module R N]
  proof: by
  intro a b hab
  obtain ⟨⟨x, m⟩, (hxm : m • a = f x)⟩ := IsLocalizedModule.surj S f a
  obtain ⟨⟨y, n⟩, (hym : n • b = f y)⟩ := IsLocalizedModule.surj S f b
  suffices h : g (f (n.val • x)) = g (f (m.val • y)) by
    apply H at h
    rw [map_smul]; rw [map_smul] at h
    rwa [← IsLocalizedModule.smul_inj f (n * m), mul_smul, mul_comm, mul_smul, hxm, hym]
  simp [← hxm, ← hym, hab, ← S.smul_def, ← mul_smul, mul_comm, ← mul_smul]

中文:
引理 injective_of_map_eq
  结论: {N : 类型} [加法交换幺半群 N] [模 R N]
  证明: by
  intro a b hab
  obtain ⟨⟨x, m⟩, (hxm : m • a = f x)⟩ := IsLocalizedModule.surj S f a
  obtain ⟨⟨y, n⟩, (hym : n • b = f y)⟩ := IsLocalizedModule.surj S f b
  suffices h : g (f (n.val • x)) = g (f (m.val • y)) by
    apply H at h
    rw [map_smul]; rw [map_smul] at h
    rwa [← IsLocalizedModule.smul_inj f (n * m), mul_smul, mul_comm, mul_smul, hxm, hym]
  simp [← hxm, ← hym, hab, ← S.smul_def, ← mul_smul, mul_comm, ← mul_smul]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.smul_inj, IsLocalizedModule.surj, S.smul_def, m.val, map_smul, mul_comm, mul_smul, n.val, smul_def, smul_inj
-/
lemma injective_of_map_eq {N : Type*} [AddCommMonoid N] [Module R N]
    {g : M' ->ₗ[R] N} (H : forall {x y}, g (f x) = g (f y) -> f x = f y) :
    Function.Injective g := by
  intro a b hab
  obtain ⟨⟨x, m⟩, (hxm : m • a = f x)⟩ := IsLocalizedModule.surj S f a
  obtain ⟨⟨y, n⟩, (hym : n • b = f y)⟩ := IsLocalizedModule.surj S f b
  suffices h : g (f (n.val • x)) = g (f (m.val • y)) by
    apply H at h
    rw [map_smul]; rw [map_smul] at h
    rwa [← IsLocalizedModule.smul_inj f (n * m), mul_smul, mul_comm, mul_smul, hxm, hym]
  simp [← hxm, ← hym, hab, ← S.smul_def, ← mul_smul, mul_comm, ← mul_smul]

/--
lemma `injective_of_map_zero` / 引理 `injective_of_map_zero`

English:
lemma injective_of_map_zero
  statement: {M M' N : Type*} [AddCommGroup M] [AddCommGroup M']
  proof: by
  refine IsLocalizedModule.injective_of_map_eq S f (fun hxy => ?_)
  rw [← sub_eq_zero]; rw [← map_sub]
  apply H
  simpa [sub_eq_zero]

中文:
引理 injective_of_map_zero
  结论: {M M' N : 类型} [加法交换群 M] [加法交换群 M']
  证明: by
  refine IsLocalizedModule.injective_of_map_eq S f (fun hxy => ?_)
  rw [← sub_eq_zero]; rw [← map_sub]
  apply H
  simpa [sub_eq_zero]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.injective_of_map_eq, injective_of_map_eq, map_sub, sub_eq_zero
-/
lemma injective_of_map_zero {M M' N : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] (f : M ->ₗ[R] M') [IsLocalizedModule S f]
    [AddCommGroup N] [Module R N] {g : M' ->ₗ[R] N} (H : forall m, g (f m) = 0 -> f m = 0) :
    Function.Injective g := by
  refine IsLocalizedModule.injective_of_map_eq S f (fun hxy => ?_)
  rw [← sub_eq_zero]; rw [← map_sub]
  apply H
  simpa [sub_eq_zero]

variable {N N'} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
variable (g : N ->ₗ[R] N') [IsLocalizedModule S g]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[R] Nₛ`. -/
noncomputable
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (M ->ₗ[R] N) ->ₗ[R] (M' ->ₗ[R] N') where
  body: lift S f (g ∘ₗ h) (IsLocalizedModule.map_units g)
  map_add' h₁ h₂ := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r h := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

中文:
定义 map
  签名: : (M ->ₗ[R] N) ->ₗ[R] (M' ->ₗ[R] N') where
  定义体: lift S f (g ∘ₗ h) (IsLocalizedModule.map_units g)
  map_add' h₁ h₂ := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r h := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.map_units, map_units
-/
def map : (M ->ₗ[R] N) ->ₗ[R] (M' ->ₗ[R] N') where
  toFun h := lift S f (g ∘ₗ h) (IsLocalizedModule.map_units g)
  map_add' h₁ h₂ := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r h := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (h : M ->ₗ[R] N)
  statement: (map S f g h) ∘ₗ f = g ∘ₗ h
  proof: lift_comp S f (g ∘ₗ h) (IsLocalizedModule.map_units g)

@[simp]

中文:
引理 map_comp
  条件: (h : M ->ₗ[R] N)
  结论: (map S f g h) ∘ₗ f = g ∘ₗ h
  证明: lift_comp S f (g ∘ₗ h) (IsLocalizedModule.map_units g)

@[simp]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.map_units, lift_comp, map_units
-/
lemma map_comp (h : M ->ₗ[R] N) : (map S f g h) ∘ₗ f = g ∘ₗ h :=
  lift_comp S f (g ∘ₗ h) (IsLocalizedModule.map_units g)

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (h : M ->ₗ[R] N) (x)
  statement: map S f g h (f x) = g (h x)
  proof: lift_apply S f (g ∘ₗ h) (IsLocalizedModule.map_units g) x

@[simp]

中文:
引理 map_apply
  条件: (h : M ->ₗ[R] N) (x)
  结论: map S f g h (f x) = g (h x)
  证明: lift_apply S f (g ∘ₗ h) (IsLocalizedModule.map_units g) x

@[simp]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.map_units, lift_apply, map_units
-/
lemma map_apply (h : M ->ₗ[R] N) (x) : map S f g h (f x) = g (h x) :=
  lift_apply S f (g ∘ₗ h) (IsLocalizedModule.map_units g) x

@[simp]
/--
lemma `map_mk'` / 引理 `map_mk'`

English:
lemma map_mk'
  given: (h : M ->ₗ[R] N) (x) (s : S)
  proof: by
  simp only [map, lift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [iso_symm_apply' S f (mk' f x s) x s (mk'_cancel' f x s)]; rw [LocalizedModule.lift_mk]
  rfl

@[simp]

中文:
引理 map_mk'
  条件: (h : M ->ₗ[R] N) (x) (s : S)
  证明: by
  simp only [map, lift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [iso_symm_apply' S f (mk' f x s) x s (mk'_cancel' f x s)]; rw [LocalizedModule.lift_mk]
  rfl

@[simp]

Depends on / 依赖: AddHom, AddHom.coe_mk, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.coe_mk, LocalizedModule, LocalizedModule.lift_mk, _cancel, coe_coe, coe_comp, coe_mk, comp_apply, iso_symm_apply, lift_mk
-/
lemma map_mk' (h : M ->ₗ[R] N) (x) (s : S) :
    map S f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s) := by
  simp only [map, lift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [iso_symm_apply' S f (mk' f x s) x s (mk'_cancel' f x s)]; rw [LocalizedModule.lift_mk]
  rfl

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map S f f .id = .id
  proof: by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  simp

@[simp]

中文:
引理 map_id
  结论: map S f f .id = .id
  证明: by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  simp

@[simp]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, _surjective
-/
lemma map_id : map S f f .id = .id := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  simp

@[simp]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (h : M ->ₗ[R] N) (h_inj : Function.Injective h)
  proof: by
  intro x y
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
  simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_mk'_iff, Subtype.exists,
    Submonoid.mk_smul, exists_prop, forall_exists_index, and_imp]
  intro c hc e
  exact ⟨c, hc, h_inj (by simpa)⟩

@[simp]

中文:
定理 map_injective
  条件: (h : M ->ₗ[R] N) (h_inj : 函数.单射 h)
  证明: by
  intro x y
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
  simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_mk'_iff, Subtype.exists,
    Submonoid.mk_smul, exists_prop, forall_exists_index, and_imp]
  intro c hc e
  exact ⟨c, hc, h_inj (by simpa)⟩

@[simp]

Depends on / 依赖: Function, Function.uncurry_apply_pair, IsLocalizedModule, IsLocalizedModule.mk, Submonoid, Submonoid.mk_smul, Subtype, Subtype.exists, _eq_mk, _iff, _surjective, and_imp, exists_prop, forall_exists_index, h_inj, map_mk, mk_smul, uncurry_apply_pair
-/
theorem map_injective (h : M ->ₗ[R] N) (h_inj : Function.Injective h) :
    Function.Injective (map S f g h) := by
  intro x y
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
  simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_mk'_iff, Subtype.exists,
    Submonoid.mk_smul, exists_prop, forall_exists_index, and_imp]
  intro c hc e
  exact ⟨c, hc, h_inj (by simpa)⟩

@[simp]
/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (h : M ->ₗ[R] N) (h_surj : Function.Surjective h)
  proof: by
  intro x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  obtain ⟨x, rfl⟩ := h_surj x
  exact ⟨mk' f x s, by simp⟩

中文:
定理 map_surjective
  条件: (h : M ->ₗ[R] N) (h_surj : 函数.满射 h)
  证明: by
  intro x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  obtain ⟨x, rfl⟩ := h_surj x
  exact ⟨mk' f x s, by simp⟩

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, _surjective, h_surj
-/
theorem map_surjective (h : M ->ₗ[R] N) (h_surj : Function.Surjective h) :
    Function.Surjective (map S f g h) := by
  intro x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  obtain ⟨x, rfl⟩ := h_surj x
  exact ⟨mk' f x s, by simp⟩

open LocalizedModule LinearEquiv LinearMap Submonoid

variable (M)

/--
lemma `iso_localizedModule_eq_refl` / 引理 `iso_localizedModule_eq_refl`

English:
lemma iso_localizedModule_eq_refl
  statement: iso S (mkLinearMap S M) = refl R (LocalizedModule S M)
  proof: by
  let f := mkLinearMap S M
  obtain ⟨e, _, univ⟩ := is_universal S f f (map_units f)
  rw [← toLinearMap_inj]; rw [univ (iso S f) ((eq_toLinearMap_symm_comp f f).1 (iso_symm_comp S f).symm)]
exact Eq.symm univ (refl R (LocalizedModule S M)) (by simp)

中文:
引理 iso_localizedModule_eq_refl
  结论: iso S (mkLinearMap S M) = refl R (LocalizedModule S M)
  证明: by
  let f := mkLinearMap S M
  obtain ⟨e, _, univ⟩ := is_universal S f f (map_units f)
  rw [← toLinearMap_inj]; rw [univ (iso S f) ((eq_toLinearMap_symm_comp f f).1 (iso_symm_comp S f).symm)]
exact Eq.symm univ (refl R (LocalizedModule S M)) (by simp)

Depends on / 依赖: Eq.symm, LocalizedModule, eq_toLinearMap_symm_comp, is_universal, iso_symm_comp, map_units, mkLinearMap, toLinearMap_inj
-/
lemma iso_localizedModule_eq_refl : iso S (mkLinearMap S M) = refl R (LocalizedModule S M) := by
  let f := mkLinearMap S M
  obtain ⟨e, _, univ⟩ := is_universal S f f (map_units f)
  rw [← toLinearMap_inj]; rw [univ (iso S f) ((eq_toLinearMap_symm_comp f f).1 (iso_symm_comp S f).symm)]
exact Eq.symm univ (refl R (LocalizedModule S M)) (by simp)

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ ->ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ ->ₗ[R] M₁') [IsLocalizedModule S f₁]

/--
lemma `map_LocalizedModules` / 引理 `map_LocalizedModules`

English:
lemma map_LocalizedModules
  given: (g : M₀ ->ₗ[R] M₁) (m : M₀) (s : S)
  proof: by
  have := (iso_apply_mk S (mkLinearMap S M₁) (g m) s).symm
  rw [iso_localizedModule_eq_refl]; rw [refl_apply] at this
  simpa [map, lift, iso_localizedModule_eq_refl S M₀]

中文:
引理 map_LocalizedModules
  条件: (g : M₀ ->ₗ[R] M₁) (m : M₀) (s : S)
  证明: by
  have := (iso_apply_mk S (mkLinearMap S M₁) (g m) s).symm
  rw [iso_localizedModule_eq_refl]; rw [refl_apply] at this
  simpa [map, lift, iso_localizedModule_eq_refl S M₀]

Depends on / 依赖: iso_apply_mk, iso_localizedModule_eq_refl, mkLinearMap, refl_apply
-/
lemma map_LocalizedModules (g : M₀ ->ₗ[R] M₁) (m : M₀) (s : S) :
    ((map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g)
    (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s := by
  have := (iso_apply_mk S (mkLinearMap S M₁) (g m) s).symm
  rw [iso_localizedModule_eq_refl]; rw [refl_apply] at this
  simpa [map, lift, iso_localizedModule_eq_refl S M₀]

/--
lemma `map_iso_commute` / 引理 `map_iso_commute`

English:
lemma map_iso_commute
  given: (g : M₀ ->ₗ[R] M₁)
  statement: (map S f₀ f₁) g ∘ₗ (iso S f₀) =
  proof: by
  ext x
  induction x using induction_on with | _ m s
  refine ((Module.End.isUnit_iff _).1 (map_units f₁ s)).1 ?_
  rw [Module.algebraMap_end_apply]; rw [Module.algebraMap_end_apply]; rw [← CompatibleSMul.map_smul]; rw [← CompatibleSMul.map_smul]; rw [smul'_mk]; rw [← mk_smul _ s.2]; rw [mk_cancel]
  simp [map, lift, iso_localizedModule_eq_refl, lift_mk]

中文:
引理 map_iso_commute
  条件: (g : M₀ ->ₗ[R] M₁)
  结论: (map S f₀ f₁) g ∘ₗ (iso S f₀) =
  证明: by
  ext x
  induction x using induction_on with | _ m s
  refine ((Module.End.isUnit_iff _).1 (map_units f₁ s)).1 ?_
  rw [Module.algebraMap_end_apply]; rw [Module.algebraMap_end_apply]; rw [← CompatibleSMul.map_smul]; rw [← CompatibleSMul.map_smul]; rw [smul'_mk]; rw [← mk_smul _ s.2]; rw [mk_cancel]
  simp [map, lift, iso_localizedModule_eq_refl, lift_mk]

Depends on / 依赖: CompatibleSMul, CompatibleSMul.map_smul, Module, Module.End.isUnit_iff, Module.algebraMap_end_apply, algebraMap_end_apply, induction_on, isUnit_iff, iso_localizedModule_eq_refl, lift_mk, map_smul, map_units, mk_cancel, mk_smul
-/
lemma map_iso_commute (g : M₀ ->ₗ[R] M₁) : (map S f₀ f₁) g ∘ₗ (iso S f₀) =
    (iso S f₁) ∘ₗ (map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g := by
  ext x
  induction x using induction_on with | _ m s
  refine ((Module.End.isUnit_iff _).1 (map_units f₁ s)).1 ?_
  rw [Module.algebraMap_end_apply]; rw [Module.algebraMap_end_apply]; rw [← CompatibleSMul.map_smul]; rw [← CompatibleSMul.map_smul]; rw [smul'_mk]; rw [← mk_smul _ s.2]; rw [mk_cancel]
  simp [map, lift, iso_localizedModule_eq_refl, lift_mk]

end IsLocalizedModule

namespace IsLocalizedModule

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ ->ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ ->ₗ[R] M₁') [IsLocalizedModule S f₁]
variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']
variable (f₂ : M₂ ->ₗ[R] M₂') [IsLocalizedModule S f₂]

/--
theorem `map_comp'` / 定理 `map_comp'`

English:
theorem map_comp'
  given: (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂)
  proof: by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f₀ x
  simp

中文:
定理 map_comp'
  条件: (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂)
  证明: by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f₀ x
  simp

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, _surjective
-/
theorem map_comp' (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) :
    map S f₀ f₂ (h ∘ₗ g) = map S f₁ f₂ h ∘ₗ map S f₀ f₁ g := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f₀ x
  simp

section Algebra

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mkOfAlgebra` / 定理 `mkOfAlgebra`

English:
theorem mkOfAlgebra
  statement: {R S S' : Type*} [CommSemiring R] [Ring S] [Ring S'] [Algebra R S]
  proof: by
  replace h₃ := fun x =>
    Iff.intro (h₃ x) fun ⟨⟨m, hm⟩, e⟩ =>
(h₁ m hm).mul_left_cancel by
        rw [← Algebra.smul_def]
        simpa [Submonoid.smul_def] using f.congr_arg e
  constructor
  · intro x
    rw [Module.End.isUnit_iff]
    constructor
    · rintro a b (e : x • a = x • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact (h₁ x x.2).mul_left_cancel e
    · intro a
      refine ⟨((h₁ x x.2).unit⁻¹ :) * a, ?_⟩
      rw [Module.algebraMap_end_apply]; rw [Algebra.smul_def]; rw [← mul_assoc]; rw [IsUnit.mul_val_inv]; rw [one_mul]
  · exact h₂
  · intro x y
    dsimp only [AlgHom.toLinearMap_apply]
    rw [← sub_eq_zero]; rw [← map_sub]; rw [h₃]
    simp_rw [smul_sub, sub_eq_zero]
    exact id

中文:
定理 mkOfAlgebra
  结论: {R S S' : 类型} [交换半环 R] [环 S] [环 S'] [代数 R S]
  证明: by
  replace h₃ := fun x =>
    Iff.intro (h₃ x) fun ⟨⟨m, hm⟩, e⟩ =>
(h₁ m hm).mul_left_cancel by
        rw [← Algebra.smul_def]
        simpa [Submonoid.smul_def] using f.congr_arg e
  constructor
  · intro x
    rw [Module.End.isUnit_iff]
    constructor
    · rintro a b (e : x • a = x • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact (h₁ x x.2).mul_left_cancel e
    · intro a
      refine ⟨((h₁ x x.2).unit⁻¹ :) * a, ?_⟩
      rw [Module.algebraMap_end_apply]; rw [Algebra.smul_def]; rw [← mul_assoc]; rw [IsUnit.mul_val_inv]; rw [one_mul]
  · exact h₂
  · intro x y
    dsimp only [AlgHom.toLinearMap_apply]
    rw [← sub_eq_zero]; rw [← map_sub]; rw [h₃]
    simp_rw [smul_sub, sub_eq_zero]
    exact id

Depends on / 依赖: Algebra, Algebra.smul_def, Iff.intro, IsUnit, IsUnit.mul_val_inv, Module, Module.End.isUnit_iff, Module.algebraMap_end_apply, Submonoid, Submonoid.smul_def, algebraMap_end_apply, congr_arg, f.congr_arg, isUnit_iff, mul_assoc, mul_left_cancel, mul_val_inv, replace, simp_rw, smul_def
-/
theorem mkOfAlgebra {R S S' : Type*} [CommSemiring R] [Ring S] [Ring S'] [Algebra R S]
    [Algebra R S'] (M : Submonoid R) (f : S ->ₐ[R] S') (h₁ : forall x in M, IsUnit (algebraMap R S' x))
    (h₂ : forall y, exists x : S × M, x.2 • y = f x.1) (h₃ : forall x, f x = 0 -> exists m : M, m • x = 0) :
    IsLocalizedModule M f.toLinearMap := by
  replace h₃ := fun x =>
    Iff.intro (h₃ x) fun ⟨⟨m, hm⟩, e⟩ =>
(h₁ m hm).mul_left_cancel by
        rw [← Algebra.smul_def]
        simpa [Submonoid.smul_def] using f.congr_arg e
  constructor
  · intro x
    rw [Module.End.isUnit_iff]
    constructor
    · rintro a b (e : x • a = x • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact (h₁ x x.2).mul_left_cancel e
    · intro a
      refine ⟨((h₁ x x.2).unit⁻¹ :) * a, ?_⟩
      rw [Module.algebraMap_end_apply]; rw [Algebra.smul_def]; rw [← mul_assoc]; rw [IsUnit.mul_val_inv]; rw [one_mul]
  · exact h₂
  · intro x y
    dsimp only [AlgHom.toLinearMap_apply]
    rw [← sub_eq_zero]; rw [← map_sub]; rw [h₃]
    simp_rw [smul_sub, sub_eq_zero]
    exact id

end Algebra

variable {R A M M' : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [IsLocalization S A]

attribute [local instance] LocalizedModule.moduleOfIsLocalization in
/--
Definition of `module` / `module` 的定义

English:
definition module
  signature: (f : M ->ₗ[R] M') [IsLocalizedModule S f]
  body: (IsLocalizedModule.iso S f).symm.toAddEquiv.module A

中文:
定义 module
  签名: (f : M ->ₗ[R] M') [是Localized模 S f]
  定义体: (IsLocalizedModule.iso S f).symm.toAddEquiv.module A
-/
@[reducible] noncomputable def module (f : M ->ₗ[R] M') [IsLocalizedModule S f] : Module A M' :=
  (IsLocalizedModule.iso S f).symm.toAddEquiv.module A

attribute [local instance] LocalizedModule.moduleOfIsLocalization in
/--
lemma `isScalarTower_module` / 引理 `isScalarTower_module`

English:
lemma isScalarTower_module
  given: (f : M ->ₗ[R] M') [IsLocalizedModule S f]
  proof: IsLocalizedModule.module S f
    IsScalarTower R A M' :=
  (IsLocalizedModule.iso S f).symm.isScalarTower A

中文:
引理 isScalarTower_module
  条件: (f : M ->ₗ[R] M') [是Localized模 S f]
  证明: IsLocalizedModule.module S f
    IsScalarTower R A M' :=
  (IsLocalizedModule.iso S f).symm.isScalarTower A

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.module, module
-/
lemma isScalarTower_module (f : M ->ₗ[R] M') [IsLocalizedModule S f] :
    letI : Module A M' := IsLocalizedModule.module S f
    IsScalarTower R A M' :=
  (IsLocalizedModule.iso S f).symm.isScalarTower A

section Subsingleton

/--
lemma `mem_ker_iff` / 引理 `mem_ker_iff`

English:
lemma mem_ker_iff
  statement: (S : Submonoid R) {g : M ->ₗ[R] M'}
  proof: by
  simpa using IsLocalizedModule.eq_zero_iff S g

中文:
引理 mem_ker_iff
  结论: (S : 子幺半群 R) {g : M ->ₗ[R] M'}
  证明: by
  simpa using IsLocalizedModule.eq_zero_iff S g

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.eq_zero_iff, eq_zero_iff
-/
lemma mem_ker_iff (S : Submonoid R) {g : M ->ₗ[R] M'}
    [IsLocalizedModule S g] {m : M} :
    m in LinearMap.ker g ↔ exists r in S, r • m = 0 := by
  simpa using IsLocalizedModule.eq_zero_iff S g

/--
lemma `subsingleton_iff_ker_eq_top` / 引理 `subsingleton_iff_ker_eq_top`

English:
lemma subsingleton_iff_ker_eq_top
  statement: (S : Submonoid R) (g : M ->ₗ[R] M')
  proof: by
  rw [← top_le_iff]
  refine ⟨fun H m _ => Subsingleton.elim _ _, fun H => (subsingleton_iff_forall_eq 0).mpr fun x => ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  simpa using @H x Submodule.mem_top

中文:
引理 subsingleton_iff_ker_eq_top
  结论: (S : 子幺半群 R) (g : M ->ₗ[R] M')
  证明: by
  rw [← top_le_iff]
  refine ⟨fun H m _ => Subsingleton.elim _ _, fun H => (subsingleton_iff_forall_eq 0).mpr fun x => ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  simpa using @H x Submodule.mem_top

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, Submodule, Submodule.mem_top, Subsingleton, Subsingleton.elim, _surjective, mem_top, subsingleton_iff_forall_eq, top_le_iff
-/
lemma subsingleton_iff_ker_eq_top (S : Submonoid R) (g : M ->ₗ[R] M')
    [IsLocalizedModule S g] :
    Subsingleton M' ↔ LinearMap.ker g = ⊤ := by
  rw [← top_le_iff]
  refine ⟨fun H m _ => Subsingleton.elim _ _, fun H => (subsingleton_iff_forall_eq 0).mpr fun x => ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  simpa using @H x Submodule.mem_top

/--
lemma `subsingleton_iff` / 引理 `subsingleton_iff`

English:
lemma subsingleton_iff
  statement: (S : Submonoid R) (g : M ->ₗ[R] M')
  proof: by
  simp_rw [subsingleton_iff_ker_eq_top S g, ← top_le_iff, SetLike.le_def,
    mem_ker_iff S, Submodule.mem_top, true_implies]

中文:
引理 subsingleton_iff
  结论: (S : 子幺半群 R) (g : M ->ₗ[R] M')
  证明: by
  simp_rw [subsingleton_iff_ker_eq_top S g, ← top_le_iff, SetLike.le_def,
    mem_ker_iff S, Submodule.mem_top, true_implies]

Depends on / 依赖: SetLike, SetLike.le_def, Submodule, Submodule.mem_top, le_def, mem_ker_iff, mem_top, simp_rw, subsingleton_iff_ker_eq_top, top_le_iff, true_implies
-/
lemma subsingleton_iff (S : Submonoid R) (g : M ->ₗ[R] M')
    [IsLocalizedModule S g] :
    Subsingleton M' ↔ forall m : M, exists r in S, r • m = 0 := by
  simp_rw [subsingleton_iff_ker_eq_top S g, ← top_le_iff, SetLike.le_def,
    mem_ker_iff S, Submodule.mem_top, true_implies]

/--
lemma `subsingleton_of_subsingleton` / 引理 `subsingleton_of_subsingleton`

English:
lemma subsingleton_of_subsingleton
  statement: (S : Submonoid R) (g : M ->ₗ[R] M') [IsLocalizedModule S g]
  proof: by
  rw [subsingleton_iff S g]
  intro m
  use 1
  simp [one_mem, Subsingleton.elim m 0]

中文:
引理 subsingleton_of_subsingleton
  结论: (S : 子幺半群 R) (g : M ->ₗ[R] M') [是Localized模 S g]
  证明: by
  rw [subsingleton_iff S g]
  intro m
  use 1
  simp [one_mem, Subsingleton.elim m 0]

Depends on / 依赖: Subsingleton, Subsingleton.elim, one_mem, subsingleton_iff
-/
lemma subsingleton_of_subsingleton (S : Submonoid R) (g : M ->ₗ[R] M') [IsLocalizedModule S g]
    [Subsingleton M] : Subsingleton M' := by
  rw [subsingleton_iff S g]
  intro m
  use 1
  simp [one_mem, Subsingleton.elim m 0]

end Subsingleton

end IsLocalizedModule

end IsLocalizedModule

namespace LocalizedModule

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/--
lemma `mem_ker_mkLinearMap_iff` / 引理 `mem_ker_mkLinearMap_iff`

English:
lemma mem_ker_mkLinearMap_iff
  given: {S : Submonoid R} {m : M}
  proof: IsLocalizedModule.mem_ker_iff S

中文:
引理 mem_ker_mkLinearMap_iff
  条件: {S : 子幺半群 R} {m : M}
  证明: IsLocalizedModule.mem_ker_iff S

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mem_ker_iff, mem_ker_iff
-/
lemma mem_ker_mkLinearMap_iff {S : Submonoid R} {m : M} :
    m in LinearMap.ker (mkLinearMap S M) ↔ exists r in S, r • m = 0 :=
  IsLocalizedModule.mem_ker_iff S

/--
lemma `subsingleton_iff_ker_eq_top` / 引理 `subsingleton_iff_ker_eq_top`

English:
lemma subsingleton_iff_ker_eq_top
  given: {S : Submonoid R}
  proof: IsLocalizedModule.subsingleton_iff_ker_eq_top S _

中文:
引理 subsingleton_iff_ker_eq_top
  条件: {S : 子幺半群 R}
  证明: IsLocalizedModule.subsingleton_iff_ker_eq_top S _

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.subsingleton_iff_ker_eq_top, subsingleton_iff_ker_eq_top
-/
lemma subsingleton_iff_ker_eq_top {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔
      LinearMap.ker (LocalizedModule.mkLinearMap S M) = ⊤ :=
  IsLocalizedModule.subsingleton_iff_ker_eq_top S _

/--
lemma `subsingleton_iff` / 引理 `subsingleton_iff`

English:
lemma subsingleton_iff
  given: {S : Submonoid R}
  proof: IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)

中文:
引理 subsingleton_iff
  条件: {S : 子幺半群 R}
  证明: IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.subsingleton_iff, LocalizedModule, LocalizedModule.mkLinearMap, mkLinearMap, subsingleton_iff
-/
lemma subsingleton_iff {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔ forall m : M, exists r in S, r • m = 0 :=
  IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] (S
  body: by
  rw [IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)]
  intro
  use 1, S.one_mem, Subsingleton.elim _ _

中文:
实例 [子单例
  签名: M] (S
  定义体: by
  rw [IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)]
  intro
  use 1, S.one_mem, Subsingleton.elim _ _

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.subsingleton_iff, LocalizedModule, LocalizedModule.mkLinearMap, S.one_mem, Subsingleton, Subsingleton.elim, mkLinearMap, one_mem, subsingleton_iff
-/
instance [Subsingleton M] (S : Submonoid R) : Subsingleton (LocalizedModule S M) := by
  rw [IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)]
  intro
  use 1, S.one_mem, Subsingleton.elim _ _

end LocalizedModule

namespace IsLocalizedModule

variable {R M A N : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
  [CommRing A] [AddCommMonoid N] [Module A N] [Algebra R A] [Module R N] [IsScalarTower R A N]
  (f : M ->ₗ[R] N)

/--
lemma `isTorsionFree_of_forall_isRegular` / 引理 `isTorsionFree_of_forall_isRegular`

English:
lemma isTorsionFree_of_forall_isRegular
  statement: (S : Submonoid R) (hS : forall s in S, s != 0 -> IsRegular s)
  proof: by
    by_cases hS₀ : 0 in S
    · have : Subsingleton N := (IsLocalizedModule.subsingleton_iff S f).2 fun _ => ⟨0, hS₀, by simp⟩
      exact Subsingleton.elim ..
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
    obtain ⟨⟨m₁, t₁⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
    obtain ⟨⟨m₂, t₂⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
replace hS : forall s in S, IsRegular s := fun s hs => hS s hs ne_of_mem_of_not_mem hs hS₀
    rw [IsLocalization.isRegular_mk' hS] at hc
    have (s : S) (x y : M) : s • x = s • y ↔ x = y := (hS _ s.2).isSMulRegular.eq_iff
    simp only [Function.uncurry_apply_pair, mk'_smul_mk', mk'_eq_mk'_iff, mul_smul, this,
      exists_const] at hxy ⊢
    simpa [smul_comm _ a, hc.isSMulRegular.eq_iff] using hxy

中文:
引理 isTorsionFree_of_对任意_isRegular
  结论: (S : 子幺半群 R) (hS : 对任意 s in S, s != 0 -> 是正则 s)
  证明: by
    by_cases hS₀ : 0 in S
    · have : Subsingleton N := (IsLocalizedModule.subsingleton_iff S f).2 fun _ => ⟨0, hS₀, by simp⟩
      exact Subsingleton.elim ..
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
    obtain ⟨⟨m₁, t₁⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
    obtain ⟨⟨m₂, t₂⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
replace hS : forall s in S, IsRegular s := fun s hs => hS s hs ne_of_mem_of_not_mem hs hS₀
    rw [IsLocalization.isRegular_mk' hS] at hc
    have (s : S) (x y : M) : s • x = s • y ↔ x = y := (hS _ s.2).isSMulRegular.eq_iff
    simp only [Function.uncurry_apply_pair, mk'_smul_mk', mk'_eq_mk'_iff, mul_smul, this,
      exists_const] at hxy ⊢
    simpa [smul_comm _ a, hc.isSMulRegular.eq_iff] using hxy

Depends on / 依赖: IsLocalization, IsLocalization.isRegular_mk, IsLocalization.mk, IsLocalizedModule, IsLocalizedModule.mk, IsLocalizedModule.subsingleton_iff, IsRegular, Subsingleton, Subsingleton.elim, _surjective, isRegular_mk, ne_of_mem_of_not_mem, replace, subsingleton_iff
-/
lemma isTorsionFree_of_forall_isRegular (S : Submonoid R) (hS : forall s in S, s != 0 -> IsRegular s)
    [IsTorsionFree R M] [IsLocalization S A] [IsLocalizedModule S f] : IsTorsionFree A N where
  isSMulRegular c hc x y hxy := by
    by_cases hS₀ : 0 in S
    · have : Subsingleton N := (IsLocalizedModule.subsingleton_iff S f).2 fun _ => ⟨0, hS₀, by simp⟩
      exact Subsingleton.elim ..
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
    obtain ⟨⟨m₁, t₁⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
    obtain ⟨⟨m₂, t₂⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
replace hS : forall s in S, IsRegular s := fun s hs => hS s hs ne_of_mem_of_not_mem hs hS₀
    rw [IsLocalization.isRegular_mk' hS] at hc
    have (s : S) (x y : M) : s • x = s • y ↔ x = y := (hS _ s.2).isSMulRegular.eq_iff
    simp only [Function.uncurry_apply_pair, mk'_smul_mk', mk'_eq_mk'_iff, mul_smul, this,
      exists_const] at hxy ⊢
    simpa [smul_comm _ a, hc.isSMulRegular.eq_iff] using hxy

/--
lemma `isTorsionFree` / 引理 `isTorsionFree`

English:
lemma isTorsionFree
  statement: [IsDomain R] [IsTorsionFree R M] (S : Submonoid R)
  proof: isTorsionFree_of_forall_isRegular f S by simp [isRegular_iff_ne_zero]

中文:
引理 isTorsionFree
  结论: [是整环 R] [是无挠 R M] (S : 子幺半群 R)
  证明: isTorsionFree_of_forall_isRegular f S by simp [isRegular_iff_ne_zero]

Depends on / 依赖: isRegular_iff_ne_zero, isTorsionFree_of_forall_isRegular
-/
lemma isTorsionFree [IsDomain R] [IsTorsionFree R M] (S : Submonoid R)
    [IsLocalization S A] [IsLocalizedModule S f] : Module.IsTorsionFree A N :=
isTorsionFree_of_forall_isRegular f S by simp [isRegular_iff_ne_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] (S
  body: isTorsionFree (LocalizedModule.mkLinearMap S M) S

中文:
实例 [是整环
  签名: R] (S
  定义体: isTorsionFree (LocalizedModule.mkLinearMap S M) S

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, isTorsionFree, mkLinearMap
-/
instance [IsDomain R] (S : Submonoid R) [IsTorsionFree R M] :
    IsTorsionFree (Localization S) (LocalizedModule S M) :=
  isTorsionFree (LocalizedModule.mkLinearMap S M) S

end IsLocalizedModule

/-!
## Localizations of modules away from an element
-/

/--
Definition of `IsLocalizedModule.Away` / `IsLocalizedModule.Away` 的定义

English:
abbreviation IsLocalizedModule.Away
  signature: {R M M' : Type*} [CommSemiring R] (x : R) [AddCommMonoid M]
  body: IsLocalizedModule (Submonoid.powers x) f

中文:
缩写 是Localized模.Away
  签名: {R M M' : 类型} [交换半环 R] (x : R) [加法交换幺半群 M]
  定义体: IsLocalizedModule (Submonoid.powers x) f
-/
protected abbrev IsLocalizedModule.Away {R M M' : Type*} [CommSemiring R] (x : R) [AddCommMonoid M]
    [Module R M] [AddCommMonoid M'] [Module R M'] (f : M ->ₗ[R] M') :=
  IsLocalizedModule (Submonoid.powers x) f

/--
Definition of `LocalizedModule.Away` / `LocalizedModule.Away` 的定义

English:
abbreviation LocalizedModule.Away
  signature: {R : Type*} [CommSemiring R] (x : R)
  body: LocalizedModule (Submonoid.powers x) M

中文:
缩写 LocalizedModule.Away
  签名: {R : 类型} [交换半环 R] (x : R)
  定义体: LocalizedModule (Submonoid.powers x) M
-/
protected abbrev LocalizedModule.Away {R : Type*} [CommSemiring R] (x : R)
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule (Submonoid.powers x) M
