/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.GroupWithZero.Submonoid.Primal
public import Mathlib.Order.WellFounded

/-!
# Unique factorization

## Main Definitions
* `WfDvdMonoid` holds for `Monoid`s for which a strict divisibility relation is
  well-founded.
* `UniqueFactorizationMonoid` holds for `WfDvdMonoid`s where
  `Irreducible` is equivalent to `Prime`
-/

@[expose] public section

assert_not_exists Field Finsupp Ideal

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

/--
Definition of `WfDvdMonoid` / `WfDvdMonoid` 的定义

English:
abbreviation WfDvdMonoid
  signature: (α : Type*) [CommMonoidWithZero α]
  body: IsWellFounded α DvdNotUnit

中文:
缩写 WfDvdMonoid
  签名: (α : 类型) [带零交换幺半群 α]
  定义体: IsWellFounded α DvdNotUnit

Depends on / 依赖: DvdNotUnit, IsWellFounded
-/
abbrev WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop :=
  IsWellFounded α DvdNotUnit

/--
theorem `wellFounded_dvdNotUnit` / 定理 `wellFounded_dvdNotUnit`

English:
theorem wellFounded_dvdNotUnit
  given: {α : Type*} [CommMonoidWithZero α] [h : WfDvdMonoid α]
  proof: h.wf

中文:
定理 wellFounded_dvdNotUnit
  条件: {α : 类型} [带零交换幺半群 α] [h : WfDvdMonoid α]
  证明: h.wf
-/
theorem wellFounded_dvdNotUnit {α : Type*} [CommMonoidWithZero α] [h : WfDvdMonoid α] :
    WellFounded (DvdNotUnit (α := α)) :=
  h.wf

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

variable [WfDvdMonoid α]

/--
theorem `exists_irreducible_factor` / 定理 `exists_irreducible_factor`

English:
theorem exists_irreducible_factor
  given: {a : α} (ha : ¬IsUnit a) (ha0 : a != 0)
  proof: let ⟨b, hs, hr⟩ := wellFounded_dvdNotUnit.has_min { b | b ∣ a ∧ ¬IsUnit b } ⟨a, dvd_rfl, ha⟩
  ⟨b,
    ⟨hs.2, fun c d he =>
      let h := dvd_trans ⟨d, he⟩ hs.1
      or_iff_not_imp_left.2 fun hc =>
        of_not_not fun hd => hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩,
    hs.1⟩

@[e

中文:
定理 存在_irreducible_factor
  条件: {a : α} (ha : ¬是单位 a) (ha0 : a != 0)
  证明: let ⟨b, hs, hr⟩ := wellFounded_dvdNotUnit.has_min { b | b ∣ a ∧ ¬IsUnit b } ⟨a, dvd_rfl, ha⟩
  ⟨b,
    ⟨hs.2, fun c d he =>
      let h := dvd_trans ⟨d, he⟩ hs.1
      or_iff_not_imp_left.2 fun hc =>
        of_not_not fun hd => hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩,
    hs.1⟩

@[e

Depends on / 依赖: IsUnit, dvd_rfl, dvd_trans, has_min, ne_zero_of_dvd_ne_zero, of_not_not, or_iff_not_imp_left, wellFounded_dvdNotUnit, wellFounded_dvdNotUnit.has_min
-/
theorem exists_irreducible_factor {a : α} (ha : ¬IsUnit a) (ha0 : a != 0) :
    exists i, Irreducible i ∧ i ∣ a :=
  let ⟨b, hs, hr⟩ := wellFounded_dvdNotUnit.has_min { b | b ∣ a ∧ ¬IsUnit b } ⟨a, dvd_rfl, ha⟩
  ⟨b,
    ⟨hs.2, fun c d he =>
      let h := dvd_trans ⟨d, he⟩ hs.1
      or_iff_not_imp_left.2 fun hc =>
        of_not_not fun hd => hr c ⟨h, hc⟩ ⟨ne_zero_of_dvd_ne_zero ha0 h, d, hd, he⟩⟩,
    hs.1⟩

@[elab_as_elim]
/--
theorem `induction_on_irreducible` / 定理 `induction_on_irreducible`

English:
theorem induction_on_irreducible
  statement: {motive : α -> Prop} (a : α)
  proof: haveI := Classical.dec
  wellFounded_dvdNotUnit.fix
    (fun a ih =>
      if ha0 : a = 0 then ha0.substr zero
      else
        if hau : IsUnit a then unit a hau
        else
          let ⟨i, i_irred, b, hb⟩ := exists_irreducible_factor hau ha0
          let hb0 : b != 0 := ne_zero_of_dvd_ne_zero

中文:
定理 induction_on_irreducible
  结论: {motive : α -> 命题} (a : α)
  证明: haveI := Classical.dec
  wellFounded_dvdNotUnit.fix
    (fun a ih =>
      if ha0 : a = 0 then ha0.substr zero
      else
        if hau : IsUnit a then unit a hau
        else
          let ⟨i, i_irred, b, hb⟩ := exists_irreducible_factor hau ha0
          let hb0 : b != 0 := ne_zero_of_dvd_ne_zero

Depends on / 依赖: Classical, Classical.dec, IsUnit, exists_irreducible_factor, ha0.substr, hb.symm, i_irred, mul_comm, ne_zero_of_dvd_ne_zero, substr, wellFounded_dvdNotUnit, wellFounded_dvdNotUnit.fix
-/
theorem induction_on_irreducible {motive : α -> Prop} (a : α)
    (zero : motive 0) (unit : forall u : α, IsUnit u -> motive u)
    (mul : forall a i : α, a != 0 -> Irreducible i -> motive a -> motive (i * a)) : motive a :=
  haveI := Classical.dec
  wellFounded_dvdNotUnit.fix
    (fun a ih =>
      if ha0 : a = 0 then ha0.substr zero
      else
        if hau : IsUnit a then unit a hau
        else
          let ⟨i, i_irred, b, hb⟩ := exists_irreducible_factor hau ha0
          let hb0 : b != 0 := ne_zero_of_dvd_ne_zero ha0 ⟨i, mul_comm i b ▸ hb⟩
hb.symm ▸ mul b i hb0 i_irred ih b ⟨hb0, i, i_irred.1, mul_comm i b ▸ hb⟩)
    a

/--
theorem `exists_factors` / 定理 `exists_factors`

English:
theorem exists_factors
  given: (a : α)
  proof: induction_on_irreducible a (fun h => (h rfl).elim)
    (fun _ hu _ => ⟨0, fun _ h => False.elim (Multiset.notMem_zero _ h), hu.unit, one_mul _⟩)
    fun a i ha0 hi ih _ =>
    let ⟨s, hs⟩ := ih ha0
    ⟨i ::ₘ s, fun b H => (Multiset.mem_cons.1 H).elim (fun h => h.symm ▸ hi) (hs.1 b), by
      rw [s.

中文:
定理 存在_factors
  条件: (a : α)
  证明: induction_on_irreducible a (fun h => (h rfl).elim)
    (fun _ hu _ => ⟨0, fun _ h => False.elim (Multiset.notMem_zero _ h), hu.unit, one_mul _⟩)
    fun a i ha0 hi ih _ =>
    let ⟨s, hs⟩ := ih ha0
    ⟨i ::ₘ s, fun b H => (Multiset.mem_cons.1 H).elim (fun h => h.symm ▸ hi) (hs.1 b), by
      rw [s.

Depends on / 依赖: False.elim, Multiset, Multiset.mem_cons, Multiset.notMem_zero, h.symm, hu.unit, induction_on_irreducible, mem_cons, mul_left, notMem_zero, one_mul, prod_cons, s.prod_cons
-/
theorem exists_factors (a : α) :
    a != 0 -> exists f : Multiset α, (forall b in f, Irreducible b) ∧ Associated f.prod a :=
  induction_on_irreducible a (fun h => (h rfl).elim)
    (fun _ hu _ => ⟨0, fun _ h => False.elim (Multiset.notMem_zero _ h), hu.unit, one_mul _⟩)
    fun a i ha0 hi ih _ =>
    let ⟨s, hs⟩ := ih ha0
    ⟨i ::ₘ s, fun b H => (Multiset.mem_cons.1 H).elim (fun h => h.symm ▸ hi) (hs.1 b), by
      rw [s.prod_cons i]
      exact hs.2.mul_left i⟩

/--
theorem `not_isUnit_iff_exists_factors_eq` / 定理 `not_isUnit_iff_exists_factors_eq`

English:
theorem not_isUnit_iff_exists_factors_eq
  given: (a : α) (hn0 : a != 0)
  proof: ⟨fun hnu => by
    obtain ⟨f, hi, u, rfl⟩ := exists_factors a hn0
obtain ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero fun h : f = 0 => hnu by simp [h]
    classical
      refine ⟨(f.erase b).cons (b * u), fun a ha => ?_, ?_, Multiset.cons_ne_zero⟩
      · obtain rfl | ha := Multiset.mem_cons.1 ha
      

中文:
定理 not_isUnit_iff_存在_factors_eq
  条件: (a : α) (hn0 : a != 0)
  证明: ⟨fun hnu => by
    obtain ⟨f, hi, u, rfl⟩ := exists_factors a hn0
obtain ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero fun h : f = 0 => hnu by simp [h]
    classical
      refine ⟨(f.erase b).cons (b * u), fun a ha => ?_, ?_, Multiset.cons_ne_zero⟩
      · obtain rfl | ha := Multiset.mem_cons.1 ha
      

Depends on / 依赖: Associated, Associated.irreducible, Multiset, Multiset.cons_ne_zero, Multiset.exists_me, Multiset.exists_mem_of_ne_zero, Multiset.mem_cons, Multiset.mem_of_mem_erase, Multiset.prod_cons, Multiset.prod_erase, classical, cons_ne_zero, exacts, exists_factors, exists_me, exists_mem_of_ne_zero, f.erase, irreducible, mem_cons, mem_of_mem_erase
-/
theorem not_isUnit_iff_exists_factors_eq (a : α) (hn0 : a != 0) :
    ¬IsUnit a ↔ exists f : Multiset α, (forall b in f, Irreducible b) ∧ f.prod = a ∧ f != ∅ :=
  ⟨fun hnu => by
    obtain ⟨f, hi, u, rfl⟩ := exists_factors a hn0
obtain ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero fun h : f = 0 => hnu by simp [h]
    classical
      refine ⟨(f.erase b).cons (b * u), fun a ha => ?_, ?_, Multiset.cons_ne_zero⟩
      · obtain rfl | ha := Multiset.mem_cons.1 ha
        exacts [Associated.irreducible ⟨u, rfl⟩ (hi b h), hi a (Multiset.mem_of_mem_erase ha)]
      · rw [Multiset.prod_cons, mul_comm b, mul_assoc, Multiset.prod_erase h, mul_comm],
    fun ⟨_, hi, he, hne⟩ =>
    let ⟨b, h⟩ := Multiset.exists_mem_of_ne_zero hne
not_isUnit_of_not_isUnit_dvd (hi b h).not_isUnit he ▸ Multiset.dvd_prod h⟩

@[deprecated (since := "2026-08-02")]
alias not_unit_iff_exists_factors_eq := not_isUnit_iff_exists_factors_eq

/--
theorem `isRelPrime_of_no_irreducible_factors` / 定理 `isRelPrime_of_no_irreducible_factors`

English:
theorem isRelPrime_of_no_irreducible_factors
  statement: {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
  proof: isRelPrime_of_no_nonunits_factors nonzero fun _z znu znz zx zy =>
    have ⟨i, h1, h2⟩ := exists_irreducible_factor znu znz
    H i h1 (h2.trans zx) (h2.trans zy)

中文:
定理 isRelPrime_of_no_irreducible_factors
  结论: {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
  证明: isRelPrime_of_no_nonunits_factors nonzero fun _z znu znz zx zy =>
    have ⟨i, h1, h2⟩ := exists_irreducible_factor znu znz
    H i h1 (h2.trans zx) (h2.trans zy)

Depends on / 依赖: exists_irreducible_factor, h2.trans, isRelPrime_of_no_nonunits_factors, nonzero
-/
theorem isRelPrime_of_no_irreducible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : forall z : α, Irreducible z -> z ∣ x -> ¬z ∣ y) : IsRelPrime x y :=
  isRelPrime_of_no_nonunits_factors nonzero fun _z znu znz zx zy =>
    have ⟨i, h1, h2⟩ := exists_irreducible_factor znu znz
    H i h1 (h2.trans zx) (h2.trans zy)

end WfDvdMonoid

section Prio

-- set_option default_priority 100

-- see Note [default priority]
/--
Unique factorization monoids are defined as cancellative `CommMonoidWithZero`s with well-founded
strict divisibility relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_existsUnique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`
-/
@[wikidata Q1052579 "This Mathlib declaration captures 'unique factorization'.
Use in conjunction with `IsDomain` to capture unique factorization domain."]
/--
Definition of `UniqueFactorizationMonoid` / `UniqueFactorizationMonoid` 的定义

English:
class UniqueFactorizationMonoid
  parameters: (α : Type*) [CommMonoidWithZero α]
  extends: IsCancelMulZero α, IsWellFounded α DvdNotUnit
  axioms and operations (1):
    - irreducible_iff_prime : forall {a : α}, Irreducible a ↔ Prime a

中文:
类 唯一分解幺半群
  参数: (α : 类型) [带零交换幺半群 α]
  继承: 是乘零消去 α, 是良基 α DvdNotUnit
  公理与运算 (1 个):
    - irreducible_iff_prime : 对任意 {a : α}, 不可约 a ↔ 素 a
-/
class UniqueFactorizationMonoid (α : Type*) [CommMonoidWithZero α] : Prop
    extends IsCancelMulZero α, IsWellFounded α DvdNotUnit where
  protected irreducible_iff_prime : forall {a : α}, Irreducible a ↔ Prime a

attribute [instance 100] UniqueFactorizationMonoid.toIsCancelMulZero

instance (priority := 100) ufm_of_decomposition_of_wfDvdMonoid
    [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] [DecompositionMonoid α] :
    UniqueFactorizationMonoid α where
  irreducible_iff_prime := irreducible_iff_prime

end Prio

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

/--
theorem `exists_prime_factors` / 定理 `exists_prime_factors`

English:
theorem exists_prime_factors
  given: (a : α)
  proof: by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  apply WfDvdMonoid.exists_factors a

中文:
定理 存在_prime_factors
  条件: (a : α)
  证明: by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  apply WfDvdMonoid.exists_factors a

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime, WfDvdMonoid, WfDvdMonoid.exists_factors, exists_factors, irreducible_iff_prime, simp_rw
-/
theorem exists_prime_factors (a : α) :
    a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  apply WfDvdMonoid.exists_factors a

/--
lemma `exists_prime_iff` / 引理 `exists_prime_iff`

English:
lemma exists_prime_iff
  proof: by
  refine ⟨fun ⟨p, hp⟩ => ⟨p, hp.ne_zero, hp.not_isUnit⟩, fun ⟨x, hx₀, hxu⟩ => ?_⟩
  obtain ⟨f, hf, -⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx₀
  exact ⟨f, UniqueFactorizationMonoid.irreducible_iff_prime.mp hf⟩

@[elab_as_elim]

中文:
引理 存在_prime_iff
  证明: by
  refine ⟨fun ⟨p, hp⟩ => ⟨p, hp.ne_zero, hp.not_isUnit⟩, fun ⟨x, hx₀, hxu⟩ => ?_⟩
  obtain ⟨f, hf, -⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx₀
  exact ⟨f, UniqueFactorizationMonoid.irreducible_iff_prime.mp hf⟩

@[elab_as_elim]

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime.mp, WfDvdMonoid, WfDvdMonoid.exists_irreducible_factor, exists_irreducible_factor, hp.ne_zero, hp.not_isUnit, irreducible_iff_prime, ne_zero, not_isUnit
-/
lemma exists_prime_iff :
    (exists (p : α), Prime p) ↔ exists (x : α), x != 0 ∧ ¬ IsUnit x := by
  refine ⟨fun ⟨p, hp⟩ => ⟨p, hp.ne_zero, hp.not_isUnit⟩, fun ⟨x, hx₀, hxu⟩ => ?_⟩
  obtain ⟨f, hf, -⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx₀
  exact ⟨f, UniqueFactorizationMonoid.irreducible_iff_prime.mp hf⟩

@[elab_as_elim]
/--
theorem `induction_on_prime` / 定理 `induction_on_prime`

English:
theorem induction_on_prime
  statement: {P : α -> Prop} (a : α) (h₁ : P 0) (h₂ : forall x : α, IsUnit x -> P x)
  proof: by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime] at h₃
  exact WfDvdMonoid.induction_on_irreducible a h₁ h₂ h₃

中文:
定理 induction_on_prime
  结论: {P : α -> 命题} (a : α) (h₁ : P 0) (h₂ : 对任意 x : α, 是单位 x -> P x)
  证明: by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime] at h₃
  exact WfDvdMonoid.induction_on_irreducible a h₁ h₂ h₃

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime, WfDvdMonoid, WfDvdMonoid.induction_on_irreducible, induction_on_irreducible, irreducible_iff_prime, simp_rw
-/
theorem induction_on_prime {P : α -> Prop} (a : α) (h₁ : P 0) (h₂ : forall x : α, IsUnit x -> P x)
    (h₃ : forall a p : α, a != 0 -> Prime p -> P a -> P (p * a)) : P a := by
  simp_rw [← UniqueFactorizationMonoid.irreducible_iff_prime] at h₃
  exact WfDvdMonoid.induction_on_irreducible a h₁ h₂ h₃

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecompositionMonoid α
  body: by
    obtain rfl | ha := eq_or_ne a 0; · exact isPrimal_zero
    obtain ⟨f, hf, u, rfl⟩ := exists_prime_factors a ha
    exact ((Submonoid.isPrimal α).multiset_prod_mem f (hf · · |>.isPrimal)).mul u.isUnit.isPrimal

中文:
实例 :
  签名: 分解幺半群 α
  定义体: by
    obtain rfl | ha := eq_or_ne a 0; · exact isPrimal_zero
    obtain ⟨f, hf, u, rfl⟩ := exists_prime_factors a ha
    exact ((Submonoid.isPrimal α).multiset_prod_mem f (hf · · |>.isPrimal)).mul u.isUnit.isPrimal

Depends on / 依赖: Submonoid, Submonoid.isPrimal, eq_or_ne, exists_prime_factors, isPrimal, isPrimal_zero, isUnit, multiset_prod_mem, u.isUnit.isPrimal
-/
instance : DecompositionMonoid α where
  primal a := by
    obtain rfl | ha := eq_or_ne a 0; · exact isPrimal_zero
    obtain ⟨f, hf, u, rfl⟩ := exists_prime_factors a ha
    exact ((Submonoid.isPrimal α).multiset_prod_mem f (hf · · |>.isPrimal)).mul u.isUnit.isPrimal

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α]

variable (α) in
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton α]
  statement: UniqueFactorizationMonoid α where
  proof: Subsingleton.elim a b
  mul_right_cancel_of_ne_zero _ a b _ := Subsingleton.elim a b
  wf := ⟨fun a => Acc.intro a fun b ⟨hb, _⟩ => (hb (Subsingleton.elim b 0)).elim⟩
  irreducible_iff_prime {a} := by simp [Subsingleton.elim a 0]

中文:
定理 of_subsingleton
  条件: [子单例 α]
  结论: 唯一分解幺半群 α where
  证明: Subsingleton.elim a b
  mul_right_cancel_of_ne_zero _ a b _ := Subsingleton.elim a b
  wf := ⟨fun a => Acc.intro a fun b ⟨hb, _⟩ => (hb (Subsingleton.elim b 0)).elim⟩
  irreducible_iff_prime {a} := by simp [Subsingleton.elim a 0]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem of_subsingleton [Subsingleton α] : UniqueFactorizationMonoid α where
  mul_left_cancel_of_ne_zero _ a b _ := Subsingleton.elim a b
  mul_right_cancel_of_ne_zero _ a b _ := Subsingleton.elim a b
  wf := ⟨fun a => Acc.intro a fun b ⟨hb, _⟩ => (hb (Subsingleton.elim b 0)).elim⟩
  irreducible_iff_prime {a} := by simp [Subsingleton.elim a 0]

variable [UniqueFactorizationMonoid α]

open scoped Classical in
/--
Definition of `factors` / `factors` 的定义

English:
definition factors
  signature: (a : α)
  body: if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)

中文:
定义 factors
  签名: (a : α)
  定义体: if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)

Depends on / 依赖: Classical, Classical.choose, UniqueFactorizationMonoid, UniqueFactorizationMonoid.exists_prime_factors, exists_prime_factors
-/
noncomputable def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)

/--
theorem `factors_prod` / 定理 `factors_prod`

English:
theorem factors_prod
  given: {a : α} (ane0 : a != 0)
  statement: Associated (factors a).prod a
  proof: by
  rw [factors]; rw [dif_neg ane0]
  exact (Classical.choose_spec (exists_prime_factors a ane0)).2

@[simp]

中文:
定理 factors_prod
  条件: {a : α} (ane0 : a != 0)
  结论: Associated (factors a).乘积 a
  证明: by
  rw [factors]; rw [dif_neg ane0]
  exact (Classical.choose_spec (exists_prime_factors a ane0)).2

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_neg, exists_prime_factors, factors
-/
theorem factors_prod {a : α} (ane0 : a != 0) : Associated (factors a).prod a := by
  rw [factors]; rw [dif_neg ane0]
  exact (Classical.choose_spec (exists_prime_factors a ane0)).2

@[simp]
/--
theorem `factors_zero` / 定理 `factors_zero`

English:
theorem factors_zero
  statement: factors (0 : α) = 0
  proof: by simp [factors]

中文:
定理 factors_zero
  结论: factors (0 : α) = 0
  证明: by simp [factors]

Depends on / 依赖: factors
-/
theorem factors_zero : factors (0 : α) = 0 := by simp [factors]

/--
theorem `ne_zero_of_mem_factors` / 定理 `ne_zero_of_mem_factors`

English:
theorem ne_zero_of_mem_factors
  given: {p a : α} (h : p in factors a)
  statement: a != 0
  proof: by
  rintro rfl
  simp at h

中文:
定理 ne_zero_of_mem_factors
  条件: {p a : α} (h : p in factors a)
  结论: a != 0
  证明: by
  rintro rfl
  simp at h
-/
theorem ne_zero_of_mem_factors {p a : α} (h : p in factors a) : a != 0 := by
  rintro rfl
  simp at h

/--
theorem `dvd_of_mem_factors` / 定理 `dvd_of_mem_factors`

English:
theorem dvd_of_mem_factors
  given: {p a : α} (h : p in factors a)
  statement: p ∣ a
  proof: dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))

中文:
定理 dvd_of_mem_factors
  条件: {p a : α} (h : p in factors a)
  结论: p ∣ a
  证明: dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))

Depends on / 依赖: Associated, Associated.dvd, Multiset, Multiset.dvd_prod, dvd_prod, dvd_trans, factors_prod, ne_zero_of_mem_factors
-/
theorem dvd_of_mem_factors {p a : α} (h : p in factors a) : p ∣ a :=
  dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))

/--
theorem `prime_of_factor` / 定理 `prime_of_factor`

English:
theorem prime_of_factor
  given: {a : α} (x : α) (hx : x in factors a)
  statement: Prime x
  proof: by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors]; rw [dif_neg ane0] at hx
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx

中文:
定理 prime_of_factor
  条件: {a : α} (x : α) (hx : x in factors a)
  结论: 素 x
  证明: by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors]; rw [dif_neg ane0] at hx
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx

Depends on / 依赖: Classical, Classical.choose_spec, UniqueFactorizationMonoid, UniqueFactorizationMonoid.exists_prime_factors, choose_spec, dif_neg, exists_prime_factors, factors, ne_zero_of_mem_factors
-/
theorem prime_of_factor {a : α} (x : α) (hx : x in factors a) : Prime x := by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors]; rw [dif_neg ane0] at hx
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx

/--
theorem `irreducible_of_factor` / 定理 `irreducible_of_factor`

English:
theorem irreducible_of_factor
  given: {a : α}
  statement: forall x : α, x in factors a -> Irreducible x
  proof: fun x h =>
  (prime_of_factor x h).irreducible

中文:
定理 irreducible_of_factor
  条件: {a : α}
  结论: 对任意 x : α, x in factors a -> 不可约 x
  证明: fun x h =>
  (prime_of_factor x h).irreducible
-/
theorem irreducible_of_factor {a : α} : forall x : α, x in factors a -> Irreducible x := fun x h =>
  (prime_of_factor x h).irreducible

open Multiset in
/--
theorem `card_factors_of_irreducible` / 定理 `card_factors_of_irreducible`

English:
theorem card_factors_of_irreducible
  given: {a : α} (ha : Irreducible a)
  statement: (factors a).card = 1
  proof: by
  have hf : factors a != 0 := by
    intro hf
    simpa [hf, Associated.comm, ha.not_isUnit] using factors_prod ha.ne_zero
  obtain ⟨b, hb⟩ := exists_mem_of_ne_zero hf
  obtain ⟨f, hf⟩ := exists_cons_of_mem hb
  rw [hf]; rw [card_cons]; rw [add_eq_right]; rw [card_eq_zero]; rw [eq_zero_iff_forall

中文:
定理 card_factors_of_irreducible
  条件: {a : α} (ha : 不可约 a)
  结论: (factors a).card = 1
  证明: by
  have hf : factors a != 0 := by
    intro hf
    simpa [hf, Associated.comm, ha.not_isUnit] using factors_prod ha.ne_zero
  obtain ⟨b, hb⟩ := exists_mem_of_ne_zero hf
  obtain ⟨f, hf⟩ := exists_cons_of_mem hb
  rw [hf]; rw [card_cons]; rw [add_eq_right]; rw [card_eq_zero]; rw [eq_zero_iff_forall

Depends on / 依赖: Associated, Associated.comm, add_eq_right, card_cons, card_eq_zero, eq_zero_iff_forall_notMem, exists_cons_of_mem, exists_mem_of_ne_zero, factors, factors_prod, ha.ne_zero, ha.not_isUnit, irreducible_of_factor, mem_cons_of_mem, ne_zero, not_isUnit, replace
-/
theorem card_factors_of_irreducible {a : α} (ha : Irreducible a) : (factors a).card = 1 := by
  have hf : factors a != 0 := by
    intro hf
    simpa [hf, Associated.comm, ha.not_isUnit] using factors_prod ha.ne_zero
  obtain ⟨b, hb⟩ := exists_mem_of_ne_zero hf
  obtain ⟨f, hf⟩ := exists_cons_of_mem hb
  rw [hf]; rw [card_cons]; rw [add_eq_right]; rw [card_eq_zero]; rw [eq_zero_iff_forall_notMem]
  intro c hc
  obtain ⟨f, rfl⟩ := exists_cons_of_mem hc
  replace hb := (irreducible_of_factor b hb).not_isUnit
  replace hc := (irreducible_of_factor c (hf ▸ mem_cons_of_mem hc)).not_isUnit
  simp [← (factors_prod ha.ne_zero).irreducible_iff, hf, irreducible_mul_iff, hb, hc] at ha

end UniqueFactorizationMonoid
