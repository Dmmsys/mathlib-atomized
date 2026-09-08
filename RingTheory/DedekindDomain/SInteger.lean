/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# `S`-integers and `S`-units of fraction fields of Dedekind domains

Let `K` be the field of fractions of a Dedekind domain `R`, and let `S` be a set of prime ideals in
the height one spectrum of `R`. An `S`-integer of `K` is defined to have `v`-adic valuation at most
one for all primes ideals `v` away from `S`, whereas an `S`-unit of `Kˣ` is defined to have `v`-adic
valuation exactly one for all prime ideals `v` away from `S`.

This file defines the subalgebra of `S`-integers of `K` and the subgroup of `S`-units of `Kˣ`, where
`K` can be specialised to the case of a number field or a function field separately.

## Main definitions

* `Set.integer`: `S`-integers.
* `Set.unit`: `S`-units.
* TODO: localised notation for `S`-integers.

## Main statements

* `Set.unitEquivUnitsInteger`: `S`-units are units of `S`-integers.
* `IsDedekindDomain.integer_empty`: `∅`-integers is the usual ring of integers.
* TODO: proof that `S`-units is the kernel of a map to a product.
* TODO: finite generation of `S`-units and Dirichlet's `S`-unit theorem.

## References

* [D Marcus, *Number Fields*][marcus1977number]
* [J W S Cassels, A Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

S integer, S-integer, S unit, S-unit
-/

@[expose] public section


noncomputable section

open IsDedekindDomain

open scoped nonZeroDivisors

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  (S : Set <| HeightOneSpectrum R) (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## `S`-integers -/

namespace Set

/-- The `R`-subalgebra of `S`-integers of `K`. -/
@[simps!]
/-
**Set.integer** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：integer : Subalgebra R K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`：valuation_le_one (r
 : R) : v.valuation K r <= 1

--- 原说明 ---
The `R`-subalgebra of `S`-integers of `K`.
-/
def integer : Subalgebra R K :=
  {
    (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring).copy
        {x : K | ∀ (v) (_ : v ∉ S), v.valuation K x ≤ 1} <|
      Set.ext fun _ => by simp [SetLike.mem_coe] with
    algebraMap_mem' := fun x v _ => v.valuation_le_one x }
/-
**Set.integer_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：integer_eq : (S.integer K).toSubring = ⨅ (v) (_ : v ∉ S), (v.valuation K).
valuationSubring.toSubring
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.coe_integer`：∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDedekind
Domain R] (S : Set (IsDedekindDomain.HeightOneSpectrum R))   (K : Type v) [inst_
2 : F…
· 使用定理 `Subring.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subring R} : (↑(⨅ i, S 
i) : Set R) = ⋂ i, S i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integer_eq :
    (S.integer K).toSubring =
      ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.toSubring :=
  SetLike.ext' <| by ext; simp
/-
**Set.integer_valuation_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：integer_valuation_le_one (x : S.integer K) {v : HeightOneSpectrum R} (hv :
 v ∉ S) : v.valuation K x <= 1
参数：x : S.integer K；hv : v ∉ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem integer_valuation_le_one (x : S.integer K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation K x ≤ 1 :=
  x.property v hv

end Set

namespace IsDedekindDomain

variable (R)

/-- If `S` is the whole set of places of `K`, then the `S`-integers are the whole of `K`. -/
/-
**IsDedekindDomain.integer_univ** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type
 v) [inst_2 : Field K] [inst_3 : Algebra R K]   [inst_4 : IsFractionRing R K], S
et.univ.integer K = ⊤
参数：R : Type u；K : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `trivial`：True

--- 原说明 ---
If `S` is the whole set of places of `K`, then the `S`-integers are the whole of
 `K`.
-/
@[simp] lemma integer_univ : (Set.univ : Set (HeightOneSpectrum R)).integer K = ⊤ := by
  ext
  tauto

/-- If `S` is the empty set, then the `S`-integers are the minimal `R`-subalgebra of `K` (which is
just `R` itself, via `Algebra.botEquivOfInjective` and `IsFractionRing.injective`). -/
/-
**IsDedekindDomain.integer_empty** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：∀ (R : Type u) [inst : CommRing R] [inst_1 : IsDedekindDomain R] (K : Type
 v) [inst_2 : Field K] [inst_3 : Algebra R K]   [inst_4 : IsFractionRing R K], ∅
.integer K = ⊥
参数：R : Type u；K : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_le_one`：valuation_le_one (r
 : R) : v.valuation K r <= 1
· 使用定理 `Subring.copy.congr_simp`：∀ {R : Type u} [inst : NonAssocRing R] (S S_1 :
 Subring R) (e_S : S = S_1) (s s_1 : Set R) (e_s : s = s_1)   (hs : s = ↑S), S.c
opy s hs = S_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subalgebra.mk.congr_simp`：∀ {R : Type u} {A : Type v} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   (toSubsemiring toSubsemirin
g_1 : Subsemir…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`：mem
_integers_of_valuation_le_one (x : K) (h : forall v : HeightOneSpectrum R, v.val
uation K x <= 1) : x in (algebraMap R K).range

--- 原说明 ---
If `S` is the empty set, then the `S`-integers are the minimal `R`-subalgebra of
 `K` (which is
just `R` itself, via `Algebra.botEquivOfInjective` and `IsFractionRing.injective
`).
-/
@[simp] lemma integer_empty : (∅ : Set (HeightOneSpectrum R)).integer K = ⊥ := by
  ext x
  simp only [Set.integer, Set.mem_empty_iff_false, not_false_eq_true, true_implies]
  refine ⟨HeightOneSpectrum.mem_integers_of_valuation_le_one K x, ?_⟩
  rintro ⟨y, rfl⟩ v
  exact v.valuation_le_one y

end IsDedekindDomain
/-! ## `S`-units -/

namespace Set

/-- The subgroup of `S`-units of `Kˣ`. -/
@[simps!]
/-
**Set.unit** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：unit : Subgroup Kˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of `S`-units of `Kˣ`.
-/
def unit : Subgroup Kˣ :=
  (⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy
      {x : Kˣ | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuation K x = 1} <|
    Set.ext fun _ => by
      simp only [mem_ofPred, SetLike.mem_coe, Subgroup.mem_iInf, Valuation.mem_unitGroup_iff]
/-
**Set.unit_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unit_eq : S.unit K = ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.u
nitGroup
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.copy_eq`：copy_eq (K : Subgroup G) (s : Set G) (hs : s = ↑K) : K
.copy s hs = K
-/
theorem unit_eq :
    S.unit K = ⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup :=
  Subgroup.copy_eq _ _ _
/-
**Set.unit_valuation_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：unit_valuation_eq_one (x : S.unit K) {v : HeightOneSpectrum R} (hv : v ∉ S
) : v.valuation K (x : Kˣ) = 1
参数：x : S.unit K；hv : v ∉ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem unit_valuation_eq_one (x : S.unit K) {v : HeightOneSpectrum R} (hv : v ∉ S) :
    v.valuation K (x : Kˣ) = 1 :=
  x.property v hv

/-- The group of `S`-units is the group of units of the ring of `S`-integers. -/
@[simps apply_val_coe symm_apply_coe]
/-
**Set.unitEquivUnitsInteger** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：unitEquivUnitsInteger : S.unit K ≃* (S.integer K)ˣ where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of `S`-units is the group of units of the ring of `S`-integers.
-/
def unitEquivUnitsInteger : S.unit K ≃* (S.integer K)ˣ where
  toFun x :=
    ⟨⟨((x : Kˣ) : K), fun v hv => (x.property v hv).le⟩,
      ⟨((x⁻¹ : Kˣ) : K), fun v hv => (x⁻¹.property v hv).le⟩,
      Subtype.ext x.val.val_inv, Subtype.ext x.val.inv_val⟩
  invFun x :=
    ⟨Units.mk0 x fun hx => x.ne_zero (ZeroMemClass.coe_eq_zero.mp hx),
    fun v hv =>
      eq_one_of_one_le_mul_left (x.val.property v hv) (x.inv.property v hv) <|
        Eq.ge <| by
          rw [← map_mul, Units.val_mk0, Subtype.mk_eq_mk.mp x.val_inv, map_one]⟩
  map_mul' _ _ := by ext; rfl

end Set

