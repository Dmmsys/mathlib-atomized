/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-!
# Factorization of ideals and fractional ideals of Dedekind domains

Every nonzero ideal `I` of a Dedekind domain `R` can be factored as a product `∏_v v^{n_v}` over the
maximal ideals of `R`, where the exponents `n_v` are natural numbers.

Similarly, every nonzero fractional ideal `I` of a Dedekind domain `R` can be factored as a product
`∏_v v^{n_v}` over the maximal ideals of `R`, where the exponents `n_v` are integers. We define
`FractionalIdeal.count K v I` (abbreviated as `val_v(I)` in the documentation) to be `n_v`, and we
prove some of its properties. If `I = 0`, we define `val_v(I) = 0`.

## Main definitions
- `FractionalIdeal.count` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of
  `R` such that `I = a⁻¹J`, then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we
  set `val_v(I) = 0`.

## Main results
- `Ideal.finite_factors` : Only finitely many maximal ideals of `R` divide a given nonzero ideal.
- `Ideal.finprod_heightOneSpectrum_factorization` : The ideal `I` equals the finprod
  `∏_v v^(val_v(I))`, where `val_v(I)` denotes the multiplicity of `v` in the factorization of `I`
  and `v` runs over the maximal ideals of `R`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization` : If `I` is a nonzero fractional ideal,
  `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`, then `I` is equal to the product
  `∏_v v^(val_v(J) - val_v(a))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization'` : If `I` is a nonzero fractional
  ideal, then `I` is equal to the product `∏_v v^(val_v(I))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization_principal` : For a nonzero `k = r/s ∈ K`,
  the fractional ideal `(k)` is equal to the product `∏_v v^(val_v(r) - val_v(s))`.
- `FractionalIdeal.finite_factors` : If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many
  maximal ideals of `R`.
- `IsDedekindDomain.exists_sup_span_eq`: For all ideals `0 < I ≤ J`,
  there exists `a` such that `J = I + ⟨a⟩`.
- `Ideal.map_algebraMap_eq_finsetProd_pow`: if `p` is a maximal ideal, then the lift of `p`
  in an extension is the product of the primes over `p` to the power the ramification index.

## Implementation notes
Since we are only interested in the factorization of nonzero fractional ideals, we define
`val_v(0) = 0` so that every `val_v` is in `ℤ` and we can avoid having to use `WithTop ℤ`.

## Tags
dedekind domain, fractional ideal, ideal, factorization
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Factorization of ideals of Dedekind domains -/

variable [IsDedekindDomain R] (v : HeightOneSpectrum R)

/-- Given a maximal ideal `v` and an ideal `I` of `R`, `maxPowDividing` returns the maximal
  power of `v` dividing `I`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.maxPowDividing** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I : Ideal R) : Ideal R
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a maximal ideal `v` and an ideal `I` of `R`, `maxPowDividing` returns the 
maximal
  power of `v` dividing `I`.
-/
def IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I : Ideal R) : Ideal R :=
  v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

open Associates in
/-
**IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count** 是 Ma
thlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count {I
 : Ideal R} (hI : I != 0) : maxPowDividing v I = v.asIdeal ^ Multiset.count v.as
Ideal (normalizedFactors I)
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing.eq_1`：∀ {R : Type u_1}
 [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.HeightO
neSpectrum R)   (I : Ideal R), v.maxPowDivid…
· 使用定理 `Associates.factors_mk`：factors_mk (a : α) (h : a != 0) : (Associates.mk 
a).factors = factors' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
· 使用定理 `Associates.count_some`：count_some (hp : Irreducible p) (s : Multiset _) 
: count p (WithTop.some s) = s.count ⟨p, hp⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.count_map_eq_count'`：count_map_eq_count' [DecidableEq β] (f : α
 -> β) (s : Multiset α) (hf : Function.Injective f) (x : α) : (s.map f).count (f
 x) = s.count x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Associates.map_subtype_coe_factors'`：map_subtype_coe_factors' {a : α} : 
(factors' a).map (↑) = (factors a).map Associates.mk
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.factors_eq_normalizedFactors`：factors_eq_norma
lizedFactors {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [S
ubsingleton Mˣ] (x : M) : factors x = normal…
· 使用定理 `Associates.mk_injective`：mk_injective [Monoid M] [Subsingleton Mˣ] : Fun
ction.Injective (@Associates.mk M _)
-/
theorem IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
    {I : Ideal R} (hI : I ≠ 0) :
    maxPowDividing v I =
      v.asIdeal ^ Multiset.count v.asIdeal (normalizedFactors I) := by
  rw [maxPowDividing, factors_mk _ hI, count_some (irreducible_mk.mpr v.irreducible),
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, map_subtype_coe_factors',
    factors_eq_normalizedFactors, ← Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal R))]

/-- Only finitely many maximal ideals of `R` divide a given nonzero ideal. -/
/-
**Ideal.finite_factors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.finite_factors {I : Ideal R} (hI : I != 0) : {v : HeightOneSpectrum 
R | v.asIdeal ∣ I}.Finite
参数：hI : I != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Set.coe_ofPred`：Set.coe_ofPred (p : α -> Prop) : ↥{ x | p x } = { x // p
 x }
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ext`：∀ {R : Type u_1} {inst : CommRin
g R} {x y : IsDedekindDomain.HeightOneSpectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…

--- 原说明 ---
Only finitely many maximal ideals of `R` divide a given nonzero ideal.
-/
theorem Ideal.finite_factors {I : Ideal R} (hI : I ≠ 0) :
    {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite := by
  rw [← Set.finite_coe_iff, Set.coe_ofPred]
  have h_fin := fintypeSubtypeDvd I hI
  refine
    Finite.of_injective (fun v => (⟨(v : HeightOneSpectrum R).asIdeal, v.2⟩ : { x // x ∣ I })) ?_
  intro v w hvw
  exact Subtype.coe_injective (HeightOneSpectrum.ext (by simpa using hvw))

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that the
  multiplicity of `v` in the factorization of `I`, denoted `val_v(I)`, is nonzero. -/
/-
**Associates.finite_factors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Associates.finite_factors {I : Ideal R} (hI : I != 0) : forallᶠ v : Height
OneSpectrum R in Filter.cofinite, ((Associates.mk v.asIdeal).count (Associates.m
k I).factors : Int) = 0
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Associates.count_ne_zero_iff_dvd`：count_ne_zero_iff_dvd {a p : α} (ha0 :
 a != 0) (hp : Irreducible p) : (Associates.mk p).count (Associates.mk a).factor
s != 0 ↔ p ∣ a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
· 使用定理 `Filter.eventually_cofinite`：eventually_cofinite {p : α -> Prop} : (foral
lᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite
· 使用定理 `Ideal.finite_factors`：Ideal.finite_factors {I : Ideal R} (hI : I != 0) :
 {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite

--- 原说明 ---
For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` s
uch that the
  multiplicity of `v` in the factorization of `I`, denoted `val_v(I)`, is nonzer
o.
-/
theorem Associates.finite_factors {I : Ideal R} (hI : I ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) = 0 := by
  have h_supp : {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count
      (Associates.mk I).factors : ℤ) = 0} = {v : HeightOneSpectrum R | v.asIdeal ∣ I} := by
    ext v
    simp_rw [Int.natCast_eq_zero]
    exact Associates.count_ne_zero_iff_dvd hI v.irreducible
  rw [Filter.eventually_cofinite, h_supp]
  exact Ideal.finite_factors hI

namespace Ideal

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
  `v^(val_v(I))` is not the unit ideal. -/
@[fun_prop]
/-
**Ideal.hasFiniteMulSupport** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：hasFiniteMulSupport {I : Ideal R} (hI : I != 0) : HasFiniteMulSupport fun 
v : HeightOneSpectrum R => v.maxPowDividing I
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_cofinite`：eventually_cofinite {p : α -> Prop} : (foral
lᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite
· 使用定理 `Associates.finite_factors`：Associates.finite_factors {I : Ideal R} (hI :
 I != 0) : forallᶠ v : HeightOneSpectrum R in Filter.cofinite, ((Associates.mk v
.asIdeal).count…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing.eq_1`：∀ {R : Type u_1}
 [inst : CommRing R] [inst_1 : IsDedekindDomain R] (v : IsDedekindDomain.HeightO
neSpectrum R)   (I : Ideal R), v.maxPowDivid…
· 使用定理 `Int.natCast_eq_zero`：∀ {n : ℕ}, ↑n = 0 ↔ n = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1

--- 原说明 ---
For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` s
uch that
  `v^(val_v(I))` is not the unit ideal.
-/
theorem hasFiniteMulSupport {I : Ideal R} (hI : I ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.maxPowDividing I :=
  haveI h_subset : {v : HeightOneSpectrum R | v.maxPowDividing I ≠ 1} ⊆
      {v : HeightOneSpectrum R |
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) ≠ 0} := by
    intro v hv h_zero
    have hv' : v.maxPowDividing I = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, Int.natCast_eq_zero.mp h_zero,
        pow_zero _]
    exact hv hv'
  Finite.subset (Filter.eventually_cofinite.mp (Associates.finite_factors hI)) h_subset

@[deprecated (since := "2026-03-03")] alias finite_mulSupport := hasFiniteMulSupport

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`. -/
@[fun_prop]
/-
**Ideal.hasFiniteMulSupport_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：hasFiniteMulSupport_coe {I : Ideal R} (hI : I != 0) : HasFiniteMulSupport 
fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^ ((Associates
.mk v.asIdeal).count (Associates.mk I).factors : Int)
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.HasFiniteMulSupport.eq_1`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] (f : α → M),   Function.HasFiniteMulSupport f = (Function.mulSupport f
).Finite
· 使用定理 `Function.mulSupport.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : One M]
 (f : ι → M), Function.mulSupport f = {x | f x ≠ 1}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.hasFiniteMulSupport`：hasFiniteMulSupport {I : Ideal R} (hI : I != 
0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I

--- 原说明 ---
For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` s
uch that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`.
-/
theorem hasFiniteMulSupport_coe {I : Ideal R} (hI : I ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) := by
  rw [HasFiniteMulSupport, mulSupport]
  simp_rw [Ne, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_eq_one]
  exact hasFiniteMulSupport hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_coe := hasFiniteMulSupport_coe

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
@[fun_prop]
/-
**Ideal.hasFiniteMulSupport_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：hasFiniteMulSupport_inv {I : Ideal R} (hI : I != 0) : HasFiniteMulSupport 
fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^ (-((Associat
es.mk v.asIdeal).count (Associates.mk I).factors : Int))
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.HasFiniteMulSupport.eq_1`：∀ {α : Type u_1} {M : Type u_2} [inst
 : One M] (f : α → M),   Function.HasFiniteMulSupport f = (Function.mulSupport f
).Finite
· 使用定理 `Function.mulSupport.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : One M]
 (f : ι → M), Function.mulSupport f = {x | f x ≠ 1}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Ideal.hasFiniteMulSupport_coe`：hasFiniteMulSupport_coe {I : Ideal R} (hI
 : I != 0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => (v.asIdeal : Fra
ctionalIdeal R⁰ K) …

--- 原说明 ---
For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` s
uch that
`v^-(val_v(I))` is not the unit ideal.
-/
theorem hasFiniteMulSupport_inv {I : Ideal R} (hI : I ≠ 0) :
    HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^
      (-((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ)) := by
  rw [HasFiniteMulSupport, mulSupport]
  simp_rw [zpow_neg, Ne, inv_eq_one]
  exact hasFiniteMulSupport_coe hI

@[deprecated (since := "2026-03-03")] alias finite_mulSupport_inv := hasFiniteMulSupport_inv

/-- For every nonzero ideal `I` of `v`, `v^(val_v(I) + 1)` does not divide `∏_v v^(val_v(I))`. -/
/-
**Ideal.finprod_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：finprod_not_dvd (I : Ideal R) (hI : I != 0) : ¬v.asIdeal ^ ((Associates.mk
 v.asIdeal).count (Associates.mk I).factors + 1) ∣ ∏ᶠ v : HeightOneSpectrum R, v
.maxPowDividing I
参数：I : Ideal R；hI : I != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.hasFiniteMulSupport`：hasFiniteMulSupport {I : Ideal R} (hI : I != 
0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_finprod_cond_ne`：mul_finprod_cond_ne (a : α) (hf : HasFiniteMulSuppo
rt f) : (f a * ∏ᶠ (i) (_ : i != a), f i) = ∏ᶠ i, f i
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `finprod_cond_ne`：finprod_cond_ne (f : α -> M) (a : α) [DecidableEq α] (h
f : HasFiniteMulSupport f) : (∏ᶠ (i) (_ : i != a), f i) = ∏ i in hf.toFinset.era
se a,…
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Prime.exists_mem_finset_dvd`：exists_mem_finset_dvd (hp : Prime p) {s : F
inset ι} {f : ι -> M₀} : p ∣ s.prod f -> exists i in s, p ∣ f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ext`：∀ {R : Type u_1} {inst : CommRin
g R} {x y : IsDedekindDomain.HeightOneSpectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Prime.dvd_prime_iff_associated`：Prime.dvd_prime_iff_associated [CommMono
idWithZero M] [IsCancelMulZero M] {p q : M} (pp : Prime p) (qp : Prime q) : p ∣ 
q ↔ Associated p q

--- 原说明 ---
For every nonzero ideal `I` of `v`, `v^(val_v(I) + 1)` does not divide `∏_v v^(v
al_v(I))`.
-/
theorem finprod_not_dvd (I : Ideal R) (hI : I ≠ 0) :
    ¬v.asIdeal ^ ((Associates.mk v.asIdeal).count (Associates.mk I).factors + 1) ∣
        ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I := by
  classical
  have hf := hasFiniteMulSupport hI
  have h_ne_zero : v.maxPowDividing I ≠ 0 := pow_ne_zero _ v.ne_bot
  rw [← mul_finprod_cond_ne v hf, pow_add, pow_one, finprod_cond_ne _ _ hf]
  intro h_contr
  have hv_prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  obtain ⟨w, hw, hvw'⟩ :=
    Prime.exists_mem_finset_dvd hv_prime ((mul_dvd_mul_iff_left h_ne_zero).mp h_contr)
  have hw_prime : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hvw := Prime.dvd_of_dvd_pow hv_prime hvw'
  rw [Prime.dvd_prime_iff_associated hv_prime hw_prime, associated_iff_eq] at hvw
  exact (Finset.mem_erase.mp hw).1 (HeightOneSpectrum.ext hvw.symm)

end Ideal

/-
**Associates.finprod_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Associates.finprod_ne_zero (I : Ideal R) : Associates.mk (∏ᶠ v : HeightOne
Spectrum R, v.maxPowDividing I) != 0
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `finprod_def`：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)
] : ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i els
e…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Submodule.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] {A : Ty
pe v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTow
er R A A] [NoZeroD…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem Associates.finprod_ne_zero (I : Ideal R) :
    Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I) ≠ 0 := by
  classical
  rw [Associates.mk_ne_zero, finprod_def]
  split_ifs
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    apply pow_ne_zero _ v.ne_bot
  · exact one_ne_zero

namespace Ideal

/-- The multiplicity of `v` in `∏_v v^(val_v(I))` equals `val_v(I)`. -/
/-
**Ideal.finprod_count** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：finprod_count (I : Ideal R) (hI : I != 0) : (Associates.mk v.asIdeal).coun
t (Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I)).factors = (As
sociates.mk v.asIdeal).count (Associates.mk I).factors
参数：I : Ideal R；hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associates.finprod_ne_zero`：Associates.finprod_ne_zero (I : Ideal R) : A
ssociates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I) != 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `finprod_mem_dvd`：finprod_mem_dvd {f : α -> N} (a : α) (hf : HasFiniteMul
Support f) : f a ∣ finprod f
· 使用定理 `Ideal.hasFiniteMulSupport`：hasFiniteMulSupport {I : Ideal R} (hI : I != 
0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.finprod_not_dvd`：finprod_not_dvd (I : Ideal R) (hI : I != 0) : ¬v.
asIdeal ^ ((Associates.mk v.asIdeal).count (Associates.mk I).factors + 1) ∣ ∏ᶠ v
 : HeightOn…
· 使用定理 `Nat.eq_of_le_of_lt_succ`：∀ {n m : ℕ}, n ≤ m → m < n + 1 → m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Associates.prime_pow_dvd_iff_le`：prime_pow_dvd_iff_le {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= count p m.fa
ctors
· 使用定理 `Associates.mk_pow`：mk_pow (a : M) (n : Nat) : Associates.mk (a ^ n) = As
sociates.mk a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_dvd_mk`：mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates
.mk b ↔ a ∣ b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a

--- 原说明 ---
The multiplicity of `v` in `∏_v v^(val_v(I))` equals `val_v(I)`.
-/
theorem finprod_count (I : Ideal R) (hI : I ≠ 0) : (Associates.mk v.asIdeal).count
    (Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I)).factors =
    (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  have h_ne_zero := Associates.finprod_ne_zero I
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have h_dvd := finprod_mem_dvd v (hasFiniteMulSupport hI)
  have h_not_dvd := Ideal.finprod_not_dvd v I hI
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at h_dvd h_ne_zero h_not_dvd
  rw [← Associates.mk_dvd_mk] at h_dvd h_not_dvd
  simp only [Associates.dvd_eq_le] at h_dvd h_not_dvd
  rw [Associates.mk_pow, Associates.prime_pow_dvd_iff_le h_ne_zero hv] at h_dvd h_not_dvd
  rw [not_le] at h_not_dvd
  apply Nat.eq_of_le_of_lt_succ h_dvd h_not_dvd

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`. -/
/-
**Ideal.finprod_heightOneSpectrum_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：finprod_heightOneSpectrum_factorization {I : Ideal R} (hI : I != 0) : ∏ᶠ v
 : HeightOneSpectrum R, v.maxPowDividing I = I
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
· 使用定理 `Associates.eq_of_eq_counts`：eq_of_eq_counts {a b : Associates α} (ha : a
 != 0) (hb : b != 0) (h : forall p : Associates α, Irreducible p -> p.count a.fa
ctors = p.count …
· 使用定理 `Associates.finprod_ne_zero`：Associates.finprod_ne_zero (I : Ideal R) : A
ssociates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I) != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `Associates.exists_rep`：exists_rep [Monoid M] (a : Associates M) : exists
 a0 : M, Associates.mk a0 = a
· 使用定理 `Ideal.finprod_count`：finprod_count (I : Ideal R) (hI : I != 0) : (Associ
ates.mk v.asIdeal).count (Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDiv
iding I))…
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0

--- 原说明 ---
The ideal `I` equals the finprod `∏_v v^(val_v(I))`.
-/
theorem finprod_heightOneSpectrum_factorization {I : Ideal R} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I = I := by
  rw [← associated_iff_eq, ← Associates.mk_eq_mk_iff_associated]
  apply Associates.eq_of_eq_counts
  · apply Associates.finprod_ne_zero I
  · apply Associates.mk_ne_zero.mpr hI
  intro v hv
  obtain ⟨J, hJv⟩ := Associates.exists_rep v
  rw [← hJv, Associates.irreducible_mk] at hv
  rw [← hJv]
  apply Ideal.finprod_count
    ⟨J, Ideal.isPrime_of_prime (irreducible_iff_prime.mp hv), Irreducible.ne_zero hv⟩ I hI

set_option backward.isDefEq.respectTransparency.types false in
/-- The ideal `I` equals the inf `⨅_v v^(val_v(I))`. -/
/-
**Ideal.iInf_maxPowDividing_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：iInf_maxPowDividing_eq {I : Ideal R} (h0 : I != 0) : ⨅ i : HeightOneSpectr
um R, i.maxPowDividing I = I
参数：h0 : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.finprod_heightOneSpectrum_factorization`：finprod_heightOneSpectrum
_factorization {I : Ideal R} (hI : I != 0) : ∏ᶠ v : HeightOneSpectrum R, v.maxPo
wDividing I = I
· 使用定理 `finprod_def`：finprod_def (f : α -> M) [Decidable (HasFiniteMulSupport f)
] : ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i in h.toFinset, f i els
e…
· 使用定理 `Ideal.hasFiniteMulSupport`：hasFiniteMulSupport {I : Ideal R} (hI : I != 
0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Ideal.prod_eq_iInf_of_pairwise_isCoprime`：prod_eq_iInf_of_pairwise_isCop
rime {s : Finset ι} {J : ι -> Ideal R} (hp : (s : Set ι).Pairwise (IsCoprime on 
J)) : ∏ i in s, J i = ⨅ i in s…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne`：isCoprime_pow_of
_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) (n m : Nat) : IsCoprime (P.asIdea
l ^ n) (Q.asIdeal ^ m)
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The ideal `I` equals the inf `⨅_v v^(val_v(I))`.
-/
theorem iInf_maxPowDividing_eq {I : Ideal R} (h0 : I ≠ 0) :
    ⨅ i : HeightOneSpectrum R, i.maxPowDividing I = I := by
  nth_rw 2 [← Ideal.finprod_heightOneSpectrum_factorization h0]
  classical
  rw [finprod_def, dif_pos (Ideal.hasFiniteMulSupport h0), Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · ext x
    constructor
    · aesop
    · simp only [Finite.mem_toFinset, mem_mulSupport, one_eq_top, ne_eq, Submodule.mem_iInf]
      intro h i
      by_cases i.maxPowDividing I = ⊤ <;> simp_all
  · intro x hx y hy hxy
    apply IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne _ _ hxy

variable (K)

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarded as fractional
ideals of `R`. -/
/-
**Ideal.finprod_heightOneSpectrum_factorization_coe** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：finprod_heightOneSpectrum_factorization_coe {I : Ideal R} (hI : I != 0) : 
(∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ ((Associates.m
k v.asIdeal).count (Associates.mk I).factors : Int)) = I
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.finprod_heightOneSpectrum_factorization`：finprod_heightOneSpectrum
_factorization {I : Ideal R} (hI : I != 0) : ∏ᶠ v : HeightOneSpectrum R, v.maxPo
wDividing I = I
· 使用定理 `FractionalIdeal.coeIdeal_finprod`：coeIdeal_finprod [IsLocalization S P] 
{α : Sort*} {f : α -> Ideal R} (hS : S <= nonZeroDivisors R) : ((∏ᶠ a : α, f a :
 Ideal R) : Fractional…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coeIdeal_pow`：coeIdeal_pow (I : Ideal R) (n : Nat) : ↑(I
 ^ n) = (I : FractionalIdeal S P) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarde
d as fractional
ideals of `R`.
-/
theorem finprod_heightOneSpectrum_factorization_coe {I : Ideal R} (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ)) = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, FractionalIdeal.coeIdeal_pow,
    zpow_natCast]

end Ideal

/-! ### Factorization of fractional ideals of Dedekind domains -/

namespace FractionalIdeal

open Int IsLocalization

open Ideal in
/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`. -/
/-
**FractionalIdeal.finprod_heightOneSpectrum_factorization** 是 Mathlib 中的一个定理，位于命
名空间 `FractionalIdeal`。
形式化陈述：finprod_heightOneSpectrum_factorization {I : FractionalIdeal R⁰ K} (hI : I
 != 0) {a : R} {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ 
* ↑J) : ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ ((Assoc
iates.mk v.asIdeal).count (Associates.mk J).factors - (Associates.mk v.asIdeal).
count (Associates.mk (Ideal.span {a})).factors : Int) = I
参数：hI : I != 0；haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ideal_factor_ne_zero`：ideal_factor_ne_zero {R} [CommRing
 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {I : FractionalIdea
l R⁰ K} (hI : I != 0) {a :…
· 使用定理 `Ideal.finprod_heightOneSpectrum_factorization_coe`：finprod_heightOneSpec
trum_factorization_coe {I : Ideal R} (hI : I != 0) : (∏ᶠ v : HeightOneSpectrum R
, (v.asIdeal : FractionalIdeal R⁰ K) ^ …
· 使用定理 `FractionalIdeal.constant_factor_ne_zero`：constant_factor_ne_zero {R} [Co
mmRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {I : Fraction
alIdeal R⁰ K} (hI : I != 0) {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.div_spanSingleton`：div_spanSingleton (J : FractionalIdea
l R₁⁰ K) (d : K) : J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `finprod_inv_distrib`：finprod_inv_distrib [DivisionCommMonoid G] (f : α -
> G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finprod_mul_distrib`：finprod_mul_distrib (hf : HasFiniteMulSupport f) (h
g : HasFiniteMulSupport g) : ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i
· 使用定理 `Ideal.hasFiniteMulSupport_coe`：hasFiniteMulSupport_coe {I : Ideal R} (hI
 : I != 0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => (v.asIdeal : Fra
ctionalIdeal R⁰ K) …
· 使用定理 `Ideal.hasFiniteMulSupport_inv`：hasFiniteMulSupport_inv {I : Ideal R} (hI
 : I != 0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => (v.asIdeal : Fra
ctionalIdeal R⁰ K) …
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b

--- 原说明 ---
If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such t
hat
`I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`.
-/
theorem finprod_heightOneSpectrum_factorization {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) = I := by
  have hJ_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI haJ
  have hJ := Ideal.finprod_heightOneSpectrum_factorization_coe K hJ_ne_zero
  have ha_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI haJ
  have ha := Ideal.finprod_heightOneSpectrum_factorization_coe K ha_ne_zero
  rw [haJ, ← div_spanSingleton, div_eq_mul_inv, ← coeIdeal_span_singleton, ← hJ, ← ha,
    ← finprod_inv_distrib]
  simp_rw [← zpow_neg]
  rw [← finprod_mul_distrib (by fun_prop) (by fun_prop)]
  apply finprod_congr
  intro v
  rw [← zpow_add₀ ((@coeIdeal_ne_zero R _ K _ _ _ _).mpr v.ne_bot), sub_eq_add_neg]

/-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`. -/
/-
**FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction** 是
 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：finprod_heightOneSpectrum_factorization_principal_fraction {n : R} (hn : n
 != 0) (d : ↥R⁰) : ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K
) ^ ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal R)).
factors - (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑d : R)}
) : Ideal R)).factors : Int) = spanSingleton R⁰ (mk' K n d)
参数：hn : n != 0；d : ↥R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ne_zero_of_mem_nonZeroDivisors`：map_ne_zero_of_mem_nonZeroDivisors [
Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F) (hg : Injective (g : M₀ -> M₀')) 
{x : M₀} (h : x in M₀⁰) …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_ne_zero_iff`：spanSingleton_ne_zero_iff {y 
: P} : spanSingleton S y != 0 ↔ y != 0
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `div_eq_zero_iff`：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `FractionalIdeal.finprod_heightOneSpectrum_factorization`：finprod_heightO
neSpectrum_factorization {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : I
deal R} (haJ : I = spanSingleton R⁰ ((algebra…

--- 原说明 ---
For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`.
-/
theorem finprod_heightOneSpectrum_factorization_principal_fraction {n : R} (hn : n ≠ 0) (d : ↥R⁰) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑d : R)}) :
        Ideal R)).factors : ℤ) = spanSingleton R⁰ (mk' K n d) := by
  have hd_ne_zero : (algebraMap R K) (d : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have h0 : spanSingleton R⁰ (mk' K n d) ≠ 0 := by
    rw [spanSingleton_ne_zero_iff, IsFractionRing.mk'_eq_div, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hn, hd_ne_zero⟩
  have hI : spanSingleton R⁰ (mk' K n d) =
      spanSingleton R⁰ ((algebraMap R K) d)⁻¹ * ↑(Ideal.span {n} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  exact finprod_heightOneSpectrum_factorization h0 hI

open Classical in
/-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`. -/
/-
**FractionalIdeal.finprod_heightOneSpectrum_factorization_principal** 是 Mathlib 
中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：finprod_heightOneSpectrum_factorization_principal {I : FractionalIdeal R⁰ 
K} (hI : I != 0) (k : K) (hk : I = spanSingleton R⁰ k) : ∏ᶠ v : HeightOneSpectru
m R, (v.asIdeal : FractionalIdeal R⁰ K) ^ ((Associates.mk v.asIdeal).count (Asso
ciates.mk (Ideal.span {choose (exists_mk'_eq R⁰ k)} : Ideal R)).factors - (Assoc
iates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑(choose (choose_spec (e
xists_mk'_eq R⁰ k)) : ↥R⁰) : R)}) : Ideal R)).factors : Int) = I
参数：hI : I != 0；k : K；hk : I = spanSingleton R⁰ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fracti
on`：finprod_heightOneSpectrum_factorization_principal_fraction {n : R} (hn : n !
= 0) (d : ↥R⁰) : ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : Fracti…

--- 原说明 ---
For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`.
-/
theorem finprod_heightOneSpectrum_factorization_principal {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (k : K) (hk : I = spanSingleton R⁰ k) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {choose
          (exists_mk'_eq R⁰ k)} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑(choose
          (choose_spec (exists_mk'_eq R⁰ k)) : ↥R⁰) : R)}) : Ideal R)).factors : ℤ) = I := by
  set n : R := choose (exists_mk'_eq R⁰ k)
  set d : ↥R⁰ := choose (choose_spec (exists_mk'_eq R⁰ k))
  have hnd : mk' K n d = k := choose_spec (choose_spec (exists_mk'_eq R⁰ k))
  have hn0 : n ≠ 0 := by
    by_contra h
    rw [← hnd, h, IsFractionRing.mk'_eq_div, map_zero, zero_div, spanSingleton_zero] at hk
    exact hI hk
  rw [finprod_heightOneSpectrum_factorization_principal_fraction hn0 d, hk, hnd]

variable (K)

open Classical in
/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`,
then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we set `val_v(I) = 0`. -/
/-
**FractionalIdeal.count** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：count (I : FractionalIdeal R⁰ K) : Int
参数：I : FractionalIdeal R⁰ K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such t
hat `I = a⁻¹J`,
then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we set `val_v(
I) = 0`.
-/
def count (I : FractionalIdeal R⁰ K) : ℤ :=
  dite (I = 0) (fun _ : I = 0 => 0) fun _ : ¬I = 0 =>
    let a := choose (exists_eq_spanSingleton_mul I)
    let J := choose (choose_spec (exists_eq_spanSingleton_mul I))
    ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ)

/-- `val_v(0) = 0`. -/
/-
**FractionalIdeal.count_zero** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_zero : count K v (0 : FractionalIdeal R⁰ K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc

--- 原说明 ---
`val_v(0) = 0`.
-/
lemma count_zero : count K v (0 : FractionalIdeal R⁰ K) = 0 := by simp only [count, dif_pos]

open Classical in
/-
**FractionalIdeal.count_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_ne_zero {I : FractionalIdeal R⁰ K} (hI : I != 0) : count K v I = ((A
ssociates.mk v.asIdeal).count (Associates.mk (choose (choose_spec (exists_eq_spa
nSingleton_mul I)))).factors - (Associates.mk v.asIdeal).count (Associates.mk (I
deal.span {choose (exists_eq_spanSingleton_mul I)})).factors : Int)
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FractionalIdeal.exists_eq_spanSingleton_mul`：exists_eq_spanSingleton_mul
 (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spa
nSingleton R₁⁰ (algebraMap R₁ K a…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma count_ne_zero {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk
      (choose (choose_spec (exists_eq_spanSingleton_mul I)))).factors -
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {choose (exists_eq_spanSingleton_mul I)})).factors : ℤ) := by
  simp only [count, dif_neg hI]

open Classical in
/-- `val_v(I)` does not depend on the choice of `a` and `J` used to represent `I`. -/
/-
**FractionalIdeal.count_well_defined** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：count_well_defined {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : I
deal R} (h_aJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) : count K v I 
= ((Associates.mk v.asIdeal).count (Associates.mk J).factors - (Associates.mk v.
asIdeal).count (Associates.mk (Ideal.span {a})).factors : Int)
参数：hI : I != 0；h_aJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.exists_eq_spanSingleton_mul`：exists_eq_spanSingleton_mul
 (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spa
nSingleton R₁⁰ (algebraMap R₁ K a…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `FractionalIdeal.ideal_factor_ne_zero`：ideal_factor_ne_zero {R} [CommRing
 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {I : FractionalIdea
l R⁰ K} (hI : I != 0) {a :…
· 使用定理 `FractionalIdeal.constant_factor_ne_zero`：constant_factor_ne_zero {R} [Co
mmRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {I : Fraction
alIdeal R⁰ K} (hI : I != 0) {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `FractionalIdeal.spanSingleton_eq_zero_iff`：spanSingleton_eq_zero_iff {y 
: P} : spanSingleton S y = 0 ↔ y = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
· 使用定理 `FractionalIdeal.count.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (K : Ty
pe u_2) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : IsFractionRing R K
] [inst_4 : IsDe…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `sub_eq_sub_iff_add_eq_add`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b
 c d : G}, a - b = c - d ↔ a + d = c + b
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Associates.count_mul`：count_mul {a : Associates α} (ha : a != 0) {b : As
sociates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) : count p (fac
tors (a * …
· 使用定理 `Associates.mk_eq_zero`：mk_eq_zero {a : M} : Associates.mk a = 0 ↔ a = 0
· 使用定理 `Associates.mk_mul_mk`：mk_mul_mk {x y : M} : Associates.mk x * Associates
.mk y = Associates.mk (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coeIdeal_injective`：coeIdeal_injective : Function.Inject
ive (fun (I : Ideal R) => (I : FractionalIdeal R⁰ K))
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
`val_v(I)` does not depend on the choice of `a` and `J` used to represent `I`.
-/
theorem count_well_defined {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) := by
  set a₁ := choose (exists_eq_spanSingleton_mul I)
  set J₁ := choose (choose_spec (exists_eq_spanSingleton_mul I))
  have h_a₁J₁ : I = spanSingleton R⁰ ((algebraMap R K) a₁)⁻¹ * ↑J₁ :=
    (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
  have h_a₁_ne_zero : a₁ ≠ 0 := (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).1
  have h_J₁_ne_zero : J₁ ≠ 0 := ideal_factor_ne_zero hI h_a₁J₁
  have h_a_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI h_aJ
  have h_J_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI h_aJ
  have h_a₁' : spanSingleton R⁰ ((algebraMap R K) a₁) ≠ 0 := by
    rw [ne_eq, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
      Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
    exact h_a₁_ne_zero
  have h_a' : spanSingleton R⁰ ((algebraMap R K) a) ≠ 0 := by
    rw [ne_eq, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
      Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h_a_ne_zero
    exact h_a_ne_zero
  have hv : Irreducible (Associates.mk v.asIdeal) := by
    exact Associates.irreducible_mk.mpr v.irreducible
  rw [h_a₁J₁, ← div_spanSingleton, ← div_spanSingleton, div_eq_div_iff h_a₁' h_a',
    ← coeIdeal_span_singleton, ← coeIdeal_span_singleton, ← coeIdeal_mul, ← coeIdeal_mul] at h_aJ
  rw [count, dif_neg hI, sub_eq_sub_iff_add_eq_add, ← natCast_add, ← natCast_add, natCast_inj,
    ← Associates.count_mul _ _ hv, ← Associates.count_mul _ _ hv, Associates.mk_mul_mk,
    Associates.mk_mul_mk, coeIdeal_injective h_aJ]
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_J_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h_a₁_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_J₁_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_a_ne_zero

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. -/
/-
**FractionalIdeal.count_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_mul {I I' : FractionalIdeal R⁰ K} (hI : I != 0) (hI' : I' != 0) : co
unt K v (I * I') = count K v I + count K v I'
参数：hI : I != 0；hI' : I' != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `FractionalIdeal.exists_eq_spanSingleton_mul`：exists_eq_spanSingleton_mul
 (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spa
nSingleton R₁⁰ (algebraMap R₁ K a…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Associates.mk_eq_zero`：mk_eq_zero {a : M} : Associates.mk a = 0 ↔ a = 0
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `FractionalIdeal.ideal_factor_ne_zero`：ideal_factor_ne_zero {R} [CommRing
 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {I : FractionalIdea
l R⁰ K} (hI : I != 0) {a :…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `FractionalIdeal.count_well_defined`：count_well_defined {I : FractionalId
eal R⁰ K} (hI : I != 0) {a : R} {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((alg
ebraMap R K) a)⁻¹ * ↑J) …
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Associates.mk_mul_mk`：mk_mul_mk {x y : M} : Associates.mk x * Associates
.mk y = Associates.mk (x * y)
· 使用定理 `Associates.count_mul`：count_mul {a : Associates α} (ha : a != 0) {b : As
sociates α} (hb : b != 0) {p : Associates α} (hp : Irreducible p) : count p (fac
tors (a * …
· 使用定理 `Ideal.span_singleton_mul_span_singleton`：span_singleton_mul_span_singlet
on (r s : R) [(span {r}).IsTwoSided] : span {r} * span {s} = (span {r * s} : Ide
al R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`.
-/
theorem count_mul {I I' : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hI' : I' ≠ 0) :
    count K v (I * I') = count K v I + count K v I' := by
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  have ha_ne_zero : Associates.mk (Ideal.span {a} : Ideal R) ≠ 0 := by
    rw [ne_eq, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  have hJ_ne_zero : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI haJ)
  obtain ⟨a', J', ha', haJ'⟩ := exists_eq_spanSingleton_mul I'
  have ha'_ne_zero : Associates.mk (Ideal.span {a'} : Ideal R) ≠ 0 := by
    rw [ne_eq, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha'
  have hJ'_ne_zero : Associates.mk J' ≠ 0 :=
    Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI' haJ')
  have h_prod : I * I' = spanSingleton R⁰ ((algebraMap R K) (a * a'))⁻¹ * ↑(J * J') := by
    rw [haJ, haJ', mul_assoc, mul_comm (J : FractionalIdeal R⁰ K), mul_assoc, ← mul_assoc,
      spanSingleton_mul_spanSingleton, coeIdeal_mul, map_mul, mul_inv,
      mul_comm (J : FractionalIdeal R⁰ K)]
  rw [count_well_defined K v hI haJ, count_well_defined K v hI' haJ',
    count_well_defined K v (mul_ne_zero hI hI') h_prod, ← Associates.mk_mul_mk,
    Associates.count_mul hJ_ne_zero hJ'_ne_zero hv, ← Ideal.span_singleton_mul_span_singleton,
    ← Associates.mk_mul_mk, Associates.count_mul ha_ne_zero ha'_ne_zero hv]
  push_cast
  ring

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. If `I` or `I'` is zero, then
`val_v(I*I') = 0`. -/
/-
**FractionalIdeal.count_mul'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_mul' (I I' : FractionalIdeal R⁰ K) [Decidable (I != 0 ∧ I' != 0)] : 
count K v (I * I') = if I != 0 ∧ I' != 0 then count K v I + count K v I' else 0
参数：I I' : FractionalIdeal R⁰ K；I != 0 ∧ I' != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `FractionalIdeal.count_mul`：count_mul {I I' : FractionalIdeal R⁰ K} (hI :
 I != 0) (hI' : I' != 0) : count K v (I * I') = count K v I + count K v I'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `FractionalIdeal.count_zero`：count_zero : count K v (0 : FractionalIdeal 
R⁰ K) = 0

--- 原说明 ---
For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. If `I` or `I'` is zer
o, then
`val_v(I*I') = 0`.
-/
theorem count_mul' (I I' : FractionalIdeal R⁰ K) [Decidable (I ≠ 0 ∧ I' ≠ 0)] :
    count K v (I * I') = if I ≠ 0 ∧ I' ≠ 0 then count K v I + count K v I' else 0 := by
  split_ifs with h
  · exact count_mul K v h.1 h.2
  · rw [← mul_ne_zero_iff, not_ne_iff] at h
    rw [h, count_zero]

/-- `val_v(1) = 0`. -/
/-
**FractionalIdeal.count_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_one : count K v (1 : FractionalIdeal R⁰ K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `FractionalIdeal.coeIdeal_top`：coeIdeal_top : ((⊤ : Ideal R) : Fractional
Ideal S P) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
· 使用定理 `FractionalIdeal.count_well_defined`：count_well_defined {I : FractionalId
eal R⁰ K} (hI : I != 0) {a : R} {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((alg
ebraMap R K) a)⁻¹ * ↑J) …
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
`val_v(1) = 0`.
-/
theorem count_one : count K v (1 : FractionalIdeal R⁰ K) = 0 := by
  have h1 : (1 : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one, Ideal.one_eq_top, coeIdeal_top, mul_one, inv_one,
      spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1, Ideal.span_singleton_one, Ideal.one_eq_top, sub_self]
/-
**FractionalIdeal.count_prod** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_prod {ι} (s : Finset ι) (I : ι -> FractionalIdeal R⁰ K) (hS : forall
 i in s, I i != 0) : count K v (∏ i in s, I i) = ∑ i in s, count K v (I i)
参数：s : Finset ι；I : ι -> FractionalIdeal R⁰ K；hS : forall i in s, I i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `FractionalIdeal.count_one`：count_one : count K v (1 : FractionalIdeal R⁰
 K) = 0
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `FractionalIdeal.count_mul`：count_mul {I I' : FractionalIdeal R⁰ K} (hI :
 I != 0) (hI' : I' != 0) : count K v (I * I') = count K v I + count K v I'
-/
theorem count_prod {ι} (s : Finset ι) (I : ι → FractionalIdeal R⁰ K) (hS : ∀ i ∈ s, I i ≠ 0) :
    count K v (∏ i ∈ s, I i) = ∑ i ∈ s, count K v (I i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, count_one]
  | insert i s hi hrec =>
    have hS' : ∀ i ∈ s, I i ≠ 0 := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hS0 : ∏ i ∈ s, I i ≠ 0 := Finset.prod_ne_zero_iff.mpr hS'
    have hi0 : I i ≠ 0 := hS i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, count_mul K v hi0 hS0, hrec hS']

/-- For every `n ∈ ℕ` and every ideal `I`, `val_v(I^n) = n*val_v(I)`. -/
/-
**FractionalIdeal.count_pow** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_pow (n : Nat) (I : FractionalIdeal R⁰ K) : count K v (I ^ n) = n * c
ount K v I
参数：n : Nat；I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `FractionalIdeal.count_one`：count_one : count K v (1 : FractionalIdeal R⁰
 K) = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `FractionalIdeal.count_mul'`：count_mul' (I I' : FractionalIdeal R⁰ K) [De
cidable (I != 0 ∧ I' != 0)] : count K v (I * I') = if I != 0 ∧ I' != 0 then coun
t K v I + count …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `FractionalIdeal.count_zero`：count_zero : count K v (0 : FractionalIdeal 
R⁰ K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
For every `n ∈ ℕ` and every ideal `I`, `val_v(I^n) = n*val_v(I)`.
-/
theorem count_pow (n : ℕ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  induction n with
  | zero => rw [pow_zero, ofNat_zero, zero_mul, count_one]
  | succ n h =>
    classical rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ^ n ≠ 0 ∧ I ≠ 0) := by order
      rw [if_neg h_neg, hI, count_zero, mul_zero]
    · rw [if_pos (And.intro (pow_ne_zero n hI) hI), h, Nat.cast_add,
        Nat.cast_one]
      ring

/-- `val_v(v) = 1`, when `v` is regarded as a fractional ideal. -/
/-
**FractionalIdeal.count_self** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_self : count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `FractionalIdeal.count_well_defined`：count_well_defined {I : FractionalId
eal R⁰ K} (hI : I != 0) {a : R} {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((alg
ebraMap R K) a)⁻¹ * ↑J) …
· 使用定理 `Associates.count_self`：count_self [Nontrivial α] {p : Associates α} (hp 
: Irreducible p) : p.count p.factors = 1
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Associates.mk_one`：mk_one [Monoid M] : Associates.mk (1 : M) = 1
· 使用定理 `Associates.factors_one`：factors_one [Nontrivial α] : factors (1 : Associ
ates α) = 0
· 使用定理 `Associates.count_zero`：count_zero (hp : Irreducible p) : count p (0 : Fa
ctorSet α) = 0
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Int.ofNat_one`：↑1 = 1

--- 原说明 ---
`val_v(v) = 1`, when `v` is regarded as a fractional ideal.
-/
theorem count_self : count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1 := by
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have h_self : (v.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑v.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hv_irred : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  rw [count_well_defined K v hv h_self, Associates.count_self hv_irred,
    Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero hv_irred, ofNat_zero, sub_zero, ofNat_one]

/-- `val_v(v^n) = n` for every `n ∈ ℕ`. -/
/-
**FractionalIdeal.count_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_pow_self (n : Nat) : count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^
 n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.count_pow`：count_pow (n : Nat) (I : FractionalIdeal R⁰ K
) : count K v (I ^ n) = n * count K v I
· 使用定理 `FractionalIdeal.count_self`：count_self : count K v (v.asIdeal : Fraction
alIdeal R⁰ K) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
`val_v(v^n) = n` for every `n ∈ ℕ`.
-/
theorem count_pow_self (n : ℕ) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_pow, count_self, mul_one]

/-- `val_v(I⁻ⁿ) = -val_v(Iⁿ)` for every `n ∈ ℤ`. -/
/-
**FractionalIdeal.count_neg_zpow** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_neg_zpow (n : Int) (I : FractionalIdeal R⁰ K) : count K v (I ^ (-n))
 = -count K v (I ^ n)
参数：n : Int；I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `FractionalIdeal.count_one`：count_one : count K v (1 : FractionalIdeal R⁰
 K) = 0
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `FractionalIdeal.count_zero`：count_zero : count K v (0 : FractionalIdeal 
R⁰ K) = 0
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.count_mul`：count_mul {I I' : FractionalIdeal R⁰ K} (hI :
 I != 0) (hI' : I' != 0) : count K v (I * I') = count K v I + count K v I'
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
`val_v(I⁻ⁿ) = -val_v(Iⁿ)` for every `n ∈ ℤ`.
-/
theorem count_neg_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ (-n)) = -count K v (I ^ n) := by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀ hI, neg_add_cancel, zpow_zero]
    exact count_one K v
/-
**FractionalIdeal.count_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_inv (I : FractionalIdeal R⁰ K) : count K v (I⁻¹) = -count K v I
参数：I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_neg_one`：zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹
· 使用定理 `FractionalIdeal.count_neg_zpow`：count_neg_zpow (n : Int) (I : Fractional
Ideal R⁰ K) : count K v (I ^ (-n)) = -count K v (I ^ n)
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
-/
theorem count_inv (I : FractionalIdeal R⁰ K) :
    count K v (I⁻¹) = -count K v I := by
  rw [← zpow_neg_one, count_neg_zpow K v (1 : ℤ) I, zpow_one]

/-- `val_v(Iⁿ) = n*val_v(I)` for every `n ∈ ℤ`. -/
/-
**FractionalIdeal.count_zpow** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_zpow (n : Int) (I : FractionalIdeal R⁰ K) : count K v (I ^ n) = n * 
count K v I
参数：n : Int；I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `FractionalIdeal.count_pow`：count_pow (n : Nat) (I : FractionalIdeal R⁰ K
) : count K v (I ^ n) = n * count K v I
· 使用定理 `Int.negSucc_eq`：∀ (n : ℕ), Int.negSucc n = -(↑n + 1)
· 使用定理 `FractionalIdeal.count_neg_zpow`：count_neg_zpow (n : Int) (I : Fractional
Ideal R⁰ K) : count K v (I ^ (-n)) = -count K v (I ^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_succ`：∀ (n : ℕ), ↑n.succ = ↑n + 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n

--- 原说明 ---
`val_v(Iⁿ) = n*val_v(I)` for every `n ∈ ℤ`.
-/
theorem count_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  obtain n | n := n
  · rw [ofNat_eq_natCast, zpow_natCast]
    exact count_pow K v n I
  · rw [negSucc_eq, count_neg_zpow, ← Int.natCast_succ, zpow_natCast, count_pow]
    ring

/-- `val_v(v^n) = n` for every `n ∈ ℤ`. -/
/-
**FractionalIdeal.count_zpow_self** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_zpow_self (n : Int) : count K v ((v.asIdeal : FractionalIdeal R⁰ K) 
^ n) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.count_zpow`：count_zpow (n : Int) (I : FractionalIdeal R⁰
 K) : count K v (I ^ n) = n * count K v I
· 使用定理 `FractionalIdeal.count_self`：count_self : count K v (v.asIdeal : Fraction
alIdeal R⁰ K) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
`val_v(v^n) = n` for every `n ∈ ℤ`.
-/
theorem count_zpow_self (n : ℤ) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_zpow, count_self, mul_one]

/-- If `v ≠ w` are two maximal ideals of `R`, then `val_v(w) = 0`. -/
/-
**FractionalIdeal.count_maximal_coprime** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：count_maximal_coprime {w : HeightOneSpectrum R} (hw : w != v) : count K v 
(w.asIdeal : FractionalIdeal R⁰ K) = 0
参数：hw : w != v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
· 使用定理 `FractionalIdeal.count_well_defined`：count_well_defined {I : FractionalId
eal R⁰ K} (hI : I != 0) {a : R} {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((alg
ebraMap R K) a)⁻¹ * ↑J) …
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Associates.mk_one`：mk_one [Monoid M] : Associates.mk (1 : M) = 1
· 使用定理 `Associates.factors_one`：factors_one [Nontrivial α] : factors (1 : Associ
ates α) = 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Associates.count_zero`：count_zero (hp : Irreducible p) : count p (0 : Fa
ctorSet α) = 0
· 使用定理 `Int.ofNat_zero`：↑0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Int.natCast_eq_zero`：∀ {n : ℕ}, ↑n = 0 ↔ n = 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Associates.factors_prime_pow`：factors_prime_pow [Nontrivial α] {p : Asso
ciates α} (hp : Irreducible p) (k : Nat) : factors (p ^ k) = WithTop.some (Multi
set.replicate k ⟨p…
· 使用定理 `Associates.count_some`：count_some (hp : Irreducible p) (s : Multiset _) 
: count p (WithTop.some s) = s.count ⟨p, hp⟩
· 使用定理 `Multiset.replicate_one`：replicate_one (a : α) : replicate 1 a = {a}
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用定理 `Multiset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Multiset α
) ↔ b = a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `v ≠ w` are two maximal ideals of `R`, then `val_v(w) = 0`.
-/
theorem count_maximal_coprime {w : HeightOneSpectrum R} (hw : w ≠ v) :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = 0 := by
  have hw_fact : (w.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑w.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hw_ne_zero : (w.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
    coeIdeal_ne_zero.mpr w.ne_bot
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  have hw' : Irreducible (Associates.mk w.asIdeal) := by apply w.associates_irreducible
  rw [count_well_defined K v hw_ne_zero hw_fact, Ideal.span_singleton_one, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one, Associates.count_zero hv, ofNat_zero, sub_zero,
    natCast_eq_zero, ← pow_one (Associates.mk w.asIdeal), Associates.factors_prime_pow hw',
    Associates.count_some hv, Multiset.replicate_one, Multiset.count_eq_zero,
    Multiset.mem_singleton]
  simp only [Subtype.mk.injEq]
  rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq, ← HeightOneSpectrum.ext_iff]
  exact Ne.symm hw
/-
**FractionalIdeal.count_maximal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_maximal (w : HeightOneSpectrum R) [Decidable (w = v)] : count K v (w
.asIdeal : FractionalIdeal R⁰ K) = if w = v then 1 else 0
参数：w : HeightOneSpectrum R；w = v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `FractionalIdeal.count_self`：count_self : count K v (v.asIdeal : Fraction
alIdeal R⁰ K) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `FractionalIdeal.count_maximal_coprime`：count_maximal_coprime {w : Height
OneSpectrum R} (hw : w != v) : count K v (w.asIdeal : FractionalIdeal R⁰ K) = 0
-/
theorem count_maximal (w : HeightOneSpectrum R) [Decidable (w = v)] :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = if w = v then 1 else 0 := by
  split_ifs with h
  · rw [h, count_self]
  · exact count_maximal_coprime K v h

/-- `val_v(∏_{w ≠ v} w^{exps w}) = 0`. -/
/-
**FractionalIdeal.count_finprod_coprime** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：count_finprod_coprime (exps : HeightOneSpectrum R -> Int) : count K v (∏ᶠ 
(w : HeightOneSpectrum R) (_ : w != v), (w.asIdeal : (FractionalIdeal R⁰ K)) ^ e
xps w) = 0
参数：exps : HeightOneSpectrum R -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_mem_induction`：finprod_mem_induction (p : M -> Prop) (hp₀ : p 1)
 (hp₁ : forall x y, p x -> p y -> p (x * y)) (hp₂ : forall x in s, p <| f x) : p
 (∏ᶠ i in s…
· 使用定理 `FractionalIdeal.count_one`：count_one : count K v (1 : FractionalIdeal R⁰
 K) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.count_mul'`：count_mul' (I I' : FractionalIdeal R⁰ K) [De
cidable (I != 0 ∧ I' != 0)] : count K v (I * I') = if I != 0 ∧ I' != 0 then coun
t K v I + count …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `FractionalIdeal.count_zpow`：count_zpow (n : Int) (I : FractionalIdeal R⁰
 K) : count K v (I ^ n) = n * count K v I
· 使用定理 `FractionalIdeal.count_maximal_coprime`：count_maximal_coprime {w : Height
OneSpectrum R} (hw : w != v) : count K v (w.asIdeal : FractionalIdeal R⁰ K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
`val_v(∏_{w ≠ v} w^{exps w}) = 0`.
-/
theorem count_finprod_coprime (exps : HeightOneSpectrum R → ℤ) :
    count K v (∏ᶠ (w : HeightOneSpectrum R) (_ : w ≠ v),
      (w.asIdeal : (FractionalIdeal R⁰ K)) ^ exps w) = 0 := by
  apply finprod_mem_induction fun I => count K v I = 0
  · exact count_one K v
  · intro I I' hI hI'
    classical
    by_cases h : I ≠ 0 ∧ I' ≠ 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow, count_maximal_coprime K v hw, mul_zero]
/-
**FractionalIdeal.count_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_finsuppProd (exps : HeightOneSpectrum R ->₀ Int) : count K v (exps.p
rod (HeightOneSpectrum.asIdeal · ^ ·)) = exps v
参数：exps : HeightOneSpectrum R ->₀ Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `FractionalIdeal.count_prod`：count_prod {ι} (s : Finset ι) (I : ι -> Frac
tionalIdeal R⁰ K) (hS : forall i in s, I i != 0) : count K v (∏ i in s, I i) = ∑
 i in s, count K…
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `FractionalIdeal.count_zpow`：count_zpow (n : Int) (I : FractionalIdeal R⁰
 K) : count K v (I ^ n) = n * count K v I
· 使用定理 `FractionalIdeal.count_maximal`：count_maximal (w : HeightOneSpectrum R) [
Decidable (w = v)] : count K v (w.asIdeal : FractionalIdeal R⁰ K) = if w = v the
n 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem count_finsuppProd (exps : HeightOneSpectrum R →₀ ℤ) :
    count K v (exps.prod (HeightOneSpectrum.asIdeal · ^ ·)) = exps v := by
  rw [Finsupp.prod, count_prod]
  · classical simp only [count_zpow, count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      exps.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, @eq_comm ℤ 0, imp_self]
  · exact fun v hv ↦ zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `exps` is finitely supported, then `val_v(∏_w w^{exps w}) = exps v`. -/
/-
**FractionalIdeal.count_finprod** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_finprod (exps : HeightOneSpectrum R -> Int) (h_exps : forallᶠ v : He
ightOneSpectrum R in Filter.cofinite, exps v = 0) : count K v (∏ᶠ v : HeightOneS
pectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ exps v) = exps v
参数：exps : HeightOneSpectrum R -> Int；h_exps : forallᶠ v : HeightOneSpectrum R in
 Filter.cofinite, exps v = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_finsetProd_of_mulSupport_subset`：finprod_eq_finsetProd_of_mul
Support_subset (f : α -> M) {s : Finset α} (h : mulSupport f subseteq (s : Set α
)) : ∏ᶠ i, f i = ∏ i in s, f i
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `FractionalIdeal.count_finsuppProd`：count_finsuppProd (exps : HeightOneSp
ectrum R ->₀ Int) : count K v (exps.prod (HeightOneSpectrum.asIdeal · ^ ·)) = ex
ps v

--- 原说明 ---
If `exps` is finitely supported, then `val_v(∏_w w^{exps w}) = exps v`.
-/
theorem count_finprod (exps : HeightOneSpectrum R → ℤ)
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    count K v (∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ exps v) = exps v := by
  convert! count_finsuppProd K v (Finsupp.mk h_exps.toFinset exps (fun _ ↦ h_exps.mem_toFinset))
  rw [finprod_eq_finsetProd_of_mulSupport_subset (s := h_exps.toFinset), Finsupp.prod]
  · rfl
  · rw [Finite.coe_toFinset]
    intro v hv h
    rw [mem_mulSupport, h, zpow_zero] at hv
    exact hv (Eq.refl 1)
/-
**FractionalIdeal.count_coe** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_coe {J : Ideal R} (hJ : J != 0) : count K v J = (Associates.mk v.asI
deal).count (Associates.mk J).factors
参数：hJ : J != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.count_well_defined`：count_well_defined {I : FractionalId
eal R⁰ K} (hI : I != 0) {a : R} {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((alg
ebraMap R K) a)⁻¹ * ↑J) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FractionalIdeal.spanSingleton.congr_simp`：∀ {R : Type u_5} [inst : CommR
ing R] (S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra 
R P]   [inst_3 : IsLocalizatio…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `sub_eq_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = a ↔
 b = 0
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Associates.mk_one`：mk_one [Monoid M] : Associates.mk (1 : M) = 1
· 使用定理 `Associates.factors_one`：factors_one [Nontrivial α] : factors (1 : Associ
ates α) = 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Associates.count_zero`：count_zero (hp : Irreducible p) : count p (0 : Fa
ctorSet α) = 0
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.associates_irreducible`：associates_ir
reducible : Irreducible Associates.mk v.asIdeal
-/
theorem count_coe {J : Ideal R} (hJ : J ≠ 0) :
    count K v J = (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  rw [count_well_defined K (J := J) (a := 1), Ideal.span_singleton_one, sub_eq_self,
    Nat.cast_eq_zero, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero v.associates_irreducible]
  · simpa only [ne_eq, coeIdeal_eq_zero]
  · simp only [map_one, inv_one, spanSingleton_one, one_mul]
/-
**FractionalIdeal.count_coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_coe_nonneg (J : Ideal R) : 0 <= count K v J
参数：J : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.count.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] (
K : Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : IsFractionRi
ng R K] [inst_4 : IsDe…
· 使用引理 `FractionalIdeal.count_zero`：count_zero : count K v (0 : FractionalIdeal 
R⁰ K) = 0
· 使用定理 `FractionalIdeal.count_coe`：count_coe {J : Ideal R} (hJ : J != 0) : count
 K v J = (Associates.mk v.asIdeal).count (Associates.mk J).factors
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem count_coe_nonneg (J : Ideal R) : 0 ≤ count K v J := by
  by_cases hJ : J = 0
  · simp only [hJ, Submodule.zero_eq_bot, coeIdeal_bot, count_zero, le_refl]
  · classical simp only [count_coe K v hJ, Nat.cast_nonneg]
/-
**FractionalIdeal.count_mono** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：count_mono {I J} (hI : I != 0) (h : I <= J) : count K v J <= count K v I
参数：hI : I != 0；h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.le_zero_iff`：le_zero_iff {I : FractionalIdeal S P} : I <
= 0 ↔ I = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `FractionalIdeal.instMulLeftMono`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   M
ulLeftMono (Fractiona…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.le_one_iff_exists_coeIdeal`：le_one_iff_exists_coeIdeal {
J : FractionalIdeal S P} : J <= (1 : FractionalIdeal S P) ↔ exists I : Ideal R, 
↑I = J
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `FractionalIdeal.count_mul`：count_mul {I I' : FractionalIdeal R⁰ K} (hI :
 I != 0) (hI' : I' != 0) : count K v (I * I') = count K v I + count K v I'
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `le_add_iff_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_
1 : LE α] [AddLeftMono α] [AddLeftReflectLE α] (a : α) {b : α},   a ≤ a + b ↔ 0 
≤ b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `FractionalIdeal.count_coe_nonneg`：count_coe_nonneg (J : Ideal R) : 0 <= 
count K v J
-/
theorem count_mono {I J} (hI : I ≠ 0) (h : I ≤ J) : count K v J ≤ count K v I := by
  by_cases hJ : J = 0
  · exact (hI (FractionalIdeal.le_zero_iff.mp (h.trans hJ.le))).elim
  have := mul_le_mul_right h J⁻¹
  rw [inv_mul_cancel₀ hJ, FractionalIdeal.le_one_iff_exists_coeIdeal] at this
  obtain ⟨J', hJ'⟩ := this
  rw [← mul_inv_cancel_left₀ hJ I, ← hJ', count_mul K v hJ, le_add_iff_nonneg_right]
  · exact count_coe_nonneg K v J'
  · exact hJ' ▸ mul_ne_zero (inv_ne_zero hJ) hI

/-- If `I` is a nonzero fractional ideal, then `I` is equal to the product `∏_v v^(count K v I)`. -/
/-
**FractionalIdeal.finprod_heightOneSpectrum_factorization'** 是 Mathlib 中的一个定理，位于
命名空间 `FractionalIdeal`。
形式化陈述：finprod_heightOneSpectrum_factorization' {I : FractionalIdeal R⁰ K} (hI : 
I != 0) : ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (coun
t K v I) = I
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.exists_eq_spanSingleton_mul`：exists_eq_spanSingleton_mul
 (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spa
nSingleton R₁⁰ (algebraMap R₁ K a…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.finprod_heightOneSpectrum_factorization`：finprod_heightO
neSpectrum_factorization {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : I
deal R} (haJ : I = spanSingleton R⁰ ((algebra…
· 使用定理 `finprod_congr`：finprod_congr {f g : α -> M} (h : forall x, f x = g x) : 
finprod f = finprod g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `FractionalIdeal.count_ne_zero`：count_ne_zero {I : FractionalIdeal R⁰ K} 
(hI : I != 0) : count K v I = ((Associates.mk v.asIdeal).count (Associates.mk (c
hoose (choose_spec …

--- 原说明 ---
If `I` is a nonzero fractional ideal, then `I` is equal to the product `∏_v v^(c
ount K v I)`.
-/
theorem finprod_heightOneSpectrum_factorization' {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (count K v I) = I := by
  have h := (Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).2
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization hI h]
  apply finprod_congr
  intro w
  apply congr_arg
  rw [count_ne_zero K w hI]

variable {K}

/-- If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
/-
**FractionalIdeal.finite_factors'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：finite_factors' {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : Idea
l R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) : forallᶠ v : Heig
htOneSpectrum R in Filter.cofinite, ((Associates.mk v.asIdeal).count (Associates
.mk J).factors : Int) - (Associates.mk v.asIdeal).count (Associates.mk (Ideal.sp
an {a})).factors = 0
参数：hI : I != 0；haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.constant_factor_ne_zero`：constant_factor_ne_zero {R} [Co
mmRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {I : Fraction
alIdeal R⁰ K} (hI : I != 0) {…
· 使用定理 `FractionalIdeal.ideal_factor_ne_zero`：ideal_factor_ne_zero {R} [CommRing
 R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {I : FractionalIdea
l R⁰ K} (hI : I != 0) {a :…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.count_ne_zero_iff_dvd`：count_ne_zero_iff_dvd {a p : α} (ha0 :
 a != 0) (hp : Irreducible p) : (Associates.mk p).count (Associates.mk a).factor
s != 0 ↔ p ∣ a
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Ideal.finite_factors`：Ideal.finite_factors {I : Ideal R} (hI : I != 0) :
 {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite

--- 原说明 ---
If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many maximal ideals of `R`.
-/
theorem finite_factors' {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors = 0 := by
  have ha_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI haJ
  have hJ_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI haJ
  have h_subset :
    {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
      ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors) = 0} ⊆
    {v : HeightOneSpectrum R | v.asIdeal ∣ J} ∪
      {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {a}} := by
    intro v hv
    have hv_irred : Irreducible v.asIdeal := v.irreducible
    by_contra h_notMem
    rw [mem_union, mem_ofPred_eq, mem_ofPred_eq] at h_notMem
    push Not at h_notMem
    rw [← Associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred, not_not,
      ← Associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred, not_not] at h_notMem
    rw [mem_ofPred_eq, h_notMem.1, h_notMem.2, sub_self] at hv
    exact hv (Eq.refl 0)
  exact Finite.subset (Finite.union (Ideal.finite_factors (ideal_factor_ne_zero hI haJ))
    (Ideal.finite_factors (constant_factor_ne_zero hI haJ))) h_subset

open Classical in
/-- `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
/-
**FractionalIdeal.finite_factors** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：finite_factors (I : FractionalIdeal R⁰ K) : forallᶠ v : HeightOneSpectrum 
R in Filter.cofinite, count K v I = 0
参数：I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FractionalIdeal.count.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] (
K : Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : IsFractionRi
ng R K] [inst_4 : IsDe…
· 使用引理 `FractionalIdeal.count_zero`：count_zero : count K v (0 : FractionalIdeal 
R⁰ K) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `FractionalIdeal.exists_eq_spanSingleton_mul`：exists_eq_spanSingleton_mul
 (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spa
nSingleton R₁⁰ (algebraMap R₁ K a…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FractionalIdeal.count_ne_zero`：count_ne_zero {I : FractionalIdeal R⁰ K} 
(hI : I != 0) : count K v I = ((Associates.mk v.asIdeal).count (Associates.mk (c
hoose (choose_spec …
· 使用定理 `FractionalIdeal.finite_factors'`：finite_factors' {I : FractionalIdeal R⁰
 K} (hI : I != 0) {a : R} {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap
 R K) a)⁻¹ * ↑J) : fo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
`val_v(I) = 0` for all but finitely many maximal ideals of `R`.
-/
theorem finite_factors (I : FractionalIdeal R⁰ K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, count K v I = 0 := by
  by_cases hI : I = 0
  · simp only [hI, count_zero, Filter.eventually_cofinite, not_true_eq_false, ofPred_false,
      finite_empty]
  · convert! finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
    rw [count_ne_zero K _ hI]

end FractionalIdeal

section div

/-- In a Dedekind domain, for every ideals `0 < I ≤ J` there exists `a` such that `J = I + ⟨a⟩`.
TODO: Show that this property uniquely characterizes Dedekind domains. -/
/-
**IsDedekindDomain.exists_sup_span_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDedekindDomain.exists_sup_span_eq {I J : Ideal R} (hIJ : I <= J) (hI : I
 != 0) : exists a, I ⊔ Ideal.span {a} = J
参数：hIJ : I <= J；hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] {A : Ty
pe v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTow
er R A A] [NoZeroD…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.finite_factors`：Ideal.finite_factors {I : Ideal R} (hI : I != 0) :
 {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`：prod_eq_mul_prod_sdiff_s
ingleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M)
 : ∏ x in s, f x = f i * ∏ x in s \ …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `instPosMulStrictMonoIdeal`：∀ {A : Type u_2} [inst : CommRing A] [IsDedek
indDomain A], PosMulStrictMono (Ideal A)
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
In a Dedekind domain, for every ideals `0 < I ≤ J` there exists `a` such that `J
 = I + ⟨a⟩`.
TODO: Show that this property uniquely characterizes Dedekind domains.
-/
lemma IsDedekindDomain.exists_sup_span_eq {I J : Ideal R} (hIJ : I ≤ J) (hI : I ≠ 0) :
    ∃ a, I ⊔ Ideal.span {a} = J := by
  classical
  obtain ⟨I, rfl⟩ := Ideal.dvd_iff_le.mpr hIJ
  simp only [ne_eq, mul_eq_zero, not_or] at hI
  obtain ⟨hJ, hI⟩ := hI
  suffices ∃ a, ∃ K, J * K = Ideal.span {a} ∧ I + K = ⊤ by
    obtain ⟨a, K, e, e'⟩ := this
    exact ⟨a, by rw [← e, ← Ideal.add_eq_sup, ← mul_add, e', Ideal.mul_top]⟩
  let s := (I.finite_factors hI).toFinset
  have : ∀ p ∈ s, J * ∏ q ∈ s, q.asIdeal < J * ∏ q ∈ s \ {p}, q.asIdeal := by
    intro p hps
    conv_rhs => rw [← mul_one (J * _)]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hps, ← mul_assoc,
      mul_right_comm _ p.asIdeal]
    refine mul_lt_mul_of_pos_left ?_ ?_
    · rw [Ideal.one_eq_top, lt_top_iff_ne_top]
      exact p.2.ne_top
    · rw [Ideal.zero_eq_bot, bot_lt_iff_ne_bot, ← Ideal.zero_eq_bot,
        mul_ne_zero_iff, Finset.prod_ne_zero_iff]
      exact ⟨hJ, fun x _ ↦ x.3⟩
  choose! a ha ha' using fun p hps ↦ SetLike.exists_of_lt (this p hps)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {∑ p ∈ s, a p} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact sum_mem fun p hp ↦ Ideal.mul_le_left (ha p hp)
  refine ⟨_, _, hK.symm, ?_⟩
  by_contra H
  obtain ⟨p, hp, h⟩ := Ideal.exists_le_maximal _ H
  let p' : HeightOneSpectrum R := ⟨p, hp.isPrime, fun e ↦ hI (by simp_all)⟩
  have hp's : p' ∈ s := by simpa [p', s, Ideal.dvd_iff_le] using le_sup_left.trans h
  have H₁ : J * K ≤ J * p := Ideal.mul_mono_right (le_sup_right.trans h)
  replace H₁ := hK.trans_le H₁ (Ideal.mem_span_singleton_self _)
  have H₂ : ∑ q ∈ s \ {p'}, a q ∈ J * p := by
    refine sum_mem fun q hq ↦ ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hq
    refine Ideal.mul_mono_right ?_ (ha q hq.1)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := p') (by simpa [hp's] using Ne.symm hq.2))
  apply ha' _ hp's
  have := IsDedekindDomain.inf_pow_eq_prod_of_prime s (fun i ↦ i.asIdeal) (fun _ ↦ 1)
    (fun i _ ↦ i.prime) (fun i _ j _ e ↦ mt HeightOneSpectrum.ext e)
  simp only [pow_one] at this
  have inst : Nonempty {x // x ∈ s} := ⟨_, hp's⟩
  rw [← this, Finset.inf_eq_iInf, iInf_subtype', Ideal.mul_iInf, Ideal.mem_iInf]
  rintro ⟨q, hq⟩
  by_cases hqp : q = p'
  · subst hqp
    convert! sub_mem H₁ H₂
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hp's, add_sub_cancel_right]
  · refine Ideal.mul_mono_right ?_ (ha p' hp's)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := q) (by simpa [hq] using hqp))

/-- In a Dedekind domain, any ideal is spanned by two elements, where one of the element
could be any fixed non-zero element in the ideal. -/
/-
**IsDedekindDomain.exists_eq_span_pair** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDedekindDomain.exists_eq_span_pair {I : Ideal R} {x : R} (hxI : x in I) 
(hx : x != 0) : exists y, I = .span {x, y}
参数：hxI : x in I；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDedekindDomain.exists_sup_span_eq`：IsDedekindDomain.exists_sup_span_eq
 {I J : Ideal R} (hIJ : I <= J) (hI : I != 0) : exists a, I ⊔ Ideal.span {a} = J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}

--- 原说明 ---
In a Dedekind domain, any ideal is spanned by two elements, where one of the ele
ment
could be any fixed non-zero element in the ideal.
-/
lemma IsDedekindDomain.exists_eq_span_pair {I : Ideal R} {x : R} (hxI : x ∈ I) (hx : x ≠ 0) :
    ∃ y, I = .span {x, y} := by
  obtain ⟨y, rfl⟩ := exists_sup_span_eq (I.span_singleton_le_iff_mem.mpr hxI) (by simpa)
  simp_rw [← Ideal.span_union, Set.union_singleton, Set.pair_comm x]
  use y
/-
**IsDedekindDomain.exists_add_spanSingleton_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDedekindDomain.exists_add_spanSingleton_mul_eq {a b c : FractionalIdeal 
R⁰ K} (hac : a <= c) (ha : a != 0) (hb : b != 0) : exists x : K, a + FractionalI
deal.spanSingleton R⁰ x * b = c
参数：hac : a <= c；ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeIdeal_le_coeIdeal`：coeIdeal_le_coeIdeal (K : Type*) [
CommRing K] [Algebra R K] [IsFractionRing R K] {I J : Ideal R} : (I : Fractional
Ideal R⁰ K) <= J ↔ I <= J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `FractionalIdeal.instMulLeftMono`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   M
ulLeftMono (Fractiona…
· 使用定理 `FractionalIdeal.instMulRightMono`：∀ {R : Type u_1} [inst : CommRing R] {
S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   
MulRightMono (Fraction…
（共 68 条，此处仅展示前 30 条）
-/
lemma IsDedekindDomain.exists_add_spanSingleton_mul_eq
    {a b c : FractionalIdeal R⁰ K} (hac : a ≤ c) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : K, a + FractionalIdeal.spanSingleton R⁰ x * b = c := by
  wlog hb' : b = 1
  · obtain ⟨x, e⟩ := this (a := b⁻¹ * a) (b := 1) (c := b⁻¹ * c) (by gcongr) (by simp [ha, hb])
      one_ne_zero rfl
    use x
    simpa [hb, ← mul_assoc, mul_add, mul_comm b (.spanSingleton _ _)] using congr(b * $e)
  subst hb'
  have H : Ideal.span {c.den.1} * a.num ≤ c.num * Ideal.span {a.den.1} := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K]
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, ←
      FractionalIdeal.den_mul_self_eq_num']
    ring_nf
    gcongr
  obtain ⟨x, hx⟩ := exists_sup_span_eq H
    (by simpa using FractionalIdeal.num_eq_zero_iff.not.mpr ha)
  refine ⟨algebraMap R K x / algebraMap R K (a.den.1 * c.den.1), ?_⟩
  refine mul_left_injective₀ (b := .spanSingleton _
    (algebraMap R K (a.den.1 * c.den.1))) ?_ ?_
  · simp [FractionalIdeal.spanSingleton_eq_zero_iff]
  · simp only [map_mul, mul_one, add_mul, FractionalIdeal.spanSingleton_mul_spanSingleton,
      isUnit_iff_ne_zero, ne_eq, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff,
      nonZeroDivisors.coe_ne_zero, or_self, not_false_eq_true, IsUnit.div_mul_cancel]
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← mul_assoc, mul_comm a,
      FractionalIdeal.den_mul_self_eq_num', ← mul_assoc, mul_right_comm,
      mul_comm c, FractionalIdeal.den_mul_self_eq_num', mul_comm]
    simp_rw [← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_mul,
      ← hx, ← FractionalIdeal.coeIdeal_sup]

namespace FractionalIdeal

/-- `c.divMod b a` (i.e. `c / b mod a`) is an arbitrary `x` such that `c = bx + a`.
This is zero if the above is not possible, i.e. when `a = 0` or `b = 0` or `¬ a ≤ c`. -/
noncomputable
/-
**FractionalIdeal.divMod** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：divMod (c b a : FractionalIdeal R⁰ K) : K
参数：c b a : FractionalIdeal R⁰ K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def divMod (c b a : FractionalIdeal R⁰ K) : K :=
  letI := Classical.propDecidable
  if h : a ≤ c ∧ a ≠ 0 ∧ b ≠ 0 then
    (IsDedekindDomain.exists_add_spanSingleton_mul_eq h.1 h.2.1 h.2.2).choose else 0
/-
**FractionalIdeal.divMod_spec** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：divMod_spec {a b c : FractionalIdeal R⁰ K} (hac : a <= c) (ha : a != 0) (h
b : b != 0) : a + spanSingleton R⁰ (c.divMod b a) * b = c
参数：hac : a <= c；ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.divMod.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {K : T
ype u_2} [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : IsFractionRing R 
K] [inst_4 : IsDe…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `IsDedekindDomain.exists_add_spanSingleton_mul_eq`：IsDedekindDomain.exist
s_add_spanSingleton_mul_eq {a b c : FractionalIdeal R⁰ K} (hac : a <= c) (ha : a
 != 0) (hb : b != 0) : exists x : K, a…
-/
lemma divMod_spec
    {a b c : FractionalIdeal R⁰ K} (hac : a ≤ c) (ha : a ≠ 0) (hb : b ≠ 0) :
    a + spanSingleton R⁰ (c.divMod b a) * b = c := by
  rw [divMod, dif_pos ⟨hac, ha, hb⟩]
  exact (IsDedekindDomain.exists_add_spanSingleton_mul_eq hac ha hb).choose_spec

@[simp]
/-
**FractionalIdeal.divMod_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：divMod_zero_left {I J : FractionalIdeal R⁰ K} : I.divMod 0 J = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma divMod_zero_left {I J : FractionalIdeal R⁰ K} : I.divMod 0 J = 0 := by
  simp [divMod]

@[simp]
/-
**FractionalIdeal.divMod_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：divMod_zero_right {I J : FractionalIdeal R⁰ K} : I.divMod J 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma divMod_zero_right {I J : FractionalIdeal R⁰ K} : I.divMod J 0 = 0 := by
  simp [divMod]

@[simp]
/-
**FractionalIdeal.zero_divMod** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：zero_divMod {I J : FractionalIdeal R⁰ K} : (0 : FractionalIdeal R⁰ K).divM
od I J = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_divMod {I J : FractionalIdeal R⁰ K} :
    (0 : FractionalIdeal R⁰ K).divMod I J = 0 := by
  simp [divMod, ← and_assoc]
/-
**FractionalIdeal.divMod_zero_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIde
al`。
形式化陈述：divMod_zero_of_not_le {a b c : FractionalIdeal R⁰ K} (hac : ¬ a <= c) : c.
divMod b a = 0
参数：hac : ¬ a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma divMod_zero_of_not_le {a b c : FractionalIdeal R⁰ K} (hac : ¬ a ≤ c) :
    c.divMod b a = 0 := by
  simp [divMod, hac]

/-- Let `I J I' J'` be nonzero fractional ideals in a Dedekind domain with `J ≤ I` and `J' ≤ I'`.
If `I/J = I'/J'` in the group of fractional ideals (i.e. `I * J' = I' * J`),
then `I/J ≃ I'/J'` as quotient `R`-modules. -/
noncomputable
/-
**FractionalIdeal.quotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：quotientEquiv (I J I' J' : FractionalIdeal R⁰ K) (H : I * J' = I' * J) (h 
: J <= I) (h' : J' <= I') (hJ' : J' != 0) (hI : I != 0) : (I ⧸ J.coeToSubmodule.
comap I.coeToSubmodule.subtype) ≃ₗ[R] I' ⧸ J'.coeToSubmodule.comap I'.coeToSubmo
dule.subtype
参数：I J I' J' : FractionalIdeal R⁰ K；H : I * J' = I' * J；h : J <= I；h' : J' <= I'
；hJ' : J' != 0；hI : I != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientEquiv (I J I' J' : FractionalIdeal R⁰ K)
    (H : I * J' = I' * J) (h : J ≤ I) (h' : J' ≤ I') (hJ' : J' ≠ 0) (hI : I ≠ 0) :
    (I ⧸ J.coeToSubmodule.comap I.coeToSubmodule.subtype) ≃ₗ[R]
      I' ⧸ J'.coeToSubmodule.comap I'.coeToSubmodule.subtype := by
  haveI : J' ⊓ spanSingleton R⁰ (I'.divMod I J') * I = spanSingleton R⁰ (I'.divMod I J') * J := by
    have := FractionalIdeal.sup_mul_inf J' (spanSingleton R⁰ (I'.divMod I J') * I)
    rwa [FractionalIdeal.sup_eq_add, divMod_spec h' hJ' hI, mul_left_comm, mul_comm J' I, H,
      mul_comm I' J, ← mul_assoc, (mul_left_injective₀ _).eq_iff] at this
    rintro rfl
    exact hJ' (by simpa using h')
  refine .ofBijective (Submodule.mapQ _ _ (LinearMap.restrict
    (Algebra.lsmul R _ _ (I'.divMod I J')) ?_) ?_) ⟨?_, ?_⟩
  · intro x hx
    refine (divMod_spec h' hJ' hI).le ?_
    exact Submodule.mem_sup_right (mul_mem_mul (mem_spanSingleton_self _ _) hx)
  · rw [← Submodule.comap_comp, LinearMap.subtype_comp_restrict, LinearMap.domRestrict,
      Submodule.comap_comp]
    refine Submodule.comap_mono ?_
    intro x hx
    refine (Submodule.mem_inf.mp (this.ge ?_)).1
    simp only [Algebra.lsmul_coe, smul_eq_mul]
    exact mul_mem_mul (mem_spanSingleton_self _ _) hx
  · rw [← LinearMap.ker_eq_bot, Submodule.mapQ, Submodule.ker_liftQ,
      LinearMap.ker_comp, Submodule.ker_mkQ, ← Submodule.comap_comp,
      LinearMap.subtype_comp_restrict, ← le_bot_iff, Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ, LinearMap.domRestrict,
      Submodule.comap_comp, ← Submodule.map_le_iff_le_comap,
      Submodule.map_comap_eq, Submodule.range_subtype]
    by_cases H' : I'.divMod I J' = 0
    · obtain rfl : J' = I' := by simpa [H'] using divMod_spec h' hJ' hI
      obtain rfl : I = J := mul_left_injective₀ hJ' (H.trans (mul_comm _ _))
      exact inf_le_left
    rw [← inv_mul_eq_iff_eq_mul₀ (by simpa [spanSingleton_eq_zero_iff] using H'), mul_inf₀
      (zero_le _), inv_mul_cancel_left₀ (by simpa [spanSingleton_eq_zero_iff] using H')] at this
    rw [← this, inf_comm, coe_inf]
    refine inf_le_inf ?_ le_rfl
    intro x hx
    rw [spanSingleton_inv]
    convert! mul_mem_mul (mem_spanSingleton_self _ _) hx
    simp [H']
  · have H : Submodule.map (Algebra.lsmul R R K (I'.divMod I J')) ↑I =
        (spanSingleton R⁰ (I'.divMod I J') * I) := by
      ext x
      simp [Submodule.mem_span_singleton_mul]
    rw [← LinearMap.range_eq_top, Submodule.mapQ, Submodule.range_liftQ,
      LinearMap.range_comp, LinearMap.restrict, LinearMap.range_codRestrict,
      LinearMap.range_domRestrict, ← top_le_iff, H,
      ← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      ← Submodule.map_top, Submodule.map_le_iff_le_comap, Submodule.comap_map_eq, Submodule.ker_mkQ,
      ← Submodule.map_le_map_iff_of_injective I'.coeToSubmodule.injective_subtype,
      Submodule.map_top, Submodule.map_sup,
      Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype, sup_comm,
      inf_eq_right.mpr, inf_eq_right.mpr]
    · exact le_trans (divMod_spec h' hJ' hI).ge (by simp)
    · exact le_trans (by simp) (divMod_spec h' hJ' hI).le
    · exact h'

end FractionalIdeal

end div

section primesOver

variable {S : Type*} [CommRing S] [Algebra S R] [Algebra.IsIntegral S R] [IsDomain S]
  [Module.IsTorsionFree S R]

open IsDedekindDomain Ideal.IsDedekindDomain HeightOneSpectrum

/--
If `p` is a maximal ideal, then the lift of `p` in an extension is the product of the primes
over `p` to the power the ramification index.
-/
/-
**Ideal.map_algebraMap_eq_finsetProd_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.map_algebraMap_eq_finsetProd_pow {p : Ideal S} [p.IsMaximal] (hp : p
 != 0) : map (algebraMap S R) p = ∏ P in p.primesOver R, P ^ P.ramificationIdx S
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_ne_bot_of_ne_bot`：map_ne_bot_of_ne_bot {R S : Type*} [CommSemi
ring R] [Semiring S] [Algebra R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥)
 : map (algebraM…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.finprod_heightOneSpectrum_factorization`：finprod_heightOneSpectrum
_factorization {I : Ideal R} (hI : I != 0) : ∏ᶠ v : HeightOneSpectrum R, v.maxPo
wDividing I = I
· 使用定理 `Ideal.finite_factors`：Ideal.finite_factors {I : Ideal R} (hI : I != 0) :
 {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite
· 使用定理 `finprod_eq_finsetProd_of_mulSupport_subset`：finprod_eq_finsetProd_of_mul
Support_subset (f : α -> M) {s : Finset α} (h : mulSupport f subseteq (s : Set α
)) : ∏ᶠ i, f i = ∏ i in s, f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Associates.count_ne_zero_iff_dvd`：count_ne_zero_iff_dvd {a p : α} (ha0 :
 a != 0) (hp : Irreducible p) : (Associates.mk p).count (Associates.mk a).factor
s != 0 ↔ p ∣ a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
· 使用定理 `Finset.prod_set_coe`：prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f 
i) = ∏ i in s.toFinset, f i
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Ideal.liesOver_iff_dvd_map`：Ideal.liesOver_iff_dvd_map [Algebra R A] {p 
: Ideal R} {P : Ideal A} (hP : P != ⊤) [p.IsMaximal] : P.LiesOver p ↔ P ∣ Ideal.
map (algebraMap …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count`
：IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count {I : Id
eal R} (hI : I != 0) : maxPowDividing v I = v.asIdeal ^ Multi…
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count`：ramificationIdx
_eq_factors_count [IsDedekindDomain S] [q.LiesOver p] (hp0 : p.map (algebraMap R
 S) != ⊥) : q.ramificationIdx R = (factors (p…
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a maximal ideal, then the lift of `p` in an extension is the product o
f the primes
over `p` to the power the ramification index.
-/
theorem Ideal.map_algebraMap_eq_finsetProd_pow {p : Ideal S} [p.IsMaximal] (hp : p ≠ 0) :
    map (algebraMap S R) p = ∏ P ∈ p.primesOver R, P ^ P.ramificationIdx S := by
  have h : map (algebraMap S R) p ≠ 0 := map_ne_bot_of_ne_bot hp
  rw [← finprod_heightOneSpectrum_factorization (I := p.map (algebraMap S R)) h]
  let hF : Fintype {v : HeightOneSpectrum R | v.asIdeal ∣ map (algebraMap S R) p} :=
    (finite_factors h).fintype
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (s := {v | v.asIdeal ∣ p.map (algebraMap S R)}.toFinset), ← Finset.prod_set_coe,
    ← Finset.prod_set_coe]
  · let _ : Fintype {v : HeightOneSpectrum R // v.asIdeal ∣ map (algebraMap S R) p} := hF
    refine Fintype.prod_equiv (equivPrimesOver _ hp) _ _ fun ⟨v, _⟩ ↦ ?_
    have : v.asIdeal.LiesOver p := by rwa [Ideal.liesOver_iff_dvd_map v.2.ne_top]
    simp [maxPowDividing_eq_pow_multiset_count _ h, ramificationIdx_eq_factors_count p v h]
  · intro v hv
    simpa [maxPowDividing, Function.mem_mulSupport, IsPrime.ne_top _,
      Associates.count_ne_zero_iff_dvd h (irreducible v)] using hv

@[deprecated (since := "2026-04-08")]
alias Ideal.map_algebraMap_eq_finset_prod_pow := Ideal.map_algebraMap_eq_finsetProd_pow

end primesOver

/-!
### Conversion between various multiplicities

We provide some lemmas that convert various ways of expressing the multiplicity of
a prime ideal `p` in the factorization of some ideal `I` into `multiplicity p.asIdeal I`.
-/

section conversion

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

namespace IsDedekindDomain.HeightOneSpectrum

variable {I : Ideal R} (hI : I ≠ ⊥) (p : HeightOneSpectrum R)
include hI

open UniqueFactorizationMonoid in
/-- Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity** 是
 Mathlib 中的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：count_normalizedFactors_eq_multiplicity : Multiset.count p.asIdeal (normal
izedFactors I) = multiplicity p.asIdeal I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `finiteMultiplicity_of_emultiplicity_eq_natCast`：finiteMultiplicity_of_em
ultiplicity_eq_natCast {n : Nat} (h : emultiplicity a b = n) : FiniteMultiplicit
y a b

--- 原说明 ---
Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`.
-/
lemma count_normalizedFactors_eq_multiplicity :
    Multiset.count p.asIdeal (normalizedFactors I) = multiplicity p.asIdeal I := by
  have := emultiplicity_eq_count_normalizedFactors (irreducible p) hI
  rw [normalize_eq p.asIdeal] at this
  apply_fun ((↑) : ℕ → ℕ∞) using CharZero.cast_injective
  rw [← this]
  exact (finiteMultiplicity_of_emultiplicity_eq_natCast this).emultiplicity_eq_multiplicity

/-- Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity** 是 Math
lib 中的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：maxPowDividing_eq_pow_multiplicity : p.maxPowDividing I = p.asIdeal ^ mult
iplicity p.asIdeal I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count`
：IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count {I : Id
eal R} (hI : I != 0) : maxPowDividing v I = v.asIdeal ^ Multi…
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplici
ty`：count_normalizedFactors_eq_multiplicity : Multiset.count p.asIdeal (normaliz
edFactors I) = multiplicity p.asIdeal I

--- 原说明 ---
Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`.
-/
lemma maxPowDividing_eq_pow_multiplicity :
    p.maxPowDividing I = p.asIdeal ^ multiplicity p.asIdeal I := by
  rw [maxPowDividing_eq_pow_multiset_count _ hI, count_normalizedFactors_eq_multiplicity hI]

/-- Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`. -/
@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.factorization_eq_multiplicity** 是 Mathlib 中
的一个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：factorization_eq_multiplicity : factorization I p.asIdeal = multiplicity p
.asIdeal I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `factorization_eq_count`：factorization_eq_count {n p : α} : factorization
 n p = Multiset.count p (normalizedFactors n)
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplici
ty`：count_normalizedFactors_eq_multiplicity : Multiset.count p.asIdeal (normaliz
edFactors I) = multiplicity p.asIdeal I

--- 原说明 ---
Normalize the multiplicity of a prime ideal `p` in the factorization of `I`
as `multiplicity p.asIdeal I`.
-/
lemma factorization_eq_multiplicity :
    factorization I p.asIdeal = multiplicity p.asIdeal I := by
  rw [factorization_eq_count, count_normalizedFactors_eq_multiplicity hI]

end IsDedekindDomain.HeightOneSpectrum

end conversion

/-!
### Lemmas about multiplicities

We collect here lemmas about the multiplicity of a prime ideal `p` in the factorization
of some ideal `I`.
These are phrased in terms of `multiplicity p.asIdeal I`.
-/

section multiplicity

@[simp]
/-
**Ideal.emultiplicity_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.emultiplicity_bot {R : Type*} [CommSemiring R] (I : Ideal R) : emult
iplicity I ⊥ = ⊤
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `Submodule.zero_eq_bot`：zero_eq_bot : (0 : Submodule R M) = ⊥
-/
lemma Ideal.emultiplicity_bot {R : Type*} [CommSemiring R] (I : Ideal R) : emultiplicity I ⊥ = ⊤ :=
  Submodule.zero_eq_bot (R := R) (M := R) ▸ emultiplicity_zero I

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
/-
**Ideal.finprod_heightOneSpectrum_pow_multiplicity** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.finprod_heightOneSpectrum_pow_multiplicity {I : Ideal R} (hI : I != 
⊥) : ∏ᶠ p : HeightOneSpectrum R, p.asIdeal ^ multiplicity p.asIdeal I = I
参数：hI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity`：m
axPowDividing_eq_pow_multiplicity : p.maxPowDividing I = p.asIdeal ^ multiplicit
y p.asIdeal I
· 使用定理 `Ideal.finprod_heightOneSpectrum_factorization`：finprod_heightOneSpectrum
_factorization {I : Ideal R} (hI : I != 0) : ∏ᶠ v : HeightOneSpectrum R, v.maxPo
wDividing I = I
-/
lemma Ideal.finprod_heightOneSpectrum_pow_multiplicity {I : Ideal R} (hI : I ≠ ⊥) :
    ∏ᶠ p : HeightOneSpectrum R, p.asIdeal ^ multiplicity p.asIdeal I = I := by
  simpa only [maxPowDividing_eq_pow_multiplicity hI]
    using finprod_heightOneSpectrum_factorization hI

namespace IsDedekindDomain.HeightOneSpectrum

variable (p : HeightOneSpectrum R) {I J : Ideal R}

/-
**IsDedekindDomain.HeightOneSpectrum.multiplicity_le_of_ideal_ge** 是 Mathlib 中的一
个引理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：multiplicity_le_of_ideal_ge (h : J <= I) (hJ : J != ⊥) : multiplicity p.as
Ideal I <= multiplicity p.asIdeal J
参数：h : J <= I；hJ : J != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplici
ty`：count_normalizedFactors_eq_multiplicity : Multiset.count p.asIdeal (normaliz
edFactors I) = multiplicity p.asIdeal I
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Ideal.count_le_of_ideal_ge`：count_le_of_ideal_ge {I J : Ideal T} (h : I 
<= J) (hI : I != ⊥) (K : Ideal T) : count K (normalizedFactors J) <= count K (no
rmalizedFactors …
-/
lemma multiplicity_le_of_ideal_ge (h : J ≤ I) (hJ : J ≠ ⊥) :
    multiplicity p.asIdeal I ≤ multiplicity p.asIdeal J := by
  rw [← count_normalizedFactors_eq_multiplicity hJ,
    ← count_normalizedFactors_eq_multiplicity <| ne_bot_of_le_ne_bot hJ h]
  exact Ideal.count_le_of_ideal_ge h hJ _

open UniqueFactorizationMonoid Multiset in
/-
**IsDedekindDomain.HeightOneSpectrum.multiplicity_sup** 是 Mathlib 中的一个引理，位于命名空间 
`IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：multiplicity_sup (hI : I != ⊥) (hJ : J != ⊥) : multiplicity p.asIdeal (I ⊔
 J) = multiplicity p.asIdeal I ⊓ multiplicity p.asIdeal J
参数：hI : I != ⊥；hJ : J != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.sup_eq_prod_inf_factors`：sup_eq_prod_inf_factors (hI : I != ⊥) (hJ
 : J != ⊥) : I ⊔ J = (normalizedFactors I inter normalizedFactors J).prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplici
ty`：count_normalizedFactors_eq_multiplicity : Multiset.count p.asIdeal (normaliz
edFactors I) = multiplicity p.asIdeal I
· 使用引理 `UniqueFactorizationMonoid.prod_inter_normalizedFactors_ne_zero`：prod_int
er_normalizedFactors_ne_zero [NormalizationMonoid α] [Nontrivial α] (a b : α) : 
(normalizedFactors a inter normalizedFactors b).prod…
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `UniqueFactorizationMonoid.normalizedFactors_prod_inter_eq_inter`：normali
zedFactors_prod_inter_eq_inter [Subsingleton αˣ] (a b : α) : normalizedFactors (
normalizedFactors a inter normalizedFactors b).prod =…
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
-/
lemma multiplicity_sup (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    multiplicity p.asIdeal (I ⊔ J) = multiplicity p.asIdeal I ⊓ multiplicity p.asIdeal J := by
  rw [Ideal.sup_eq_prod_inf_factors hI hJ, ← count_normalizedFactors_eq_multiplicity ?h,
    ← count_normalizedFactors_eq_multiplicity hI, ← count_normalizedFactors_eq_multiplicity hJ]
  case h => exact prod_inter_normalizedFactors_ne_zero I J
  rw [normalizedFactors_prod_inter_eq_inter]
  exact count_inter ..

variable (I J) in
/-
**IsDedekindDomain.HeightOneSpectrum.emultiplicity_sup** 是 Mathlib 中的一个引理，位于命名空间
 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：emultiplicity_sup : emultiplicity p.asIdeal (I ⊔ J) = emultiplicity p.asId
eal I ⊓ emultiplicity p.asIdeal J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Ideal.emultiplicity_bot`：Ideal.emultiplicity_bot {R : Type*} [CommSemiri
ng R] (I : Ideal R) : emultiplicity I ⊥ = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `FiniteMultiplicity.of_prime_left`：FiniteMultiplicity.of_prime_left [Comm
MonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] {a b : α} (ha : Prime a) (
hb : b != 0) : FiniteM…
· 使用定理 `instWfDvdMonoidIdeal`：∀ {A : Type u_2} [inst : CommRing A] [IsDedekindDo
main A], WfDvdMonoid (Ideal A)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.prime`：prime : Prime v.asIdeal
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.multiplicity_sup`：multiplicity_sup (h
I : I != ⊥) (hJ : J != ⊥) : multiplicity p.asIdeal (I ⊔ J) = multiplicity p.asId
eal I ⊓ multiplicity p.asIdeal J
-/
lemma emultiplicity_sup :
    emultiplicity p.asIdeal (I ⊔ J) = emultiplicity p.asIdeal I ⊓ emultiplicity p.asIdeal J := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  rcases eq_or_ne J ⊥ with rfl | hJ
  · simp
  have : I ⊔ J ≠ ⊥ := by grind
  have H {I' : Ideal R} (h : I' ≠ ⊥) : FiniteMultiplicity p.asIdeal I' :=
    FiniteMultiplicity.of_prime_left (prime p) h
  rw [(H this).emultiplicity_eq_multiplicity, (H hI).emultiplicity_eq_multiplicity,
    (H hJ).emultiplicity_eq_multiplicity, multiplicity_sup _ hI hJ]
  norm_cast

variable {ι : Type*} [Finite ι]
/-
**IsDedekindDomain.HeightOneSpectrum.emultiplicity_iSup** 是 Mathlib 中的一个引理，位于命名空
间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：emultiplicity_iSup (I : ι -> Ideal R) : emultiplicity p.asIdeal (⨆ i, I i)
 = ⨅ i, emultiplicity p.asIdeal (I i)
参数：I : ι -> Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
· 使用定理 `iInf_of_empty`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] [IsEmpty ι] (f : ι → α), iInf f = ⊤
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `iSup_option`：iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, 
f (Option.some b)
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.emultiplicity_sup`：emultiplicity_sup 
: emultiplicity p.asIdeal (I ⊔ J) = emultiplicity p.asIdeal I ⊓ emultiplicity p.
asIdeal J
· 使用定理 `iInf_option`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
(f : Option β → α), ⨅ o, f o = f none ⊓ ⨅ b, f (some b)
-/
lemma emultiplicity_iSup (I : ι → Ideal R) :
    emultiplicity p.asIdeal (⨆ i, I i) = ⨅ i, emultiplicity p.asIdeal (I i) := by
  induction ι using Finite.induction_empty_option with
  | h_empty =>
    rw [iSup_of_empty, iInf_of_empty]
    exact emultiplicity_zero _
  | of_equiv e ih =>
    specialize ih (I ∘ e)
    rw [← sSup_range, ← sInf_range] at ih ⊢
    rw [EquivLike.range_comp I e] at ih
    rw [ih]
    exact congrArg _ <| EquivLike.range_comp (emultiplicity p.asIdeal <| I ·) e
  | h_option ih =>
    rw [iSup_option, emultiplicity_sup p .., ih, iInf_option]
/-
**IsDedekindDomain.HeightOneSpectrum.multiplicity_iSup** 是 Mathlib 中的一个引理，位于命名空间
 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：multiplicity_iSup [Nonempty ι] {I : ι -> Ideal R} (hI : forall i, I i != ⊥
) : multiplicity p.asIdeal (⨆ i, I i) = ⨅ i, multiplicity p.asIdeal (I i)
参数：hI : forall i, I i != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.of_prime_left`：FiniteMultiplicity.of_prime_left [Comm
MonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] {a b : α} (ha : Prime a) (
hb : b != 0) : FiniteM…
· 使用定理 `instWfDvdMonoidIdeal`：∀ {A : Type u_2} [inst : CommRing A] [IsDedekindDo
main A], WfDvdMonoid (Ideal A)
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.prime`：prime : Prime v.asIdeal
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_eq_bot`：iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用引理 `IsDedekindDomain.HeightOneSpectrum.emultiplicity_iSup`：emultiplicity_iSu
p (I : ι -> Ideal R) : emultiplicity p.asIdeal (⨆ i, I i) = ⨅ i, emultiplicity p
.asIdeal (I i)
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
-/
lemma multiplicity_iSup [Nonempty ι] {I : ι → Ideal R} (hI : ∀ i, I i ≠ ⊥) :
    multiplicity p.asIdeal (⨆ i, I i) = ⨅ i, multiplicity p.asIdeal (I i) := by
  have H i : FiniteMultiplicity p.asIdeal (I i) :=
    FiniteMultiplicity.of_prime_left (prime p) <| hI i
  have H' : FiniteMultiplicity p.asIdeal (⨆ i, I i) := by
    refine FiniteMultiplicity.of_prime_left (prime p) ?_
    contrapose! hI
    rw [← bot_eq_zero, iSup_eq_bot] at hI
    exact ⟨Classical.ofNonempty, hI _⟩
  have := emultiplicity_iSup p I
  simp only [H'.emultiplicity_eq_multiplicity, (H _).emultiplicity_eq_multiplicity] at this
  exact_mod_cast this

end IsDedekindDomain.HeightOneSpectrum

end multiplicity

