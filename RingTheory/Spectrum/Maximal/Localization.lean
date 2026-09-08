/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Maximal spectrum of a commutative (semi)ring

Localization results.
-/

@[expose] public section

noncomputable section

variable (R S P : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]

namespace MaximalSpectrum

variable {R}

open PrimeSpectrum Set

variable (R : Type*)
variable [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its maximal ideals
viewed as subalgebras of its field of fractions. -/
/-
**MaximalSpectrum.iInf_localization_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `MaximalSpe
ctrum`。
形式化陈述：iInf_localization_eq_bot : (⨅ v : MaximalSpectrum R, Localization.subalgeb
ra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `Algebra.mem_iInf`：mem_iInf {ι : Sort*} {S : ι -> Subalgebra R A} {x : A}
 : x in ⨅ i, S i ↔ forall i, x in S i
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
An integral domain is equal to the intersection of its localizations at all its 
maximal ideals
viewed as subalgebras of its field of fractions.
-/
theorem iInf_localization_eq_bot : (⨅ v : MaximalSpectrum R,
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_bot, Algebra.mem_iInf]
  constructor
  · contrapose
    intro hrange hlocal
    let denom : Ideal R := (1 : Submodule R K).comap (LinearMap.toSpanSingleton R K x)
    have hdenom : (1 : R) ∉ denom := by simpa [denom] using hrange
    rcases denom.exists_le_maximal (denom.ne_top_iff_one.mpr hdenom) with ⟨max, hmax, hle⟩
    rcases hlocal ⟨max, hmax⟩ with ⟨n, d, hd, rfl⟩
    exact hd (hle ⟨n, by simp [Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ <|
      (map_ne_zero_iff _ <| IsFractionRing.injective R K).mpr fun h ↦ hd (h ▸ max.zero_mem :)]⟩)
  · rintro ⟨y, rfl⟩ ⟨v, hv⟩
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩

end MaximalSpectrum

namespace PrimeSpectrum

variable (R : Type*)
variable [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral domain is equal to the intersection of its localizations at all its prime ideals
viewed as subalgebras of its field of fractions. -/
/-
**PrimeSpectrum.iInf_localization_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：iInf_localization_eq_bot : ⨅ v : PrimeSpectrum R, Localization.subalgebra.
ofField K _ (v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MaximalSpectrum.iInf_localization_eq_bot`：iInf_localization_eq_bot : (⨅ 
v : MaximalSpectrum R, Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_
le_nonZeroDivisors) = ⊥

--- 原说明 ---
An integral domain is equal to the intersection of its localizations at all its 
prime ideals
viewed as subalgebras of its field of fractions.
-/
theorem iInf_localization_eq_bot : ⨅ v : PrimeSpectrum R,
    Localization.subalgebra.ofField K _ (v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  refine bot_unique (.trans (fun _ ↦ ?_) (MaximalSpectrum.iInf_localization_eq_bot R K).le)
  simpa only [Algebra.mem_iInf] using fun hx ⟨v, hv⟩ ↦ hx ⟨v, hv.isPrime⟩

end PrimeSpectrum

namespace MaximalSpectrum

/-- The product of localizations at all maximal ideals of a commutative semiring. -/
/-
**MaximalSpectrum.PiLocalization** 是 Mathlib 中的一个缩写定义，位于命名空间 `MaximalSpectrum`。
形式化陈述：PiLocalization : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of localizations at all maximal ideals of a commutative semiring.
-/
abbrev PiLocalization : Type _ := Π I : MaximalSpectrum R, Localization.AtPrime I.1

/-- The canonical ring homomorphism from a commutative semiring to the product of its
localizations at all maximal ideals. It is always injective. -/
/-
**MaximalSpectrum.toPiLocalization** 是 Mathlib 中的一个定义，位于命名空间 `MaximalSpectrum`。
形式化陈述：toPiLocalization : R ->ₐ[R] PiLocalization R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical ring homomorphism from a commutative semiring to the product of it
s
localizations at all maximal ideals. It is always injective.
-/
def toPiLocalization : R →ₐ[R] PiLocalization R := Algebra.ofId R (PiLocalization R)
/-
**MaximalSpectrum.toPiLocalization_injective** 是 Mathlib 中的一个定理，位于命名空间 `MaximalS
pectrum`。
形式化陈述：toPiLocalization_injective : Function.Injective (toPiLocalization R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem toPiLocalization_injective : Function.Injective (toPiLocalization R) := fun r r' eq ↦ by
  rw [← one_mul r, ← one_mul r']
  by_contra ne
  have ⟨I, mI, hI⟩ := (Module.eqIdeal R r r').exists_le_maximal ((Ideal.ne_top_iff_one _).mpr ne)
  have ⟨s, hs⟩ := (IsLocalization.eq_iff_exists I.primeCompl _).mp (congr_fun eq ⟨I, mI⟩)
  exact s.2 (hI hs)
/-
**MaximalSpectrum.toPiLocalization_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Maxima
lSpectrum`。
形式化陈述：toPiLocalization_apply_apply {r I} : toPiLocalization R r I = algebraMap R
 _ r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPiLocalization_apply_apply {r I} : toPiLocalization R r I = algebraMap R _ r := rfl

variable {R S} (f : R →+* S) (g : S →+* P) (hf : Function.Bijective f) (hg : Function.Bijective g)

/-- Functoriality of `PiLocalization` but restricted to bijective ring homs.
If R and S are commutative rings, surjectivity would be enough. -/
/-
**MaximalSpectrum.mapPiLocalization** 是 Mathlib 中的一个定义，位于命名空间 `MaximalSpectrum`。
形式化陈述：mapPiLocalization : PiLocalization R ->+* PiLocalization S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `PiLocalization` but restricted to bijective ring homs.
If R and S are commutative rings, surjectivity would be enough.
-/
noncomputable def mapPiLocalization : PiLocalization R →+* PiLocalization S :=
  RingHom.pi fun I ↦ (Localization.localRingHom _ _ f rfl).comp <|
    Pi.evalRingHom _ (⟨_, I.2.comap_bijective f hf⟩ : MaximalSpectrum R)
/-
**MaximalSpectrum.mapPiLocalization_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Maxima
lSpectrum`。
形式化陈述：mapPiLocalization_naturality : (mapPiLocalization f hf).comp (toPiLocaliza
tion R) = (toPiLocalization S).toRingHom.comp f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsLocalization.mk'.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
theorem mapPiLocalization_naturality :
    (mapPiLocalization f hf).comp (toPiLocalization R) =
      (toPiLocalization S).toRingHom.comp f := by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl
/-
**MaximalSpectrum.mapPiLocalization_id** 是 Mathlib 中的一个定理，位于命名空间 `MaximalSpectru
m`。
形式化陈述：mapPiLocalization_id : mapPiLocalization (.id R) Function.bijective_id = .
id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_id`：comap_id : I.comap (RingHom.id R) = I
· 使用定理 `Localization.localRingHom_id`：localRingHom_id : localRingHom I I (RingHo
m.id R) (Ideal.comap_id I).symm = RingHom.id _
-/
theorem mapPiLocalization_id : mapPiLocalization (.id R) Function.bijective_id = .id _ :=
  RingHom.ext fun _ ↦ funext fun _ ↦ congr($(Localization.localRingHom_id _) _)
/-
**MaximalSpectrum.mapPiLocalization_comp** 是 Mathlib 中的一个定理，位于命名空间 `MaximalSpect
rum`。
形式化陈述：mapPiLocalization_comp : mapPiLocalization (g.comp f) (hg.comp hf) = (mapP
iLocalization g hg).comp (mapPiLocalization f hf)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `Localization.localRingHom_comp`：localRingHom_comp {S : Type*} [CommSemir
ing S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P) [hK : K.IsPrime] (f : R ->+*
 S) (hIJ : I = J.com…
-/
theorem mapPiLocalization_comp :
    mapPiLocalization (g.comp f) (hg.comp hf) =
      (mapPiLocalization g hg).comp (mapPiLocalization f hf) :=
  RingHom.ext fun _ ↦ funext fun _ ↦ congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)

set_option backward.isDefEq.respectTransparency false in
/-
**MaximalSpectrum.mapPiLocalization_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Maximal
Spectrum`。
形式化陈述：mapPiLocalization_bijective : Function.Bijective (mapPiLocalization f hf)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MaximalSpectrum.mapPiLocalization_comp`：mapPiLocalization_comp : mapPiLo
calization (g.comp f) (hg.comp hf) = (mapPiLocalization g hg).comp (mapPiLocaliz
ation f hf)
· 使用定理 `RingEquiv.comp_symm`：comp_symm (e : R ≃+* S) : (e : R ->+* S).comp (e.sy
mm : S ->+* R) = RingHom.id S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MaximalSpectrum.mapPiLocalization.congr_simp`：∀ {R : Type u_1} {S : Type
 u_2} [inst : CommSemiring R] [inst_1 : CommSemiring S] (f f_1 : R →+* S) (e_f :
 f = f_1)   (hf : Function.Bijecti…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MaximalSpectrum.mapPiLocalization_id`：mapPiLocalization_id : mapPiLocali
zation (.id R) Function.bijective_id = .id _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingEquiv.symm_comp`：symm_comp (e : R ≃+* S) : (e.symm : S ->+* R).comp 
(e : R ->+* S) = RingHom.id R
-/
theorem mapPiLocalization_bijective : Function.Bijective (mapPiLocalization f hf) := by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization f hf)
    (mapPiLocalization (f.symm : S →+* R) f.symm.bijective) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp]
    simp_rw [RingEquiv.symm_comp, mapPiLocalization_id]

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)] [∀ i, Nontrivial (R i)]

/-
**MaximalSpectrum.toPiLocalization_not_surjective_of_infinite** 是 Mathlib 中的一个定理
，位于命名空间 `MaximalSpectrum`。
形式化陈述：toPiLocalization_not_surjective_of_infinite [Infinite ι] : ¬ Function.Surj
ective (toPiLocalization (Π i, R i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite`：exists_
maximal_notMem_range_sigmaToPi_of_infinite : exists (I : Ideal (Π i, R i)) (_ : 
I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaTo…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MaximalSpectrum.toPiLocalization_injective`：toPiLocalization_injective :
 Function.Injective (toPiLocalization R)
· 使用定理 `Ideal.IsMaximal.comap_piEvalRingHom`：∀ {ι : Type u_4} {R : ι → Type u_5}
 [inst : (i : ι) → Semiring (R i)] {i : ι} {I : Ideal (R i)},   I.IsMaximal → (I
deal.comap (Pi.evalRingHo…
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem toPiLocalization_not_surjective_of_infinite [Infinite ι] :
    ¬ Function.Surjective (toPiLocalization (Π i, R i)) := fun surj ↦ by
  classical
  have ⟨J, max, notMem⟩ := PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite R
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max⟩ 1)
  have : r = 0 := funext fun i ↦ toPiLocalization_injective _ <| funext fun I ↦ by
    replace hr := congr_fun hr ⟨_, I.2.comap_piEvalRingHom⟩
    dsimp only [toPiLocalization_apply_apply, Subtype.coe_mk] at hr
    simp_rw [toPiLocalization_apply_apply,
      ← Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply, hr]
    rw [Function.update_of_ne]; · simp_rw [Pi.zero_apply, map_zero]
    exact fun h ↦ notMem ⟨⟨i, I.1, I.2.isPrime⟩, PrimeSpectrum.ext congr($h.1)⟩
  replace hr := congr_fun hr ⟨J, max⟩
  rw [this, map_zero, Function.update_self] at hr
  exact zero_ne_one hr

variable {R}
/-
**MaximalSpectrum.finite_of_toPiLocalization_pi_surjective** 是 Mathlib 中的一个定理，位于
命名空间 `MaximalSpectrum`。
形式化陈述：finite_of_toPiLocalization_pi_surjective (h : Function.Surjective (toPiLoc
alization (Π i, R i))) : Finite ι
参数：h : Function.Surjective (toPiLocalization (Π i, R i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MaximalSpectrum.toPiLocalization_not_surjective_of_infinite`：toPiLocaliz
ation_not_surjective_of_infinite [Infinite ι] : ¬ Function.Surjective (toPiLocal
ization (Π i, R i))
-/
theorem finite_of_toPiLocalization_pi_surjective
    (h : Function.Surjective (toPiLocalization (Π i, R i))) :
    Finite ι := by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

end Pi

set_option backward.isDefEq.respectTransparency false in
/-
**MaximalSpectrum.finite_of_toPiLocalization_surjective** 是 Mathlib 中的一个定理，位于命名空
间 `MaximalSpectrum`。
形式化陈述：finite_of_toPiLocalization_surjective (surj : Function.Surjective (toPiLoc
alization R)) : Finite (MaximalSpectrum R)
参数：surj : Function.Surjective (toPiLocalization R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MaximalSpectrum.toPiLocalization_injective`：toPiLocalization_injective :
 Function.Injective (toPiLocalization R)
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MaximalSpectrum.mapPiLocalization_bijective`：mapPiLocalization_bijective
 : Function.Bijective (mapPiLocalization f hf)
· 使用定理 `MaximalSpectrum.finite_of_toPiLocalization_pi_surjective`：finite_of_toPi
Localization_pi_surjective (h : Function.Surjective (toPiLocalization (Π i, R i)
)) : Finite ι
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MaximalSpectrum.mapPiLocalization_naturality`：mapPiLocalization_naturali
ty : (mapPiLocalization f hf).comp (toPiLocalization R) = (toPiLocalization S).t
oRingHom.comp f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
-/
theorem finite_of_toPiLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    Finite (MaximalSpectrum R) := by
  replace surj := mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩
    |>.2.comp surj
  rw [← AlgHom.coe_toRingHom,
    ← RingHom.coe_comp, mapPiLocalization_naturality, RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

end MaximalSpectrum

namespace PrimeSpectrum

/-- The product of localizations at all prime ideals of a commutative semiring. -/
/-
**PrimeSpectrum.PiLocalization** 是 Mathlib 中的一个缩写定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：PiLocalization : Type _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
The product of localizations at all prime ideals of a commutative semiring.
-/
abbrev PiLocalization : Type _ := Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl

/-- The canonical ring homomorphism from a commutative semiring to the product of its
localizations at all prime ideals. It is always injective. -/
/-
**PrimeSpectrum.toPiLocalization** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：toPiLocalization : R ->ₐ[R] PiLocalization R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
The canonical ring homomorphism from a commutative semiring to the product of it
s
localizations at all prime ideals. It is always injective.
-/
def toPiLocalization : R →ₐ[R] PiLocalization R := Algebra.ofId R (PiLocalization R)
/-
**PrimeSpectrum.toPiLocalization_injective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpect
rum`。
形式化陈述：toPiLocalization_injective : Function.Injective (toPiLocalization R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `MaximalSpectrum.toPiLocalization_injective`：toPiLocalization_injective :
 Function.Injective (toPiLocalization R)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem toPiLocalization_injective : Function.Injective (toPiLocalization R) :=
  fun _ _ eq ↦ MaximalSpectrum.toPiLocalization_injective R <|
    funext fun I ↦ congr_fun eq I.toPrimeSpectrum

/-- The projection from the product of localizations at primes to the product of
localizations at maximal ideals. -/
/-
**PrimeSpectrum.piLocalizationToMaximal** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum
`。
形式化陈述：piLocalizationToMaximal : PiLocalization R ->ₐ[R] MaximalSpectrum.PiLocali
zation R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
The projection from the product of localizations at primes to the product of
localizations at maximal ideals.
-/
def piLocalizationToMaximal : PiLocalization R →ₐ[R] MaximalSpectrum.PiLocalization R :=
  AlgHom.pi fun I ↦ Pi.evalAlgHom _ _ I.toPrimeSpectrum
/-
**PrimeSpectrum.piLocalizationToMaximal_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Pr
imeSpectrum`。
形式化陈述：piLocalizationToMaximal_surjective : Function.Surjective (piLocalizationTo
Maximal R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
-/
theorem piLocalizationToMaximal_surjective : Function.Surjective (piLocalizationToMaximal R) := by
  classical
  exact fun r ↦ ⟨fun I ↦ if h : I.1.IsMaximal then r ⟨_, h⟩ else 0, funext fun _ ↦ dif_pos _⟩

variable {R}

/-- If R has Krull dimension ≤ 0, then `piLocalizationToIsMaximal R` is an isomorphism. -/
/-
**PrimeSpectrum.piLocalizationToMaximalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：piLocalizationToMaximalEquiv (h : forall I : Ideal R, I.IsPrime -> I.IsMax
imal) : PiLocalization R ≃+* MaximalSpectrum.PiLocalization R where __
参数：h : forall I : Ideal R, I.IsPrime -> I.IsMaximal。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
If R has Krull dimension ≤ 0, then `piLocalizationToIsMaximal R` is an isomorphi
sm.
-/
def piLocalizationToMaximalEquiv (h : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) :
    PiLocalization R ≃+* MaximalSpectrum.PiLocalization R where
  __ := piLocalizationToMaximal R
  invFun := RingHom.pi fun I ↦ Pi.evalRingHom _ (⟨_, h _ I.2⟩ : MaximalSpectrum R)
/-
**PrimeSpectrum.piLocalizationToMaximal_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Pri
meSpectrum`。
形式化陈述：piLocalizationToMaximal_bijective (h : forall I : Ideal R, I.IsPrime -> I.
IsMaximal) : Function.Bijective (piLocalizationToMaximal R)
参数：h : forall I : Ideal R, I.IsPrime -> I.IsMaximal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem piLocalizationToMaximal_bijective (h : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) :
    Function.Bijective (piLocalizationToMaximal R) :=
  (piLocalizationToMaximalEquiv h).bijective
/-
**PrimeSpectrum.piLocalizationToMaximal_comp_toPiLocalization** 是 Mathlib 中的一个定理
，位于命名空间 `PrimeSpectrum`。
形式化陈述：piLocalizationToMaximal_comp_toPiLocalization : (piLocalizationToMaximal R
).comp (toPiLocalization R) = MaximalSpectrum.toPiLocalization R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
theorem piLocalizationToMaximal_comp_toPiLocalization :
    (piLocalizationToMaximal R).comp (toPiLocalization R) = MaximalSpectrum.toPiLocalization R :=
  rfl

variable {S}
/-
**PrimeSpectrum.isMaximal_of_toPiLocalization_surjective** 是 Mathlib 中的一个定理，位于命名
空间 `PrimeSpectrum`。
形式化陈述：isMaximal_of_toPiLocalization_surjective (surj : Function.Surjective (toPi
Localization R)) (I : PrimeSpectrum R) : I.1.IsMaximal
参数：surj : Function.Surjective (toPiLocalization R)；I : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
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
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
-/
theorem isMaximal_of_toPiLocalization_surjective (surj : Function.Surjective (toPiLocalization R))
    (I : PrimeSpectrum R) : I.1.IsMaximal := by
  classical
  have ⟨J, max, le⟩ := I.1.exists_le_maximal I.2.ne_top
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max.isPrime⟩ 1)
  by_contra h
  have hJ : algebraMap _ _ r = _ := (congr_fun hr _).trans (Function.update_self ..)
  have hI : algebraMap _ _ r = _ := congr_fun hr I
  rw [← IsLocalization.lift_eq (M := J.primeCompl) (S := Localization J.primeCompl), hJ, map_one,
    Function.update_of_ne] at hI
  · exact one_ne_zero hI
  · intro eq; have : I.1 = J := congr_arg (·.1) eq; exact h (this ▸ max)
  · exact fun ⟨s, hs⟩ ↦ IsLocalization.map_units (M := I.1.primeCompl) _ ⟨s, fun h ↦ hs (le h)⟩

variable (f : R →+* S)

/-- A ring homomorphism induces a homomorphism between the products of localizations at primes. -/
/-
**PrimeSpectrum.mapPiLocalization** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：mapPiLocalization : PiLocalization R ->+* PiLocalization S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
A ring homomorphism induces a homomorphism between the products of localizations
 at primes.
-/
noncomputable def mapPiLocalization : PiLocalization R →+* PiLocalization S :=
  RingHom.pi fun I ↦ (Localization.localRingHom _ I.1 f rfl).comp (Pi.evalRingHom _ (comap f I))
/-
**PrimeSpectrum.mapPiLocalization_naturality** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：mapPiLocalization_naturality : (mapPiLocalization f).comp (toPiLocalizatio
n R) = (toPiLocalization S).toRingHom.comp f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsLocalization.mk'.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
theorem mapPiLocalization_naturality :
    (mapPiLocalization f).comp (toPiLocalization R) = (toPiLocalization S).toRingHom.comp f := by
  ext r I
  change Localization.localRingHom _ _ _ rfl (algebraMap _ _ r) = algebraMap _ _ (f r)
  simp_rw [← IsLocalization.mk'_one (M := (I.1.comap f).primeCompl), Localization.localRingHom_mk',
    ← IsLocalization.mk'_one (M := I.1.primeCompl), Submonoid.coe_one, map_one f]
  rfl
/-
**PrimeSpectrum.mapPiLocalization_id** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：mapPiLocalization_id : mapPiLocalization (.id R) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_id`：comap_id : I.comap (RingHom.id R) = I
· 使用定理 `Localization.localRingHom_id`：localRingHom_id : localRingHom I I (RingHo
m.id R) (Ideal.comap_id I).symm = RingHom.id _
-/
theorem mapPiLocalization_id : mapPiLocalization (.id R) = .id _ := by
  ext; exact congr($(Localization.localRingHom_id _) _)
/-
**PrimeSpectrum.mapPiLocalization_comp** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：mapPiLocalization_comp (g : S ->+* P) : mapPiLocalization (g.comp f) = (ma
pPiLocalization g).comp (mapPiLocalization f)
参数：g : S ->+* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Localization.localRingHom_comp`：localRingHom_comp {S : Type*} [CommSemir
ing S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P) [hK : K.IsPrime] (f : R ->+*
 S) (hIJ : I = J.com…
-/
theorem mapPiLocalization_comp (g : S →+* P) :
    mapPiLocalization (g.comp f) = (mapPiLocalization g).comp (mapPiLocalization f) := by
  ext; exact congr($(Localization.localRingHom_comp _ _ _ _ rfl _ rfl) _)
/-
**PrimeSpectrum.mapPiLocalization_bijective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：mapPiLocalization_bijective (hf : Function.Bijective f) : Function.Bijecti
ve (mapPiLocalization f)
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.mapPiLocalization_comp`：mapPiLocalization_comp (g : S ->+*
 P) : mapPiLocalization (g.comp f) = (mapPiLocalization g).comp (mapPiLocalizati
on f)
· 使用定理 `RingEquiv.comp_symm`：comp_symm (e : R ≃+* S) : (e : R ->+* S).comp (e.sy
mm : S ->+* R) = RingHom.id S
· 使用定理 `PrimeSpectrum.mapPiLocalization_id`：mapPiLocalization_id : mapPiLocaliza
tion (.id R) = .id _
· 使用定理 `RingEquiv.symm_comp`：symm_comp (e : R ≃+* S) : (e.symm : S ->+* R).comp 
(e : R ->+* S) = RingHom.id R
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
theorem mapPiLocalization_bijective (hf : Function.Bijective f) :
    Function.Bijective (mapPiLocalization f) := by
  let f := RingEquiv.ofBijective f hf
  let e := RingEquiv.ofRingHom (mapPiLocalization (f : R →+* S)) (mapPiLocalization f.symm) ?_ ?_
  · exact e.bijective
  · rw [← mapPiLocalization_comp, RingEquiv.comp_symm, mapPiLocalization_id]
  · rw [← mapPiLocalization_comp, RingEquiv.symm_comp, mapPiLocalization_id]

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)] [∀ i, Nontrivial (R i)]

/-
**PrimeSpectrum.toPiLocalization_not_surjective_of_infinite** 是 Mathlib 中的一个定理，位
于命名空间 `PrimeSpectrum`。
形式化陈述：toPiLocalization_not_surjective_of_infinite [Infinite ι] : ¬ Function.Surj
ective (toPiLocalization (Π i, R i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `MaximalSpectrum.toPiLocalization_not_surjective_of_infinite`：toPiLocaliz
ation_not_surjective_of_infinite [Infinite ι] : ¬ Function.Surjective (toPiLocal
ization (Π i, R i))
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `PrimeSpectrum.piLocalizationToMaximal_comp_toPiLocalization`：piLocalizat
ionToMaximal_comp_toPiLocalization : (piLocalizationToMaximal R).comp (toPiLocal
ization R) = MaximalSpectrum.toPiLocalization R
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `PrimeSpectrum.piLocalizationToMaximal_surjective`：piLocalizationToMaxima
l_surjective : Function.Surjective (piLocalizationToMaximal R)
-/
theorem toPiLocalization_not_surjective_of_infinite [Infinite ι] :
    ¬ Function.Surjective (toPiLocalization (Π i, R i)) :=
  fun surj ↦ MaximalSpectrum.toPiLocalization_not_surjective_of_infinite R <| by
    rw [← AlgHom.coe_toRingHom, ← piLocalizationToMaximal_comp_toPiLocalization]
    exact (piLocalizationToMaximal_surjective _).comp surj

variable {R}
/-
**PrimeSpectrum.finite_of_toPiLocalization_pi_surjective** 是 Mathlib 中的一个定理，位于命名
空间 `PrimeSpectrum`。
形式化陈述：finite_of_toPiLocalization_pi_surjective (h : Function.Surjective (toPiLoc
alization (Π i, R i))) : Finite ι
参数：h : Function.Surjective (toPiLocalization (Π i, R i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PrimeSpectrum.toPiLocalization_not_surjective_of_infinite`：toPiLocalizat
ion_not_surjective_of_infinite [Infinite ι] : ¬ Function.Surjective (toPiLocaliz
ation (Π i, R i))
-/
theorem finite_of_toPiLocalization_pi_surjective
    (h : Function.Surjective (toPiLocalization (Π i, R i))) :
    Finite ι := by
  contrapose! h
  exact toPiLocalization_not_surjective_of_infinite _

end Pi

/-
**PrimeSpectrum.finite_of_toPiLocalization_surjective** 是 Mathlib 中的一个定理，位于命名空间 
`PrimeSpectrum`。
形式化陈述：finite_of_toPiLocalization_surjective (surj : Function.Surjective (toPiLoc
alization R)) : Finite (PrimeSpectrum R)
参数：surj : Function.Surjective (toPiLocalization R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PrimeSpectrum.mapPiLocalization_bijective`：mapPiLocalization_bijective (
hf : Function.Bijective f) : Function.Bijective (mapPiLocalization f)
· 使用定理 `PrimeSpectrum.toPiLocalization_injective`：toPiLocalization_injective : F
unction.Injective (toPiLocalization R)
· 使用定理 `PrimeSpectrum.finite_of_toPiLocalization_pi_surjective`：finite_of_toPiLo
calization_pi_surjective (h : Function.Surjective (toPiLocalization (Π i, R i)))
 : Finite ι
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.coe_comp`：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp
 hmn : α -> γ) = hnp ∘ hmn
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `PrimeSpectrum.mapPiLocalization_naturality`：mapPiLocalization_naturality
 : (mapPiLocalization f).comp (toPiLocalization R) = (toPiLocalization S).toRing
Hom.comp f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
-/
theorem finite_of_toPiLocalization_surjective
    (surj : Function.Surjective (toPiLocalization R)) :
    Finite (PrimeSpectrum R) := by
  replace surj := (mapPiLocalization_bijective _ ⟨toPiLocalization_injective R, surj⟩).2.comp surj
  rw [← AlgHom.coe_toRingHom,
    ← RingHom.coe_comp, mapPiLocalization_naturality, RingHom.coe_comp] at surj
  exact finite_of_toPiLocalization_pi_surjective surj.of_comp

end PrimeSpectrum

