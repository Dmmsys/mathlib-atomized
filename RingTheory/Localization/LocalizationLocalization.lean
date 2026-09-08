/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Localizations of localizations

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section



open Function

namespace IsLocalization

section LocalizationLocalization

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S] [Algebra R S]
variable (N : Submonoid S) (T : Type*) [CommSemiring T] [Algebra R T]


section

variable [Algebra S T] [IsScalarTower R S T]

-- This should only be defined when `S` is the localization `M⁻¹R`, hence the nolint.
/-- Localizing w.r.t. `M ⊆ R` and then w.r.t. `N ⊆ S = M⁻¹R` is equal to the localization of `R`
w.r.t. this submonoid. See `localization_localization_isLocalization`.
-/
@[nolint unusedArguments]
/-
**IsLocalization.localizationLocalizationSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Is
Localization`。
形式化陈述：localizationLocalizationSubmodule : Submonoid R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Localizing w.r.t. `M ⊆ R` and then w.r.t. `N ⊆ S = M⁻¹R` is equal to the localiz
ation of `R`
w.r.t. this submonoid. See `localization_localization_isLocalization`.
-/
def localizationLocalizationSubmodule : Submonoid R :=
  (N ⊔ M.map (algebraMap R S)).comap (algebraMap R S)

variable {M N}

@[simp]
/-
**IsLocalization.mem_localizationLocalizationSubmodule** 是 Mathlib 中的一个定理，位于命名空间
 `IsLocalization`。
形式化陈述：mem_localizationLocalizationSubmodule {x : R} : x in localizationLocalizat
ionSubmodule M N ↔ exists (y : N) (z : M), algebraMap R S x = y * algebraMap R S
 z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.localizationLocalizationSubmodule.eq_1`：∀ {R : Type u_1} 
[inst : CommSemiring R] (M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring 
S]   [inst_2 : Algebra R S] (N : Submonoid …
· 使用定理 `Submonoid.mem_comap`：mem_comap {S : Submonoid N} {f : F} {x : M} : x in 
S.comap f ↔ f x in S
· 使用定理 `Submonoid.mem_sup`：mem_sup {s t : Submonoid N} {x : N} : x in s ⊔ t ↔ ex
ists y in s, exists z in t, y * z = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mem_localizationLocalizationSubmodule {x : R} :
    x ∈ localizationLocalizationSubmodule M N ↔
      ∃ (y : N) (z : M), algebraMap R S x = y * algebraMap R S z := by
  rw [localizationLocalizationSubmodule, Submonoid.mem_comap, Submonoid.mem_sup]
  constructor
  · rintro ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, e.symm⟩
  · rintro ⟨y, z, e⟩
    exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩

variable (M N)
variable [IsLocalization M S]
/-
**IsLocalization.localization_localization_map_units** 是 Mathlib 中的一个定理，位于命名空间 `
IsLocalization`。
形式化陈述：localization_localization_map_units [IsLocalization N T] (y : localization
LocalizationSubmodule M N) : IsUnit (algebraMap R T y)
参数：y : localizationLocalizationSubmodule M N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mem_localizationLocalizationSubmodule`：mem_localizationLo
calizationSubmodule {x : R} : x in localizationLocalizationSubmodule M N ↔ exist
s (y : N) (z : M), algebraMap R S x = y * …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsUnit.mul_iff`：mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} 
: IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem localization_localization_map_units [IsLocalization N T]
    (y : localizationLocalizationSubmodule M N) : IsUnit (algebraMap R T y) := by
  obtain ⟨y', z, eq⟩ := mem_localizationLocalizationSubmodule.mp y.prop
  rw [IsScalarTower.algebraMap_apply R S T, eq, map_mul, IsUnit.mul_iff]
  exact ⟨IsLocalization.map_units T y', (IsLocalization.map_units _ z).map (algebraMap S T)⟩
/-
**IsLocalization.localization_localization_surj** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alization`。
形式化陈述：localization_localization_surj [IsLocalization N T] (x : T) : exists y : R
 × localizationLocalizationSubmodule M N, x * algebraMap R T y.2 = algebraMap R 
T y.1
参数：x : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.mem_localizationLocalizationSubmodule`：mem_localizationLo
calizationSubmodule {x : R} : x in localizationLocalizationSubmodule M N ↔ exist
s (y : N) (z : M), algebraMap R S x = y * …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
-/
theorem localization_localization_surj [IsLocalization N T] (x : T) :
    ∃ y : R × localizationLocalizationSubmodule M N,
        x * algebraMap R T y.2 = algebraMap R T y.1 := by
  rcases IsLocalization.surj N x with ⟨⟨y, s⟩, eq₁⟩
  -- x = y / s
  rcases IsLocalization.surj M y with ⟨⟨z, t⟩, eq₂⟩
  -- y = z / t
  rcases IsLocalization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩
  -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃
  refine ⟨⟨z * t', z' * t, ?_⟩, ?_⟩ -- x = y / s = (z * t') / (z' * t)
  · rw [mem_localizationLocalizationSubmodule]
    refine ⟨s, t * t', ?_⟩
    rw [map_mul, ← eq₃, mul_assoc, ← map_mul, mul_comm t, Submonoid.coe_mul]
  · simp only [map_mul, IsScalarTower.algebraMap_apply R S T, ← eq₃, ← eq₂, ← eq₁]
    ring
/-
**IsLocalization.localization_localization_exists_of_eq** 是 Mathlib 中的一个定理，位于命名空
间 `IsLocalization`。
形式化陈述：localization_localization_exists_of_eq [IsLocalization N T] (x y : R) : al
gebraMap R T x = algebraMap R T y -> exists c : localizationLocalizationSubmodul
e M N, ↑c * x = ↑c * y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mem_localizationLocalizationSubmodule`：mem_localizationLo
calizationSubmodule {x : R} : x in localizationLocalizationSubmodule M N ↔ exist
s (y : N) (z : M), algebraMap R S x = y * …
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
theorem localization_localization_exists_of_eq [IsLocalization N T] (x y : R) :
    algebraMap R T x = algebraMap R T y →
      ∃ c : localizationLocalizationSubmodule M N, ↑c * x = ↑c * y := by
  rw [IsScalarTower.algebraMap_apply R S T, IsScalarTower.algebraMap_apply R S T,
    IsLocalization.eq_iff_exists N T]
  rintro ⟨z, eq₁⟩
  rcases IsLocalization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩
  dsimp only at eq₂
  suffices (algebraMap R S) (x * z' : R) = (algebraMap R S) (y * z') by
    obtain ⟨c, eq₃ : ↑c * (x * z') = ↑c * (y * z')⟩ := (IsLocalization.eq_iff_exists M S).mp this
    refine ⟨⟨c * z', ?_⟩, ?_⟩
    · rw [mem_localizationLocalizationSubmodule]
      refine ⟨z, c * s, ?_⟩
      rw [map_mul, ← eq₂, Submonoid.coe_mul, map_mul, mul_left_comm]
    · rwa [mul_comm _ z', mul_comm _ z', ← mul_assoc, ← mul_assoc] at eq₃
  rw [map_mul, map_mul, ← eq₂, ← mul_assoc, ← mul_assoc, mul_comm _ (z : S), eq₁,
    mul_comm _ (z : S)]

/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, we have
`N ⁻¹ S = T = (f⁻¹ (N • f(M))) ⁻¹ R`. I.e., the localization of a localization is a localization.
-/
/-
**IsLocalization.localization_localization_isLocalization** 是 Mathlib 中的一个定理，位于命
名空间 `IsLocalization`。
形式化陈述：localization_localization_isLocalization [IsLocalization N T] : IsLocaliza
tion (localizationLocalizationSubmodule M N) T where map_units
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.localization_localization_map_units`：localization_localiz
ation_map_units [IsLocalization N T] (y : localizationLocalizationSubmodule M N)
 : IsUnit (algebraMap R T y)
· 使用定理 `IsLocalization.localization_localization_surj`：localization_localization
_surj [IsLocalization N T] (x : T) : exists y : R × localizationLocalizationSubm
odule M N, x * algebraMap R T y.2 =…
· 使用定理 `IsLocalization.localization_localization_exists_of_eq`：localization_loca
lization_exists_of_eq [IsLocalization N T] (x y : R) : algebraMap R T x = algebr
aMap R T y -> exists c : localizationLocali…

--- 原说明 ---
Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization
 map, we have
`N ⁻¹ S = T = (f⁻¹ (N • f(M))) ⁻¹ R`. I.e., the localization of a localization i
s a localization.
-/
theorem localization_localization_isLocalization [IsLocalization N T] :
    IsLocalization (localizationLocalizationSubmodule M N) T where
  map_units := localization_localization_map_units M N T
  surj := localization_localization_surj M N T
  exists_of_eq := localization_localization_exists_of_eq M N T _ _

include M in
/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, if
`N` contains all the units of `S`, then `N ⁻¹ S = T = (f⁻¹ N) ⁻¹ R`. I.e., the localization of a
localization is a localization.
-/
/-
**IsLocalization.localization_localization_isLocalization_of_has_all_units** 是 M
athlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：localization_localization_isLocalization_of_has_all_units [IsLocalization 
N T] (H : forall x : S, IsUnit x -> x in N) : IsLocalization (N.comap (algebraMa
p R S)) T
参数：H : forall x : S, IsUnit x -> x in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.localization_localization_isLocalization`：localization_lo
calization_isLocalization [IsLocalization N T] : IsLocalization (localizationLoc
alizationSubmodule M N) T where map_units

--- 原说明 ---
Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization
 map, if
`N` contains all the units of `S`, then `N ⁻¹ S = T = (f⁻¹ N) ⁻¹ R`. I.e., the l
ocalization of a
localization is a localization.
-/
theorem localization_localization_isLocalization_of_has_all_units [IsLocalization N T]
    (H : ∀ x : S, IsUnit x → x ∈ N) : IsLocalization (N.comap (algebraMap R S)) T := by
  convert! localization_localization_isLocalization M N T using 1
  dsimp [localizationLocalizationSubmodule]
  congr
  symm
  rw [sup_eq_left]
  rintro _ ⟨x, hx, rfl⟩
  exact H _ (IsLocalization.map_units _ ⟨x, hx⟩)

include M in
/--
Given a submodule `M ⊆ R` and a prime ideal `p` of `S = M⁻¹R`, with `f : R →+* S` the localization
map, then `T = Sₚ` is the localization of `R` at `f⁻¹(p)`.
-/
/-
**IsLocalization.isLocalization_isLocalization_atPrime_isLocalization** 是 Mathli
b 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isLocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p
.IsPrime] [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T (p.comap (alge
braMap R S))
参数：p : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.localization_localization_isLocalization_of_has_all_units
`：localization_localization_isLocalization_of_has_all_units [IsLocalization N T]
 (H : forall x : S, IsUnit x -> x in N) : IsLocalization (N.co…
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤

--- 原说明 ---
Given a submodule `M ⊆ R` and a prime ideal `p` of `S = M⁻¹R`, with `f : R →+* S
` the localization
map, then `T = Sₚ` is the localization of `R` at `f⁻¹(p)`.
-/
theorem isLocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
    [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T (p.comap (algebraMap R S)) := by
  apply localization_localization_isLocalization_of_has_all_units M p.primeCompl T
  intro x hx hx'
  exact (Hp.1 : ¬_) (p.eq_top_of_isUnit_mem hx' hx)
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal (Localization M)) [p.IsPrime] : Algebra R (Localization.AtPrime p) :=
  inferInstance
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal (Localization M)) [p.IsPrime] :
    IsScalarTower R (Localization M) (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq' rfl
/-
**IsLocalization.isLocalization_atPrime_localization_atPrime** 是 Mathlib 中的一个实例，
位于命名空间 `IsLocalization`。
形式化陈述：isLocalization_atPrime_localization_atPrime (p : Ideal (Localization M)) [
p.IsPrime] : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMa
p R _))
参数：p : Ideal (Localization M)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`：isL
ocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
 [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T …
· 使用定理 `IsLocalization.instIsScalarTowerLocalizationAtPrime`：∀ {R : Type u_1} [i
nst : CommSemiring R] (M : Submonoid R) (p : Ideal (Localization M)) [inst_1 : p
.IsPrime],   IsScalarTower R (Localizatio…
-/
instance isLocalization_atPrime_localization_atPrime (p : Ideal (Localization M))
    [p.IsPrime] : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap R _)) :=
  isLocalization_isLocalization_atPrime_isLocalization M _ _

/-- Given a submodule `M ⊆ R` and a prime ideal `p` of `M⁻¹R`, with `f : R →+* S` the localization
map, then `(M⁻¹R)ₚ` is isomorphic (as an `R`-algebra) to the localization of `R` at `f⁻¹(p)`.
-/
/-
**IsLocalization.localizationLocalizationAtPrimeIsoLocalization** 是 Mathlib 中的一个
定义，位于命名空间 `IsLocalization`。
形式化陈述：localizationLocalizationAtPrimeIsoLocalization (p : Ideal (Localization M)
) [p.IsPrime] : Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃
ₐ[R] Localization.AtPrime p
参数：p : Ideal (Localization M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a submodule `M ⊆ R` and a prime ideal `p` of `M⁻¹R`, with `f : R →+* S` th
e localization
map, then `(M⁻¹R)ₚ` is isomorphic (as an `R`-algebra) to the localization of `R`
 at `f⁻¹(p)`.
-/
noncomputable def localizationLocalizationAtPrimeIsoLocalization (p : Ideal (Localization M))
    [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃ₐ[R] Localization.AtPrime p :=
  IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _

end

variable (S)

/-- Given submonoids `M ≤ N` of `R`, this is the canonical algebra structure
of `M⁻¹S` acting on `N⁻¹S`. -/
/-
**IsLocalization.localizationAlgebraOfSubmonoidLe** 是 Mathlib 中的一个缩写定义，位于命名空间 `I
sLocalization`。
形式化陈述：localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M <= N) [IsLocal
ization M S] [IsLocalization N T] : Algebra S T
参数：M N : Submonoid R；h : M <= N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given submonoids `M ≤ N` of `R`, this is the canonical algebra structure
of `M⁻¹S` acting on `N⁻¹S`.
-/
noncomputable abbrev localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] : Algebra S T :=
  (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra

/-- If `M ≤ N` are submonoids of `R`, then the natural map `M⁻¹S →+* N⁻¹S` commutes with the
localization maps -/
/-
**IsLocalization.localization_isScalarTower_of_submonoid_le** 是 Mathlib 中的一个定理，位
于命名空间 `IsLocalization`。
形式化陈述：localization_isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M <= N
) [IsLocalization M S] [IsLocalization N T] : @IsScalarTower R S T _ (localizati
onAlgebraOfSubmonoidLe S T M N h).toSMul _
参数：M N : Submonoid R；h : M <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.lift_comp`：lift_comp : (lift hg).comp (algebraMap R S) = 
g

--- 原说明 ---
If `M ≤ N` are submonoids of `R`, then the natural map `M⁻¹S →+* N⁻¹S` commutes 
with the
localization maps
-/
theorem localization_isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] :
    @IsScalarTower R S T _ (localizationAlgebraOfSubmonoidLe S T M N h).toSMul _ :=
  letI := localizationAlgebraOfSubmonoidLe S T M N h
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
/-
**IsLocalization.instAlgebraLocalizationAtPrime** 是 Mathlib 中的一个实例，位于命名空间 `IsLoc
alization`。
形式化陈述：instAlgebraLocalizationAtPrime (x : Ideal R) [H : x.IsPrime] [IsDomain R] 
: Algebra (Localization.AtPrime x) (Localization (nonZeroDivisors R))
参数：x : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instAlgebraLocalizationAtPrime (x : Ideal R) [H : x.IsPrime] [IsDomain R] :
    Algebra (Localization.AtPrime x) (Localization (nonZeroDivisors R)) :=
  localizationAlgebraOfSubmonoidLe _ _ x.primeCompl (nonZeroDivisors R)
    (by
      intro a ha
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact fun h => ha (h.symm ▸ x.zero_mem))
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (Localization.AtPrime p) (FractionRing R) :=
  localization_isScalarTower_of_submonoid_le (Localization.AtPrime p) (FractionRing R)
    p.primeCompl (nonZeroDivisors R) p.primeCompl_le_nonZeroDivisors

/-- If `M ≤ N` are submonoids of `R`, then `N⁻¹S` is also the localization of `M⁻¹S` at `N`. -/
/-
**IsLocalization.isLocalization_of_submonoid_le** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alization`。
形式化陈述：isLocalization_of_submonoid_le (M N : Submonoid R) (h : M <= N) [IsLocaliz
ation M S] [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] : IsLocaliza
tion (N.map (algebraMap R S)) T where map_units
参数：M N : Submonoid R；h : M <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_image_iff`：exists_image_iff (f : α -> β) (x : Set α) (P : β -
> Prop) : (exists a : f '' x, P a) ↔ exists a : x, P (f a)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b

--- 原说明 ---
If `M ≤ N` are submonoids of `R`, then `N⁻¹S` is also the localization of `M⁻¹S`
 at `N`.
-/
theorem isLocalization_of_submonoid_le (M N : Submonoid R) (h : M ≤ N) [IsLocalization M S]
    [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] :
    IsLocalization (N.map (algebraMap R S)) T where
  map_units := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units T ⟨y, hy⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
  surj y := by
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj N y
    refine ⟨⟨algebraMap R S x, _, _, s.prop, rfl⟩, ?_⟩
    simpa [← IsScalarTower.algebraMap_apply] using! e
  exists_of_eq {x₁ x₂} := by
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := IsLocalization.surj M x₁
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := IsLocalization.surj M x₂
    refine (Set.exists_image_iff (algebraMap R S) N fun c => c * x₁ = c * x₂).mpr.comp ?_
    dsimp only at e₁ e₂ ⊢
    suffices algebraMap R T (y₁ * s₂) = algebraMap R T (y₂ * s₁) →
        ∃ a : N, algebraMap R S (a * (y₁ * s₂)) = algebraMap R S (a * (y₂ * s₁)) by
      have h₁ := @IsUnit.mul_left_inj T _ _ (algebraMap S T x₁) (algebraMap S T x₂)
        (IsLocalization.map_units T ⟨(s₁ : R), h s₁.prop⟩)
      have h₂ := @IsUnit.mul_left_inj T _ _ ((algebraMap S T x₁) * (algebraMap R T s₁))
        ((algebraMap S T x₂) * (algebraMap R T s₁))
        (IsLocalization.map_units T ⟨(s₂ : R), h s₂.prop⟩)
      simp only [IsScalarTower.algebraMap_apply R S T] at h₁ h₂
      simp only [IsScalarTower.algebraMap_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
        mul_right_comm _ (algebraMap R S s₂),
        (IsLocalization.map_units S s₁).mul_left_inj,
        (IsLocalization.map_units S s₂).mul_left_inj] at this
      rw [h₂, h₁] at this
      simpa only [mul_comm] using! this
    simp_rw [IsLocalization.eq_iff_exists N T, IsLocalization.eq_iff_exists M S]
    intro ⟨a, e⟩
    exact ⟨a, 1, by convert! e using 1 <;> simp⟩

/-- If `M ≤ N` are submonoids of `R` such that `∀ x : N, ∃ m : R, m * x ∈ M`, then the
localization at `N` is equal to the localization of `M`. -/
/-
**IsLocalization.isLocalization_of_is_exists_mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `
IsLocalization`。
形式化陈述：isLocalization_of_is_exists_mul_mem (M N : Submonoid R) [IsLocalization M 
S] (h : M <= N) (h' : forall x : N, exists m : R, m * x in M) : IsLocalization N
 S where map_units y
参数：M N : Submonoid R；h : M <= N；h' : forall x : N, exists m : R, m * x in M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_iff`：mul_iff [Monoid M] [IsDedekindFiniteMonoid M] {x y : M} 
: IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y

--- 原说明 ---
If `M ≤ N` are submonoids of `R` such that `∀ x : N, ∃ m : R, m * x ∈ M`, then t
he
localization at `N` is equal to the localization of `M`.
-/
theorem isLocalization_of_is_exists_mul_mem (M N : Submonoid R) [IsLocalization M S] (h : M ≤ N)
    (h' : ∀ x : N, ∃ m : R, m * x ∈ M) : IsLocalization N S where
  map_units y := by
    obtain ⟨m, hm⟩ := h' y
    have := IsLocalization.map_units S ⟨_, hm⟩
    rw [map_mul] at this
    exact (IsUnit.mul_iff.mp this).2
  surj z := by
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M z
    exact ⟨⟨y, _, h s.prop⟩, e⟩
  exists_of_eq {_ _} := by
    rw [IsLocalization.eq_iff_exists M]
    exact fun ⟨x, hx⟩ => ⟨⟨_, h x.prop⟩, hx⟩
/-
**IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le** 是 Mathlib 中的一个定理，位于命名空间
 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Type u_2) [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommSemiring T] [inst_
4 : Algebra R T] {M N : Submonoid R} (h : M ≤ N) [inst_5 : IsLocalization M S]  
 [inst_6 : IsLocalization N T] [inst_7 : Algebra S T] [IsScalarTower R S T] (x :
 R) (y : ↥M),   IsLocalization.mk' T x ⟨↑y, ⋯⟩ = (algebraMap S T) (IsLocalizatio
n.mk' S x y)
参数：S : Type u_2；T : Type u_3；h : M ≤ N；x : R；y : ↥M；algebraMap S T；IsLocalizatio
n.mk' S x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalization.mk'_eq_iff_eq_mul`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk'_eq_algebraMap_mk'_of_submonoid_le {M N : Submonoid R} (h : M ≤ N) [IsLocalization M S]
    [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] (x : R) (y : {a : R // a ∈ M}) :
    mk' T x ⟨y.1, h y.2⟩ = algebraMap S T (mk' S x y) :=
  mk'_eq_iff_eq_mul.mpr (by simp only [IsScalarTower.algebraMap_apply R S T, ← map_mul, mk'_spec])

end LocalizationLocalization

end IsLocalization

namespace IsFractionRing

variable {R : Type*} [CommRing R] (M : Submonoid R)

open IsLocalization

set_option backward.isDefEq.respectTransparency false in
/-
**IsFractionRing.isFractionRing_of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `IsF
ractionRing`。
形式化陈述：isFractionRing_of_isLocalization (S T : Type*) [CommRing S] [CommRing T] [
Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [IsLocalization M
 S] [IsFractionRing R T] (hM : M <= nonZeroDivisors R) : IsFractionRing S T
参数：S T : Type*；hM : M <= nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.isLocalization_of_submonoid_le`：isLocalization_of_submono
id_le (M N : Submonoid R) (h : M <= N) [IsLocalization M S] [IsLocalization N T]
 [Algebra S T] [IsScalarTower R S T…
· 使用定理 `IsLocalization.isLocalization_of_is_exists_mul_mem`：isLocalization_of_is
_exists_mul_mem (M N : Submonoid R) [IsLocalization M S] (h : M <= N) (h' : fora
ll x : N, exists m : R, m * x in M) : Is…
· 使用定理 `IsLocalization.map_nonZeroDivisors_le`：map_nonZeroDivisors_le [IsLocaliz
ation M S] : (nonZeroDivisors R).map (algebraMap R S) <= nonZeroDivisors S
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_right`：mem_nonZeroDivisors_iff_right : r in M₀⁰ 
↔ forall x, x * r = 0 -> x = 0
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem isFractionRing_of_isLocalization (S T : Type*) [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] [IsLocalization M S] [IsFractionRing R T]
    (hM : M ≤ nonZeroDivisors R) : IsFractionRing S T := by
  have := isLocalization_of_submonoid_le S T M (nonZeroDivisors R) hM
  refine @isLocalization_of_is_exists_mul_mem _ _ _ _ _ _ _ this ?_ ?_
  · exact map_nonZeroDivisors_le M S
  · rintro ⟨x, -, hx⟩
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M x
    use algebraMap R S s
    rw [mul_comm, Subtype.coe_mk, e]
    refine Set.mem_image_of_mem (algebraMap R S) (mem_nonZeroDivisors_iff_right.mpr ?_)
    intro z hz
    apply IsLocalization.injective S hM
    rw [map_zero]
    apply hx
    rw [← (map_units S s).mul_left_inj, mul_assoc, e, ← map_mul, hz, map_zero,
      zero_mul]
/-
**IsFractionRing.isFractionRing_of_isDomain_of_isLocalization** 是 Mathlib 中的一个定理
，位于命名空间 `IsFractionRing`。
形式化陈述：isFractionRing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [C
ommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower
 R S T] [IsLocalization M S] [IsFractionRing R T] : IsFractionRing S T
参数：S T : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.nontrivial`：∀ (R : Type u_8) (S : Type u_9) [inst : CommS
emiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   [h : IsFractionRin
g R S] [hR : No…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `IsFractionRing.isFractionRing_of_isLocalization`：isFractionRing_of_isLoc
alization (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [A
lgebra S T] [IsScalarTower R S T] [Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `comm`：comm [Std.Symm r] {a b : α} : r a b ↔ r b a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `IsLocalization.mk'_eq_zero_iff`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra 
R S] [inst_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isFractionRing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization M S] [IsFractionRing R T] : IsFractionRing S T := by
  have := IsFractionRing.nontrivial R T
  have := (algebraMap S T).domain_nontrivial
  apply isFractionRing_of_isLocalization M S T
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro hx'
  apply @zero_ne_one S
  rw [← (algebraMap R S).map_one, ← @mk'_one R _ M, @comm _ Eq, mk'_eq_zero_iff]
  exact ⟨⟨x, hx⟩, by simp [hx']⟩
/-
**IsFractionRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsFractionRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    IsFractionRing (Localization.AtPrime p) (FractionRing R) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl
    (Localization.AtPrime p) (FractionRing R)

end IsFractionRing

