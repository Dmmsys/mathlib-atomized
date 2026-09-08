/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Junyan Xu
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Localization preserves unique factorization

## Main results

* `UniqueFactorizationMonoid.of_isLocalization`: a localization of a unique factorization monoid
  is still a unique factorization monoid. In particular, a localization of a UFD is a UFD provided
  it is nontrivial.
-/

@[expose] public section

variable {M N : Type*}

namespace Submonoid.LocalizationMap

variable [CommMonoidWithZero M] [CommMonoidWithZero N] {S : Submonoid M}

/-
**Submonoid.LocalizationMap.map_prime** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：map_prime (f : S.LocalizationMap N) {m : M} (prime : Prime m) (n0 : f m !=
 0) (nu : ¬ IsUnit (f m)) : Prime (f m)
参数：f : S.LocalizationMap N；prime : Prime m；n0 : f m != 0；nu : ¬ IsUnit (f m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUnit.dvd_mul_right`：dvd_mul_right (hu : IsUnit u) : a ∣ b * u ↔ a ∣ b
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.map_dvd_map`：∀ {M : Type u_1} {N : Type u_2} [
inst : CommMonoid M] {S : Submonoid M} [inst_1 : CommMonoid N]   (f : S.Localiza
tionMap N) {m₁ m₂ : M}, f m…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submonoid.mul_def`：mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2
⟩
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `IsUnit.dvd_mul_left`：dvd_mul_left (hu : IsUnit u) : a ∣ u * b ↔ a ∣ b
-/
theorem map_prime (f : S.LocalizationMap N) {m : M} (prime : Prime m)
    (n0 : f m ≠ 0) (nu : ¬ IsUnit (f m)) : Prime (f m) := by
  refine ⟨n0, nu, fun n₁ n₂ dvd ↦ ?_⟩
  have ⟨⟨m₁, s₁⟩, eq₁⟩ := f.surj n₁
  have ⟨⟨m₂, s₂⟩, eq₂⟩ := f.surj n₂
  have := (f.map_units (s₁ * s₂)).dvd_mul_right.mpr dvd
  rw [Submonoid.mul_def, map_mul, mul_mul_mul_comm, eq₁, eq₂, ← map_mul, f.map_dvd_map] at this
  have ⟨s, hs, dvd⟩ := this
  rw [← mul_assoc] at dvd
  obtain dvd | dvd := prime.dvd_or_dvd dvd
  all_goals have := map_dvd f dvd
  · rw [map_mul, (f.map_units ⟨s, hs⟩).dvd_mul_left, ← eq₁, (f.map_units s₁).dvd_mul_right] at this
    exact .inl this
  · rw [← eq₂, (f.map_units s₂).dvd_mul_right] at this; exact .inr this
/-
**Submonoid.LocalizationMap.eq_isUnit_map_mul_irreducible_of_irreducible_map** 是
 Mathlib 中的一个定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：eq_isUnit_map_mul_irreducible_of_irreducible_map [WfDvdMonoid M] (f : S.Lo
calizationMap N) {m : M} (hm : Irreducible (f m)) : exists u m' : M, IsUnit (f u
) ∧ Irreducible m' ∧ m = u * m'
参数：f : S.LocalizationMap N；hm : Irreducible (f m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.induction_on_irreducible`：induction_on_irreducible {motive :
 α -> Prop} (a : α) (zero : motive 0) (unit : forall u : α, IsUnit u -> motive u
) (mul : forall a i : α, a…
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Submonoid.LocalizationMap.map_zero`：∀ {M : Type u_1} [inst : CommMonoidW
ithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N]   (f
 : S.LocalizationMap N),…
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `irreducible_mul_iff`：irreducible_mul_iff : Irreducible (x * y) ↔ Irreduc
ible x ∧ IsUnit y ∨ Irreducible y ∧ IsUnit x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_isUnit_map_mul_irreducible_of_irreducible_map [WfDvdMonoid M] (f : S.LocalizationMap N)
    {m : M} (hm : Irreducible (f m)) : ∃ u m' : M, IsUnit (f u) ∧ Irreducible m' ∧ m = u * m' := by
  induction m using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hm.ne_zero f.map_zero).elim
  | unit u hu => exact (hm.not_isUnit (hu.map f)).elim
  | mul a i ha0 hi ha =>
    rw [map_mul, irreducible_mul_iff] at hm
    obtain hia | hai := hm
    · exact ⟨a, i, hia.2, hi, mul_comm ..⟩
    · obtain ⟨u, m', hu, hm', rfl⟩ := ha hai.1
      exact ⟨u * i, m', by simpa using hu.mul hai.2, hm', by ac_rfl⟩

open UniqueFactorizationMonoid in
/-
**Submonoid.LocalizationMap.uniqueFactorizationMonoid** 是 Mathlib 中的一个定理，位于命名空间 
`Submonoid.LocalizationMap`。
形式化陈述：uniqueFactorizationMonoid (f : S.LocalizationMap N) [UniqueFactorizationMo
noid M] : UniqueFactorizationMonoid N
参数：f : S.LocalizationMap N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.isCancelMulZero`：isCancelMulZero (f : Localiza
tionMap S N) [IsCancelMulZero M] : IsCancelMulZero N
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.of_exists_prime_factors`：UniqueFactorizationMo
noid.of_exists_prime_factors : UniqueFactorizationMonoid α
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
· 使用定理 `Submonoid.LocalizationMap.map_prime`：map_prime (f : S.LocalizationMap N)
 {m : M} (prime : Prime m) (n0 : f m != 0) (nu : ¬ IsUnit (f m)) : Prime (f m)
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_factors`：dvd_of_mem_factors {p a : 
α} (h : p in factors a) : p ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `associated_unit_mul_right`：associated_unit_mul_right {N : Type*} [CommMo
noid N] (a u : N) (hu : IsUnit u) : Associated a (u * a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsUnit.multisetProd_iff`：IsUnit.multisetProd_iff [CommMonoid M] {s : Mul
tiset M} : IsUnit s.prod ↔ forall a in s, IsUnit a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associated.of_eq`：Associated.of_eq [Monoid M] {a b : M} (h : a = b) : a 
~ᵤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.prod_filter_mul_prod_filter_not`：prod_filter_mul_prod_filter_no
t (p) [DecidablePred p] : (s.filter p).prod * (s.filter (fun a => ¬ p a)).prod =
 s.prod
· 使用定理 `MonoidHom.map_multiset_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : Com
mMonoid M] [inst_1 : CommMonoid N] (f : M →* N) (s : Multiset M),   f s.prod = (
Multiset.map (⇑f)…
（共 39 条，此处仅展示前 30 条）
-/
theorem uniqueFactorizationMonoid (f : S.LocalizationMap N)
    [UniqueFactorizationMonoid M] : UniqueFactorizationMonoid N :=
  have := f.isCancelMulZero
  .of_exists_prime_factors fun n hn ↦ by
    classical
    have ⟨⟨m, s⟩, eq⟩ := f.surj n
    use ((factors m).map f).filter (¬ IsUnit ·)
    rw [Ne, ← (f.map_units s).mul_left_eq_zero, eq] at hn
    refine ⟨fun x hx ↦ ?_, .trans (eq ▸ ?_) ((associated_mul_unit_left _ _ (f.map_units s)))⟩
    · rw [Multiset.mem_filter, Multiset.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx.1
      exact f.map_prime (prime_of_factor _ hp)
        (mt (fun h ↦ eq_zero_of_zero_dvd <| h ▸ map_dvd f (dvd_of_mem_factors hp)) hn) hx.2
    · exact .trans (.trans (associated_unit_mul_right _ _ <|
        IsUnit.multisetProd_iff.mpr fun x hx ↦ (Multiset.mem_filter.mp hx).2) <| .of_eq <|
        (Multiset.prod_filter_mul_prod_filter_not _).trans (f.toMonoidHom.map_multiset_prod _).symm)
        ((factors_prod (mt (by simp [·]) hn)).map f)

end Submonoid.LocalizationMap

variable [CommSemiring M] (S : Submonoid M)

/-- A localization of a unique factorization monoid is still a unique factorization monoid. -/
/-
**UniqueFactorizationMonoid.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueFactorizationMonoid.of_isLocalization (N : Type*) [CommSemiring N] [
Algebra M N] [IsLocalization S N] [UniqueFactorizationMonoid M] : UniqueFactoriz
ationMonoid N
参数：N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.uniqueFactorizationMonoid`：uniqueFactorization
Monoid (f : S.LocalizationMap N) [UniqueFactorizationMonoid M] : UniqueFactoriza
tionMonoid N

--- 原说明 ---
A localization of a unique factorization monoid is still a unique factorization 
monoid.
-/
theorem UniqueFactorizationMonoid.of_isLocalization (N : Type*) [CommSemiring N] [Algebra M N]
    [IsLocalization S N] [UniqueFactorizationMonoid M] : UniqueFactorizationMonoid N :=
  (IsLocalization.toLocalizationMap S N).uniqueFactorizationMonoid
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniqueFactorizationMonoid M] : UniqueFactorizationMonoid (Localization S) :=
  (Localization.monoidOf S).uniqueFactorizationMonoid
