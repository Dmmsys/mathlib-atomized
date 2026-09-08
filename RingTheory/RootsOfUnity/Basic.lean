/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.RingTheory.IntegralDomain

-- TODO: remove Mathlib.Algebra.CharP.Reduced and move the last two lemmas to Lemmas

/-!
# Roots of unity

We define roots of unity in the context of an arbitrary commutative monoid,
as a subgroup of the group of units.

## Main definitions

* `rootsOfUnity n M`, for `n : ℕ` is the subgroup of the units of a commutative monoid `M`
  consisting of elements `x` that satisfy `x ^ n = 1`.

## Main results

* `rootsOfUnity.isCyclic`: the roots of unity in an integral domain form a cyclic group.

## Implementation details

It is desirable that `rootsOfUnity` is a subgroup,
and it will mainly be applied to rings (e.g. the ring of integers in a number field) and fields.
We therefore implement it as a subgroup of the units of a commutative monoid.

We have chosen to define `rootsOfUnity n` for `n : ℕ` and add a `[NeZero n]` typeclass
assumption when we need `n` to be non-zero (which is the case for most interesting statements).
Note that `rootsOfUnity 0 M` is the top subgroup of `Mˣ` (as the condition `ζ^0 = 1` is
satisfied for all units).
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

variable {M N G R S F : Type*}
variable [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]

section rootsOfUnity

variable {k l : ℕ}

/-- `rootsOfUnity k M` is the subgroup of elements `m : Mˣ` that satisfy `m ^ k = 1`. -/
/-
**rootsOfUnity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rootsOfUnity (k : Nat) (M : Type*) [CommMonoid M] : Subgroup Mˣ where carr
ier
参数：k : Nat；M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rootsOfUnity k M` is the subgroup of elements `m : Mˣ` that satisfy `m ^ k = 1`
.
-/
def rootsOfUnity (k : ℕ) (M : Type*) [CommMonoid M] : Subgroup Mˣ where
  carrier := {ζ | ζ ^ k = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_ofPred_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_ofPred_eq, inv_pow, inv_one]

@[simp]
/-
**mem_rootsOfUnity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rootsOfUnity (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnity k M ↔ ζ ^ k = 1
参数：k : Nat；ζ : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_rootsOfUnity (k : ℕ) (ζ : Mˣ) : ζ ∈ rootsOfUnity k M ↔ ζ ^ k = 1 :=
  Iff.rfl
/-
**rootsOfUnity_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity_eq_ker : rootsOfUnity k M = (powMonoidHom k).ker
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootsOfUnity_eq_ker : rootsOfUnity k M = (powMonoidHom k).ker := by
  rfl
/-
**ker_zpowGroupHom_eq_rootsOfUnity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ker_zpowGroupHom_eq_rootsOfUnity {k : Int} : (zpowGroupHom k).ker = rootsO
fUnity k.natAbs M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpowGroupHom_apply`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (n : 
ℤ) (x : α), (zpowGroupHom n) x = x ^ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_zpowGroupHom_eq_rootsOfUnity {k : ℤ} :
    (zpowGroupHom k).ker = rootsOfUnity k.natAbs M := by
  ext; simp

/-- A variant of `mem_rootsOfUnity` using `ζ : Mˣ`. -/
/-
**mem_rootsOfUnity'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rootsOfUnity' (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnity k M ↔ (ζ : M) ^ k
 = 1
参数：k : Nat；ζ : Mˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_rootsOfUnity`：mem_rootsOfUnity (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnit
y k M ↔ ζ ^ k = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A variant of `mem_rootsOfUnity` using `ζ : Mˣ`.
-/
theorem mem_rootsOfUnity' (k : ℕ) (ζ : Mˣ) : ζ ∈ rootsOfUnity k M ↔ (ζ : M) ^ k = 1 := by
  rw [mem_rootsOfUnity]; norm_cast

@[simp]
/-
**rootsOfUnity_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity_one (M : Type*) [CommMonoid M] : rootsOfUnity 1 M = ⊥
参数：M : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rootsOfUnity_one (M : Type*) [CommMonoid M] : rootsOfUnity 1 M = ⊥ := by
  ext1
  simp only [mem_rootsOfUnity, pow_one, Subgroup.mem_bot]

@[simp]
/-
**rootsOfUnity_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rootsOfUnity_zero (M : Type*) [CommMonoid M] : rootsOfUnity 0 M = ⊤
参数：M : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rootsOfUnity_zero (M : Type*) [CommMonoid M] : rootsOfUnity 0 M = ⊤ := by
  ext1
  simp only [mem_rootsOfUnity, pow_zero, Subgroup.mem_top]
/-
**rootsOfUnity.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity.coe_injective {n : Nat} : Function.Injective (fun x : rootsOf
Unity n M => x.val.val)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem rootsOfUnity.coe_injective {n : ℕ} :
    Function.Injective (fun x : rootsOfUnity n M ↦ x.val.val) :=
  Units.val_injective.comp Subtype.val_injective

/-- Make an element of `rootsOfUnity` from a member of the base ring, and a proof that it has
a positive power equal to one. -/
@[simps! coe_val]
/-
**rootsOfUnity.mkOfPowEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rootsOfUnity.mkOfPowEq (ζ : M) {n : Nat} [NeZero n] (h : ζ ^ n = 1) : root
sOfUnity n M
参数：ζ : M；h : ζ ^ n = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an element of `rootsOfUnity` from a member of the base ring, and a proof th
at it has
a positive power equal to one.
-/
def rootsOfUnity.mkOfPowEq (ζ : M) {n : ℕ} [NeZero n] (h : ζ ^ n = 1) : rootsOfUnity n M :=
  ⟨Units.ofPowEqOne ζ n h <| NeZero.ne n, Units.pow_ofPowEqOne _ _⟩

@[simp]
/-
**rootsOfUnity.coe_mkOfPowEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity.coe_mkOfPowEq {ζ : M} {n : Nat} [NeZero n] (h : ζ ^ n = 1) : 
((rootsOfUnity.mkOfPowEq _ h : Mˣ) : M) = ζ
参数：h : ζ ^ n = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootsOfUnity.coe_mkOfPowEq {ζ : M} {n : ℕ} [NeZero n] (h : ζ ^ n = 1) :
    ((rootsOfUnity.mkOfPowEq _ h : Mˣ) : M) = ζ :=
  rfl
/-
**rootsOfUnity_le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity_le_of_dvd (h : k ∣ l) : rootsOfUnity k M <= rootsOfUnity l M
参数：h : k ∣ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem rootsOfUnity_le_of_dvd (h : k ∣ l) : rootsOfUnity k M ≤ rootsOfUnity l M := by
  obtain ⟨d, rfl⟩ := h
  intro ζ h
  simp_all only [mem_rootsOfUnity, pow_mul, one_pow]
/-
**map_rootsOfUnity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_rootsOfUnity (f : Mˣ ->* Nˣ) (k : Nat) : (rootsOfUnity k M).map f <= r
ootsOfUnity k N
参数：f : Mˣ ->* Nˣ；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_rootsOfUnity (f : Mˣ →* Nˣ) (k : ℕ) : (rootsOfUnity k M).map f ≤ rootsOfUnity k N := by
  rintro _ ⟨ζ, h, rfl⟩
  simp_all only [← map_pow, mem_rootsOfUnity, SetLike.mem_coe, map_one]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (rootsOfUnity 1 M) := by simp [subsingleton_iff]
/-
**rootsOfUnity_inf_rootsOfUnity** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rootsOfUnity_inf_rootsOfUnity {m n : Nat} : (rootsOfUnity m M ⊓ rootsOfUni
ty n M) = rootsOfUnity (m.gcd n) M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rootsOfUnity_inf_rootsOfUnity {m n : ℕ} :
    (rootsOfUnity m M ⊓ rootsOfUnity n M) = rootsOfUnity (m.gcd n) M := by
  ext
  simp
/-
**disjoint_rootsOfUnity_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_rootsOfUnity_of_coprime {m n : Nat} (h : m.Coprime n) : Disjoint 
(rootsOfUnity m M) (rootsOfUnity n M)
参数：h : m.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `rootsOfUnity_inf_rootsOfUnity`：rootsOfUnity_inf_rootsOfUnity {m n : Nat}
 : (rootsOfUnity m M ⊓ rootsOfUnity n M) = rootsOfUnity (m.gcd n) M
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用定理 `rootsOfUnity_one`：rootsOfUnity_one (M : Type*) [CommMonoid M] : rootsOfU
nity 1 M = ⊥
-/
lemma disjoint_rootsOfUnity_of_coprime {m n : ℕ} (h : m.Coprime n) :
    Disjoint (rootsOfUnity m M) (rootsOfUnity n M) := by
  simp [disjoint_iff_inf_le, rootsOfUnity_inf_rootsOfUnity, Nat.coprime_iff_gcd_eq_one.mp h]

@[norm_cast]
/-
**rootsOfUnity.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnity.coe_pow [CommMonoid R] (ζ : rootsOfUnity k R) (m : Nat) : (((
ζ ^ m :) : Rˣ) : R) = ((ζ : Rˣ) : R) ^ m
参数：ζ : rootsOfUnity k R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.coe_pow`：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G
) ^ n
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
-/
theorem rootsOfUnity.coe_pow [CommMonoid R] (ζ : rootsOfUnity k R) (m : ℕ) :
    (((ζ ^ m :) : Rˣ) : R) = ((ζ : Rˣ) : R) ^ m := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

/-- The canonical isomorphism from the `n`th roots of unity in `Mˣ`
to the `n`th roots of unity in `M`. -/
/-
**rootsOfUnityUnitsMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rootsOfUnityUnitsMulEquiv (M : Type*) [CommMonoid M] (n : Nat) : rootsOfUn
ity n Mˣ ≃* rootsOfUnity n M where toFun ζ
参数：M : Type*；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism from the `n`th roots of unity in `Mˣ`
to the `n`th roots of unity in `M`.
-/
def rootsOfUnityUnitsMulEquiv (M : Type*) [CommMonoid M] (n : ℕ) :
    rootsOfUnity n Mˣ ≃* rootsOfUnity n M where
  toFun ζ := ⟨ζ.val, (mem_rootsOfUnity ..).mpr <| (mem_rootsOfUnity' ..).mp ζ.prop⟩
  invFun ζ := ⟨toUnits ζ.val, by
    simp only [mem_rootsOfUnity, ← map_pow, EmbeddingLike.map_eq_one_iff]
    exact (mem_rootsOfUnity ..).mp ζ.prop⟩
  left_inv ζ := by simp only [toUnits_val_apply, Subtype.coe_eta]
  right_inv ζ := by simp only [val_toUnits_apply, Subtype.coe_eta]
  map_mul' ζ ζ' := by simp only [Subgroup.coe_mul, Units.val_mul, MulMemClass.mk_mul_mk]

section CommMonoid

variable [CommMonoid R] [CommMonoid S] [FunLike F R S]

/-- Restrict a ring homomorphism to the nth roots of unity. -/
/-
**restrictRootsOfUnity** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：restrictRootsOfUnity [MonoidHomClass F R S] (σ : F) (n : Nat) : rootsOfUni
ty n R ->* rootsOfUnity n S
参数：σ : F；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a ring homomorphism to the nth roots of unity.
-/
def restrictRootsOfUnity [MonoidHomClass F R S] (σ : F) (n : ℕ) :
    rootsOfUnity n R →* rootsOfUnity n S :=
  { toFun := fun ξ ↦ ⟨Units.map σ (ξ : Rˣ), by
      rw [mem_rootsOfUnity, ← map_pow, Units.ext_iff, Units.coe_map, ξ.prop]
      exact map_one σ⟩
    map_one' := by ext1; simp only [OneMemClass.coe_one, map_one]
    map_mul' := fun ξ₁ ξ₂ ↦ by
      ext1; simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk] }

@[simp]
/-
**restrictRootsOfUnity_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：restrictRootsOfUnity_coe_apply [MonoidHomClass F R S] (σ : F) (ζ : rootsOf
Unity k R) : (restrictRootsOfUnity σ k ζ : Sˣ) = σ (ζ : Rˣ)
参数：σ : F；ζ : rootsOfUnity k R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictRootsOfUnity_coe_apply [MonoidHomClass F R S] (σ : F) (ζ : rootsOfUnity k R) :
    (restrictRootsOfUnity σ k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

/-- Restrict a monoid isomorphism to the nth roots of unity. -/
nonrec def MulEquiv.restrictRootsOfUnity (σ : R ≃* S) (n : ℕ) :
    rootsOfUnity n R ≃* rootsOfUnity n S where
  toFun := restrictRootsOfUnity σ n
  invFun := restrictRootsOfUnity σ.symm n
  left_inv ξ := by ext; exact σ.symm_apply_apply _
  right_inv ξ := by ext; exact σ.apply_symm_apply _
  map_mul' := (restrictRootsOfUnity _ n).map_mul

@[simp]
/-
**MulEquiv.restrictRootsOfUnity_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.restrictRootsOfUnity_coe_apply (σ : R ≃* S) (ζ : rootsOfUnity k R
) : (σ.restrictRootsOfUnity k ζ : Sˣ) = σ (ζ : Rˣ)
参数：σ : R ≃* S；ζ : rootsOfUnity k R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulEquiv.restrictRootsOfUnity_coe_apply (σ : R ≃* S) (ζ : rootsOfUnity k R) :
    (σ.restrictRootsOfUnity k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

@[simp]
/-
**MulEquiv.restrictRootsOfUnity_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquiv.restrictRootsOfUnity_symm (σ : R ≃* S) : (σ.restrictRootsOfUnity 
k).symm = σ.symm.restrictRootsOfUnity k
参数：σ : R ≃* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MulEquiv.restrictRootsOfUnity_symm (σ : R ≃* S) :
    (σ.restrictRootsOfUnity k).symm = σ.symm.restrictRootsOfUnity k :=
  rfl

@[simp]
/-
**Units.val_set_image_rootsOfUnity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.val_set_image_rootsOfUnity [NeZero k] : ((↑) : Rˣ -> _) '' (rootsOfU
nity k R) = {z : R | z^k = 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_rootsOfUnity'`：mem_rootsOfUnity' (k : Nat) (ζ : Mˣ) : ζ in rootsOfUn
ity k M ↔ (ζ : M) ^ k = 1
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
-/
theorem Units.val_set_image_rootsOfUnity [NeZero k] :
    ((↑) : Rˣ → _) '' (rootsOfUnity k R) = {z : R | z^k = 1} := by
  ext x
  exact ⟨fun ⟨y,hy1,hy2⟩ => by rw [← hy2]; exact (mem_rootsOfUnity' k y).mp hy1,
    fun h ↦ ⟨(rootsOfUnity.mkOfPowEq x h), ⟨Subtype.coe_prop (rootsOfUnity.mkOfPowEq x h), rfl⟩⟩⟩
/-
**Units.val_set_image_rootsOfUnity_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.val_set_image_rootsOfUnity_one : ((↑) : Rˣ -> R) '' (rootsOfUnity 1 
R) = {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rootsOfUnity_one`：rootsOfUnity_one (M : Type*) [CommMonoid M] : rootsOfU
nity 1 M = ⊥
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Units.val_set_image_rootsOfUnity_one : ((↑) : Rˣ → R) '' (rootsOfUnity 1 R) = {1} := by
  simp

end CommMonoid

section CommRing

variable [CommRing R]

open Set in
/-
**Units.val_set_image_rootsOfUnity_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.val_set_image_rootsOfUnity_two [NoZeroDivisors R] : ((↑) : Rˣ -> R) 
'' (rootsOfUnity 2 R) = {1, -1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.val_set_image_rootsOfUnity`：Units.val_set_image_rootsOfUnity [NeZe
ro k] : ((↑) : Rˣ -> _) '' (rootsOfUnity k R) = {z : R | z^k = 1}
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Units.val_set_image_rootsOfUnity_two [NoZeroDivisors R] :
    ((↑) : Rˣ → R) '' (rootsOfUnity 2 R) = {1, -1} := by
  ext x
  simp
/-
**mem_rootsOfUnity_iff_isRoot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rootsOfUnity_iff_isRoot (k : Nat) (ζ : Rˣ) : ζ in rootsOfUnity k R ↔ (
X ^ k - 1 : R[X]).IsRoot ζ
参数：k : Nat；ζ : Rˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_rootsOfUnity_iff_isRoot (k : ℕ) (ζ : Rˣ) :
    ζ ∈ rootsOfUnity k R ↔ (X ^ k - 1 : R[X]).IsRoot ζ := by
  simp [-mem_rootsOfUnity, mem_rootsOfUnity', sub_eq_zero]

end CommRing

section IsDomain

-- The following results need `k` to be nonzero.
variable [NeZero k] [CommRing R] [IsDomain R]

/-
**mem_rootsOfUnity_iff_mem_nthRoots** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rootsOfUnity_iff_mem_nthRoots {ζ : Rˣ} : ζ in rootsOfUnity k R ↔ (ζ : 
R) in nthRoots k (1 : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_nthRoots`：mem_nthRoots {n : Nat} (hn : 0 < n) {a x : R} :
 x in nthRoots n a ↔ x ^ n = a
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_rootsOfUnity_iff_mem_nthRoots {ζ : Rˣ} :
    ζ ∈ rootsOfUnity k R ↔ (ζ : R) ∈ nthRoots k (1 : R) := by
  simp only [mem_rootsOfUnity, mem_nthRoots (NeZero.pos k), Units.ext_iff, Units.val_one,
    Units.val_pow_eq_pow_val]

variable (k R)

/-- Equivalence between the `k`-th roots of unity in `R` and the `k`-th roots of `1`.

This is implemented as equivalence of subtypes,
because `rootsOfUnity` is a subgroup of the group of units,
whereas `nthRoots` is a multiset. -/
/-
**rootsOfUnityEquivNthRoots** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rootsOfUnityEquivNthRoots : rootsOfUnity k R ≃ { x // x in nthRoots k (1 :
 R) } where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between the `k`-th roots of unity in `R` and the `k`-th roots of `1`
.

This is implemented as equivalence of subtypes,
because `rootsOfUnity` is a subgroup of the group of units,
whereas `nthRoots` is a multiset.
-/
def rootsOfUnityEquivNthRoots : rootsOfUnity k R ≃ { x // x ∈ nthRoots k (1 : R) } where
  toFun x := ⟨(x : Rˣ), mem_rootsOfUnity_iff_mem_nthRoots.mp x.2⟩
  invFun x := by
    refine ⟨⟨x, ↑x ^ (k - 1 : ℕ), ?_, ?_⟩, ?_⟩
    all_goals
      rcases x with ⟨x, hx⟩; rw [mem_nthRoots <| NeZero.pos k] at hx
      simp only [← pow_succ, ← pow_succ', hx, tsub_add_cancel_of_le NeZero.one_le]
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, hx, Units.val_one]

variable {k R}

@[simp]
/-
**rootsOfUnityEquivNthRoots_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnityEquivNthRoots_apply (x : rootsOfUnity k R) : (rootsOfUnityEqui
vNthRoots R k x : R) = ((x : Rˣ) : R)
参数：x : rootsOfUnity k R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rootsOfUnityEquivNthRoots_apply (x : rootsOfUnity k R) :
    (rootsOfUnityEquivNthRoots R k x : R) = ((x : Rˣ) : R) :=
  rfl

@[simp]
/-
**rootsOfUnityEquivNthRoots_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rootsOfUnityEquivNthRoots_symm_apply (x : { x // x in nthRoots k (1 : R) }
) : (((rootsOfUnityEquivNthRoots R k).symm x : Rˣ) : R) = (x : R)
参数：x : { x // x in nthRoots k (1 : R) }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem rootsOfUnityEquivNthRoots_symm_apply (x : { x // x ∈ nthRoots k (1 : R) }) :
    (((rootsOfUnityEquivNthRoots R k).symm x : Rˣ) : R) = (x : R) :=
  rfl

variable (k R)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite (rootsOfUnity k R) := by
  classical
  exact .of_equiv { x // x ∈ nthRoots k (1 : R) } (rootsOfUnityEquivNthRoots R k).symm
/-
**rootsOfUnity.isCyclic** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：rootsOfUnity.isCyclic : IsCyclic (rootsOfUnity k R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_injective_ringHom`：isCyclic_of_injective_ringHom [Finite G] 
(f : G ->* R) (hf : Injective f) : IsCyclic G
· 使用定理 `instFiniteSubtypeUnitsMemSubgroupRootsOfUnity`：∀ (R : Type u_4) (k : ℕ) 
[NeZero k] [inst : CommRing R] [IsDomain R], Finite ↥(rootsOfUnity k R)
· 使用定理 `rootsOfUnity.coe_injective`：rootsOfUnity.coe_injective {n : Nat} : Funct
ion.Injective (fun x : rootsOfUnity n M => x.val.val)
-/
instance rootsOfUnity.isCyclic : IsCyclic (rootsOfUnity k R) :=
  isCyclic_of_injective_ringHom ((Units.coeHom R).comp (rootsOfUnity k R).subtype) coe_injective
/-
**card_rootsOfUnity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_rootsOfUnity : Nat.card (rootsOfUnity k R) <= k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
· 使用定理 `Multiset.card_attach`：card_attach {m : Multiset α} : card (attach m) = c
ard m
· 使用定理 `Polynomial.card_nthRoots`：card_nthRoots (n : Nat) (a : R) : Multiset.car
d (nthRoots n a) <= n
-/
theorem card_rootsOfUnity : Nat.card (rootsOfUnity k R) ≤ k := by
  classical
  calc
    Nat.card (rootsOfUnity k R) = Nat.card { x // x ∈ nthRoots k (1 : R) } :=
      Nat.card_congr (rootsOfUnityEquivNthRoots R k)
    _ = Fintype.card { x // x ∈ nthRoots k (1 : R) } := Nat.card_eq_fintype_card
    _ ≤ Multiset.card (nthRoots k (1 : R)).attach := Multiset.card_le_card (Multiset.dedup_le _)
    _ = Multiset.card (nthRoots k (1 : R)) := Multiset.card_attach
    _ ≤ k := card_nthRoots k 1

variable {k R}
/-
**map_rootsOfUnity_eq_pow_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_rootsOfUnity_eq_pow_self [FunLike F R R] [MonoidHomClass F R R] (σ : F
) (ζ : rootsOfUnity k R) : exists m : Nat, σ (ζ : Rˣ) = ((ζ : Rˣ) : R) ^ m
参数：σ : F；ζ : rootsOfUnity k R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_cyclic`：MonoidHom.map_cyclic [h : IsCyclic G] (σ : G ->* G
) : exists m : Int, forall g : G, σ g = g ^ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `restrictRootsOfUnity_coe_apply`：restrictRootsOfUnity_coe_apply [MonoidHo
mClass F R S] (σ : F) (ζ : rootsOfUnity k R) : (restrictRootsOfUnity σ k ζ : Sˣ)
 = σ (ζ : Rˣ)
· 使用引理 `zpow_mod_orderOf`：zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf
 x : Int)) = x ^ z
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `instFiniteSubtypeUnitsMemSubgroupRootsOfUnity`：∀ (R : Type u_4) (k : ℕ) 
[NeZero k] [inst : CommRing R] [IsDomain R], Finite ↥(rootsOfUnity k R)
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `rootsOfUnity.coe_pow`：rootsOfUnity.coe_pow [CommMonoid R] (ζ : rootsOfUn
ity k R) (m : Nat) : (((ζ ^ m :) : Rˣ) : R) = ((ζ : Rˣ) : R) ^ m
-/
theorem map_rootsOfUnity_eq_pow_self [FunLike F R R] [MonoidHomClass F R R] (σ : F)
    (ζ : rootsOfUnity k R) :
    ∃ m : ℕ, σ (ζ : Rˣ) = ((ζ : Rˣ) : R) ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ k)
  rw [← restrictRootsOfUnity_coe_apply, hm, ← zpow_mod_orderOf, ← Int.toNat_of_nonneg
      (m.emod_nonneg (Int.natCast_ne_zero.mpr (pos_iff_ne_zero.mp (orderOf_pos ζ)))),
    zpow_natCast, rootsOfUnity.coe_pow]
  exact ⟨(m % orderOf ζ).toNat, rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {L : Type*} [LeftCancelMonoid L] [Finite L] :
    Finite (L →* Rˣ) := by
  let S := rootsOfUnity (Monoid.exponent L) R
  have : Finite (L →* S) := .of_injective _ DFunLike.coe_injective
  refine .of_surjective (fun f : L →* S ↦ (Subgroup.subtype _).comp f) fun f ↦ ?_
  have H a : f a ∈ S := by
    rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
  exact ⟨.codRestrict f S H, MonoidHom.ext fun _ ↦ by simp⟩

end IsDomain

section Reduced

variable (R) [CommRing R] [IsReduced R]

-- simp normal form is `mem_rootsOfUnity_prime_pow_mul_iff'`
/-
**mem_rootsOfUnity_prime_pow_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rootsOfUnity_prime_pow_mul_iff (p k : Nat) (m : Nat) [ExpChar R p] {ζ 
: Rˣ} : ζ in rootsOfUnity (p ^ k * m) R ↔ ζ in rootsOfUnity m R
参数：p k : Nat；m : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_rootsOfUnity_prime_pow_mul_iff (p k : ℕ) (m : ℕ) [ExpChar R p] {ζ : Rˣ} :
    ζ ∈ rootsOfUnity (p ^ k * m) R ↔ ζ ∈ rootsOfUnity m R := by
  simp only [mem_rootsOfUnity', ExpChar.pow_prime_pow_mul_eq_one_iff]

/-- A variant of `mem_rootsOfUnity_prime_pow_mul_iff` in terms of `ζ ^ _` -/
@[simp]
/-
**mem_rootsOfUnity_prime_pow_mul_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rootsOfUnity_prime_pow_mul_iff' (p k : Nat) (m : Nat) [ExpChar R p] {ζ
 : Rˣ} : ζ ^ (p ^ k * m) = 1 ↔ ζ in rootsOfUnity m R
参数：p k : Nat；m : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_rootsOfUnity`：mem_rootsOfUnity (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnit
y k M ↔ ζ ^ k = 1
· 使用定理 `mem_rootsOfUnity_prime_pow_mul_iff`：mem_rootsOfUnity_prime_pow_mul_iff (
p k : Nat) (m : Nat) [ExpChar R p] {ζ : Rˣ} : ζ in rootsOfUnity (p ^ k * m) R ↔ 
ζ in rootsOfUnity m R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A variant of `mem_rootsOfUnity_prime_pow_mul_iff` in terms of `ζ ^ _`
-/
theorem mem_rootsOfUnity_prime_pow_mul_iff' (p k : ℕ) (m : ℕ) [ExpChar R p] {ζ : Rˣ} :
    ζ ^ (p ^ k * m) = 1 ↔ ζ ∈ rootsOfUnity m R := by
  rw [← mem_rootsOfUnity, mem_rootsOfUnity_prime_pow_mul_iff]

end Reduced

end rootsOfUnity

section cyclic

namespace IsCyclic

/-- The isomorphism from the group of group homomorphisms from a finite cyclic group `G` of order
`n` into another group `G'` to the group of `n`th roots of unity in `G'` determined by a generator
`g` of `G`. It sends `φ : G →* G'` to `φ g`. -/
noncomputable
/-
**IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator** 是 Mathlib 中的一个定义，位于命名空间 `I
sCyclic`。
形式化陈述：monoidHomMulEquivRootsOfUnityOfGenerator {G : Type*} [CommGroup G] {g : G}
 (hg : forall (x : G), x in Subgroup.zpowers g) (G' : Type*) [CommGroup G'] : (G
 ->* G') ≃* rootsOfUnity (Nat.card G) G' where toFun φ
参数：hg : forall (x : G), x in Subgroup.zpowers g；G' : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomMulEquivRootsOfUnityOfGenerator {G : Type*} [CommGroup G] {g : G}
    (hg : ∀ (x : G), x ∈ Subgroup.zpowers g) (G' : Type*) [CommGroup G'] :
    (G →* G') ≃* rootsOfUnity (Nat.card G) G' where
  toFun φ := ⟨(IsUnit.map φ <| Group.isUnit g).unit, by
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      ← map_pow, pow_card_eq_one', map_one, Units.val_one]⟩
  invFun ζ := monoidHomOfForallMemZpowers hg (g' := (ζ.val : G')) <| by
    simpa only [orderOf_eq_card_of_forall_mem_zpowers hg, orderOf_dvd_iff_pow_eq_one,
      ← Units.val_pow_eq_pow_val, Units.val_eq_one] using! ζ.prop
  left_inv φ := (MonoidHom.eq_iff_eq_on_generator hg _ φ).mpr <| by
    simp only [IsUnit.unit_spec, monoidHomOfForallMemZpowers_apply_gen]
  right_inv φ := Subtype.ext <| by
    simp only [monoidHomOfForallMemZpowers_apply_gen, IsUnit.unit_of_val_units]
  map_mul' x y := by
    simp only [MonoidHom.mul_apply, MulMemClass.mk_mul_mk, Subtype.mk.injEq, Units.ext_iff,
      IsUnit.unit_spec, Units.val_mul]

/-- The group of group homomorphisms from a finite cyclic group `G` of order `n` into another
group `G'` is (noncanonically) isomorphic to the group of `n`th roots of unity in `G'`. -/
/-
**IsCyclic.monoidHom_mulEquiv_rootsOfUnity** 是 Mathlib 中的一个引理，位于命名空间 `IsCyclic`。
形式化陈述：monoidHom_mulEquiv_rootsOfUnity (G : Type*) [CommGroup G] [IsCyclic G] (G'
 : Type*) [CommGroup G'] : Nonempty (G ->* G') ≃* rootsOfUnity (Nat.card G) G'
参数：G : Type*；G' : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g

--- 原说明 ---
The group of group homomorphisms from a finite cyclic group `G` of order `n` int
o another
group `G'` is (noncanonically) isomorphic to the group of `n`th roots of unity i
n `G'`.
-/
lemma monoidHom_mulEquiv_rootsOfUnity (G : Type*) [CommGroup G] [IsCyclic G]
    (G' : Type*) [CommGroup G'] :
    Nonempty <| (G →* G') ≃* rootsOfUnity (Nat.card G) G' := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact ⟨monoidHomMulEquivRootsOfUnityOfGenerator hg G'⟩

end IsCyclic

end cyclic

