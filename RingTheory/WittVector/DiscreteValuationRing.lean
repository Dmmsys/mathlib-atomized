/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth, Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.MulCoeff
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.LinearCombination

/-!

# Witt vectors over a perfect ring

This file establishes that Witt vectors over a perfect field are a discrete valuation ring.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `WittVector.exists_eq_pow_p_mul`: the existence of this element `b` over a perfect ring
* `WittVector.exists_eq_pow_p_mul'`: the existence of this unit `b` over a perfect field
* `WittVector.isDiscreteValuationRing`: `𝕎 k` is a discrete valuation ring if `k` is a perfect field

-/

@[expose] public section


noncomputable section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

section CommRing

variable {k : Type*} [CommRing k] [CharP k p]

/-- This is the `n+1`st coefficient of our inverse. -/
/-
**WittVector.succNthValUnits** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：succNthValUnits (n : Nat) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) -> k) 
: k
参数：n : Nat；a : Units k；A : 𝕎 k；bs : Fin (n + 1) -> k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `n+1`st coefficient of our inverse.
-/
def succNthValUnits (n : ℕ) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) → k) : k :=
  -↑(a⁻¹ ^ p ^ (n + 1)) *
    (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)

/--
Recursively defines the sequence of coefficients for the inverse to a Witt vector whose first entry
is a unit.
-/
/-
**WittVector.inverseCoeff** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：{p : ℕ} → [hp : Fact (Nat.Prime p)] → {k : Type u_1} → [inst : CommRing k]
 → [CharP k p] → kˣ → WittVector p k → ℕ → k
参数：Nat.Prime p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursively defines the sequence of coefficients for the inverse to a Witt vecto
r whose first entry
is a unit.
-/
noncomputable def inverseCoeff (a : Units k) (A : 𝕎 k) : ℕ → k
  | 0 => ↑a⁻¹
  | n + 1 => succNthValUnits n a A fun i => inverseCoeff a A i.val

/--
Upgrade a Witt vector `A` whose first entry `A.coeff 0` is a unit to be, itself, a unit in `𝕎 k`.
-/
/-
**WittVector.mkUnit** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k)
参数：hA : A.coeff 0 = a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrade a Witt vector `A` whose first entry `A.coeff 0` is a unit to be, itself,
 a unit in `𝕎 k`.
-/
def mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k) :=
  Units.mkOfMulEqOne A (@WittVector.mk' p _ (inverseCoeff a A)) (by
    ext n
    induction n with
    | zero => simp [WittVector.mul_coeff_zero, inverseCoeff, hA]
    | succ n => ?_
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
      nthRemainder p n (truncateFun (n + 1) A) fun i : Fin (n + 1) => inverseCoeff a A i
    have H := Units.mul_inv (a ^ p ^ (n + 1))
    linear_combination (norm := skip) -H_coeff * H
    have ha : (a : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1)) := by norm_cast
    have ha_inv : (↑a⁻¹ : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1))⁻¹ := by norm_cast
    simp only [nthRemainder_spec, inverseCoeff, succNthValUnits, hA,
      one_coeff_eq_of_pos, Nat.succ_pos', ha_inv, ha, inv_pow]
    ring!)

@[simp]
/-
**WittVector.coe_mkUnit** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coe_mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mkUnit hA : 𝕎 k
) = A
参数：hA : A.coeff 0 = a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mkUnit hA : 𝕎 k) = A :=
  rfl

end CommRing

section Field

variable {k : Type*} [Field k] [CharP k p]

/-
**WittVector.isUnit_of_coeff_zero_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`
。
形式化陈述：isUnit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 != 0) : IsUnit x
参数：x : 𝕎 k；hx : x.coeff 0 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem isUnit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 ≠ 0) : IsUnit x := by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  have hy : x.coeff 0 = y := rfl
  exact (mkUnit hy).isUnit

variable (p)
/-
**WittVector.irreducible** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：irreducible : Irreducible (p : 𝕎 k)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.constantCoeff_apply`：∀ {p : ℕ} {R : Type u_1} [inst : CommRin
g R] [inst_1 : Fact (Nat.Prime p)] (x : WittVector p R),   WittVector.constantCo
eff x = x.coeff 0
· 使用定理 `WittVector.coeff_p_zero`：coeff_p_zero [CharP R p] : (p : 𝕎 R).coeff 0 = 
0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `WittVector.instNoZeroDivisorsOfCharP`：∀ {p : ℕ} {R : Type u_1} [hp : Fac
t (Nat.Prime p)] [inst : CommRing R] [CharP R p] [NoZeroDivisors R],   NoZeroDiv
isors (WittVector p R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `WittVector.p_nonzero`：p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) !
= 0
· 使用定理 `WittVector.verschiebung_nonzero`：verschiebung_nonzero {x : 𝕎 R} (hx : x 
!= 0) : exists n : Nat, exists x' : 𝕎 R, x'.coeff 0 != 0 ∧ x = verschiebung^[n] 
x'
· 使用定理 `WittVector.isUnit_of_coeff_zero_ne_zero`：isUnit_of_coeff_zero_ne_zero (x
 : 𝕎 k) (hx : x.coeff 0 != 0) : IsUnit x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WittVector.coeff_p_one`：coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `WittVector.iterate_verschiebung_mul`：iterate_verschiebung_mul (x y : 𝕎 R
) (i j : Nat) : verschiebung^[i] x * verschiebung^[j] y = verschiebung^[i + j] (
frobenius^[j] x * frobeni…
-/
theorem irreducible : Irreducible (p : 𝕎 k) := by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [constantCoeff_apply, coeff_p_zero, not_isUnit_zero] using
      (constantCoeff : WittVector p k →+* _).isUnit_map hp
  refine ⟨hp, fun a b hab => ?_⟩
  obtain ⟨ha0, hb0⟩ : a ≠ 0 ∧ b ≠ 0 := by
    rw [← mul_ne_zero_iff]; intro h; rw [h] at hab; exact p_nonzero p k hab
  obtain ⟨m, a, ha, rfl⟩ := verschiebung_nonzero ha0
  obtain ⟨n, b, hb, rfl⟩ := verschiebung_nonzero hb0
  cases m; · exact Or.inl (isUnit_of_coeff_zero_ne_zero a ha)
  rcases n with - | n; · exact Or.inr (isUnit_of_coeff_zero_ne_zero b hb)
  rw [iterate_verschiebung_mul] at hab
  apply_fun fun x => coeff x 1 at hab
  simp only [coeff_p_one, Nat.add_succ, add_comm _ n, Function.iterate_succ', Function.comp_apply,
    verschiebung_coeff_add_one, verschiebung_coeff_zero] at hab
  exact (one_ne_zero hab).elim

end Field

section PerfectRing

variable {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]

/-
**WittVector.exists_eq_pow_p_mul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：exists_eq_pow_p_mul (a : 𝕎 k) (ha : a != 0) : exists (m : Nat) (b : 𝕎 k), 
b.coeff 0 != 0 ∧ a = (p : 𝕎 k) ^ m * b
参数：a : 𝕎 k；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.verschiebung_nonzero`：verschiebung_nonzero {x : 𝕎 R} (hx : x 
!= 0) : exists n : Nat, exists x' : 𝕎 R, x'.coeff 0 != 0 ∧ x = verschiebung^[n] 
x'
· 使用定理 `Function.Surjective.iterate`：∀ {α : Type u} {f : α → α}, Function.Surjec
tive f → ∀ (n : ℕ), Function.Surjective f^[n]
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `WittVector.frobenius_bijective`：frobenius_bijective [PerfectRing R p] : 
Function.Bijective (@WittVector.frobenius p R _ _)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Function.Commute.comp_iterate`：comp_iterate (h : Commute f g) (n : Nat) 
: (f ∘ g)^[n] = f^[n] ∘ g^[n]
· 使用定理 `WittVector.verschiebung_frobenius_comm`：verschiebung_frobenius_comm [Cha
rP R p] : Function.Commute (verschiebung : 𝕎 R -> 𝕎 R) frobenius
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WittVector.iterate_frobenius_coeff`：iterate_frobenius_coeff (x : 𝕎 R) (i
 k : Nat) : (frobenius^[i] x).coeff k = x.coeff k ^ p ^ i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `WittVector.verschiebung_frobenius`：verschiebung_frobenius [CharP R p] (x
 : 𝕎 R) : verschiebung (frobenius x) = x * p
-/
theorem exists_eq_pow_p_mul (a : 𝕎 k) (ha : a ≠ 0) :
    ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c
  rw [WittVector.iterate_frobenius_coeff] at hc
  have := congr_fun (WittVector.verschiebung_frobenius_comm.comp_iterate m) b
  simp only [Function.comp_apply] at this
  rw [← this] at hcm
  refine ⟨m, b, ?_, ?_⟩
  · contrapose hc
    simp [hc, zero_pow <| pow_ne_zero _ hp.out.ne_zero]
  · simp_rw [← mul_left_iterate (p : 𝕎 k) m]
    convert! hcm using 2
    ext1 x
    rw [mul_comm, ← WittVector.verschiebung_frobenius x]; rfl

end PerfectRing

section PerfectField

variable {k : Type*} [Field k] [CharP k p] [PerfectRing k p]

/-
**WittVector.exists_eq_pow_p_mul'** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a != 0) : exists (m : Nat) (b : Units
 (𝕎 k)), a = (p : 𝕎 k) ^ m * b
参数：a : 𝕎 k；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.exists_eq_pow_p_mul`：exists_eq_pow_p_mul (a : 𝕎 k) (ha : a !=
 0) : exists (m : Nat) (b : 𝕎 k), b.coeff 0 != 0 ∧ a = (p : 𝕎 k) ^ m * b
-/
theorem exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a ≠ 0) :
    ∃ (m : ℕ) (b : Units (𝕎 k)), a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  let b₀ := Units.mk0 (b.coeff 0) h₁
  have hb₀ : b.coeff 0 = b₀ := rfl
  exact ⟨m, mkUnit hb₀, h₂⟩

/-- The ring of Witt Vectors of a perfect field of positive characteristic is a DVR.
-/
/-
**WittVector.isDiscreteValuationRing** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：isDiscreteValuationRing : IsDiscreteValuationRing (𝕎 k)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`：ofHasUn
itMulPowIrreducibleFactorization {R : Type u} [CommRing R] [IsDomain R] (hR : Ha
sUnitMulPowIrreducibleFactorization R) : IsDiscreteVa…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `WittVector.irreducible`：irreducible : Irreducible (p : 𝕎 k)
· 使用定理 `WittVector.exists_eq_pow_p_mul'`：exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a 
!= 0) : exists (m : Nat) (b : Units (𝕎 k)), a = (p : 𝕎 k) ^ m * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The ring of Witt Vectors of a perfect field of positive characteristic is a DVR.
-/
instance isDiscreteValuationRing : IsDiscreteValuationRing (𝕎 k) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization (by
    refine ⟨p, irreducible p, fun {x} hx => ?_⟩
    obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
    exact ⟨n, b, hb.symm⟩)

end PerfectField

end WittVector

