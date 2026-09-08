/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Expand

/-!
## Expand power series

Given a power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `PowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `PowerSeries.expand`: expand a power series by a nonzero factor of p,
  so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section

namespace PowerSeries

variable {τ R S : Type*} [CommRing R] [CommRing S] (p : ℕ) (hp : p ≠ 0)

/-- Expand the power series by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `PowerSeries.expand`. -/
/-
**PowerSeries.expand** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：expand : PowerSeries R ->ₐ[R] PowerSeries R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Expand the power series by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `PowerSeries.expand`.
-/
noncomputable def expand : PowerSeries R →ₐ[R] PowerSeries R :=
  MvPowerSeries.expand p hp
/-
**PowerSeries.expand_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_apply (f : PowerSeries R) : expand p hp f = subst (X ^ p) f
参数：f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_apply (f : PowerSeries R) : expand p hp f = subst (X ^ p) f := by
  simp [expand, MvPowerSeries.expand, subst, X]
/-
**PowerSeries.expand_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_C (r : R) : expand p hp (C r : PowerSeries R) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `PowerSeries.smul_eq_C_mul`：smul_eq_C_mul (f : R⟦X⟧) (a : R) : a • f = C 
a * f
· 使用定理 `PowerSeries.expand.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (p : ℕ) (h
p : p ≠ 0), PowerSeries.expand p hp = MvPowerSeries.expand p hp
· 使用定理 `AlgHom.map_smul_of_tower`：map_smul_of_tower {R'} [SMul R' A] [SMul R' B]
 [LinearMap.CompatibleSMul A B R' R] (r : R') (x : A) : φ (r • x) = r • φ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem expand_C (r : R) : expand p hp (C r : PowerSeries R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]
/-
**PowerSeries.expand_mul_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_mul_eq_comp (q : Nat) (hq : q != 0) : expand (p * q) (p.mul_ne_zero
 hp hq) = (expand p hp (R
参数：q : Nat；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.expand_mul_eq_comp`：expand_mul_eq_comp : expand (σ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_mul_eq_comp (q : ℕ) (hq : q ≠ 0) :
    expand (p * q) (p.mul_ne_zero hp hq) = (expand p hp (R := R)).comp (expand q hq) := by
  ext1 i
  simp [expand, MvPowerSeries.expand_mul_eq_comp p hp q hq]
/-
**PowerSeries.expand_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_mul (q : Nat) (hq : q != 0) (φ : PowerSeries R) : φ.expand (p * q) 
(p.mul_ne_zero hp hq) = (φ.expand q hq).expand p hp
参数：q : Nat；hq : q != 0；φ : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `PowerSeries.expand_mul_eq_comp`：expand_mul_eq_comp (q : Nat) (hq : q != 
0) : expand (p * q) (p.mul_ne_zero hp hq) = (expand p hp (R
-/
theorem expand_mul (q : ℕ) (hq : q ≠ 0) (φ : PowerSeries R) :
    φ.expand (p * q) (p.mul_ne_zero hp hq) = (φ.expand q hq).expand p hp :=
  DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ
/-
**PowerSeries.expand_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_smul (a : R) (φ : PowerSeries R) : expand p hp (a • φ) = a • φ.expa
nd p hp
参数：a : R；φ : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.map_smul_of_tower`：map_smul_of_tower {R'} [SMul R' A] [SMul R' B]
 [LinearMap.CompatibleSMul A B R' R] (r : R') (x : A) : φ (r • x) = r • φ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem expand_smul (a : R) (φ : PowerSeries R) :
    expand p hp (a • φ) = a • φ.expand p hp := AlgHom.map_smul_of_tower _ _ _

@[simp]
/-
**PowerSeries.expand_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_X : expand p hp (X (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.substAlgHom_X`：substAlgHom_X (ha : HasSubst a) : substAlgHom
 ha (X : R⟦X⟧) = a
· 使用定理 `PowerSeries.HasSubst.X_pow`：∀ {R : Type u_2} [inst : CommRing R] {n : ℕ}
, n ≠ 0 → PowerSeries.HasSubst (PowerSeries.X ^ n)
-/
theorem expand_X : expand p hp (X (R := R)) = X ^ p :=
  substAlgHom_X (HasSubst.X_pow hp)

@[simp]
/-
**PowerSeries.expand_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_monomial (d : Nat) (r : R) : expand p hp (monomial d r) = monomial 
(p * d) r
参数：d : Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.expand_monomial`：expand_monomial (d : σ ->₀ Nat) (r : R) :
 expand p hp (monomial d r) = monomial (p • d) r
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_monomial (d : ℕ) (r : R) :
    expand p hp (monomial d r) = monomial (p * d) r := by
  simp [expand, monomial, MvPowerSeries.expand_monomial]

@[simp]
/-
**PowerSeries.expand_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_one : expand 1 one_ne_zero = AlgHom.id R (PowerSeries R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.expand_one`：expand_one : expand 1 one_ne_zero = AlgHom.id 
R (MvPowerSeries σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_one : expand 1 one_ne_zero = AlgHom.id R (PowerSeries R) := by
  simp [expand]
/-
**PowerSeries.expand_one_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_one_apply (f : PowerSeries R) : expand 1 one_ne_zero f = f
参数：f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.expand_one`：expand_one : expand 1 one_ne_zero = AlgHom.id R 
(PowerSeries R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_one_apply (f : PowerSeries R) : expand 1 one_ne_zero f = f := by simp

@[simp]
/-
**PowerSeries.map_expand** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_expand (f : R ->+* S) (φ : PowerSeries R) : map f (expand p hp φ) = ex
pand p hp (map f φ)
参数：f : R ->+* S；φ : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.map_expand`：map_expand (f : R ->+* S) (φ : MvPowerSeries σ
 R) : map f (expand p hp φ) = expand p hp (map f φ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_expand (f : R →+* S) (φ : PowerSeries R) :
    map f (expand p hp φ) = expand p hp (map f φ) := by
  simp [map, expand, MvPowerSeries.map_expand]
/-
**PowerSeries.expand_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：expand_subst {f : MvPowerSeries τ S} (hf : HasSubst f) (φ : PowerSeries S)
 : (subst f φ).expand p hp = subst (f.expand p hp) φ
参数：hf : HasSubst f；φ : PowerSeries S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.expand_subst`：expand_subst {f : σ -> MvPowerSeries τ R} (h
f : HasSubst f) {φ : MvPowerSeries σ R} : expand p hp (subst f φ) = subst (fun i
 => (f i).expand…
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
-/
theorem expand_subst {f : MvPowerSeries τ S} (hf : HasSubst f) (φ : PowerSeries S) :
    (subst f φ).expand p hp = subst (f.expand p hp) φ := by
  rw [PowerSeries.subst, MvPowerSeries.expand_subst _ hp (HasSubst.const hf) (φ := φ),
    PowerSeries.subst]

/- TODO : In the original file of multivariate polynomial, there are two theorems about rename
here, but we don't have rename for multivariate power series. And for `eval₂Hom`, `eval₂`
and `aeval`, the expression does not look good. -/

variable (φ : PowerSeries R) (q : ℕ) (hq : 0 < q)

@[simp]
/-
**PowerSeries.coeff_expand_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_expand_mul (m : Nat) : (expand p hp φ).coeff (p * m) = φ.coeff m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `PowerSeries.expand.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (p : ℕ) (h
p : p ≠ 0), PowerSeries.expand p hp = MvPowerSeries.expand p hp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `MvPowerSeries.coeff_expand_smul`：coeff_expand_smul (φ : MvPowerSeries σ 
R) (m : σ ->₀ Nat) : (expand p hp φ).coeff (p • m) = φ.coeff m
-/
theorem coeff_expand_mul (m : ℕ) :
    (expand p hp φ).coeff (p * m) = φ.coeff m := by
  rw [coeff, coeff, expand, ← smul_eq_mul, ← Finsupp.smul_single, MvPowerSeries.coeff_expand_smul]

@[simp]
/-
**PowerSeries.constantCoeff_expand** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_expand (φ : PowerSeries R) : (φ.expand p hp).constantCoeff =
 φ.constantCoeff
参数：φ : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PowerSeries.coeff_expand_mul`：coeff_expand_mul (m : Nat) : (expand p hp 
φ).coeff (p * m) = φ.coeff m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_expand (φ : PowerSeries R) :
    (φ.expand p hp).constantCoeff = φ.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← mul_zero p, coeff_expand_mul]
  simp
/-
**PowerSeries.coeff_expand_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_expand_of_not_dvd {m : Nat} (h : ¬ p ∣ m) : (expand p hp φ).coeff m 
= 0
参数：h : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `PowerSeries.expand.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (p : ℕ) (h
p : p ≠ 0), PowerSeries.expand p hp = MvPowerSeries.expand p hp
· 使用定理 `MvPowerSeries.coeff_expand_of_not_dvd`：coeff_expand_of_not_dvd (φ : MvPo
werSeries σ R) {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i) : (expand p hp φ).coeff m
 = 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem coeff_expand_of_not_dvd {m : ℕ} (h : ¬ p ∣ m) :
    (expand p hp φ).coeff m = 0 := by
  rw [coeff, expand, MvPowerSeries.coeff_expand_of_not_dvd (i := ())]
  simpa
/-
**PowerSeries.support_expand_subset** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：support_expand_subset : (expand p hp φ).support subseteq φ.support.image (
p • ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.expand.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (p : ℕ) (h
p : p ≠ 0), PowerSeries.expand p hp = MvPowerSeries.expand p hp
· 使用定理 `MvPowerSeries.support_expand`：support_expand (φ : MvPowerSeries σ R) : (
expand p hp φ).support = φ.support.image (p • ·)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem support_expand_subset :
    (expand p hp φ).support ⊆ φ.support.image (p • ·) := by
  rw [expand, MvPowerSeries.support_expand]
/-
**PowerSeries.support_expand** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：support_expand : (expand p hp φ).support = φ.support.image (p • ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.expand.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (p : ℕ) (h
p : p ≠ 0), PowerSeries.expand p hp = MvPowerSeries.expand p hp
· 使用定理 `MvPowerSeries.support_expand`：support_expand (φ : MvPowerSeries σ R) : (
expand p hp φ).support = φ.support.image (p • ·)
-/
theorem support_expand :
    (expand p hp φ).support = φ.support.image (p • ·) := by
  rw [expand, MvPowerSeries.support_expand]
/-
**PowerSeries.coeff_expand** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_expand {n : Nat} : (φ.expand p hp).coeff n = if p ∣ n then φ.coeff (
n / p) else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `PowerSeries.coeff_expand_mul`：coeff_expand_mul (m : Nat) : (expand p hp 
φ).coeff (p * m) = φ.coeff m
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `PowerSeries.coeff_expand_of_not_dvd`：coeff_expand_of_not_dvd {m : Nat} (
h : ¬ p ∣ m) : (expand p hp φ).coeff m = 0
-/
theorem coeff_expand {n : ℕ} :
    (φ.expand p hp).coeff n = if p ∣ n then φ.coeff (n / p) else 0 := by
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    rw [hq, coeff_expand_mul, Nat.mul_div_cancel_left _ (p.pos_of_ne_zero hp)]
  exact coeff_expand_of_not_dvd p hp _ h

@[simp]
/-
**PowerSeries.order_expand** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_expand : (φ.expand p hp).order = p • φ.order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.order_eq_order`：order_eq_order {φ : R⟦X⟧} : φ.order = MvPowe
rSeries.order φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.order_expand`：order_expand (φ : MvPowerSeries σ R) : (φ.ex
pand p hp).order = p • φ.order
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem order_expand : (φ.expand p hp).order = p • φ.order := by
  simp_rw [expand, order_eq_order, MvPowerSeries.order_expand p hp φ]

end PowerSeries

