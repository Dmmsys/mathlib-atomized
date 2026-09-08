/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Expand

/-!
## Expand multivariate power series

Given a multivariate power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `MvPowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPowerSeries.expand`: expand a multi variate power series by a nonzero factor of p,
  so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] (p : ℕ) (hp : p ≠ 0)

/-- Expand the power series by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `PowerSeries.expand`. -/
/-
**MvPowerSeries.expand** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：expand : MvPowerSeries σ R ->ₐ[R] MvPowerSeries σ R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n

--- 原说明 ---
Expand the power series by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `PowerSeries.expand`.
-/
noncomputable def expand : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.X_pow hp)
/-
**MvPowerSeries.expand_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_C (r : R) : expand p hp (C r : MvPowerSeries σ R) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPowerSeries.smul_eq_C_mul`：smul_eq_C_mul (f : MvPowerSeries σ R) (a : 
R) : a • f = C a * f
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `MvPowerSeries.expand.eq_1`：∀ {σ : Type u_1} {R : Type u_3} [inst : CommR
ing R] (p : ℕ) (hp : p ≠ 0),   MvPowerSeries.expand p hp = MvPowerSeries.substAl
gHom ⋯
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
theorem expand_C (r : R) : expand p hp (C r : MvPowerSeries σ R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

@[simp]
/-
**MvPowerSeries.expand_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_X (i : σ) : expand p hp (X i : MvPowerSeries σ R) = X i ^ p
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.substAlgHom_X`：substAlgHom_X (ha : HasSubst a) (s : σ) : s
ubstAlgHom (R
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
-/
theorem expand_X (i : σ) : expand p hp (X i : MvPowerSeries σ R) = X i ^ p :=
  substAlgHom_X (HasSubst.X_pow hp) i

@[simp]
/-
**MvPowerSeries.expand_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_monomial (d : σ ->₀ Nat) (r : R) : expand p hp (monomial d r) = mon
omial (p • d) r
参数：d : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.expand.eq_1`：∀ {σ : Type u_1} {R : Type u_3} [inst : CommR
ing R] (p : ℕ) (hp : p ≠ 0),   MvPowerSeries.expand p hp = MvPowerSeries.substAl
gHom ⋯
· 使用定理 `MvPowerSeries.substAlgHom_monomial`：substAlgHom_monomial (ha : HasSubst 
a) (e : σ ->₀ Nat) (r : R) : substAlgHom ha (monomial e r) = (algebraMap R (MvPo
werSeries τ S) r) * (e.p…
· 使用定理 `MvPowerSeries.monomial_eq'`：∀ {σ : Type u_1} {R : Type u_2} [inst : Comm
Semiring R] (e : σ →₀ ℕ) (r : R),   (MvPowerSeries.monomial e) r = MvPowerSeries
.C r * e.prod fu…
· 使用定理 `Finsupp.prod.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : CommMonoid N] (f : α →₀ M) (g : α → M → N),   f.prod g = ∏ 
a ∈ f.s…
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Finsupp.support_smul`：support_smul [Zero M] [SMulZeroClass R M] {b : R} 
{g : α ->₀ M} : (b • g).support subseteq g.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPowerSeries.algebraMap_apply`：algebraMap_apply {r : R} : algebraMap R 
(MvPowerSeries σ A) r = C (algebraMap R A r)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem expand_monomial (d : σ →₀ ℕ) (r : R) :
    expand p hp (monomial d r) = monomial (p • d) r := by
  rw [expand, substAlgHom_monomial (HasSubst.X_pow hp), monomial_eq', Finsupp.prod,
    Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul, algebraMap_apply, Algebra.algebraMap_self]
  · simp

@[simp]
/-
**MvPowerSeries.expand_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_one : expand 1 one_ne_zero = AlgHom.id R (MvPowerSeries σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MvPowerSeries.substAlgHom.congr_simp`：∀ {σ : Type u_1} {R : Type u_3} [i
nst : CommRing R] {τ : Type u_4} {S : Type u_5} [inst_1 : CommRing S]   [inst_2 
: Algebra R S] {a a_1 : σ …
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPowerSeries.subst_self`：subst_self : subst (MvPowerSeries.X : σ -> MvP
owerSeries σ R) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_one : expand 1 one_ne_zero = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 i
  simp [expand, subst_self]
/-
**MvPowerSeries.expand_one_apply** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_one_apply (f : MvPowerSeries σ R) : expand 1 one_ne_zero f = f
参数：f : MvPowerSeries σ R。
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
theorem expand_one_apply (f : MvPowerSeries σ R) : expand 1 one_ne_zero f = f := by simp

@[simp]
/-
**MvPowerSeries.map_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_expand (f : R ->+* S) (φ : MvPowerSeries σ R) : map f (expand p hp φ) 
= expand p hp (map f φ)
参数：f : R ->+* S；φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `MvPowerSeries.map_subst`：map_subst {a : σ -> MvPowerSeries τ R} (ha : Ha
sSubst a) {h : R ->+* S} (f : MvPowerSeries σ R) : (f.subst a).map h = (f.map h)
.subst (fun i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.map_X`：map_X (s : σ) : map f (X s) = X s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_expand (f : R →+* S) (φ : MvPowerSeries σ R) :
    map f (expand p hp φ) = expand p hp (map f φ) := by
  simp [expand, map_subst (HasSubst.X_pow hp)]

section

/-
**MvPowerSeries.HasSubst.expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubs
t`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_2} {S : Type u_4} [inst : CommRing S] (p : ℕ)
 (hp : p ≠ 0) {f : σ → MvPowerSeries τ S},   MvPowerSeries.HasSubst f → MvPowerS
eries.HasSubst fun i => (MvPowerSeries.expand p hp) (f i)
参数：p : ℕ；hp : p ≠ 0；MvPowerSeries.expand p hp；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.comp`：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u
_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S} {υ : Type u_7}   {T : Type u
_8} [inst_1 : Com…
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
-/
theorem HasSubst.expand {f : σ → MvPowerSeries τ S} (hf : HasSubst f) :
    HasSubst fun i ↦ expand p hp (f i) := comp hf (HasSubst.X_pow hp)
/-
**MvPowerSeries.expand_comp_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：expand_comp_substAlgHom {f : σ -> MvPowerSeries τ S} (hf : HasSubst f) : (
expand p hp).comp (substAlgHom hf) = substAlgHom (HasSubst.expand p hp hf)
参数：hf : HasSubst f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MvPowerSeries.HasSubst.expand`：∀ {σ : Type u_1} {τ : Type u_2} {S : Type
 u_4} [inst : CommRing S] (p : ℕ) (hp : p ≠ 0) {f : σ → MvPowerSeries τ S},   Mv
PowerSeries.HasSubs…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.substAlgHom.congr_simp`：∀ {σ : Type u_1} {R : Type u_3} [i
nst : CommRing R] {τ : Type u_4} {S : Type u_5} [inst_1 : CommRing S]   [inst_2 
: Algebra R S] {a a_1 : σ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_comp_substAlgHom {f : σ → MvPowerSeries τ S} (hf : HasSubst f) :
    (expand p hp).comp (substAlgHom hf) = substAlgHom (HasSubst.expand p hp hf) := by
  ext1 i
  simp [expand, subst_comp_subst_apply hf (HasSubst.X_pow hp)]
/-
**MvPowerSeries.expand_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_substAlgHom {f : σ -> MvPowerSeries τ S} (hf : HasSubst f) {φ : MvP
owerSeries σ S} : expand p hp (substAlgHom hf φ) = substAlgHom (HasSubst.expand 
p hp hf) φ
参数：hf : HasSubst f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.HasSubst.expand`：∀ {σ : Type u_1} {τ : Type u_2} {S : Type
 u_4} [inst : CommRing S] (p : ℕ) (hp : p ≠ 0) {f : σ → MvPowerSeries τ S},   Mv
PowerSeries.HasSubs…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `MvPowerSeries.expand_comp_substAlgHom`：expand_comp_substAlgHom {f : σ ->
 MvPowerSeries τ S} (hf : HasSubst f) : (expand p hp).comp (substAlgHom hf) = su
bstAlgHom (HasSubst.expand …
-/
theorem expand_substAlgHom {f : σ → MvPowerSeries τ S} (hf : HasSubst f) {φ : MvPowerSeries σ S} :
    expand p hp (substAlgHom hf φ) = substAlgHom (HasSubst.expand p hp hf) φ := by
  rw [← AlgHom.comp_apply, expand_comp_substAlgHom]
/-
**MvPowerSeries.expand_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_subst {f : σ -> MvPowerSeries τ R} (hf : HasSubst f) {φ : MvPowerSe
ries σ R} : expand p hp (subst f φ) = subst (fun i => (f i).expand p hp) φ
参数：hf : HasSubst f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.HasSubst.expand`：∀ {σ : Type u_1} {τ : Type u_2} {S : Type
 u_4} [inst : CommRing S] (p : ℕ) (hp : p ≠ 0) {f : σ → MvPowerSeries τ S},   Mv
PowerSeries.HasSubs…
· 使用定理 `MvPowerSeries.expand_substAlgHom`：expand_substAlgHom {f : σ -> MvPowerSe
ries τ S} (hf : HasSubst f) {φ : MvPowerSeries σ S} : expand p hp (substAlgHom h
f φ) = substAlgHom (Ha…
-/
theorem expand_subst {f : σ → MvPowerSeries τ R} (hf : HasSubst f) {φ : MvPowerSeries σ R} :
    expand p hp (subst f φ) = subst (fun i ↦ (f i).expand p hp) φ := by
  rw [← substAlgHom_apply hf, expand_substAlgHom, substAlgHom_apply]

end

/- TODO : In the original file of `MvPolynomial`, there are two theorems about `rename`
here, but we don't have `rename` for `MvPowerSeries`. And for `eval₂Hom`, `eval₂`
and `aeval`, the expression doesn't look good. -/

variable (q : ℕ) (hq : q ≠ 0)

/-
**MvPowerSeries.expand_mul_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_mul_eq_comp : expand (σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.substAlgHom.congr_simp`：∀ {σ : Type u_1} {R : Type u_3} [i
nst : CommRing R] {τ : Type u_4} {S : Type u_5} [inst_1 : CommRing S]   [inst_2 
: Algebra R S] {a a_1 : σ …
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.subst_pow`：subst_pow (ha : HasSubst a) (f : MvPowerSeries 
σ R) (n : Nat) : subst a (f ^ n) = (subst a f) ^ n
· 使用定理 `MvPowerSeries.subst_X`：subst_X (ha : HasSubst a) (s : σ) : subst (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem expand_mul_eq_comp :
    expand (σ := σ) (R := R) (p * q) (p.mul_ne_zero hp hq) = (expand p hp).comp (expand q hq) := by
  ext1 i
  simp [expand, pow_mul, subst_comp_subst_apply (HasSubst.X_pow hq) (HasSubst.X_pow hp),
    subst_pow (HasSubst.X_pow hp), subst_X (HasSubst.X_pow hp)]
/-
**MvPowerSeries.expand_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_mul (φ : MvPowerSeries σ R) : φ.expand (p * q) (p.mul_ne_zero hp hq
) = (φ.expand q hq).expand p hp
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `MvPowerSeries.expand_mul_eq_comp`：expand_mul_eq_comp : expand (σ
-/
theorem expand_mul (φ : MvPowerSeries σ R) : φ.expand (p * q) (p.mul_ne_zero hp hq) =
    (φ.expand q hq).expand p hp :=
  DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

@[simp]
/-
**MvPowerSeries.coeff_expand_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_expand_smul (φ : MvPowerSeries σ R) (m : σ ->₀ Nat) : (expand p hp φ
).coeff (p • m) = φ.coeff m
参数：φ : MvPowerSeries σ R；m : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MvPowerSeries.monomial_smul_eq`：∀ {σ : Type u_1} {R : Type u_2} [inst : 
CommSemiring R] (e : σ →₀ ℕ) (p : ℕ) (r : R),   (MvPowerSeries.monomial (p • e))
 r = MvPowerSeries.C…
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem coeff_expand_smul (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    (expand p hp φ).coeff (p • m) = φ.coeff m := by
  classical
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp), smul_eq_mul]
  have {d : σ →₀ ℕ} : (d.prod fun s e ↦ (X s (R := R) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [finsum_eq_single _ m]
  · rw [this, coeff_monomial, if_pos rfl, mul_one]
  · intro d hd
    rw [this, coeff_monomial, if_neg _, mul_zero]
    simp [nsmul_right_inj hp, hd.symm]

@[simp]
/-
**MvPowerSeries.constantCoeff_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_expand (φ : MvPowerSeries σ R) : (φ.expand p hp).constantCoe
ff = φ.constantCoeff
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff :
 ⇑(coeff (R
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MvPowerSeries.coeff_expand_smul`：coeff_expand_smul (φ : MvPowerSeries σ 
R) (m : σ ->₀ Nat) : (expand p hp φ).coeff (p • m) = φ.coeff m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_expand (φ : MvPowerSeries σ R) :
    (φ.expand p hp).constantCoeff = φ.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
  simp
/-
**MvPowerSeries.coeff_expand_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：coeff_expand_of_not_dvd (φ : MvPowerSeries σ R) {m : σ ->₀ Nat} {i : σ} (h
 : ¬ p ∣ m i) : (expand p hp φ).coeff m = 0
参数：φ : MvPowerSeries σ R；h : ¬ p ∣ m i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_zero_of_forall_eq_zero`：∀ {α : Type u_1} {M : Type u_5} [inst 
: AddCommMonoid M] {f : α → M}, (∀ (x : α), f x = 0) → ∑ᶠ (i : α), f i = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `MvPowerSeries.HasSubst.X_pow`：∀ {σ : Type u_1} {S : Type u_5} [inst : Co
mmRing S] {n : ℕ},   n ≠ 0 → MvPowerSeries.HasSubst fun s => MvPowerSeries.X s ^
 n
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.monomial_smul_eq`：∀ {σ : Type u_1} {R : Type u_2} [inst : 
CommSemiring R] (e : σ →₀ ℕ) (p : ℕ) (r : R),   (MvPowerSeries.monomial (p • e))
 r = MvPowerSeries.C…
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
-/
theorem coeff_expand_of_not_dvd (φ : MvPowerSeries σ R) {m : σ →₀ ℕ} {i : σ} (h : ¬ p ∣ m i) :
    (expand p hp φ).coeff m = 0 := by
  classical
  contrapose! h
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp)] at h
  obtain ⟨d, hd⟩ : ∃ (d : σ →₀ ℕ), (coeff m) (d.prod fun s e ↦ ((X s (R := R)) ^ p) ^ e) ≠ 0 := by
    by_contra! hc
    rw [finsum_eq_zero_of_forall_eq_zero fun d => by simp [hc d]] at h
    contradiction
  have : (d.prod fun s e ↦ ((X s (R := R)) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [this, coeff_monomial] at hd
  have meq : m = p • d := by
    by_contra hc
    rw [if_neg hc] at hd
    contradiction
  simp [meq]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPowerSeries.support_expand_subset** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：support_expand_subset (φ : MvPowerSeries σ R) : (expand p hp φ).support su
bseteq φ.support.image (p • ·)
参数：φ : MvPowerSeries σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MvPowerSeries.coeff_expand_of_not_dvd`：coeff_expand_of_not_dvd (φ : MvPo
werSeries σ R) {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i) : (expand p hp φ).coeff m
 = 0
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Nat.eq_mul_of_div_eq_right`：∀ {a b c : ℕ}, b ∣ a → a / b = c → a = b * c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_apply`：coeff_apply (f : MvPowerSeries σ R) (d : σ ->
₀ Nat) : coeff d f = f d
· 使用定理 `MvPowerSeries.coeff_expand_smul`：coeff_expand_smul (φ : MvPowerSeries σ 
R) (m : σ ->₀ Nat) : (expand p hp φ).coeff (p • m) = φ.coeff m
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
-/
theorem support_expand_subset (φ : MvPowerSeries σ R) :
    (expand p hp φ).support ⊆ φ.support.image (p • ·) := by
  intro d hd
  have : ∀ i, p ∣ d i := fun _ => by_contra fun hc => hd (coeff_expand_of_not_dvd p hp φ hc)
  let m := d.mapRange (fun n => n / p) (Nat.zero_div p)
  have eq_aux : p • m = d := (Finsupp.ext fun a => Nat.eq_mul_of_div_eq_right (this a) rfl).symm
  rw [Function.mem_support, ← eq_aux, ← coeff_apply (expand p hp φ), coeff_expand_smul,
    coeff_apply] at hd
  exact ⟨m, hd, eq_aux⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPowerSeries.support_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：support_expand (φ : MvPowerSeries σ R) : (expand p hp φ).support = φ.suppo
rt.image (p • ·)
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPowerSeries.support_expand_subset`：support_expand_subset (φ : MvPowerS
eries σ R) : (expand p hp φ).support subseteq φ.support.image (p • ·)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_apply`：coeff_apply (f : MvPowerSeries σ R) (d : σ ->
₀ Nat) : coeff d f = f d
· 使用定理 `MvPowerSeries.coeff_expand_smul`：coeff_expand_smul (φ : MvPowerSeries σ 
R) (m : σ ->₀ Nat) : (expand p hp φ).coeff (p • m) = φ.coeff m
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
-/
theorem support_expand (φ : MvPowerSeries σ R) :
    (expand p hp φ).support = φ.support.image (p • ·) := by
  refine (support_expand_subset p hp φ).antisymm ?_
  intro d hd
  obtain ⟨n, hn₁, hn₂⟩ := hd
  simp only [← hn₂, Function.mem_support]
  by_contra hc
  rw [Function.mem_support, ← coeff_apply φ, ← coeff_expand_smul p hp, coeff_apply, hc] at hn₁
  contradiction

@[simp]
/-
**MvPowerSeries.order_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_expand (φ : MvPowerSeries σ R) : (φ.expand p hp).order = p • φ.order
参数：φ : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MvPowerSeries.order_zero`：order_zero : (0 : MvPowerSeries σ R).order = ⊤
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPowerSeries.exists_coeff_ne_zero_and_order`：exists_coeff_ne_zero_and_o
rder (h : f.order.toNat = f.order) : exists d : σ ->₀ Nat, coeff d f != 0 ∧ degr
ee d = f.order
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPowerSeries.ne_zero_iff_order_finite`：ne_zero_iff_order_finite : f != 
0 ↔ f.order.toNat = f.order
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPowerSeries.order_le`：order_le {d : σ ->₀ Nat} (h : coeff d f != 0) : 
f.order <= degree d
· 使用定理 `MvPowerSeries.coeff_expand_smul`：coeff_expand_smul (φ : MvPowerSeries σ 
R) (m : σ ->₀ Nat) : (expand p hp φ).coeff (p • m) = φ.coeff m
· 使用定理 `MvPowerSeries.le_order`：le_order {n : Nat∞} (h : forall d : σ ->₀ Nat, d
egree d < n -> coeff d f = 0) : n <= f.order
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `MvPowerSeries.coeff_of_lt_order`：coeff_of_lt_order {d : σ ->₀ Nat} (h : 
degree d < f.order) : coeff d f = 0
（共 35 条，此处仅展示前 30 条）
-/
theorem order_expand (φ : MvPowerSeries σ R) :
    (φ.expand p hp).order = p • φ.order := by
  by_cases! hφ : φ = 0
  · simpa [hφ] using (ENat.mul_top (by norm_cast)).symm
  · apply eq_of_le_of_ge
    · obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order (ne_zero_iff_order_finite.mp hφ)
      have : p • φ.order = (p • d).degree := by simp [← hd₂]
      rw [this]
      exact order_le <| (coeff_expand_smul p hp φ _) ▸ hd₁
    · refine MvPowerSeries.le_order fun d hd => ?_
      by_cases! h : ∀ i, p ∣ d i
      · obtain ⟨m, hm⟩ : ∃ m, p • m = d := ⟨d.mapRange (fun a ↦ a / p) (by simp),
          by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
        rw [← hm, coeff_expand_smul, coeff_of_lt_order]
        simp only [← hm, map_nsmul, smul_eq_mul, Nat.cast_mul, nsmul_eq_mul] at hd
        exact lt_of_mul_lt_mul_left' hd
      · obtain ⟨i, hi⟩ := h
        exact coeff_expand_of_not_dvd p hp φ hi

section MvPolynomial

/-- For any multivariate polynomial `φ`, then `MvPolynomial.expand p φ` and
`MvPowerSeries.expand p hp ↑φ` coincide. -/
@[simp]
/-
**MvPowerSeries.expand_eq_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：expand_eq_expand {φ : MvPolynomial σ R} : expand p hp (↑φ) = (φ.expand p :
 MvPowerSeries σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_expand_smul`：coeff_expand_smul (φ : MvPowerSeries σ 
R) (m : σ ->₀ Nat) : (expand p hp φ).coeff (p • m) = φ.coeff m
· 使用引理 `MvPolynomial.coeff_expand_smul`：coeff_expand_smul (hp : p != 0) (φ : MvP
olynomial σ R) (m : σ ->₀ Nat) : (expand p φ).coeff (p • m) = φ.coeff m
· 使用定理 `MvPolynomial.coeff_coe`：coeff_coe (n : σ ->₀ Nat) : MvPowerSeries.coeff 
n ↑φ = coeff n φ
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `MvPowerSeries.coeff_expand_of_not_dvd`：coeff_expand_of_not_dvd (φ : MvPo
werSeries σ R) {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i) : (expand p hp φ).coeff m
 = 0
· 使用引理 `MvPolynomial.coeff_expand_of_not_dvd`：coeff_expand_of_not_dvd {m : σ ->₀
 Nat} {i : σ} (h : ¬ p ∣ m i) : (expand p φ).coeff m = 0

--- 原说明 ---
For any multivariate polynomial `φ`, then `MvPolynomial.expand p φ` and
`MvPowerSeries.expand p hp ↑φ` coincide.
-/
theorem expand_eq_expand {φ : MvPolynomial σ R} :
    expand p hp (↑φ) = (φ.expand p : MvPowerSeries σ R) := by
  ext n
  simp only [MvPolynomial.coeff_coe]
  by_cases! h : ∀ i, p ∣ n i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = n := ⟨n.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, coeff_expand_smul p hp _ _, φ.coeff_expand_smul _ hp, φ.coeff_coe]
  · obtain ⟨i, hi⟩ := h
    rw [coeff_expand_of_not_dvd p hp _ hi, MvPolynomial.coeff_expand_of_not_dvd _ hi]
/-
**MvPowerSeries.trunc'_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] (p : ℕ) (hp : p ≠ 0) [
inst_1 : DecidableEq σ] {n : σ →₀ ℕ}   (φ : MvPowerSeries σ R),   (MvPowerSeries
.trunc' R (p • n)) ((MvPowerSeries.expand p hp) φ) =     (MvPolynomial.expand p)
 ((MvPowerSeries.trunc' R n) φ)
参数：p : ℕ；hp : p ≠ 0；φ : MvPowerSeries σ R；MvPowerSeries.trunc' R (p • n)；(MvPowe
rSeries.expand p hp) φ；MvPolynomial.expand p；(MvPowerSeries.trunc' R n) φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_trunc'`：coeff_trunc' (m n : σ ->₀ Nat) (φ : MvPowerS
eries σ R) : (trunc' R n φ).coeff m = if m <= n then coeff m φ else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MvPowerSeries.coeff_expand_smul`：coeff_expand_smul (φ : MvPowerSeries σ 
R) (m : σ ->₀ Nat) : (expand p hp φ).coeff (p • m) = φ.coeff m
· 使用引理 `MvPolynomial.coeff_expand_smul`：coeff_expand_smul (hp : p != 0) (φ : MvP
olynomial σ R) (m : σ ->₀ Nat) : (expand p φ).coeff (p • m) = φ.coeff m
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.coe_le_coe`：∀ {ι : Type u_1} {M : Type u_2} [inst : Zero M] [ins
t_1 : LE M] {f g : ι →₀ M}, ⇑f ≤ ⇑g ↔ f ≤ g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.mul_lt_mul_of_pos_left`：∀ {n m k : ℕ}, n < m → k > 0 → k * n < k * m
· 使用定理 `Nat.ne_zero_iff_zero_lt`：∀ {n : ℕ}, n ≠ 0 ↔ 0 < n
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用引理 `MvPolynomial.coeff_expand_of_not_dvd`：coeff_expand_of_not_dvd {m : σ ->₀
 Nat} {i : σ} (h : ¬ p ∣ m i) : (expand p φ).coeff m = 0
· 使用定理 `MvPowerSeries.coeff_expand_of_not_dvd`：coeff_expand_of_not_dvd (φ : MvPo
werSeries σ R) {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i) : (expand p hp φ).coeff m
 = 0
-/
theorem trunc'_expand [DecidableEq σ] {n : σ →₀ ℕ} (φ : MvPowerSeries σ R) :
    trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p := by
  ext d
  by_cases! h : ∀ i, p ∣ d i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = d := ⟨d.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    by_cases h_le : m ≤ n
    · rw [← hm, coeff_trunc', if_pos (nsmul_le_nsmul_right h_le p), coeff_expand_smul,
        MvPolynomial.coeff_expand_smul _ hp, coeff_trunc', if_pos h_le]
    · have not_le : ¬ p • m ≤ p • n := by
        obtain ⟨i, hi⟩ : ∃ i, m i > n i := by
          by_contra! hc
          exact h_le (Finsupp.coe_le_coe.mp hc)
        have : ¬ p • m i ≤ p • n i := by
          simp [Nat.mul_lt_mul_of_pos_left hi (p.ne_zero_iff_zero_lt.mp hp)]
        exact Not.intro fun a ↦ this (a i)
      rw [coeff_trunc', ← hm, if_neg not_le, MvPolynomial.coeff_expand_smul _ hp, coeff_trunc',
        if_neg h_le]
  · obtain ⟨i, hi⟩ := h
    rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]
    by_cases hd : d ≤ p • n
    · rw [coeff_trunc', if_pos hd, coeff_expand_of_not_dvd _ hp _ hi]
    rw [coeff_trunc', if_neg hd]

include hp in
/-
**MvPowerSeries.trunc'_expand_trunc'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_3} [inst : CommRing R] (p : ℕ),   p ≠ 0 →    
 ∀ {n m : σ →₀ ℕ},       n ≤ m →         ∀ [inst_1 : DecidableEq σ] (f : MvPower
Series σ R),           (MvPolynomial.expand p) ((MvPowerSeries.trunc' R n) f) = 
            (MvPowerSeries.trunc' R (p • n)) ↑((MvPolynomial.expand p) ((MvPower
Series.trunc' R m) f))
参数：p : ℕ；f : MvPowerSeries σ R；MvPolynomial.expand p；(MvPowerSeries.trunc' R n) 
f；MvPowerSeries.trunc' R (p • n)；(MvPolynomial.expand p) ((MvPowerSeries.trunc' 
R m) f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.expand_eq_expand`：expand_eq_expand {φ : MvPolynomial σ R} 
: expand p hp (↑φ) = (φ.expand p : MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.trunc'_expand`：∀ {σ : Type u_1} {R : Type u_3} [inst : Com
mRing R] (p : ℕ) (hp : p ≠ 0) [inst_1 : DecidableEq σ] {n : σ →₀ ℕ}   (φ : MvPow
erSeries σ R),   …
· 使用定理 `MvPowerSeries.trunc'_trunc'`：∀ {σ : Type u_1} {R : Type u_2} [inst : Dec
idableEq σ] [inst_1 : CommSemiring R] {n m : σ →₀ ℕ},   n ≤ m →     ∀ (φ : MvPow
erSeries σ R), (M…
-/
theorem trunc'_expand_trunc' {n m : σ →₀ ℕ} (h : n ≤ m) [DecidableEq σ] (f : MvPowerSeries σ R) :
    (MvPolynomial.expand p) (trunc' R n f) = (trunc' R (p • n))
      ↑((MvPolynomial.expand p) (trunc' R m f)) := by
  rw [← expand_eq_expand p hp, trunc'_expand, ← trunc'_trunc' h]

end MvPolynomial

section ExpChar

variable [ExpChar R p]

/-
**MvPowerSeries.map_frobenius_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：map_frobenius_expand {f : MvPowerSeries σ R} : (f.expand p hp).map (froben
ius R p) = f ^ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.trunc'`：trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ :
 MvPowerSeries σ R) : trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.eq_iff_frequently_trunc'_eq`：∀ {σ : Type u_1} {R : Type u_
2} [inst : DecidableEq σ] [inst_1 : CommSemiring R] {f g : MvPowerSeries σ R},  
 f = g ↔ ∃ᶠ (m : σ →₀ ℕ) in Fil…
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_self_nsmul`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Preorder 
M] [AddLeftMono M] {a : M} {n : ℕ}, 0 ≤ a → n ≠ 0 → a ≤ n • a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.map_expand`：map_expand (f : R ->+* S) (φ : MvPolynomial σ R
) : map f (expand p φ) = expand p (map f φ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.expand_eq_expand`：expand_eq_expand {φ : MvPolynomial σ R} 
: expand p hp (↑φ) = (φ.expand p : MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.map_expand`：map_expand (f : R ->+* S) (φ : MvPowerSeries σ
 R) : map f (expand p hp φ) = expand p hp (map f φ)
· 使用定理 `MvPowerSeries.trunc'_map`：∀ {σ : Type u_1} {R : Type u_2} {S : Type u_3}
 [inst : DecidableEq σ] [inst_1 : CommSemiring R]   [inst_2 : CommSemiring S] (n
 : σ →₀ ℕ) (f …
· 使用定理 `MvPowerSeries.trunc'_expand`：∀ {σ : Type u_1} {R : Type u_3} [inst : Com
mRing R] (p : ℕ) (hp : p ≠ 0) [inst_1 : DecidableEq σ] {n : σ →₀ ℕ}   (φ : MvPow
erSeries σ R),   …
· 使用定理 `MvPowerSeries.trunc'_trunc'_pow`：∀ {σ : Type u_1} {R : Type u_2} [inst :
 DecidableEq σ] [inst_1 : CommSemiring R] {n : σ →₀ ℕ} {k : ℕ},   1 ≤ k →     ∀ 
(φ : MvPowerSeries σ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用引理 `expChar_ne_zero`：expChar_ne_zero (p : Nat) [hR : ExpChar R p] : p != 0
· 使用定理 `MvPolynomial.coe_pow`：coe_pow (n : Nat) : ((φ ^ n : MvPolynomial σ R) : 
MvPowerSeries σ R) = (φ : MvPowerSeries σ R) ^ n
· 使用定理 `MvPolynomial.map_frobenius_expand`：map_frobenius_expand {f : MvPolynomia
l σ R} : (f.expand p).map (frobenius R p) = f ^ p
· 使用定理 `MvPowerSeries.trunc'_expand_trunc'`：∀ {σ : Type u_1} {R : Type u_3} [ins
t : CommRing R] (p : ℕ),   p ≠ 0 →     ∀ {n m : σ →₀ ℕ},       n ≤ m →         ∀
 [inst_1 : DecidableEq σ…
-/
theorem map_frobenius_expand {f : MvPowerSeries σ R} :
    (f.expand p hp).map (frobenius R p) = f ^ p := by
  classical
  rw [eq_iff_frequently_trunc'_eq, Filter.frequently_atTop]
  intro n
  use (p • n)
  refine ⟨le_self_nsmul zero_le hp, ?_⟩
  · have : (((trunc' R (p • n) f).expand p).map (frobenius R p)).toMvPowerSeries =
      MvPowerSeries.map (frobenius R p) ((trunc' R (p • n) f).expand p) := by
      simp only [MvPolynomial.map_expand, ← expand_eq_expand p hp, map_expand]
      congr
    rw [trunc'_map, trunc'_expand, ← trunc'_trunc'_pow (Nat.one_le_iff_ne_zero.mpr
      (expChar_ne_zero R p)), ← MvPolynomial.coe_pow p, ← MvPolynomial.map_frobenius_expand, this,
        trunc'_map, trunc'_expand_trunc' p hp (le_self_nsmul zero_le hp)]
/-
**MvPowerSeries.map_iterateFrobenius_expand** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries`。
形式化陈述：map_iterateFrobenius_expand (f : MvPowerSeries σ R) (n : Nat) : map (itera
teFrobenius R p n) (expand (p ^ n) (pow_ne_zero n hp) f) = f ^ p ^ n
参数：f : MvPowerSeries σ R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iterateFrobenius_zero`：iterateFrobenius_zero : iterateFrobenius R p 0 = 
RingHom.id R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MvPowerSeries.expand.congr_simp`：∀ {σ : Type u_1} {R : Type u_3} [inst :
 CommRing R] (p p_1 : ℕ) (e_p : p = p_1) (hp : p ≠ 0),   MvPowerSeries.expand p 
hp = MvPowerSeries.ex…
· 使用定理 `MvPowerSeries.expand_one`：expand_one : expand 1 one_ne_zero = AlgHom.id 
R (MvPowerSeries σ R)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `MvPowerSeries.map_frobenius_expand`：map_frobenius_expand {f : MvPowerSer
ies σ R} : (f.expand p hp).map (frobenius R p) = f ^ p
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `iterateFrobenius.congr_simp`：∀ (R : Type u_3) [inst : CommSemiring R] (p
 p_1 : ℕ) (e_p : p = p_1) (n n_1 : ℕ),   n = n_1 → ∀ [inst_1 : ExpChar R p], ite
rateFrobenius R p…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `iterateFrobenius_add`：iterateFrobenius_add : iterateFrobenius R p (m + n
) = (iterateFrobenius R p m).comp (iterateFrobenius R p n)
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用引理 `iterateFrobenius_one`：iterateFrobenius_one : iterateFrobenius R p 1 = fr
obenius R p
-/
theorem map_iterateFrobenius_expand (f : MvPowerSeries σ R) (n : ℕ) :
    map (iterateFrobenius R p n) (expand (p ^ n) (pow_ne_zero n hp) f) = f ^ p ^ n := by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p hp, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

end ExpChar

end MvPowerSeries

