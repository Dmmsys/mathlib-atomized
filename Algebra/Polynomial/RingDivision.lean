/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Theory of univariate polynomials

We prove basic results about univariate polynomials.

-/

@[expose] public section

assert_not_exists Ideal.map

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] {p q : R[X]}

section

variable [Semiring S]

/-
**Polynomial.natDegree_pos_of_aeval_root** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p != 0) {z : S}
 (hz : aeval z p = 0) (inj : forall x : R, algebraMap R S x = 0 -> x = 0) : 0 < 
p.natDegree
参数：hp : p != 0；hz : aeval z p = 0；inj : forall x : R, algebraMap R S x = 0 -> x 
= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_pos_of_eval₂_root`：natDegree_pos_of_eval₂_root {p :
 R[X]} (hp : p != 0) (f : R ->+* S) {z : S} (hz : eval₂ f z p = 0) (inj : forall
 x : R, f x = 0 -> x = 0) : …
-/
theorem natDegree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S}
    (hz : aeval z p = 0) (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.natDegree :=
  natDegree_pos_of_eval₂_root hp (algebraMap R S) hz inj
/-
**Polynomial.degree_pos_of_aeval_root** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p != 0) {z : S} (h
z : aeval z p = 0) (inj : forall x : R, algebraMap R S x = 0 -> x = 0) : 0 < p.d
egree
参数：hp : p != 0；hz : aeval z p = 0；inj : forall x : R, algebraMap R S x = 0 -> x 
= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Polynomial.natDegree_pos_of_aeval_root`：natDegree_pos_of_aeval_root [Alg
ebra R S] {p : R[X]} (hp : p != 0) {z : S} (hz : aeval z p = 0) (inj : forall x 
: R, algebraMap R S x = 0 ->…
-/
theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_aeval_root hp hz inj)

end

/-
**Polynomial.smul_modByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q)
参数：c : R；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_smul_le`：degree_smul_le {S : Type*} [SMulZeroClass S R
] (a : S) (p : R[X]) : degree (a • p) <= degree p
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.modByMonic_eq_of_not_monic`：modByMonic_eq_of_not_monic (p : R
[X]) (hq : ¬Monic q) : p %ₘ q = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
            (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]

/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
/-
**Polynomial.modByMonicHom** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：modByMonicHom (q : R[X]) : R[X] ->ₗ[R] R[X] where toFun p
参数：q : R[X]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.add_modByMonic`：add_modByMonic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ 
q = p₁ %ₘ q + p₂ %ₘ q
· 使用定理 `Polynomial.smul_modByMonic`：smul_modByMonic (c : R) (p : R[X]) : c • p %
ₘ q = c • (p %ₘ q)

--- 原说明 ---
`_ %ₘ q` as an `R`-linear map.
-/
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic
/-
**Polynomial.mem_ker_modByMonic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_ker_modByMonic (hq : q.Monic) {p : R[X]} : p in LinearMap.ker (modByMo
nicHom q) ↔ q ∣ p
参数：hq : q.Monic。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Polynomial.modByMonic_eq_zero_iff_dvd`：modByMonic_eq_zero_iff_dvd (hq : 
Monic q) : p %ₘ q = 0 ↔ q ∣ p
-/
theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p ∈ LinearMap.ker (modByMonicHom q) ↔ q ∣ p :=
  LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)

section

variable [Ring S]

/-
**Polynomial.aeval_modByMonic_eq_self_of_root** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} {x : S} (hx : 
aeval x q = 0) : aeval x (p %ₘ q) = aeval x p
参数：hx : aeval x q = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.modByMonic_eq_sub_mul_div`：modByMonic_eq_sub_mul_div : forall
 p q : R[X], p %ₘ q = p - q * (p /ₘ q) | p, q => letI
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p := by
  --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  simp [modByMonic_eq_sub_mul_div, hx]

end

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

/-
**Polynomial.trailingDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailin
gDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.trailingDegree_zero`：trailingDegree_zero : trailingDegree (0 
: R[X]) = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Polynomial.trailingDegree_eq_natTrailingDegree`：trailingDegree_eq_natTra
ilingDegree (hp : p != 0) : trailingDegree p = (natTrailingDegree p : Nat∞)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Polynomial.natTrailingDegree_mul`：natTrailingDegree_mul [NoZeroDivisors 
R] (hp : p != 0) (hq : q != 0) : (p * q).natTrailingDegree = p.natTrailingDegree
 + q.natTrailingDegree
· 使用定理 `WithTop.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
-/
theorem trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), natTrailingDegree_mul hp hq]
    apply WithTop.coe_add

end NoZeroDivisors


section CommRing

variable [CommRing R]

/-
**Polynomial.rootMultiplicity_eq_rootMultiplicity** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} : p.rootMultiplici
ty t = (p.comp (X + C t)).rootMultiplicity 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.algEquivAevalXAddC_apply`：∀ {R : Type u_3} [inst : CommRing R
] (t : R) (a : Polynomial R),   (Polynomial.algEquivAevalXAddC t) a = (Polynomia
l.aeval (Polynomial.X + P…
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `multiplicity_map_eq`：multiplicity_map_eq {F : Type*} [EquivLike F α β] [
MulEquivClass F α β] (f : F) {a b : α} : multiplicity (f a) (f b) = multiplicity
 a b
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
-/
theorem rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).rootMultiplicity 0 := by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0, sub_zero]
  convert! (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

/-- See `Polynomial.rootMultiplicity_eq_natTrailingDegree'` for the special case of `t = 0`. -/
/-
**Polynomial.rootMultiplicity_eq_natTrailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} : p.rootMultiplic
ity t = (p.comp (X + C t)).natTrailingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.rootMultiplicity_eq_rootMultiplicity`：rootMultiplicity_eq_roo
tMultiplicity {p : R[X]} {t : R} : p.rootMultiplicity t = (p.comp (X + C t)).roo
tMultiplicity 0
· 使用引理 `Polynomial.rootMultiplicity_eq_natTrailingDegree'`：rootMultiplicity_eq_n
atTrailingDegree' : p.rootMultiplicity 0 = p.natTrailingDegree

--- 原说明 ---
See `Polynomial.rootMultiplicity_eq_natTrailingDegree'` for the special case of 
`t = 0`.
-/
theorem rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).natTrailingDegree :=
  rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

section nonZeroDivisors

open scoped nonZeroDivisors

/-
**Polynomial.Monic.mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Mon
ic`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {p : Polynomial R}, p.Monic → p ∈ nonZe
roDivisors (Polynomial R)
参数：Polynomial R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.mem_nonzeroDivisors_of_coeff_mem`：mem_nonzeroDivisors_of_coef
f_mem {p : R[X]} (n : Nat) (hp : p.coeff n in R⁰) : p in R[X]⁰
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
-/
theorem Monic.mem_nonZeroDivisors {p : R[X]} (h : p.Monic) : p ∈ R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ (h.coeff_natDegree ▸ one_mem R⁰)
/-
**Polynomial.mem_nonZeroDivisors_of_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：mem_nonZeroDivisors_of_leadingCoeff {p : R[X]} (h : p.leadingCoeff in R⁰) 
: p in R[X]⁰
参数：h : p.leadingCoeff in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.mem_nonzeroDivisors_of_coeff_mem`：mem_nonzeroDivisors_of_coef
f_mem {p : R[X]} (n : Nat) (hp : p.coeff n in R⁰) : p in R[X]⁰
-/
theorem mem_nonZeroDivisors_of_leadingCoeff {p : R[X]} (h : p.leadingCoeff ∈ R⁰) : p ∈ R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ h
/-
**Polynomial.mem_nonZeroDivisors_of_trailingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：mem_nonZeroDivisors_of_trailingCoeff {p : R[X]} (h : p.trailingCoeff in R⁰
) : p in R[X]⁰
参数：h : p.trailingCoeff in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.mem_nonzeroDivisors_of_coeff_mem`：mem_nonzeroDivisors_of_coef
f_mem {p : R[X]} (n : Nat) (hp : p.coeff n in R⁰) : p in R[X]⁰
-/
theorem mem_nonZeroDivisors_of_trailingCoeff {p : R[X]} (h : p.trailingCoeff ∈ R⁰) : p ∈ R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ h

end nonZeroDivisors

/-
**Polynomial._root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one** 是 Mathlib 中的
一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one [IsDomain R] [Ring S] [Algebra R S]
    [FaithfulSMul R S] {p : R[X]} (hp : Irreducible p) (hdeg : p.natDegree ≠ 1) {x : S}
    (hx : x ∈ (algebraMap R S).range) : p.aeval x ≠ 0 := by
  obtain ⟨_, rfl⟩ := hx
  rw [aeval_algebraMap_apply_eq_algebraMap_eval]
  exact fun heq ↦ hp.not_isRoot_of_natDegree_ne_one hdeg <|
    FaithfulSMul.algebraMap_injective _ _ <| map_zero (algebraMap R S) ▸ heq
/-
**Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：natDegree_pos_of_monic_of_aeval_eq_zero [Nontrivial R] [Semiring S] [Algeb
ra R S] [FaithfulSMul R S] {p : R[X]} (hp : p.Monic) {x : S} (hx : aeval x p = 0
) : 0 < p.natDegree
参数：hp : p.Monic；hx : aeval x p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_pos_of_aeval_root`：natDegree_pos_of_aeval_root [Alg
ebra R S] {p : R[X]} (hp : p != 0) {z : S} (hz : aeval z p = 0) (inj : forall x 
: R, algebraMap R S x = 0 ->…
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem natDegree_pos_of_monic_of_aeval_eq_zero [Nontrivial R] [Semiring S] [Algebra R S]
    [FaithfulSMul R S] {p : R[X]} (hp : p.Monic) {x : S} (hx : aeval x p = 0) :
    0 < p.natDegree :=
  natDegree_pos_of_aeval_root (Monic.ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap R S)).mp (FaithfulSMul.algebraMap_injective R S))
/-
**Polynomial.rootMultiplicity_mul_X_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：rootMultiplicity_mul_X_sub_C_pow {p : R[X]} {a : R} {n : Nat} (h : p != 0)
 : (p * (X - C a) ^ n).rootMultiplicity a = p.rootMultiplicity a + n
参数：h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.mul_left_ne_zero`：∀ {R : Type u} [inst : Semiring R] {p
 : Polynomial R}, p.Monic → ∀ {q : Polynomial R}, q ≠ 0 → q * p ≠ 0
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.rootMultiplicity_le_iff`：rootMultiplicity_le_iff (p0 : p != 0
) (a : R) (n : Nat) : rootMultiplicity a p <= n ↔ ¬(X - C a) ^ (n + 1) ∣ p
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `dvd_cancel_right_mem_nonZeroDivisors`：dvd_cancel_right_mem_nonZeroDiviso
rs (hr : r in R⁰) : x * r ∣ y * r ↔ x ∣ y
· 使用定理 `Polynomial.Monic.mem_nonZeroDivisors`：∀ {R : Type u} [inst : CommRing R]
 {p : Polynomial R}, p.Monic → p ∈ nonZeroDivisors (Polynomial R)
· 使用引理 `Polynomial.pow_rootMultiplicity_not_dvd`：pow_rootMultiplicity_not_dvd (p
0 : p != 0) (a : R) : ¬(X - C a) ^ (rootMultiplicity a p + 1) ∣ p
· 使用引理 `Polynomial.le_rootMultiplicity_iff`：le_rootMultiplicity_iff (p0 : p != 0
) {a : R} {n : Nat} : n <= rootMultiplicity a p ↔ (X - C a) ^ n ∣ p
· 使用定理 `mul_dvd_mul_right`：mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c
· 使用定理 `Polynomial.pow_rootMultiplicity_dvd`：pow_rootMultiplicity_dvd (p : R[X])
 (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p
-/
theorem rootMultiplicity_mul_X_sub_C_pow {p : R[X]} {a : R} {n : ℕ} (h : p ≠ 0) :
    (p * (X - C a) ^ n).rootMultiplicity a = p.rootMultiplicity a + n := by
  have h2 := monic_X_sub_C a |>.pow n |>.mul_left_ne_zero h
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h2, add_assoc, add_comm n, ← add_assoc, pow_add,
      dvd_cancel_right_mem_nonZeroDivisors (monic_X_sub_C a |>.pow n |>.mem_nonZeroDivisors)]
    exact pow_rootMultiplicity_not_dvd h a
  · rw [le_rootMultiplicity_iff h2, pow_add]
    exact mul_dvd_mul_right (pow_rootMultiplicity_dvd p a) _

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
/-
**Polynomial.rootMultiplicity_X_sub_C_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : Nat) : rootMultip
licity a ((X - C a) ^ n) = n
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.rootMultiplicity_mul_X_sub_C_pow`：rootMultiplicity_mul_X_sub_
C_pow {p : R[X]} {a : R} {n : Nat} (h : p != 0) : (p * (X - C a) ^ n).rootMultip
licity a = p.rootMultiplicity a +…
· 使用定理 `RingHom.map_one_ne_zero`：map_one_ne_zero [Nontrivial β] : f 1 != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
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
· 使用定理 `Polynomial.rootMultiplicity_C`：rootMultiplicity_C (r a : R) : rootMultip
licity a (C r) = 0

--- 原说明 ---
The multiplicity of `a` as root of `(X - a) ^ n` is `n`.
-/
theorem rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this
/-
**Polynomial.rootMultiplicity_X_sub_C_self** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} : rootMultiplicity x 
(X - C x) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.rootMultiplicity_X_sub_C_pow`：rootMultiplicity_X_sub_C_pow [N
ontrivial R] (a : R) (n : Nat) : rootMultiplicity a ((X - C a) ^ n) = n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} :
    rootMultiplicity x (X - C x) = 1 :=
  pow_one (X - C x) ▸ rootMultiplicity_X_sub_C_pow x 1
/-
**Polynomial.rootMultiplicity_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} : rootMu
ltiplicity x (X - C y) = if x = y then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.rootMultiplicity_X_sub_C_self`：rootMultiplicity_X_sub_C_self 
[Nontrivial R] {x : R} : rootMultiplicity x (X - C x) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.rootMultiplicity_eq_zero`：rootMultiplicity_eq_zero {p : R[X]}
 {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.root_X_sub_C`：root_X_sub_C : IsRoot (X - C a) b ↔ a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} :
    rootMultiplicity x (X - C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))
/-
**Polynomial.rootMultiplicity_comp_C_mul_X_add_C_le** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem rootMultiplicity_comp_C_mul_X_add_C_le (p : R[X]) (a b c : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).rootMultiplicity c ≤ p.rootMultiplicity (a * c + b) := by
  let : Invertible a := ha.invertible
  rcases eq_or_ne p 0 with rfl | hp; · simp
  rw [le_rootMultiplicity_iff hp]
  have h := pow_rootMultiplicity_dvd (p.comp (C a * X + C b)) c
  rw [dvd_comp_C_mul_X_add_C_iff, pow_comp] at h
  refine (pow_dvd_pow_of_dvd ((isUnit_C.mpr ha).dvd_mul_left.mp (dvd_of_eq ?_)) _).trans h
  simp [← map_mul, mul_sub, ← mul_assoc, sub_sub, add_comm, mul_add]
/-
**Polynomial.rootMultiplicity_comp_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：rootMultiplicity_comp_C_mul_X_add_C (p : R[X]) (a b c : R) (ha : IsUnit a)
 : (p.comp (C a * X + C b)).rootMultiplicity c = p.rootMultiplicity (a * c + b)
参数：p : R[X]；a b c : R；ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `_private.Mathlib.Algebra.Polynomial.RingDivision.0.Polynomial.rootMultip
licity_comp_C_mul_X_add_C_le`：∀ {R : Type u} [inst : CommRing R] (p : Polynomial
 R) (a b c : R),   IsUnit a →     Polynomial.rootMultiplicity c (p.comp (Polynom
ial.C a * …
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
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
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `Polynomial.comp_X`：comp_X : p.comp X = p
· 使用定理 `invOf_mul_self'`：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : ⅟a * a = 1
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
-/
theorem rootMultiplicity_comp_C_mul_X_add_C (p : R[X]) (a b c : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).rootMultiplicity c = p.rootMultiplicity (a * c + b) := by
  let : Invertible a := ha.invertible
  apply le_antisymm (rootMultiplicity_comp_C_mul_X_add_C_le p a b c ha)
  have := rootMultiplicity_comp_C_mul_X_add_C_le
    (p.comp (C a * X + C b)) ⅟a (- ⅟a * b) (a * c + b) (isUnit_of_invertible ⅟a)
  simpa [comp_assoc, mul_add, ← mul_assoc, ← map_mul] using this
/-
**Polynomial.rootMultiplicity_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_mul' {p q : R[X]} {x : R} (hpq : (p /ₘ (X - C x) ^ p.root
Multiplicity x).eval x * (q /ₘ (X - C x) ^ q.rootMultiplicity x).eval x != 0) : 
rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q
参数：hpq : (p /ₘ (X - C x) ^ p.rootMultiplicity x).eval x * (q /ₘ (X - C x) ^ q.ro
otMultiplicity x).eval x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_eq_natTrailingDegree`：rootMultiplicity_eq_na
tTrailingDegree {p : R[X]} {t : R} : p.rootMultiplicity t = (p.comp (X + C t)).n
atTrailingDegree
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natTrailingDegree_mul'`：natTrailingDegree_mul' (h : p.trailin
gCoeff * q.trailingCoeff != 0) : (p * q).natTrailingDegree = p.natTrailingDegree
 + q.natTrailingDegree
· 使用引理 `Polynomial.eval_divByMonic_eq_trailingCoeff_comp`：eval_divByMonic_eq_tra
ilingCoeff_comp {p : R[X]} {t : R} : (p /ₘ (X - C t) ^ p.rootMultiplicity t).eva
l t = (p.comp (X + C t)).trailingCoeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rootMultiplicity_mul' {p q : R[X]} {x : R}
    (hpq : (p /ₘ (X - C x) ^ p.rootMultiplicity x).eval x *
      (q /ₘ (X - C x) ^ q.rootMultiplicity x).eval x ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  simp_rw [eval_divByMonic_eq_trailingCoeff_comp] at hpq
  simp_rw [rootMultiplicity_eq_natTrailingDegree, mul_comp, natTrailingDegree_mul' hpq]
/-
**Polynomial.Monic.neg_one_pow_natDegree_mul_comp_neg_X** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {p : Polynomial R}, p.Monic → ((-1) ^ p
.natDegree * p.comp (-Polynomial.X)).Monic
参数：(-1) ^ p.natDegree * p.comp (-Polynomial.X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one`：monic_mul_C_of_leadin
gCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) : Monic (p * C b)
· 使用定理 `Polynomial.comp_neg_X_leadingCoeff_eq`：∀ {R : Type u} [inst : Ring R] (p
 : Polynomial R),   (p.comp (-Polynomial.X)).leadingCoeff = (-1) ^ p.natDegree *
 p.leadingCoeff
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem Monic.neg_one_pow_natDegree_mul_comp_neg_X {p : R[X]} (hp : p.Monic) :
    ((-1) ^ p.natDegree * p.comp (-X)).Monic := by
  simp only [Monic]
  calc
    ((-1) ^ p.natDegree * p.comp (-X)).leadingCoeff =
        (p.comp (-X) * C ((-1) ^ p.natDegree)).leadingCoeff := by
      simp [mul_comm]
    _ = 1 := by
      apply monic_mul_C_of_leadingCoeff_mul_eq_one
      simp [← pow_add, hp]

variable [IsDomain R] {p q : R[X]}
/-
**Polynomial.degree_eq_degree_of_associated** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q
参数：h : Associated p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Polynomial.degree_coe_units`：degree_coe_units [Nontrivial R] (u : R[X]ˣ)
 : degree (u : R[X]) = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  simp [hu.symm]
/-
**Polynomial.prime_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：prime_X_sub_C (r : R) : Prime (X - C r)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.not_isUnit_X_sub_C`：not_isUnit_X_sub_C [Nontrivial R] (r : R)
 : ¬IsUnit (X - C r)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    exact id⟩
/-
**Polynomial.prime_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：prime_X : Prime (X : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.prime_X_sub_C`：prime_X_sub_C (r : R) : Prime (X - C r)
-/
theorem prime_X : Prime (X : R[X]) := by
  convert! prime_X_sub_C (0 : R)
  simp
/-
**Polynomial.Monic.prime_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Monic`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [IsDomain R] {p : Polynomial R}, p.degr
ee = 1 → p.Monic → Prime p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
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
· 使用定理 `Polynomial.eq_X_add_C_of_degree_eq_one`：eq_X_add_C_of_degree_eq_one (h :
 degree p = 1) : p = C p.leadingCoeff * X + C (p.coeff 0)
· 使用定理 `Polynomial.prime_X_sub_C`：prime_X_sub_C (r : R) : Prime (X - C r)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _
/-
**Polynomial.irreducible_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：irreducible_X_sub_C (r : R) : Irreducible (X - C r)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Polynomial.prime_X_sub_C`：prime_X_sub_C (r : R) : Prime (X - C r)
-/
theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) :=
  (prime_X_sub_C r).irreducible
/-
**Polynomial.irreducible_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：irreducible_X : Irreducible (X : R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Polynomial.prime_X`：prime_X : Prime (X : R[X])
-/
theorem irreducible_X : Irreducible (X : R[X]) :=
  Prime.irreducible prime_X
/-
**Polynomial.Monic.irreducible_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial.Monic`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [IsDomain R] {p : Polynomial R}, p.degr
ee = 1 → p.Monic → Irreducible p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Polynomial.Monic.prime_of_degree_eq_one`：∀ {R : Type u} [inst : CommRing
 R] [IsDomain R] {p : Polynomial R}, p.degree = 1 → p.Monic → Prime p
-/
theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).irreducible

/-- A degree 1 polynomial `C a * X + C b` is irreducible
if `a, b` are relatively prime. -/
/-
**Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：irreducible_of_degree_eq_one_of_isRelPrime_coeff {p : R[X]} (hp : p.degree
 = 1) (hc : IsRelPrime (p.coeff 0) (p.coeff 1)) : Irreducible p where not_isUnit
 h
参数：hp : p.degree = 1；hc : IsRelPrime (p.coeff 0) (p.coeff 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.WithBot.add_eq_one_iff`：add_eq_one_iff {n m : WithBot Nat} : n + m =
 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero (h : degree p 
= 0) : p = C (coeff p 0)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A degree 1 polynomial `C a * X + C b` is irreducible
if `a, b` are relatively prime.
-/
theorem irreducible_of_degree_eq_one_of_isRelPrime_coeff
    {p : R[X]} (hp : p.degree = 1) (hc : IsRelPrime (p.coeff 0) (p.coeff 1)) :
    Irreducible p where
  not_isUnit h := by
    obtain ⟨u, -, h⟩ := isUnit_iff.mp h
    apply not_le.mpr (zero_lt_one' (WithBot ℕ))
    simp [← hp, ← h, degree_C_le]
  isUnit_or_isUnit f g h := by
    wlog! H : f.degree ≤ g.degree generalizing f g
    · rw [mul_comm] at h
      exact (this g f h H.le).symm
    left
    rw [h, degree_mul, Nat.WithBot.add_eq_one_iff] at hp
    rcases hp with ⟨hf, hg⟩ | ⟨hf, hg⟩; swap
    · simp [← not_lt, hf, hg] at H
    replace hf := f.eq_C_of_degree_eq_zero hf
    rw [hf]
    apply IsUnit.map C
    rw [h, hf, coeff_C_mul, coeff_C_mul] at hc
    apply hc <;> simp
/-
**Polynomial.irreducible_C_mul_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：irreducible_C_mul_X_add_C {a b : R} (ha : a != 0) (hab : IsRelPrime a b) :
 Irreducible (C a * X + C b)
参数：ha : a != 0；hab : IsRelPrime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff`：irreducible
_of_degree_eq_one_of_isRelPrime_coeff {p : R[X]} (hp : p.degree = 1) (hc : IsRel
Prime (p.coeff 0) (p.coeff 1)) : Irreducible p wh…
· 使用定理 `Mathlib.Tactic.ComputeDegree.degree_eq_of_le_of_coeff_ne_zero'`：degree_e
q_of_le_of_coeff_ne_zero' {deg m o : WithBot Nat} {c : R} {p : R[X]} (h_deg_le :
 degree p <= m) (coeff_eq : coeff p (WithBot.unbotD …
· 使用定理 `Polynomial.degree_add_le_of_le`：degree_add_le_of_le {a b : WithBot Nat} 
(hp : degree p <= a) (hq : degree q <= b) : degree (p + q) <= max a b
· 使用定理 `Polynomial.degree_mul_le_of_le`：degree_mul_le_of_le {a b : WithBot Nat} 
(hp : degree p <= a) (hq : degree q <= b) : degree (p * q) <= a + b
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Polynomial.degree_X_le`：degree_X_le : degree (X : R[X]) <= 1
· 使用定理 `Mathlib.Tactic.ComputeDegree.coeff_congr_lhs`：coeff_congr_lhs (h : coeff
 f m = r) (natDeg_eq_coeff : m = n) : coeff f n = r
· 使用定理 `Mathlib.Tactic.ComputeDegree.coeff_add_of_eq`：coeff_add_of_eq {n : Nat} 
{a b : R} {f g : R[X]} (h_add_left : f.coeff n = a) (h_add_right : g.coeff n = b
) : (f + g).coeff n = a + b
· 使用定理 `Mathlib.Tactic.ComputeDegree.coeff_mul_add_of_le_natDegree_of_eq_ite`：co
eff_mul_add_of_le_natDegree_of_eq_ite {d df dg : Nat} {a b : R} {f g : R[X]} (h_
mul_left : natDegree f <= df) (h_mul_right : natDegree g <…
· 使用定理 `Mathlib.Tactic.ComputeDegree.natDegree_C_le`：natDegree_C_le (a : R) : na
tDegree (C a) <= 0
· 使用定理 `Polynomial.natDegree_X_le`：natDegree_X_le : (X : R[X]).natDegree <= 1
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `Polynomial.coeff_X`：coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 
0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 39 条，此处仅展示前 30 条）
-/
theorem irreducible_C_mul_X_add_C {a b : R} (ha : a ≠ 0) (hab : IsRelPrime a b) :
    Irreducible (C a * X + C b) := by
  apply irreducible_of_degree_eq_one_of_isRelPrime_coeff
  · compute_degree!
  · simpa using hab.symm
/-
**Polynomial.aeval_ne_zero_of_isCoprime** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：aeval_ne_zero_of_isCoprime {R} [CommSemiring R] [Nontrivial S] [Semiring S
] [Algebra R S] {p q : R[X]} (h : IsCoprime p q) (s : S) : aeval s p != 0 ∨ aeva
l s q != 0
参数：h : IsCoprime p q；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma aeval_ne_zero_of_isCoprime {R} [CommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S]
    {p q : R[X]} (h : IsCoprime p q) (s : S) : aeval s p ≠ 0 ∨ aeval s q ≠ 0 := by
  by_contra! ⟨hp, hq⟩
  rcases h with ⟨_, _, h⟩
  apply_fun aeval s at h
  simp only [map_add, map_mul, map_one, hp, hq, mul_zero, add_zero, zero_ne_one] at h
/-
**Polynomial.isCoprime_X_sub_C_of_isUnit_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a 
- b)) : IsCoprime (X - C a) (X - C b)
参数：h : IsUnit (a - b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul_comm`：neg_mul_comm (a b : α) : -a * b = a * -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `Polynomial.C_sub`：C_sub : C (a - b) = C a - C b
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
-/
theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - C a) (X - C b) :=
  ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩

open scoped Function in -- required for scoped `on` notation
/-
**Polynomial.pairwise_coprime_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I -> K} (H : Func
tion.Injective s) : Pairwise (IsCoprime on fun i : I => X - C (s i))
参数：H : Function.Injective s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isCoprime_X_sub_C_of_isUnit_sub`：isCoprime_X_sub_C_of_isUnit_
sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) : IsCoprime (X - C a) (X - C
 b)
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - C (s i)) := fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit
/-
**Polynomial.rootMultiplicity_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q != 0) : rootMultipl
icity x (p * q) = rootMultiplicity x p + rootMultiplicity x q
参数：hpq : p * q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootMultiplicity_eq_multiplicity`：rootMultiplicity_eq_multipl
icity [DecidableEq R] (p : R[X]) (a : R) : rootMultiplicity a p = if p = 0 then 
0 else multiplicity (X - C a) p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `multiplicity_mul`：multiplicity_mul {p a b : α} (hp : Prime p) (hfin : Fi
niteMultiplicity p (a * b)) : multiplicity p (a * b) = multiplicity p a + multip
licity…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Polynomial.prime_X_sub_C`：prime_X_sub_C (r : R) : Prime (X - C r)
· 使用定理 `Polynomial.finiteMultiplicity_X_sub_C`：finiteMultiplicity_X_sub_C (a : R
) (h0 : p != 0) : FiniteMultiplicity (X - C a) p
-/
theorem rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  classical
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q), if_neg hpq, rootMultiplicity_eq_multiplicity p,
    if_neg hp, rootMultiplicity_eq_multiplicity q, if_neg hq,
    multiplicity_mul (prime_X_sub_C x) (finiteMultiplicity_X_sub_C _ hpq)]

open Multiset in
/-
**Polynomial.exists_multiset_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_multiset_roots [DecidableEq R] : forall {p : R[X]} (_ : p != 0), ex
ists s : Multiset R, (Multiset.card s : WithBot Nat) <= degree p ∧ forall a, s.c
ount a = rootMultiplicity a p | p, hp => haveI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_multiset_roots._unary`：∀ {R : Type u} [inst : CommRing
 R] [IsDomain R] [inst_2 : DecidableEq R] (_x : (p : Polynomial R) ×' p ≠ 0),   
∃ s, ↑s.card ≤ _x.1.degree ∧ …
-/
theorem exists_multiset_roots [DecidableEq R] :
    ∀ {p : R[X]} (_ : p ≠ 0), ∃ s : Multiset R,
      (Multiset.card s : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = rootMultiplicity a p
  | p, hp =>
    haveI := Classical.propDecidable (∃ x, IsRoot p x)
    if h : ∃ x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) ≠ 0 := fun h => by
        rw [← mul_divByMonic_eq_iff_isRoot.2 hx, h, mul_zero] at hp; exact hp rfl
      have wf : degree (p /ₘ (X - C x)) < degree p :=
        degree_divByMonic_lt _ _ hp ((degree_X_sub_C x).symm ▸ by decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots _ (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) ≤ degree p := by
        simpa using Nat.WithBot.one_le_iff_zero_lt.mpr hpd
      have hdiv0 : p /ₘ (X - C x) ≠ 0 :=
        mt (divByMonic_eq_zero_iff (monic_X_sub_C x)).1 <| not_lt.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = Multiset.card t + 1 := by
            congr
            exact mod_cast Multiset.card_cons _ _
          _ ≤ degree p := by
            rw [← degree_add_divByMonic (monic_X_sub_C x) hdeg, degree_X_sub_C, add_comm]
            exact add_le_add (le_refl (1 : WithBot ℕ)) htd,
        by
          intro a
          conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hx]
          rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
            rootMultiplicity_X_sub_C, ← htr a]
          split_ifs with ha
          · rw [ha, count_cons_self, add_comm]
          · rw [count_cons_of_ne ha, zero_add]⟩
    else
      ⟨0, (degree_eq_natDegree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_le _), by
        intro a
        rw [count_zero, rootMultiplicity_eq_zero (not_exists.mp h a)]⟩
termination_by p => natDegree p
decreasing_by {
  apply (Nat.cast_lt (α := WithBot ℕ)).mp
  simp only [degree_eq_natDegree hp, degree_eq_natDegree hd0] at wf
  assumption}

end CommRing

end Polynomial

