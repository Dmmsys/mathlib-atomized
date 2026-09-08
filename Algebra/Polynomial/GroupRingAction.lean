/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `MulSemiringAction` to `Polynomial`.
-/

@[expose] public section


variable (M : Type*) [Monoid M]

open Polynomial

namespace Polynomial

variable (R : Type*) [Semiring R]

variable {M} in
-- In this statement, we use `HSMul.hSMul m` as LHS instead of `(m • ·)`
-- to avoid a spurious lambda-expression that complicates rewriting with this lemma.
/-
**Polynomial.smul_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_eq_map [MulSemiringAction M R] (m : M) : HSMul.hSMul m = map (MulSemi
ringAction.toRingHom M R m)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `MulSemiringAction.toRingHom_apply`：∀ (M : Type u_1) [inst : Monoid M] (R
 : Type v) [inst_1 : Semiring R] [inst_2 : MulSemiringAction M R] (x : M)   (x_1
 : R), (MulSemiringActi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_eq_map [MulSemiringAction M R] (m : M) :
    HSMul.hSMul m = map (MulSemiringAction.toRingHom M R m) := by
  ext
  simp
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [MulSemiringAction M R] : MulSemiringAction M R[X] :=
  { Polynomial.distribMulAction with
    smul_one := fun m ↦
      smul_eq_map R m ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m _ _ ↦
      smul_eq_map R m ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

variable {M R}
variable [MulSemiringAction M R]

@[simp]
/-
**Polynomial.smul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_X (m : M) : (m • X : R[X]) = X
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.smul_eq_map`：smul_eq_map [MulSemiringAction M R] (m : M) : HS
Mul.hSMul m = map (MulSemiringAction.toRingHom M R m)
-/
theorem smul_X (m : M) : (m • X : R[X]) = X :=
  (smul_eq_map R m).symm ▸ map_X _

variable (S : Type*) [CommSemiring S] [MulSemiringAction M S]
/-
**Polynomial.smul_eval_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_eval_smul (m : M) (f : S[X]) (x : S) : (m • f).eval (m • x) = m • f.e
val x
参数：m : M；f : S[X]；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on`：∀ {R : Type u} [inst : Semiring R] {motive : Po
lynomial R → Prop} (p : Polynomial R),   (∀ (a : R), motive (Polynomial.C a)) → 
    (∀ (p q :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smul_C`：smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • 
C r = C (s • r)
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂
· 使用定理 `smul_pow'`：∀ {M : Type u_2} {A : Type u_3} [inst : Monoid M] [inst_1 : M
onoid A] [inst_2 : MulDistribMulAction M A] (r : M) (x : A)   (n : ℕ), r • x ^ …
· 使用定理 `Polynomial.smul_X`：smul_X (m : M) : (m • X : R[X]) = X
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
-/
theorem smul_eval_smul (m : M) (f : S[X]) (x : S) : (m • f).eval (m • x) = m • f.eval x :=
  Polynomial.induction_on f (fun r ↦ by rw [smul_C, eval_C, eval_C])
    (fun f g ihf ihg ↦ by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r _ ↦ by
    rw [smul_mul', smul_pow', smul_C, smul_X, eval_mul, eval_C, eval_X_pow, eval_mul, eval_C,
      eval_X_pow, smul_mul', smul_pow']

variable (G : Type*) [Group G]
/-
**Polynomial.eval_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_smul' [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) : f.eval (g 
• x) = g • (g⁻¹ • f).eval x
参数：g : G；f : S[X]；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.smul_eval_smul`：smul_eval_smul (m : M) (f : S[X]) (x : S) : (
m • f).eval (m • x) = m • f.eval x
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem eval_smul' [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    f.eval (g • x) = g • (g⁻¹ • f).eval x := by
  rw [← smul_eval_smul, smul_inv_smul]
/-
**Polynomial.smul_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：smul_eval [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) : (g • f).eva
l x = g • f.eval (g⁻¹ • x)
参数：g : G；f : S[X]；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.smul_eval_smul`：smul_eval_smul (m : M) (f : S[X]) (x : S) : (
m • f).eval (m • x) = m • f.eval x
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem smul_eval [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    (g • f).eval x = g • f.eval (g⁻¹ • x) := by
  rw [← smul_eval_smul, smul_inv_smul]

end Polynomial

section CommRing

variable (G : Type*) [Group G] [Fintype G]
variable (R : Type*) [CommRing R] [MulSemiringAction G R]

open MulAction

/-- the product of `(X - g • x)` over distinct `g • x`. -/
/-
**prodXSubSMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：prodXSubSMul (x : R) : R[X]
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the product of `(X - g • x)` over distinct `g • x`.
-/
noncomputable def prodXSubSMul (x : R) : R[X] :=
  letI := Classical.decEq R
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g ↦
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)
/-
**prodXSubSMul.monic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prodXSubSMul.monic (x : R) : (prodXSubSMul G R x).Monic
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_prod_of_monic`：monic_prod_of_monic (s : Finset ι) (f : 
ι -> R[X]) (hs : forall i in s, Monic (f i)) : Monic (∏ i in s, f i)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem prodXSubSMul.monic (x : R) : (prodXSubSMul G R x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_X_sub_C _
/-
**prodXSubSMul.eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prodXSubSMul.eval (x : R) : (prodXSubSMul G R x).eval x = 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodXSubSMul.eval (x : R) : (prodXSubSMul G R x).eval x = 0 :=
  letI := Classical.decEq R
  (map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] →* R) _ _).trans <|
    Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) <| by simp
/-
**prodXSubSMul.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prodXSubSMul.smul (x : R) (g : G) : g • prodXSubSMul G R x = prodXSubSMul 
G R x
参数：x : R；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.smul_prod'`：Finset.smul_prod' {r : M} {f : γ -> N} {s : Finset γ}
 : (r • ∏ x in s, f x) = ∏ x in s, r • f x
· 使用引理 `Fintype.prod_bijective`：prod_bijective (e : ι -> κ) (he : e.Bijective) (
f : ι -> M) (g : κ -> M) (h : forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.ofQuotientStabilizer_smul`：ofQuotientStabilizer_smul (g : G) (
g' : G ⧸ MulAction.stabilizer G x) : ofQuotientStabilizer G x (g • g') = g • ofQ
uotientStabilizer G x g'
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Polynomial.smul_X`：smul_X (m : M) : (m • X : R[X]) = X
· 使用定理 `Polynomial.smul_C`：smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • 
C r = C (s • r)
-/
theorem prodXSubSMul.smul (x : R) (g : G) : g • prodXSubSMul G R x = prodXSubSMul G R x :=
  letI := Classical.decEq R
  Finset.smul_prod'.trans <|
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' ↦ by
      rw [ofQuotientStabilizer_smul, smul_sub, Polynomial.smul_X, Polynomial.smul_C]
/-
**prodXSubSMul.coeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prodXSubSMul.coeff (x : R) (g : G) (n : Nat) : g • (prodXSubSMul G R x).co
eff n = (prodXSubSMul G R x).coeff n
参数：x : R；g : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用定理 `prodXSubSMul.smul`：prodXSubSMul.smul (x : R) (g : G) : g • prodXSubSMul 
G R x = prodXSubSMul G R x
-/
theorem prodXSubSMul.coeff (x : R) (g : G) (n : ℕ) :
    g • (prodXSubSMul G R x).coeff n = (prodXSubSMul G R x).coeff n := by
  rw [← Polynomial.coeff_smul, prodXSubSMul.smul]

end CommRing

namespace MulSemiringActionHom

variable {M}
variable {P : Type*} [CommSemiring P] [MulSemiringAction M P]
variable {Q : Type*} [CommSemiring Q] [MulSemiringAction M Q]

open Polynomial

/-- An equivariant map induces an equivariant map on polynomials. -/
/-
**MulSemiringActionHom.polynomial** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringActionHo
m`。
形式化陈述：{M : Type u_1} →   [inst : Monoid M] →     {P : Type u_2} →       [inst_1 
: CommSemiring P] →         [inst_2 : MulSemiringAction M P] →           {Q : Ty
pe u_3} →             [inst_3 : CommSemiring Q] →               [inst_4 : MulSem
iringAction M Q] → (P →+*[M] Q) → Polynomial P →+*[M] Polynomial Q
参数：P →+*[M] Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivariant map induces an equivariant map on polynomials.
-/
protected noncomputable def polynomial (g : P →+*[M] Q) : P[X] →+*[M] Q[X] where
  toFun := map g
  map_smul' m p :=
    Polynomial.induction_on p
      (fun b ↦ by rw [MonoidHom.id_apply, smul_C, map_C, coe_fn_coe, g.map_smul, map_C,
          coe_fn_coe, smul_C])
      (fun p q ihp ihq ↦ by
        rw [smul_add, Polynomial.map_add, ihp, ihq, Polynomial.map_add, smul_add])
      fun n b _ ↦ by rw [MonoidHom.id_apply, smul_mul', smul_C, smul_pow', smul_X,
        Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X, coe_fn_coe, g.map_smul, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
        smul_mul', smul_C, smul_pow', smul_X, coe_fn_coe]
  map_zero' := Polynomial.map_zero (g : P →+* Q)
  map_add' _ _ := Polynomial.map_add (g : P →+* Q)
  map_one' := Polynomial.map_one (g : P →+* Q)
  map_mul' _ _ := Polynomial.map_mul (g : P →+* Q)

@[simp]
/-
**MulSemiringActionHom.coe_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActi
onHom`。
形式化陈述：coe_polynomial (g : P ->+*[M] Q) : (g.polynomial : P[X] -> Q[X]) = map g
参数：g : P ->+*[M] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_polynomial (g : P →+*[M] Q) : (g.polynomial : P[X] → Q[X]) = map g := rfl

end MulSemiringActionHom

