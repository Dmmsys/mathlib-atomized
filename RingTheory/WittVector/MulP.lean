/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.IsPoly

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mulN_isPoly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p -- type as `\bbW`

open MvPolynomial

noncomputable section

variable (p) in
/-- `wittMulN p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
/-
**WittVector.wittMulN** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) → [hp : Fact (Nat.Prime p)] → ℕ → ℕ → MvPolynomial ℕ ℤ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`wittMulN p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`.
-/
noncomputable def wittMulN : ℕ → ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | n + 1 => fun k => bind₁ (Function.uncurry <| ![wittMulN n, X]) (wittAdd p k)
/-
**WittVector.mulN_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mulN_coeff (n : Nat) (x : 𝕎 R) (k : Nat) : (x * n).coeff k = aeval x.coeff
 (wittMulN p n k)
参数：n : Nat；x : 𝕎 R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WittVector.wittMulN.eq_2`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ),  
 WittVector.wittMulN p n.succ = fun k =>     (MvPolynomial.bind₁ (Function.uncur
ry ![WittVecto…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.aeval_bind₁`：aeval_bind₁ [Algebra R S] (f : τ -> S) (g : σ 
-> MvPolynomial τ R) (φ : MvPolynomial σ R) : aeval f (bind₁ g φ) = aeval (fun i
 => aeval f (g…
· 使用定理 `WittVector.add_coeff`：add_coeff (x y : 𝕎 R) (n : Nat) : (x + y).coeff n 
= peval (wittAdd p n) ![x.coeff, y.coeff]
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
（共 34 条，此处仅展示前 30 条）
-/
theorem mulN_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) :
    (x * n).coeff k = aeval x.coeff (wittMulN p n k) := by
  induction n generalizing k with
  | zero => simp only [Nat.cast_zero, mul_zero, zero_coeff, wittMulN, Pi.zero_apply, map_zero]
  | succ n ih =>
    rw [wittMulN, Nat.cast_add, Nat.cast_one, mul_add, mul_one, aeval_bind₁, add_coeff]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1 ⟨b, i⟩
    fin_cases b
    · simp [Function.uncurry, Matrix.cons_val_zero, ih]
    · simp [Function.uncurry, Matrix.cons_val_one, aeval_X]

variable (p)

/-- Multiplication by `n` is a polynomial function. -/
@[is_poly]
/-
**WittVector.mulN_isPoly** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mulN_isPoly (n : Nat) : IsPoly p fun _ _Rcr x => x * n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WittVector.mulN_coeff`：mulN_coeff (n : Nat) (x : 𝕎 R) (k : Nat) : (x * n
).coeff k = aeval x.coeff (wittMulN p n k)

--- 原说明 ---
Multiplication by `n` is a polynomial function.
-/
theorem mulN_isPoly (n : ℕ) : IsPoly p fun _ _Rcr x => x * n :=
  ⟨⟨wittMulN p n, fun R _Rcr x => by funext k; exact mulN_coeff n x k⟩⟩

@[simp]
/-
**WittVector.bind** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_wittMulN_wittPolynomial (n k : ℕ) :
    bind₁ (wittMulN p n) (wittPolynomial p ℤ k) = n * wittPolynomial p ℤ k := by
  induction n with
  | zero => simp [wittMulN, zero_mul, bind₁_zero_wittPolynomial]
  | succ n ih =>
    rw [wittMulN, ← bind₁_bind₁, wittAdd, wittStructureInt_prop]
    simp only [map_add, Nat.cast_succ, bind₁_X_right]
    rw [add_mul, one_mul, bind₁_rename, bind₁_rename]
    simp only [ih, Function.uncurry, Function.comp_def, bind₁_X_left, AlgHom.id_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

end

end WittVector

