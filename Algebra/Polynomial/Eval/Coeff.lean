/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluation of polynomials

This file contains results on the interaction of `Polynomial.eval` and `Polynomial.coeff`
-/

@[expose] public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R →+* S) (x : S)

@[simp]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0) := by
  simp +contextual only [eval₂_eq_sum, zero_pow_eq, mul_ite, mul_zero,
    mul_one, sum, Classical.not_not, mem_support_iff, sum_ite_eq', ite_eq_left_iff, map_zero,
    imp_true_iff]

@[simp]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_C_X : eval₂ C X p = p :=
  Polynomial.induction_on' p (fun p q hp hq => by simp [hp, hq]) fun n x => by
    rw [eval₂_monomial, ← smul_X_eq_monomial, C_mul']

end

section Eval

variable {x : R}

/-
**Polynomial.coeff_zero_eq_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero_eq_eval_zero (p : R[X]) : coeff p 0 = p.eval 0
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_eq_sum`：eval_eq_sum : p.eval x = p.sum fun e a => a * x 
^ e
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem coeff_zero_eq_eval_zero (p : R[X]) : coeff p 0 = p.eval 0 :=
  calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by simp
    _ = p.eval 0 := by
      symm
      rw [eval_eq_sum]
      exact Finset.sum_eq_single _ (fun b _ hb => by simp [zero_pow hb]) (by simp)
/-
**Polynomial.zero_isRoot_iff_coeff_zero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：zero_isRoot_iff_coeff_zero_eq_zero {p : R[X]} : IsRoot p 0 ↔ p.coeff 0 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero_isRoot_iff_coeff_zero_eq_zero {p : R[X]} : IsRoot p 0 ↔ p.coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, IsRoot]

alias ⟨coeff_zero_eq_zero_of_zero_isRoot, zero_isRoot_of_coeff_zero_eq_zero⟩ :=
  zero_isRoot_iff_coeff_zero_eq_zero

end Eval

section Map

variable [Semiring S]
variable (f : R →+* S)

@[simp]
/-
**Polynomial.coeff_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff p n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map.eq_1`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S),   Polynomial.map f = Polynomial.eval₂ (Polynom
ial.C.com…
· 使用定理 `Polynomial.eval₂_def`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring R
] [inst_1 : Semiring S] (f : R →+* S) (x : S) (p : Polynomial R),   Polynomial.e
val₂ f x p…
· 使用定理 `Polynomial.coeff_sum`：coeff_sum [Semiring S] (n : Nat) (f : Nat -> R -> 
S[X]) : coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n
· 使用定理 `Polynomial.sum.eq_1`：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} [
inst_1 : AddCommMonoid S] (p : Polynomial R) (f : ℕ → R → S),   p.sum f = ∑ n ∈ 
p.support…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) := by
  rw [map, eval₂_def, coeff_sum, sum]
  simp_all
/-
**Polynomial.coeff_map_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coeff_map_eq_comp (p : R[X]) (f : R ->+* S) : (p.map f).coeff = f ∘ p.coef
f
参数：p : R[X]；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
-/
lemma coeff_map_eq_comp (p : R[X]) (f : R →+* S) : (p.map f).coeff = f ∘ p.coeff := by
  ext n; exact coeff_map ..
/-
**Polynomial.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.map f).map g = p.map (
g.comp f)
参数：g : S ->+* T；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_map [Semiring T] (g : S →+* T) (p : R[X]) : (p.map f).map g = p.map (g.comp f) :=
  ext (by simp [coeff_map])

@[simp]
/-
**Polynomial.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_id : p.map (RingHom.id _) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_id : p.map (RingHom.id _) = p := by simp [Polynomial.ext_iff, coeff_map]

/-- The polynomial ring over a finite product of rings is isomorphic to
the product of polynomial rings over individual rings. -/
/-
**Polynomial.piEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：piEquiv {ι} [Finite ι] (R : ι -> Type*) [forall i, Semiring (R i)] : (fora
ll i, R i)[X] ≃+* forall i, (R i)[X]
参数：R : ι -> Type*；R i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomial ring over a finite product of rings is isomorphic to
the product of polynomial rings over individual rings.
-/
def piEquiv {ι} [Finite ι] (R : ι → Type*) [∀ i, Semiring (R i)] :
    (∀ i, R i)[X] ≃+* ∀ i, (R i)[X] :=
  .ofBijective (RingHom.pi fun i ↦ mapRingHom (Pi.evalRingHom R i))
    ⟨fun p q h ↦ by ext n i; simpa using congr_arg (fun p ↦ coeff (p i) n) h,
      fun p ↦ ⟨.ofFinsupp <| .ofCoeff <| .ofSupportFinite (fun n i ↦ coeff (p i) n) <|
        (Set.finite_iUnion fun i ↦ (p i).support.finite_toSet).subset fun n hn ↦ by
          simp only [Set.mem_iUnion, Finset.mem_coe, mem_support_iff, Function.mem_support] at hn ⊢
          contrapose! hn; exact funext hn, by ext i n; exact coeff_map _ _⟩⟩
/-
**Polynomial.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_injective (hf : Function.Injective f) : Function.Injective (map f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
-/
theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := fun p q h =>
  ext fun m => hf <| by rw [← coeff_map f, ← coeff_map f, h]
/-
**Polynomial.map_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_injective_iff : Function.Injective (map f) ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
-/
theorem map_injective_iff : Function.Injective (map f) ↔ Function.Injective f :=
  ⟨fun h r r' eq ↦ by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩
/-
**Polynomial.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_surjective (hf : Function.Surjective f) : Function.Surjective (map f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
-/
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := fun p =>
  p.induction_on'
    (by rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩; exact ⟨p + q, Polynomial.map_add f⟩)
    fun n s ↦
    let ⟨r, hr⟩ := hf s
    ⟨monomial n r, by rw [map_monomial f, hr]⟩
/-
**Polynomial.map_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_surjective_iff : Function.Surjective (map f) ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
-/
theorem map_surjective_iff : Function.Surjective (map f) ↔ Function.Surjective f :=
  ⟨fun h s ↦ let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa using congr(coeff $h 0)⟩, map_surjective f⟩

variable {f}
/-
**Polynomial.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p : Polynomial R} [inst_1
 : Semiring S] {f : R →+* S},   Function.Injective ⇑f → (Polynomial.map f p = 0 
↔ p = 0)
参数：Polynomial.map f p = 0 ↔ p = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
-/
protected theorem map_eq_zero_iff (hf : Function.Injective f) : p.map f = 0 ↔ p = 0 :=
  map_eq_zero_iff (mapRingHom f) (map_injective f hf)
/-
**Polynomial.map_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p : Polynomial R} [inst_1
 : Semiring S] {f : R →+* S},   Function.Injective ⇑f → (Polynomial.map f p ≠ 0 
↔ p ≠ 0)
参数：Polynomial.map f p ≠ 0 ↔ p ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Polynomial.map_eq_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
-/
protected theorem map_ne_zero_iff (hf : Function.Injective f) : p.map f ≠ 0 ↔ p ≠ 0 :=
  (Polynomial.map_eq_zero_iff hf).not

variable (f)

@[simp]
/-
**Polynomial.mapRingHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[X]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
-/
theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[X] :=
  RingHom.ext fun _x => map_id

@[simp]
/-
**Polynomial.mapRingHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mapRingHom_comp [Semiring T] (f : S ->+* T) (g : R ->+* S) : (mapRingHom f
).comp (mapRingHom g) = mapRingHom (f.comp g)
参数：f : S ->+* T；g : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
-/
theorem mapRingHom_comp [Semiring T] (f : S →+* T) (g : R →+* S) :
    (mapRingHom f).comp (mapRingHom g) = mapRingHom (f.comp g) :=
  RingHom.ext <| Polynomial.map_map g f
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_map [Semiring T] (g : S →+* T) (x : T) :
    (p.map f).eval₂ g x = p.eval₂ (g.comp f) x := by
  rw [eval₂_eq_eval_map, eval₂_eq_eval_map, map_map]

@[simp]
/-
**Polynomial.eval_zero_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_zero_map (f : R ->+* S) (p : R[X]) : (p.map f).eval 0 = f (p.eval 0)
参数：f : R ->+* S；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_zero_map (f : R →+* S) (p : R[X]) : (p.map f).eval 0 = f (p.eval 0) := by
  simp [← coeff_zero_eq_eval_zero]

@[simp]
/-
**Polynomial.eval_one_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_one_map (f : R ->+* S) (p : R[X]) : (p.map f).eval 1 = f (p.eval 1)
参数：f : R ->+* S；p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem eval_one_map (f : R →+* S) (p : R[X]) : (p.map f).eval 1 = f (p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [one_pow, mul_one, eval_monomial, map_monomial]

@[simp]
/-
**Polynomial.eval_natCast_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_natCast_map (f : R ->+* S) (p : R[X]) (n : Nat) : (p.map f).eval (n :
 S) = f (p.eval n)
参数：f : R ->+* S；p : R[X]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem eval_natCast_map (f : R →+* S) (p : R[X]) (n : ℕ) :
    (p.map f).eval (n : S) = f (p.eval n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_natCast f, eval_monomial, map_monomial, f.map_pow, f.map_mul]

@[simp]
/-
**Polynomial.eval_intCast_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_intCast_map {R S : Type*} [Ring R] [Ring S] (f : R ->+* S) (p : R[X])
 (i : Int) : (p.map f).eval (i : S) = f (p.eval i)
参数：f : R ->+* S；p : R[X]；i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.induction_on'`：∀ {R : Type u} [inst : Semiring R] {motive : P
olynomial R → Prop} (p : Polynomial R),   (∀ (p q : Polynomial R), motive p → mo
tive q → motiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_monomial`：map_monomial {n a} : (monomial n a).map f = mon
omial n (f a)
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
-/
theorem eval_intCast_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (p : R[X]) (i : ℤ) :
    (p.map f).eval (i : S) = f (p.eval i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, Polynomial.map_add, map_add, eval_add]
  | monomial n r => simp only [map_intCast, eval_monomial, map_monomial, map_pow, map_mul]

end Map

section HomEval₂

variable [Semiring S] [Semiring T] (f : R →+* S) (g : S →+* T) (p)

/-
**Polynomial.hom_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) := by
  rw [← eval₂_map, eval₂_at_apply, eval_map]

end HomEval₂

end Semiring

section CommSemiring

section Eval

section

variable [Semiring R] {p q : R[X]} {x : R} [Semiring S] (f : R →+* S)

/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x) :=
  RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

end

section

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

/-
**Polynomial.evalRingHom_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：evalRingHom_zero : evalRingHom 0 = constantCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
-/
theorem evalRingHom_zero : evalRingHom 0 = constantCoeff :=
  DFunLike.ext _ _ fun p => p.coeff_zero_eq_eval_zero.symm

end

end Eval

section Map

/-
**Polynomial.support_map_subset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_map_subset [Semiring R] [Semiring S] (f : R ->+* S) (p : R[X]) : (
map f p).support subseteq p.support
参数：f : R ->+* S；p : R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem support_map_subset [Semiring R] [Semiring S] (f : R →+* S) (p : R[X]) :
    (map f p).support ⊆ p.support := by
  intro x
  contrapose
  simp +contextual
/-
**Polynomial.support_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_map_of_injective [Semiring R] [Semiring S] (p : R[X]) {f : R ->+* 
S} (hf : Function.Injective f) : (map f p).support = p.support
参数：p : R[X]；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem support_map_of_injective [Semiring R] [Semiring S] (p : R[X]) {f : R →+* S}
    (hf : Function.Injective f) : (map f p).support = p.support := by
  simp_rw [Finset.ext_iff, mem_support_iff, coeff_map, ← map_zero f, hf.ne_iff,
    forall_const]

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)
/-
**Polynomial.IsRoot.map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsRoot`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : CommSemiring
 S] {f : R →+* S} {x : R} {p : Polynomial R},   p.IsRoot x → (Polynomial.map f p
).IsRoot (f x)
参数：Polynomial.map f p；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Polynomial.eval₂_hom`：eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x)
· 使用定理 `Polynomial.IsRoot.eq_zero`：∀ {R : Type u} [inst : Semiring R] {p : Polyn
omial R} {x : R}, p.IsRoot x → Polynomial.eval x p = 0
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
theorem IsRoot.map {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot p x) : IsRoot (p.map f) (f x) := by
  rw [IsRoot, eval_map, eval₂_hom, h.eq_zero, f.map_zero]
/-
**Polynomial.IsRoot.of_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsRoot`。
形式化陈述：∀ {S : Type v} [inst : CommSemiring S] {R : Type u_1} [inst_1 : Ring R] {f
 : R →+* S} {x : R} {p : Polynomial R},   (Polynomial.map f p).IsRoot (f x) → Fu
nction.Injective ⇑f → p.IsRoot x
参数：Polynomial.map f p；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero'`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_
9} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [Add
MonoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.eval₂_hom`：eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
-/
theorem IsRoot.of_map {R} [Ring R] {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
    (hf : Function.Injective f) : IsRoot p x := by
  rwa [IsRoot, ← (injective_iff_map_eq_zero' f).mp hf, ← eval₂_hom, ← eval_map]
/-
**Polynomial.isRoot_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isRoot_map_iff {R : Type*} [CommRing R] {f : R ->+* S} {x : R} {p : R[X]} 
(hf : Function.Injective f) : IsRoot (p.map f) (f x) ↔ IsRoot p x
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsRoot.of_map`：∀ {S : Type v} [inst : CommSemiring S] {R : Ty
pe u_1} [inst_1 : Ring R] {f : R →+* S} {x : R} {p : Polynomial R},   (Polynomia
l.map f p).IsR…
· 使用定理 `Polynomial.IsRoot.map`：∀ {R : Type u} {S : Type v} [inst : CommSemiring 
R] [inst_1 : CommSemiring S] {f : R →+* S} {x : R} {p : Polynomial R},   p.IsRoo
t x → (Poly…
-/
theorem isRoot_map_iff {R : Type*} [CommRing R] {f : R →+* S} {x : R} {p : R[X]}
    (hf : Function.Injective f) : IsRoot (p.map f) (f x) ↔ IsRoot p x :=
  ⟨fun h => h.of_map hf, fun h => h.map⟩

end Map

end CommSemiring

end Polynomial

