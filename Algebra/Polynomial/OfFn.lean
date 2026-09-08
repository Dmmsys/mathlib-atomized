/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.List.ToFinsupp
public import Mathlib.LinearAlgebra.Pi
/-!
# `Polynomial.ofFn` and `Polynomial.toFn`

In this file we introduce `ofFn` and `toFn`, two functions that associate a polynomial to the vector
of its coefficients and vice versa. We prove some basic APIs for these functions.

## Main definitions

- `Polynomial.toFn n` associates to a polynomial the vector of its first `n` coefficients.
- `Polynomial.ofFn n` associates to a vector of length `n` the polynomial that has the entries of
  the vector as coefficients.
-/

@[expose] public section

namespace Polynomial

section toFn

variable {R : Type*} [Semiring R]

/-- `toFn n f` is the vector of the first `n` coefficients of the polynomial `f`. -/
/-
**Polynomial.toFn** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：toFn (n : Nat) : R[X] ->ₗ[R] Fin n -> R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toFn n f` is the vector of the first `n` coefficients of the polynomial `f`.
-/
noncomputable def toFn (n : ℕ) : R[X] →ₗ[R] Fin n → R := LinearMap.pi (fun i ↦ lcoeff R i)
/-
**Polynomial.toFn_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFn_zero (n : Nat) : toFn n (0 : R[X]) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFn_zero (n : ℕ) : toFn n (0 : R[X]) = 0 := by simp

end toFn
section ofFn

variable {R : Type*} [Semiring R] [DecidableEq R]

set_option backward.isDefEq.respectTransparency false in
/-- `ofFn n v` is the polynomial whose coefficients are the entries of the vector `v`. -/
/-
**Polynomial.ofFn** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：ofFn (n : Nat) : (Fin n -> R) ->ₗ[R] R[X] where toFun v
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofFn n v` is the polynomial whose coefficients are the entries of the vector `v
`.
-/
def ofFn (n : ℕ) : (Fin n → R) →ₗ[R] R[X] where
  toFun v := ⟨.ofCoeff (List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
  map_smul' x p := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
/-
**Polynomial.ofFn_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFn_zero (n : Nat) : ofFn n (0 : Fin n -> R) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFn_zero (n : ℕ) : ofFn n (0 : Fin n → R) = 0 := by simp

@[simp]
/-
**Polynomial.ofFn_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFn_zero' (v : Fin 0 -> R) : ofFn 0 v = 0
参数：v : Fin 0 -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFn_zero' (v : Fin 0 → R) : ofFn 0 v = 0 := rfl
/-
**Polynomial.ne_zero_of_ofFn_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：ne_zero_of_ofFn_ne_zero {n : Nat} {v : Fin n -> R} (h : ofFn n v != 0) : n
 != 0
参数：h : ofFn n v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_zero_of_ofFn_ne_zero {n : ℕ} {v : Fin n → R} (h : ofFn n v ≠ 0) : n ≠ 0 := by
  contrapose h
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- If `i < n` the `i`-th coefficient of `ofFn n v` is `v i`. -/
@[simp]
/-
**Polynomial.ofFn_coeff_eq_val_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFn_coeff_eq_val_of_lt {n i : Nat} (v : Fin n -> R) (hi : i < n) : (ofFn 
n v).coeff i = v ⟨i, hi⟩
参数：v : Fin n -> R；hi : i < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.coeff_ofFinsupp`：coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p
.coeff
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `i < n` the `i`-th coefficient of `ofFn n v` is `v i`.
-/
theorem ofFn_coeff_eq_val_of_lt {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [ofFn, hi]

set_option backward.isDefEq.respectTransparency false in
/-- If `n ≤ i` the `i`-th coefficient of `ofFn n v` is `0`. -/
@[simp]
/-
**Polynomial.ofFn_coeff_eq_zero_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFn_coeff_eq_zero_of_ge {n i : Nat} (v : Fin n -> R) (hi : n <= i) : (ofF
n n v).coeff i = 0
参数：v : Fin n -> R；hi : n <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.coeff_ofFinsupp`：coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p
.coeff
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.not_lt_of_ge`：∀ {a b : ℕ}, b ≥ a → ¬b < a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `n ≤ i` the `i`-th coefficient of `ofFn n v` is `0`.
-/
theorem ofFn_coeff_eq_zero_of_ge {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) :
    (ofFn n v).coeff i = 0 := by
  simp [ofFn, Nat.not_lt_of_ge hi]

/-- `ofFn n v` has `natDegree` smaller than `n`. -/
/-
**Polynomial.ofFn_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFn_natDegree_lt {n : Nat} (h : 1 <= n) (v : Fin n -> R) : (ofFn n v).nat
Degree < n
参数：h : 1 <= n；v : Fin n -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_iff_le_pred`：∀ {m n : ℕ}, 0 < n → (m < n ↔ m ≤ n - 1)
· 使用定理 `Polynomial.natDegree_le_iff_coeff_eq_zero`：natDegree_le_iff_coeff_eq_zer
o : p.natDegree <= n ↔ forall N : Nat, n < N -> p.coeff N = 0
· 使用定理 `Polynomial.ofFn_coeff_eq_zero_of_ge`：ofFn_coeff_eq_zero_of_ge {n i : Nat
} (v : Fin n -> R) (hi : n <= i) : (ofFn n v).coeff i = 0
· 使用定理 `Nat.le_of_pred_lt`：∀ {n : ℕ} {m : ℕ}, m.pred < n → m ≤ n

--- 原说明 ---
`ofFn n v` has `natDegree` smaller than `n`.
-/
theorem ofFn_natDegree_lt {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  exact fun _ h ↦ ofFn_coeff_eq_zero_of_ge _ <| Nat.le_of_pred_lt h

/-- `ofFn n v` has `degree` smaller than `n`. -/
/-
**Polynomial.ofFn_degree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFn_degree_lt {n : Nat} (v : Fin n -> R) : (ofFn n v).degree < n
参数：v : Fin n -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Batteries.compareOfLessAndEq_eq_lt`：∀ {α : Type u_1} {x y : α} [inst : L
T α] [inst_1 : Decidable (x < y)] [inst_2 : DecidableEq α],   compareOfLessAndEq
 x y = Ordering.lt ↔ x <…
· 使用定理 `Polynomial.natDegree_lt_iff_degree_lt`：natDegree_lt_iff_degree_lt (hp : 
p != 0) : p.natDegree < n ↔ p.degree < ↑n
· 使用定理 `Polynomial.ofFn_natDegree_lt`：ofFn_natDegree_lt {n : Nat} (h : 1 <= n) (
v : Fin n -> R) : (ofFn n v).natDegree < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用引理 `Polynomial.ne_zero_of_ofFn_ne_zero`：ne_zero_of_ofFn_ne_zero {n : Nat} {v
 : Fin n -> R} (h : ofFn n v != 0) : n != 0

--- 原说明 ---
`ofFn n v` has `degree` smaller than `n`.
-/
theorem ofFn_degree_lt {n : ℕ} (v : Fin n → R) : (ofFn n v).degree < n := by
  by_cases h : ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
      <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| ne_zero_of_ofFn_ne_zero h) _
/-
**Polynomial.ofFn_eq_sum_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ofFn_eq_sum_monomial {n : Nat} (v : Fin n -> R) : ofFn n v = ∑ i : Fin n, 
monomial i (v i)
参数：v : Fin n -> R。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.toFinsupp.congr_simp`：∀ {M : Type u_1} [inst : Zero M] (l l_1 : Lis
t M),   l = l_1 →     ∀ {inst_1 : DecidablePred fun x => l.getD x 0 ≠ 0} [inst_2
 : DecidablePre…
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `List.toFinsupp_nil`：toFinsupp_nil [DecidablePred fun i => getD ([] : Lis
t M) i 0 != 0] : toFinsupp ([] : List M) = 0
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.as_sum_range'`：as_sum_range' (p : R[X]) (n : Nat) (hn : p.nat
Degree < n) : p = ∑ i in range n, monomial i (coeff p i)
· 使用定理 `Polynomial.ofFn_natDegree_lt`：ofFn_natDegree_lt {n : Nat} (h : 1 <= n) (
v : Fin n -> R) : (ofFn n v).natDegree < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `Polynomial.ofFn_coeff_eq_val_of_lt`：ofFn_coeff_eq_val_of_lt {n i : Nat} 
(v : Fin n -> R) (hi : i < n) : (ofFn n v).coeff i = v ⟨i, hi⟩
-/
theorem ofFn_eq_sum_monomial {n : ℕ} (v : Fin n → R) : ofFn n v =
    ∑ i : Fin n, monomial i (v i) := by
  by_cases h : n = 0
  · subst h
    simp [ofFn]
  · rw [as_sum_range' (ofFn n v) n <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v]
    simp [Finset.sum_range]

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.toFn_comp_ofFn_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：toFn_comp_ofFn_eq_id (n : Nat) (v : Fin n -> R) : toFn n (ofFn n v) = v
参数：n : Nat；v : Fin n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.coeff_ofFinsupp`：coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p
.coeff
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFn_comp_ofFn_eq_id (n : ℕ) (v : Fin n → R) : toFn n (ofFn n v) = v := by
  simp [toFn, ofFn, LinearMap.pi]
/-
**Polynomial.injective_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：injective_ofFn (n : Nat) : Function.Injective (ofFn (R
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Polynomial.toFn_comp_ofFn_eq_id`：toFn_comp_ofFn_eq_id (n : Nat) (v : Fin
 n -> R) : toFn n (ofFn n v) = v
-/
theorem injective_ofFn (n : ℕ) : Function.Injective (ofFn (R := R) n) :=
  Function.LeftInverse.injective <| toFn_comp_ofFn_eq_id n

omit [DecidableEq R] in
/-
**Polynomial.surjective_toFn** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：surjective_toFn (n : Nat) : Function.Surjective (toFn (R
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Polynomial.toFn_comp_ofFn_eq_id`：toFn_comp_ofFn_eq_id (n : Nat) (v : Fin
 n -> R) : toFn n (ofFn n v) = v
-/
theorem surjective_toFn (n : ℕ) : Function.Surjective (toFn (R := R) n) :=
  open scoped Classical in
  Function.RightInverse.surjective <| toFn_comp_ofFn_eq_id n
/-
**Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：ofFn_comp_toFn_eq_id_of_natDegree_lt {n : Nat} {p : R[X]} (h_deg : p.natDe
gree < n) : ofFn n (toFn n p) = p
参数：h_deg : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.ofFn_coeff_eq_val_of_lt`：ofFn_coeff_eq_val_of_lt {n i : Nat} 
(v : Fin n -> R) (hi : i < n) : (ofFn n v).coeff i = v ⟨i, hi⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.ofFn_coeff_eq_zero_of_ge`：ofFn_coeff_eq_zero_of_ge {n i : Nat
} (v : Fin n -> R) (hi : n <= i) : (ofFn n v).coeff i = 0
-/
theorem ofFn_comp_toFn_eq_id_of_natDegree_lt {n : ℕ} {p : R[X]} (h_deg : p.natDegree < n) :
    ofFn n (toFn n p) = p := by
  ext i
  by_cases! h : i < n
  · simp [h, toFn]
  · have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt <| by lia
    simp [*]

end ofFn

end Polynomial

